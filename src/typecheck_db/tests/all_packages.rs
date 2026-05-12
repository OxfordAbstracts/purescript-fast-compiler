//! Acceptance test: run `typecheck_db` against every package
//! source under `tests/fixtures/packages/<pkg>/src/**.purs` and
//! assert no errors.
//!
//! Mirrors `tests/build.rs::build_all_packages` but drives the new
//! `typecheck_db` pipeline via `check_many_modules`. Discovery
//! rules match the legacy test (only packages with a `src/`
//! subdirectory; `.purs` files inside that tree).
//!
//! Discovery / parsing helpers live in `typecheck_db::test_support`
//! so the criterion bench under `benches/` can share them.
//! Runtime is dominated by typechecking ~4800 modules.

use std::fs;

use crate::parser::parse;
use crate::typecheck_db::driver_multi::{
    check_many_modules, ModuleInput, MultiModuleError,
};
use crate::typecheck_db::test_support::{
    extract_panic_msg, gather_package_src_sources, module_name_of,
    package_modules_by_name, transitive_closure_of,
};

const FIXTURES_ROOT: &str = "tests/fixtures";

/// Focused reproducer: typecheck a single package module + its
/// transitive closure. Used while bisecting all-packages failures.
fn check_single_package_module(target: &str) -> Result<(), String> {
    let pkgs = package_modules_by_name();
    if !pkgs.contains_key(target) {
        return Err(format!("module {target} not found in packages"));
    }
    let closure = transitive_closure_of(target, &pkgs);
    eprintln!(
        "Checking {} (closure of {} modules)",
        target,
        closure.len(),
    );
    let started = std::time::Instant::now();
    let report = check_many_modules(closure);
    eprintln!("Closure check completed in {:.2?}", started.elapsed());

    for e in &report.errors {
        return Err(format!("driver error: {e:?}"));
    }
    for r in &report.results {
        if r.name == target {
            if let Some(err) = &r.inference_error {
                return Err(format!("{}: infer: {err:?}", r.name));
            }
            if let Some(ce) = r.constraint_errors.first() {
                return Err(format!(
                    "{}: constraint {:?}: {} (args={:?}, span={:?}, decl_span={:?})",
                    r.name,
                    ce.kind,
                    ce.constraint.class.name,
                    ce.constraint.args,
                    ce.span,
                    ce.decl_span,
                ));
            }
            if let Some(ke) = r.kind_errors.first() {
                return Err(format!("{}: kind: {:?}", r.name, ke.kind));
            }
            if let Some(ie) = r.import_errors.first() {
                return Err(format!("{}: import: {:?}", r.name, ie.kind));
            }
        }
    }
    Ok(())
}

/// Print a list of failing modules, one per line, to stderr. Used
/// during gap-closing work to find which packages are broken
/// without running the full all_packages_typecheck (which uses
/// >10GB memory for the per-result aggregation across 4800+
/// modules). Run with:
///   cargo test --release --lib all_packages_failing_modules \
///     -- --ignored --nocapture
#[test]
#[ignore = "diagnostic helper — prints failing modules; not a pass/fail test"]
fn all_packages_failing_modules() {
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .name("all_packages_failing".into())
            .stack_size(512 * 1024 * 1024)
            .spawn(|| {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    run_all_packages_failing_summary,
                ));
                std::panic::set_hook(previous);
                match outcome {
                    Ok(res) => res,
                    Err(payload) => Err(format!("panicked: {}", extract_panic_msg(payload))),
                }
            })
            .expect("spawn fixture-check thread")
            .join();
    let inner = match join_result {
        Ok(r) => r,
        Err(payload) => Err(format!(
            "worker thread lost at top level: {}",
            extract_panic_msg(payload),
        )),
    };
    if let Err(msg) = inner {
        panic!("all_packages_failing_modules: {msg}");
    }
}

/// Streamlined acceptance summary. Doesn't accumulate per-result
/// reasons — just prints the (module, error_kind) pair as soon as
/// it's known. Memory stays bounded.
fn run_all_packages_failing_summary() -> Result<(), String> {
    let started = std::time::Instant::now();
    let files = gather_package_src_sources();
    if files.is_empty() {
        return Err(format!(
            "no .purs files found under {}/packages/*/src",
            FIXTURES_ROOT,
        ));
    }
    eprintln!("Discovered {} files in {:.2?}", files.len(), started.elapsed());
    let mut parsed: Vec<ModuleInput> = Vec::with_capacity(files.len());
    let mut seen_names: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for file in &files {
        let src = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => return Err(format!("failed to read {}: {e}", file.display())),
        };
        let module = match parse(&src) {
            Ok(m) => m,
            Err(e) => return Err(format!("parse error in {}: {e:?}", file.display())),
        };
        let name = module_name_of(&module);
        if seen_names.insert(name.clone()) {
            parsed.push(ModuleInput::new(name, src, module));
        }
    }
    let total = parsed.len();
    eprintln!("Parsed {} modules in {:.2?}", total, started.elapsed());
    let report = check_many_modules(parsed);
    eprintln!(
        "Multi-module check completed in {:.2?}",
        started.elapsed(),
    );
    for e in &report.errors {
        eprintln!("DRIVER_ERROR: {e:?}");
    }
    let mut failing = 0;
    for result in &report.results {
        let mut reasons: Vec<String> = Vec::new();
        if let Some(ve) = result.validation_errors.first() {
            reasons.push(format!("validation:{:?}", ve.kind));
        }
        if let Some(ke) = result.kind_errors.first() {
            reasons.push(format!("kind:{:?}", ke.kind));
        }
        if let Some(ce) = result.coercible_errors.first() {
            reasons.push(format!("coercible:{:?}", ce.kind));
        }
        if let Some(err) = &result.inference_error {
            reasons.push(format!("infer:{err:?}"));
        }
        if let Some(ie) = result.import_errors.first() {
            reasons.push(format!("import:{:?}", ie.kind));
        }
        if let Some(ce) = result.constraint_errors.first() {
            reasons.push(format!(
                "constraint:{:?} primary:{:?} decl_span:{:?}",
                ce.kind, ce.span, ce.decl_span,
            ));
        }
        if !reasons.is_empty() {
            failing += 1;
            eprintln!("FAIL: {} | {}", result.name, reasons.join(" ; "));
        }
    }
    eprintln!("=== summary: {}/{} failing in {:.2?} ===", failing, total, started.elapsed());
    Ok(())
}

/// Reproducer for the Test.PMock 17-second hot module. Drops to a
/// fast iteration loop. Includes a 5-second wall-clock budget that
/// will fail the test if perf regresses.
#[test]
fn repro_pmock_perf() {
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .name("repro_pmock".into())
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || {
                        let started = std::time::Instant::now();
                        let res = check_single_package_module("Test.PMock");
                        let elapsed = started.elapsed();
                        if let Err(msg) = res {
                            return Err(msg);
                        }
                        if elapsed > std::time::Duration::from_secs(5) {
                            return Err(format!(
                                "Test.PMock took {:?} — exceeds 5s budget",
                                elapsed,
                            ));
                        }
                        Ok(())
                    },
                ));
                std::panic::set_hook(previous);
                match outcome {
                    Ok(res) => res,
                    Err(payload) => Err(format!("panicked: {}", extract_panic_msg(payload))),
                }
            })
            .expect("spawn repro thread")
            .join();
    let inner = match join_result {
        Ok(r) => r,
        Err(payload) => Err(format!(
            "thread lost at top level: {}",
            extract_panic_msg(payload),
        )),
    };
    if let Err(msg) = inner {
        panic!("repro_pmock_perf: {msg}");
    }
}

/// Repro for the Blessed.UI.Base.Element.Property module that
/// triggered a 9GB memory blow-up during the all-packages sweep.
/// The module has heavily polymorphic getter/setter signatures
/// with `Row.Cons prop a r' PropertiesRow` constraints — a deep
/// concrete row + several free unif positions.
#[test]
#[ignore = "Blessed.UI.Base.Element.Property triggered OOM during all-packages sweep — track here while triaging."]
fn repro_blessed_property_perf() {
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .name("repro_blessed_property".into())
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || {
                        let started = std::time::Instant::now();
                        let res = check_single_package_module(
                            "Blessed.UI.Base.Element.Property",
                        );
                        let elapsed = started.elapsed();
                        if let Err(msg) = res {
                            return Err(msg);
                        }
                        if elapsed > std::time::Duration::from_secs(10) {
                            return Err(format!(
                                "Blessed.UI.Base.Element.Property took {:?} — exceeds 10s budget",
                                elapsed,
                            ));
                        }
                        Ok(())
                    },
                ));
                std::panic::set_hook(previous);
                match outcome {
                    Ok(res) => res,
                    Err(payload) => Err(format!("panicked: {}", extract_panic_msg(payload))),
                }
            })
            .expect("spawn repro thread")
            .join();
    let inner = match join_result {
        Ok(r) => r,
        Err(payload) => Err(format!(
            "thread lost at top level: {}",
            extract_panic_msg(payload),
        )),
    };
    if let Err(msg) = inner {
        panic!("repro_blessed_property_perf: {msg}");
    }
}

/// Reproducer for the Deku.DOM 26-second hot module.
#[test]
#[ignore = "Deku.DOM closure is still 35s; module itself is 5s. Track here while triaging."]
fn repro_deku_dom_perf() {
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .name("repro_deku_dom".into())
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || {
                        let started = std::time::Instant::now();
                        let res = check_single_package_module("Deku.DOM");
                        let elapsed = started.elapsed();
                        if let Err(msg) = res {
                            return Err(msg);
                        }
                        if elapsed > std::time::Duration::from_secs(10) {
                            return Err(format!(
                                "Deku.DOM took {:?} — exceeds 10s budget",
                                elapsed,
                            ));
                        }
                        Ok(())
                    },
                ));
                std::panic::set_hook(previous);
                match outcome {
                    Ok(res) => res,
                    Err(payload) => Err(format!("panicked: {}", extract_panic_msg(payload))),
                }
            })
            .expect("spawn repro thread")
            .join();
    let inner = match join_result {
        Ok(r) => r,
        Err(payload) => Err(format!(
            "thread lost at top level: {}",
            extract_panic_msg(payload),
        )),
    };
    if let Err(msg) = inner {
        panic!("repro_deku_dom_perf: {msg}");
    }
}

#[test]
#[ignore = "diagnostic — compose direction"]
fn repro_next_router() {
    check_single_package_module("Next.Router").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
#[ignore = "diagnostic — rank2 ST cluster"]
fn repro_foreign_object() {
    check_single_package_module("Foreign.Object").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
#[ignore = "diagnostic — rank2 ST cluster"]
fn repro_jelly_render() {
    check_single_package_module("Jelly.Render").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
#[ignore = "diagnostic — rank2 ST cluster"]
fn repro_routing_duplex_generic() {
    check_single_package_module("Routing.Duplex.Generic").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
fn repro_hylograph_shape_arc() {
    let inner = check_single_package_module("Hylograph.Shape.Arc");
    if let Err(msg) = inner {
        panic!("repro_hylograph_shape_arc: {msg}");
    }
}

#[test]
fn repro_hylograph_d3_simulation() {
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .name("repro_hylograph".into())
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || check_single_package_module("Hylograph.Kernel.D3.Simulation"),
                ));
                std::panic::set_hook(previous);
                match outcome {
                    Ok(res) => res,
                    Err(payload) => Err(format!("panicked: {}", extract_panic_msg(payload))),
                }
            })
            .expect("spawn repro thread")
            .join();
    let inner = match join_result {
        Ok(r) => r,
        Err(payload) => Err(format!(
            "thread lost at top level: {}",
            extract_panic_msg(payload),
        )),
    };
    if let Err(msg) = inner {
        panic!("repro_hylograph_d3_simulation: {msg}");
    }
}

#[test]
#[ignore = "diagnostic — MonadThrow Error Effect cluster"]
fn repro_webb_monad_prelude() {
    check_single_package_module("Webb.Monad.Prelude").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
#[ignore = "diagnostic — Eq String solver issue"]
fn repro_node_fs_constants() {
    check_single_package_module("Node.FS.Constants").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
#[ignore = "diagnostic — rank-2 forall Parent z => z -> r"]
fn repro_webb_parent_wrap() {
    check_single_package_module("Webb.AffList.Data.Node.Parent").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
#[ignore = "diagnostic — point-free rank-N (sub-cluster A)"]
fn repro_fft_nth() {
    check_single_package_module("Data.Complex.FFT").unwrap_or_else(|m| panic!("{m}"));
}

#[test]
#[ignore = "diagnostic — Doc Infinite (sub-cluster B)"]
fn repro_dodo_appendspacebreak() {
    check_single_package_module("Dodo").unwrap_or_else(|m| panic!("{m}"));
}

/// Bisect: import the real Prelude/etc. but only define `nth`.
#[test]
#[ignore = "diagnostic — bisect FFT nth"]
fn repro_synth_fft_nth_minimal() {
    use crate::typecheck_db::driver_multi::{check_many_modules, ModuleInput};
    use crate::typecheck_db::tests::harness::{module_name, parse_source};
    use crate::typecheck_db::test_support::{
        gather_package_src_sources, package_modules_by_name, transitive_closure_of,
    };
    let main = r#"module Test where

import Prelude
import Data.Array ((!!)) as Array
import Data.Maybe (fromJust)
import Partial.Unsafe (unsafePartial)

nth :: forall a. Array a -> Int -> a
nth xs i =  unsafePartial fromJust $ xs Array.!! i

infixl 6 nth as !!
"#;
    // Base closure for Test — pull in what `import` mentions.
    let pkgs = package_modules_by_name();
    let mut closure: Vec<ModuleInput> = Vec::new();
    for target in &["Prelude", "Data.Array", "Data.Maybe", "Partial.Unsafe"] {
        for m in transitive_closure_of(target, &pkgs) {
            if !closure.iter().any(|c| c.name == m.name) {
                closure.push(m);
            }
        }
    }
    let m = parse_source(main);
    closure.push(ModuleInput::new(module_name(&m), main, m));
    let report = check_many_modules(closure);
    if let Some(err) = report.errors.first() {
        panic!("driver: {err:?}");
    }
    for r in &report.results {
        if r.name == "Test" {
            if let Some(err) = &r.inference_error {
                panic!("inference error in Test: {err:?}");
            }
        }
    }
}

/// Tiny synthetic for sub-cluster A. Mimics
/// `unsafePartial fromJust $ xs !! i` from FFT — the rank-2
/// `unsafePartial :: (Partial => a) -> a` applied to `fromJust ::
/// Partial => Maybe b -> b` should NOT trigger an `?N ~ Maybe ?N`
/// occurs check.
#[test]
#[ignore = "diagnostic — synthetic for unsafePartial fromJust"]
fn repro_synth_unsafe_partial_fromjust() {
    use crate::typecheck_db::driver_multi::{check_many_modules, ModuleInput};
    use crate::typecheck_db::tests::harness::{module_name, parse_source};
    let other = r#"module Other where

data Maybe a = Nothing | Just a

foreign import fromJust :: forall a. Partial => Maybe a -> a
foreign import _unsafePartial :: forall a b. a -> b

unsafePartial :: forall a. (Partial => a) -> a
unsafePartial = _unsafePartial

foreign import index :: forall a. Array a -> Int -> Maybe a

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

applyOp :: forall a b. (a -> b) -> a -> b
applyOp = apply

indexOp :: forall a. Array a -> Int -> Maybe a
indexOp = index

infixr 0 applyOp as $
infixl 8 indexOp as !!
"#;
    let main = r#"module Test where

import Other (unsafePartial, fromJust, ($))
import Other ((!!)) as Arr

nth :: forall a. Array a -> Int -> a
nth xs i = unsafePartial fromJust $ xs Arr.!! i
"#;
    let mut parsed: Vec<ModuleInput> = Vec::new();
    for src in &[other, main] {
        let m = parse_source(src);
        parsed.push(ModuleInput::new(module_name(&m), *src, m));
    }
    let report = check_many_modules(parsed);
    if let Some(err) = report.errors.first() {
        panic!("driver: {err:?}");
    }
    for r in &report.results {
        if r.name == "Test" {
            if let Some(err) = &r.inference_error {
                panic!("inference error in Test: {err:?}");
            }
        }
    }
}

#[test]
#[ignore = "end-to-end acceptance target; gap-closing work in progress"]
fn all_packages_typecheck() {
    // Heavy AST walks across 4800+ modules routinely overflow the
    // default 2MB thread stack. Mirror the other heavy tests and
    // run on a 512MB stack inside `catch_unwind`. NB: stack-overflow
    // SIGSEGVs still abort the process — `catch_unwind` only traps
    // ordinary panics.
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .name("all_packages_check".into())
            .stack_size(512 * 1024 * 1024)
            .spawn(|| {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    run_all_packages_check,
                ));
                std::panic::set_hook(previous);
                match outcome {
                    Ok(res) => res,
                    Err(payload) => Err(format!("panicked: {}", extract_panic_msg(payload))),
                }
            })
            .expect("spawn fixture-check thread")
            .join();

    let inner = match join_result {
        Ok(r) => r,
        Err(payload) => Err(format!(
            "worker thread lost at top level: {}",
            extract_panic_msg(payload),
        )),
    };
    if let Err(msg) = inner {
        panic!("typecheck_db all-packages: {msg}");
    }
}

fn run_all_packages_check() -> Result<(), String> {
    let started = std::time::Instant::now();

    let files = gather_package_src_sources();
    if files.is_empty() {
        return Err(format!(
            "no .purs files found under {}/packages/*/src",
            FIXTURES_ROOT,
        ));
    }
    eprintln!(
        "Discovered {} package source files in {:.2?}",
        files.len(),
        started.elapsed(),
    );

    // Parse every file. Bail on the first parse error — parsing
    // is not this pass's responsibility.
    let parse_started = std::time::Instant::now();
    let mut parsed: Vec<ModuleInput> = Vec::with_capacity(files.len());
    let mut seen_names: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for file in &files {
        let src = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => return Err(format!("failed to read {}: {e}", file.display())),
        };
        let module = match parse(&src) {
            Ok(m) => m,
            Err(e) => return Err(format!("parse error in {}: {e:?}", file.display())),
        };
        let name = module_name_of(&module);
        // Diamond-dep duplicates: keep the first parse, skip the
        // rest (the typechecker requires exactly one copy per name).
        if seen_names.insert(name.clone()) {
            parsed.push(ModuleInput::new(name, src, module));
        }
    }
    let total = parsed.len();
    eprintln!(
        "Parsed {} modules in {:.2?}",
        total,
        parse_started.elapsed(),
    );

    let check_started = std::time::Instant::now();
    let report = check_many_modules(parsed);
    eprintln!(
        "Multi-module check completed in {:.2?}",
        check_started.elapsed(),
    );

    // Driver-level errors first.
    let mut driver_errors: Vec<String> = Vec::new();
    for e in &report.errors {
        match e {
            MultiModuleError::CycleInModules(cycle) => {
                driver_errors.push(format!("cycle: {}", cycle.join(" \u{2194} ")));
            }
            other => driver_errors.push(format!("{other:?}")),
        }
    }

    // Per-module diagnostics. Aggregate across results so the
    // summary surfaces the entire gap.
    struct ModuleFailure {
        name: String,
        reasons: Vec<String>,
    }
    let mut failures: Vec<ModuleFailure> = Vec::new();
    let mut error_counts: std::collections::HashMap<&'static str, usize> =
        std::collections::HashMap::new();

    for result in &report.results {
        let mut reasons: Vec<String> = Vec::new();
        if let Some(ve) = result.validation_errors.first() {
            *error_counts.entry("Validation").or_default() += 1;
            reasons.push(format!("validation: {:?}", ve.kind));
        }
        if let Some(ke) = result.kind_errors.first() {
            *error_counts.entry("Kind").or_default() += 1;
            reasons.push(format!("kind: {:?}", ke.kind));
        }
        if let Some(ce) = result.coercible_errors.first() {
            *error_counts.entry("Coercible").or_default() += 1;
            reasons.push(format!("coercible: {:?}", ce.kind));
        }
        if let Some(err) = &result.inference_error {
            *error_counts.entry("Inference").or_default() += 1;
            reasons.push(format!("infer: {err:?}"));
        }
        if let Some(ie) = result.import_errors.first() {
            *error_counts.entry("Import").or_default() += 1;
            reasons.push(format!("import: {:?}", ie.kind));
        }
        if let Some(ce) = result.constraint_errors.first() {
            *error_counts.entry("Constraint").or_default() += 1;
            reasons.push(format!(
                "constraint {:?}: {}",
                ce.kind, ce.constraint.class.name,
            ));
        }
        // Non-exhaustive patterns are warnings in the reference
        // compiler — mirror `build_all_packages` and don't fail
        // on them.
        let _ = result.exhaustiveness_errors;

        if !reasons.is_empty() {
            failures.push(ModuleFailure {
                name: result.name.clone(),
                reasons,
            });
        }
    }

    let failing = failures.len();
    let passing = total.saturating_sub(failing);
    // Write summary to a file so it can be captured outside of test harness.
    let dump_path = std::env::var("ALL_PACKAGES_DUMP_FILE")
        .unwrap_or_else(|_| "/tmp/all_packages_summary.txt".to_string());
    let mut dump_file = std::fs::File::create(&dump_path)
        .ok();
    macro_rules! out {
        ($($arg:tt)*) => {
            eprintln!($($arg)*);
            if let Some(ref mut f) = dump_file {
                use std::io::Write;
                let _ = writeln!(f, $($arg)*);
            }
        };
    }
    out!("=== typecheck_db package-set summary ===");
    out!("modules processed: {total}");
    out!("passing:           {passing}");
    out!("failing:           {failing}");
    out!("driver errors:     {}", driver_errors.len());
    out!("total wall time:   {:.2?}", started.elapsed());
    if !error_counts.is_empty() {
        let mut sorted_counts: Vec<_> = error_counts.iter().collect();
        sorted_counts.sort_by(|a, b| b.1.cmp(a.1));
        out!("\nError distribution:");
        for (kind, count) in &sorted_counts {
            out!("  {:>4} {}", count, kind);
        }
    }
    if !failures.is_empty() {
        // detailed per-error-kind counts within each category
        let mut detail_counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        for f in &failures {
            for r in &f.reasons {
                let key = r.split('(').next().unwrap_or(r).trim().to_string();
                *detail_counts.entry(key).or_default() += 1;
            }
        }
        let mut sorted_detail: Vec<_> = detail_counts.iter().collect();
        sorted_detail.sort_by(|a, b| b.1.cmp(a.1));
        out!("\nDetailed error breakdown:");
        for (kind, count) in &sorted_detail {
            out!("  {:>4} {}", count, kind);
        }
        let limit = std::env::var("ALL_PACKAGES_SHOW").ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(40);
        out!("\nFirst {} failing modules:", limit);
        for f in failures.iter().take(limit) {
            out!("  {}: {}", f.name, f.reasons.join("; "));
        }
    }

    if !driver_errors.is_empty() {
        return Err(format!(
            "driver errors:\n  {}",
            driver_errors.join("\n  "),
        ));
    }
    if !failures.is_empty() {
        return Err(format!(
            "{failing}/{total} modules failed acceptance check",
        ));
    }
    Ok(())
}
