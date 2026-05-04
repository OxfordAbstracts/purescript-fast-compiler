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
                    "{}: constraint {:?}: {}",
                    r.name, ce.kind, ce.constraint.class.name,
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

#[test]
#[ignore = "reproducer for stack overflow on Hylograph.Kernel.D3.Simulation"]
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
    eprintln!("=== typecheck_db package-set summary ===");
    eprintln!("modules processed: {total}");
    eprintln!("passing:           {passing}");
    eprintln!("failing:           {failing}");
    eprintln!("driver errors:     {}", driver_errors.len());
    eprintln!("total wall time:   {:.2?}", started.elapsed());
    if !error_counts.is_empty() {
        let mut sorted_counts: Vec<_> = error_counts.iter().collect();
        sorted_counts.sort_by(|a, b| b.1.cmp(a.1));
        eprintln!("\nError distribution:");
        for (kind, count) in &sorted_counts {
            eprintln!("  {:>4} {}", count, kind);
        }
    }
    if !failures.is_empty() {
        eprintln!("\nFirst 40 failing modules:");
        for f in failures.iter().take(40) {
            eprintln!("  {}: {}", f.name, f.reasons.join("; "));
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
