//! Acceptance test: every module of the Prelude package typechecks
//! standalone, with no other support packages loaded.
//!
//! Concretely, walk `tests/fixtures/packages/prelude/src/` for
//! `.purs` files, parse them all, and run them through
//! `check_many_modules`. Assert zero driver errors, zero
//! per-module diagnostics. If a typechecker change regresses any
//! Prelude module, this test reports the first offending module +
//! diagnostic by name — much more actionable than the umbrella
//! "all passing fixtures" test.
//!
//! Lives in `src/typecheck_db/tests/` (alongside the per-fixture
//! suite) so it runs under the same library-test harness with the
//! same caching + threading conventions.

use std::fs;
use std::path::{Path, PathBuf};

use crate::cst;
use crate::parser::parse;
use crate::typecheck_db::driver_multi::{
    check_many_modules, ModuleInput, MultiModuleError,
};

const PRELUDE_RELATIVE: &str = "tests/fixtures/packages/prelude/src";

fn prelude_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(PRELUDE_RELATIVE)
}

fn collect_purs_files(root: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    if !root.exists() {
        return out;
    }
    let entries = match fs::read_dir(root) {
        Ok(e) => e,
        Err(_) => return out,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name == ".spago" || name == "output" || name == ".psc-package" {
            continue;
        }
        if path.is_dir() {
            out.extend(collect_purs_files(&path));
        } else if path.extension().and_then(|s| s.to_str()) == Some("purs") {
            out.push(path);
        }
    }
    out
}

fn module_name_of(m: &cst::Module) -> String {
    m.name
        .value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
}

#[test]
#[ignore = "typechecker still has gaps that surface in Prelude (e.g. Data.Ord); \
            run with `cargo test -- --ignored prelude_typechecks_clean` as a \
            forcing function until the gaps close"]
fn prelude_typechecks_clean() {
    // Spawn on a 64MB-stack thread — Prelude's mutual-instance
    // chains exercise deep typechecker recursion that overflows
    // the default test-thread stack.
    let join_result = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(run)
        .expect("spawn prelude-check thread")
        .join();
    if let Err(payload) = join_result {
        // Propagate the inner panic message so the test failure
        // banner names the actual root cause instead of "Any {..}".
        let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
            (*s).to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "prelude check thread panicked (non-string payload)".to_string()
        };
        panic!("{msg}");
    }
}

fn run() {
    let root = prelude_root();
    let files = collect_purs_files(&root);
    assert!(
        !files.is_empty(),
        "no .purs files under {} — fixture data missing?",
        root.display(),
    );

    let mut inputs: Vec<ModuleInput> = Vec::with_capacity(files.len());
    for file in &files {
        let src = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => panic!("failed to read {}: {e}", file.display()),
        };
        let module = match parse(&src) {
            Ok(m) => m,
            Err(e) => panic!("parse error in {}: {e:?}", file.display()),
        };
        let name = module_name_of(&module);
        inputs.push(ModuleInput::new(name, src, module));
    }

    let report = check_many_modules(inputs);

    // Driver-level errors first: a cycle or unknown-module error
    // means subsequent module diagnostics aren't trustworthy.
    for e in &report.errors {
        match e {
            MultiModuleError::CycleInModules(cycle) => {
                panic!(
                    "Prelude has a module cycle: {}",
                    cycle.join(" \u{2194} "),
                );
            }
            other => panic!("driver error checking Prelude: {other:?}"),
        }
    }

    // Per-module: surface the first offending module and the
    // first diagnostic on it. Test output stays focused on a
    // single root cause to drive iterative fixes.
    for result in &report.results {
        if let Some(err) = &result.inference_error {
            panic!("Prelude::{}: inference error: {err:?}", result.name);
        }
        if let Some(ie) = result.import_errors.first() {
            panic!(
                "Prelude::{}: import error: {:?}",
                result.name, ie.kind,
            );
        }
        if let Some(ne) = result.exhaustiveness_errors.first() {
            panic!(
                "Prelude::{}: non-exhaustive {} (missing {:?})",
                result.name, ne.type_name, ne.missing,
            );
        }
        if let Some(ce) = result.constraint_errors.first() {
            panic!(
                "Prelude::{}: constraint {:?} on {}",
                result.name, ce.kind, ce.constraint.class.name,
            );
        }
    }
}
