//! Per-build-unit tests for `tests/fixtures/original-compiler/passing/`.
//!
//! Each `.purs` file at the top level of that directory is one
//! "build unit". A same-named directory (e.g. `2018.purs` +
//! `2018/`) holds additional supporting modules that compile
//! together with the primary file.
//!
//! The list of build units lives in [passing_fixtures_list.rs],
//! one `check_build_unit!(ident, "fixture")` (or
//! `check_build_unit_ignored!(ident, "fixture", "reason")`) per
//! line. `include!`d at the bottom of this file so the macros and
//! the `run_build_unit` helper are in scope when each entry
//! expands.

use ntest_timeout::timeout;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::cst;
use crate::parser::parse;
use crate::typecheck_db::driver::TypecheckDb;
use crate::typecheck_db::driver_multi::{
    check_many_modules_with_db, ModuleInput, MultiModuleError,
};

const FIXTURES_ROOT: &str = "tests/fixtures";

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn passing_root() -> PathBuf {
    manifest_dir()
        .join(FIXTURES_ROOT)
        .join("original-compiler")
        .join("passing")
}

fn packages_root() -> PathBuf {
    manifest_dir().join(FIXTURES_ROOT).join("packages")
}

/// Recursively gather every `.purs` file under `root`, skipping
/// Spago / build caches.
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

/// All package modules already parsed into `ModuleInput`, cached
/// so the 394 generated tests don't each pay the
/// "read + parse ~8888 package files" cost. `cst::Module: Clone`,
/// so we hand each test its own clone.
fn package_modules() -> &'static Vec<ModuleInput> {
    static CACHE: OnceLock<Vec<ModuleInput>> = OnceLock::new();
    CACHE.get_or_init(|| {
        let root = packages_root();
        let files = collect_purs_files(&root);
        let mut out = Vec::with_capacity(files.len());
        for file in files {
            let src = match fs::read_to_string(&file) {
                Ok(s) => s,
                Err(e) => panic!("failed to read package source {}: {e}", file.display()),
            };
            let module = match parse(&src) {
                Ok(m) => m,
                Err(e) => panic!("parse error in {}: {e:?}", file.display()),
            };
            let name = module_name_of(&module);
            out.push(ModuleInput::new(name, src, module));
        }
        out
    })
}

/// State shared across every fixture test. Built once on first
/// access: open an in-memory `TypecheckDb`, type-check the entire
/// package set against it (so subsequent tests cache-hit on every
/// unchanged package decl), and record any panic as
/// `warmup_error`. A poisoned or broken warmup short-circuits
/// every test with the same error message — thousands of tests
/// don't each re-hit the same typechecker bug.
struct SharedState {
    db: Mutex<TypecheckDb>,
    /// `Some` iff package warmup panicked; holds the panic
    /// message so tests can report it without re-running.
    warmup_error: Option<String>,
}

fn shared_state() -> &'static SharedState {
    static STATE: OnceLock<SharedState> = OnceLock::new();
    STATE.get_or_init(|| {
        // Warmup runs on a dedicated 64MB-stack thread — same as
        // the per-test thread below. Prelude-driven AST walks
        // legitimately go deep and overflow the default 2–8MB
        // test-thread stack.
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let mut db =
                    TypecheckDb::open_in_memory().expect("open in-memory TypecheckDb");
                let pkgs = package_modules();
                let mut inputs: Vec<ModuleInput> = Vec::with_capacity(pkgs.len());
                for m in pkgs {
                    inputs.push(ModuleInput::new(
                        m.name.clone(),
                        m.source.clone(),
                        m.module.clone(),
                    ));
                }
                let previous_hook = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || check_many_modules_with_db(&mut db, inputs),
                ));
                std::panic::set_hook(previous_hook);
                let warmup_error = match outcome {
                    Ok(_) => None,
                    Err(payload) => Some(format!(
                        "package warmup panicked: {}",
                        extract_panic_msg(payload),
                    )),
                };
                (db, warmup_error)
            })
            .expect("spawn warmup thread");
        let (db, warmup_error) = handle.join().unwrap_or_else(|payload| {
            (
                TypecheckDb::open_in_memory().expect("fallback TypecheckDb"),
                Some(format!(
                    "package warmup thread crashed: {}",
                    extract_panic_msg(payload),
                )),
            )
        });
        SharedState { db: Mutex::new(db), warmup_error }
    })
}

/// Gather the build unit's own source files: the primary `.purs`
/// plus every `.purs` inside the same-named directory (if any).
fn build_unit_sources(name: &str) -> Vec<(PathBuf, String)> {
    let root = passing_root();
    let primary = root.join(format!("{name}.purs"));
    if !primary.exists() {
        panic!(
            "build unit primary file missing: {} (looked under {})",
            primary.display(),
            root.display(),
        );
    }
    let mut out: Vec<(PathBuf, String)> = Vec::new();
    let primary_src = match fs::read_to_string(&primary) {
        Ok(s) => s,
        Err(e) => panic!("failed to read primary {}: {e}", primary.display()),
    };
    out.push((primary, primary_src));

    let support_dir = root.join(name);
    if support_dir.is_dir() {
        for path in collect_purs_files(&support_dir) {
            let src = match fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => panic!("failed to read support {}: {e}", path.display()),
            };
            out.push((path, src));
        }
    }
    out
}

/// Extract the canonical module name from a parsed module CST.
fn module_name_of(m: &cst::Module) -> String {
    m.name
        .value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
}

/// Extract a readable string from a panic payload. Handles the
/// two common shapes (`&'static str` and `String`) plus a
/// fallback for exotic payloads.
fn extract_panic_msg(payload: Box<dyn std::any::Any + Send + 'static>) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "panicked (non-string payload)".to_string()
    }
}

pub(crate) fn run_build_unit(name: &str) {
    let state = shared_state();
    if let Some(msg) = &state.warmup_error {
        // Every test fails with the same message until the
        // underlying typechecker bug is fixed — fast + obvious.
        eprintln!("build unit {name}: {msg}");
        panic!("build unit {name}: {msg}");
    }

    // Spawn on a dedicated 64MB-stack thread — some fixtures +
    // Prelude trigger deep AST walks that overflow the default
    // stack. `catch_unwind` inside the thread silences the
    // default panic-print so we control the output formatting.
    let owned_name = name.to_string();
    let join_result: Result<Result<Vec<String>, String>, _> =
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || run_inner(&owned_name),
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
    match inner {
        Ok(_errors) => { /* success */ }
        Err(msg) => {
            eprintln!("build unit {name}: {msg}");
            panic!("build unit {name}: {msg}");
        }
    }
}

/// Runs the actual check. Returns `Err(msg)` on a detected
/// diagnostic; `Ok(_)` on a clean report.
fn run_inner(name: &str) -> Result<Vec<String>, String> {
    // Build-unit's own files: parsed fresh each test (fast — at
    // most a handful per build unit). Overlaid onto the cached
    // package-module map.
    let pkgs = package_modules();
    let mut by_name: std::collections::HashMap<String, ModuleInput> =
        std::collections::HashMap::with_capacity(pkgs.len() + 4);
    for m in pkgs {
        by_name.insert(
            m.name.clone(),
            ModuleInput::new(m.name.clone(), m.source.clone(), m.module.clone()),
        );
    }
    for (path, src) in build_unit_sources(name) {
        let module = match parse(&src) {
            Ok(m) => m,
            Err(e) => return Err(format!("parse error in {}: {e:?}", path.display())),
        };
        let mod_name = module_name_of(&module);
        by_name.insert(mod_name.clone(), ModuleInput::new(mod_name, src, module));
    }
    let parsed: Vec<ModuleInput> = by_name.into_values().collect();

    // The shared DB is already pre-warmed with packages — this
    // call only does real work for the few build-unit modules.
    // `unwrap_or_else(|p| p.into_inner())` recovers from a
    // poisoned mutex (a previous test's panic) so one failure
    // doesn't poison the entire run.
    let state = shared_state();
    let mut db = state.db.lock().unwrap_or_else(|p| p.into_inner());
    let report = check_many_modules_with_db(&mut db, parsed);
    drop(db);

    for e in &report.errors {
        match e {
            MultiModuleError::CycleInModules(cycle) => {
                return Err(format!(
                    "cycle among modules: {}",
                    cycle.join(" \u{2194} "),
                ));
            }
            other => return Err(format!("driver error: {other:?}")),
        }
    }
    for result in &report.results {
        if let Some(err) = &result.inference_error {
            return Err(format!(
                "inference error in {}: {err:?}",
                result.name,
            ));
        }
        if let Some(ie) = result.import_errors.first() {
            return Err(format!(
                "import error in {}: {:?}",
                result.name, ie.kind,
            ));
        }
        if let Some(ne) = result.exhaustiveness_errors.first() {
            return Err(format!(
                "non-exhaustive pattern in {} ({}: missing {:?})",
                result.name, ne.type_name, ne.missing,
            ));
        }
        if let Some(ce) = result.constraint_errors.first() {
            return Err(format!(
                "constraint error in {} ({:?} on {})",
                result.name, ce.kind, ce.constraint.class.name,
            ));
        }
    }
    Ok(Vec::new())
}

// ---------------------------------------------------------------------------
// Macros: one passing variant + one ignored variant. The build
// script picks per fixture based on `passing_fixtures_ignore.txt`.
// ---------------------------------------------------------------------------

macro_rules! check_build_unit {
    ($test_name:ident, $fixture:literal) => {
        #[test]
        #[timeout(20000)]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_build_unit($fixture);
        }
    };
}

macro_rules! check_build_unit_ignored {
    ($test_name:ident, $fixture:literal, $reason:literal) => {
        #[test]
        #[timeout(20000)]
        #[ignore = $reason]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_build_unit($fixture);
        }
    };
}

// `include!` wires in the hand-maintained test list. Each entry
// is a macro invocation that expands to a `#[test]` function.
include!("passing_fixtures_list.rs");
