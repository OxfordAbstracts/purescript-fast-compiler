//! Per-build-unit tests for `tests/fixtures/original-compiler/passing/`.
//!
//! Each `.purs` file at the top level of that directory is one
//! "build unit". A same-named directory (e.g. `2018.purs` +
//! `2018/`) holds additional supporting modules that compile
//! together with the primary file.
//!
//! The build script ([build.rs](../../../../../build.rs)) scans
//! the fixtures directory and writes one `check_build_unit!(...)`
//! invocation per build unit into
//! `$OUT_DIR/passing_fixtures_gen.rs`, which we `include!()` at
//! the bottom of this file. The list of build units known to fail
//! is in [passing_fixtures_ignore.txt] — those entries get the
//! `_ignored` macro variant so `cargo test` stays green while
//! still surfacing them under `cargo test -- --ignored`.

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

/// Process-wide `TypecheckDb` shared across every test. Tests
/// serialize on its mutex, but in exchange the per-decl cache
/// from the first test makes every subsequent test's package
/// work a near-free hit.
fn shared_db() -> &'static Mutex<TypecheckDb> {
    static DB: OnceLock<Mutex<TypecheckDb>> = OnceLock::new();
    DB.get_or_init(|| {
        Mutex::new(TypecheckDb::open_in_memory().expect("open in-memory TypecheckDb"))
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

pub(crate) fn run_build_unit(name: &str) {
    // Spawn on a dedicated 64MB-stack thread — Prelude + a fixture
    // can build deep AST walks that overflow the default stack.
    let owned_name = name.to_string();
    let join_result = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run_inner(&owned_name))
        .expect("spawn fixture-check thread")
        .join();
    if let Err(payload) = join_result {
        // Propagate the inner panic message so test output points
        // at the real failure instead of a generic "thread panicked".
        let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
            (*s).to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "fixture-check thread panicked (non-string payload)".to_string()
        };
        panic!("{msg}");
    }
}

fn run_inner(name: &str) {
    // Start from the cached parsed package modules. Clone so we
    // don't hand the cached vec out by reference (each test owns
    // its own input list because dedup may overwrite entries).
    let pkgs = package_modules();
    let mut by_name: std::collections::HashMap<String, ModuleInput> =
        std::collections::HashMap::with_capacity(pkgs.len() + 4);
    for m in pkgs {
        by_name.insert(
            m.name.clone(),
            ModuleInput::new(m.name.clone(), m.source.clone(), m.module.clone()),
        );
    }

    // Build-unit's own files: parsed fresh each test (fast — at
    // most a handful per build unit) and overwriting any package
    // module of the same name.
    for (path, src) in build_unit_sources(name) {
        let module = match parse(&src) {
            Ok(m) => m,
            Err(e) => panic!("parse error in {}: {e:?}", path.display()),
        };
        let mod_name = module_name_of(&module);
        by_name.insert(mod_name.clone(), ModuleInput::new(mod_name, src, module));
    }
    let parsed: Vec<ModuleInput> = by_name.into_values().collect();

    // Acquire the shared DB. The first test through pays the full
    // package-typecheck cost; subsequent tests cache-hit on every
    // unchanged package decl. `unwrap_or_else(|p| p.into_inner())`
    // recovers from a poisoned mutex (a previous test's panic) so
    // one failure doesn't poison the entire run.
    let mutex = shared_db();
    let mut db = mutex.lock().unwrap_or_else(|p| p.into_inner());
    let report = check_many_modules_with_db(&mut db, parsed);
    drop(db);

    // Cycles are fatal — the modules in them never get checked.
    for e in &report.errors {
        match e {
            MultiModuleError::CycleInModules(cycle) => {
                panic!(
                    "cycle among modules in build unit {name}: {}",
                    cycle.join(" \u{2194} "),
                );
            }
            other => panic!("driver error in build unit {name}: {other:?}"),
        }
    }

    // Per-module diagnostics. Surface the first failure with a
    // clear attribution to (build unit, module, kind, detail).
    // Subsequent failures are likely cascades from the first.
    for result in &report.results {
        if let Some(err) = &result.inference_error {
            panic!(
                "build unit {name}: inference error in {}: {err:?}",
                result.name,
            );
        }
        if let Some(ie) = result.import_errors.first() {
            panic!(
                "build unit {name}: import error in {}: {:?}",
                result.name, ie.kind,
            );
        }
        if let Some(ne) = result.exhaustiveness_errors.first() {
            panic!(
                "build unit {name}: non-exhaustive pattern in {} ({}: missing {:?})",
                result.name, ne.type_name, ne.missing,
            );
        }
        if let Some(ce) = result.constraint_errors.first() {
            panic!(
                "build unit {name}: constraint error in {} ({:?} on {})",
                result.name, ce.kind, ce.constraint.class.name,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Macros: one passing variant + one ignored variant. The build
// script picks per fixture based on `passing_fixtures_ignore.txt`.
// ---------------------------------------------------------------------------

macro_rules! check_build_unit {
    ($test_name:ident, $fixture:literal) => {
        #[test]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_build_unit($fixture);
        }
    };
}

macro_rules! check_build_unit_ignored {
    ($test_name:ident, $fixture:literal, $reason:literal) => {
        #[test]
        #[ignore = $reason]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_build_unit($fixture);
        }
    };
}

// `include!` wires in the build-script-generated test list. If
// the file doesn't exist, the build hasn't run; cargo will surface
// that as a compile error pointing at this line.
include!(concat!(env!("OUT_DIR"), "/passing_fixtures_gen.rs"));
