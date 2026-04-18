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
use std::sync::OnceLock;

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

/// All package modules already parsed, indexed by canonical
/// module name. Tests pick only the ones they transitively import
/// rather than dragging in all ~8888 modules, so per-test
/// typecheck work scales with the fixture's import closure.
fn package_modules_by_name() -> &'static std::collections::HashMap<String, ModuleInput> {
    static CACHE: OnceLock<std::collections::HashMap<String, ModuleInput>> =
        OnceLock::new();
    CACHE.get_or_init(|| {
        let root = packages_root();
        let files = collect_purs_files(&root);
        let mut out = std::collections::HashMap::with_capacity(files.len());
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
            // First write wins — some packages redefine the same
            // module (diamond-dep duplicates in spago); the
            // typechecker needs exactly one copy.
            out.entry(name.clone()).or_insert(ModuleInput::new(name, src, module));
        }
        out
    })
}

/// Pull out each top-level import target from a CST.
fn imports_of(module: &cst::Module) -> Vec<String> {
    module
        .imports
        .iter()
        .map(|imp| {
            imp.module
                .parts
                .iter()
                .map(|p| crate::interner::resolve(*p).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect()
}

/// Compute the transitive import closure of `seed_names` against
/// the package map. Only modules that live in the packages map
/// (and haven't already been seeded by the build unit) come back.
fn transitive_imports(
    seed_modules: &[ModuleInput],
    pkgs: &std::collections::HashMap<String, ModuleInput>,
) -> Vec<ModuleInput> {
    let already: std::collections::HashSet<String> =
        seed_modules.iter().map(|m| m.name.clone()).collect();
    let mut visited: std::collections::HashSet<String> = already.clone();
    let mut stack: Vec<String> = seed_modules
        .iter()
        .flat_map(|m| imports_of(&m.module))
        .collect();
    let mut out: Vec<ModuleInput> = Vec::new();
    while let Some(name) = stack.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        if let Some(m) = pkgs.get(&name) {
            stack.extend(imports_of(&m.module));
            out.push(ModuleInput::new(
                m.name.clone(),
                m.source.clone(),
                m.module.clone(),
            ));
        }
    }
    out
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
    // 1) Parse the build-unit's own files (fast — a handful at
    //    most).
    let mut fixture_modules: Vec<ModuleInput> = Vec::new();
    for (path, src) in build_unit_sources(name) {
        let module = match parse(&src) {
            Ok(m) => m,
            Err(e) => return Err(format!("parse error in {}: {e:?}", path.display())),
        };
        let mod_name = module_name_of(&module);
        fixture_modules.push(ModuleInput::new(mod_name, src, module));
    }

    // 2) Pull in only the packages this fixture transitively
    //    imports. This replaces the "load all 8888 packages"
    //    warmup with a per-test closure that's usually < 100
    //    modules — each test finishes in seconds.
    let pkgs = package_modules_by_name();
    let closure = transitive_imports(&fixture_modules, pkgs);

    // 3) Dedupe by module name; fixture wins on collision.
    let mut by_name: std::collections::HashMap<String, ModuleInput> =
        std::collections::HashMap::with_capacity(fixture_modules.len() + closure.len());
    for m in closure {
        by_name.insert(m.name.clone(), m);
    }
    for m in fixture_modules {
        by_name.insert(m.name.clone(), m);
    }
    let parsed: Vec<ModuleInput> = by_name.into_values().collect();

    // 4) Drive the multi-module check against a fresh
    //    `TypecheckDb`. Each fixture test owns its own empty cache
    //    so a bug one test triggers can't bleed into the next.
    let mut db = TypecheckDb::open_in_memory()
        .expect("open in-memory TypecheckDb");
    let report = check_many_modules_with_db(&mut db, parsed);

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
        #[ignore]
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
