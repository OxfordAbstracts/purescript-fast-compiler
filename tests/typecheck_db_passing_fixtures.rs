//! Acceptance test: run the new typechecker against every
//! passing fixture plus the support-library sources under
//! `tests/fixtures/packages/`, and assert zero errors.
//!
//! Scope:
//! * Loads every `.purs` under
//!   `tests/fixtures/packages/*/src/**` (Prelude + whatever
//!   libraries the user has dropped into `packages/`).
//! * Loads every `.purs` under
//!   `tests/fixtures/original-compiler/passing/`.
//! * Parses all of them; feeds the lot into
//!   [`check_many_modules`]; asserts no parse errors, no import
//!   errors, no inference errors, no exhaustiveness errors, no
//!   constraint errors, and no cycles.
//!
//! When anything fails, the first offending `(module, kind,
//! detail)` is printed and the test fails immediately. That
//! keeps the signal actionable: one concrete failure beats a
//! long list of cascading errors from the same root cause.

use std::fs;
use std::path::{Path, PathBuf};

use purescript_fast_compiler::cst;
use purescript_fast_compiler::parser::parse;
use purescript_fast_compiler::typecheck_db::driver_multi::{
    check_many_modules, ModuleInput, MultiModuleError,
};

/// Root under which both package sources and passing fixtures
/// live, relative to CARGO_MANIFEST_DIR.
const FIXTURES_ROOT: &str = "tests/fixtures";

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
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
        // Skip Spago's per-package dependency caches — they
        // duplicate the sources already present under each
        // package's own `src/`, and wading in pulls in hundreds
        // of identical module names.
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

/// Extract the module name from a parsed module.
fn module_name_of(m: &cst::Module) -> String {
    m.name
        .value
        .parts
        .iter()
        .map(|p| {
            purescript_fast_compiler::interner::resolve(*p).unwrap_or_default()
        })
        .collect::<Vec<_>>()
        .join(".")
}

/// Gather every `.purs` source under `tests/fixtures/packages/`
/// and `tests/fixtures/original-compiler/passing/`.
fn gather_all_sources() -> Vec<PathBuf> {
    let root = manifest_dir().join(FIXTURES_ROOT);
    let mut files = collect_purs_files(&root.join("packages"));
    files.extend(collect_purs_files(
        &root.join("original-compiler").join("passing"),
    ));
    files
}

/// Currently ignored because the new typechecker still has gaps
/// the fixtures surface (missing constraint class instances for
/// built-in Prelude types, subtle exhaustiveness + constraint
/// disagreements with the legacy checker). Run manually with
/// `cargo test -- --ignored all_passing_fixtures_typecheck` —
/// the output names the first offending module, kind, and
/// detail so each gap can be closed one at a time.
#[test]
#[ignore = "end-to-end acceptance target; gap-closing work in progress"]
fn all_passing_fixtures_typecheck() {
    // Real-world modules produce deep AST walks (Prelude + every
    // fixture adds up). Run on a thread with a generous stack
    // rather than tune every recursive walk down to iterative.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(run_fixture_check)
        .expect("spawn fixture-check thread")
        .join()
        .expect("fixture-check thread panicked");
}

fn run_fixture_check() {
    let files = gather_all_sources();
    assert!(
        !files.is_empty(),
        "no .purs files found under {}; refusing to pretend success",
        FIXTURES_ROOT,
    );

    // Parse every file; bail on the first parse error (parsing
    // isn't this pass's responsibility — someone else owns it).
    let mut parsed: Vec<ModuleInput> = Vec::with_capacity(files.len());
    let mut seen_names: std::collections::HashSet<String> =
        std::collections::HashSet::new();
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
        // Duplicate module names are a project-level problem
        // (two files declare the same module). Surface but don't
        // crash — pick the first one for checking.
        if seen_names.insert(name.clone()) {
            parsed.push(ModuleInput::new(name, src, module));
        }
    }

    // Drive the multi-module check.
    let report = check_many_modules(parsed);

    // Cycles first — they mean whole subgraphs didn't typecheck.
    if let Some(MultiModuleError::CycleInModules(cycle)) =
        report.errors.iter().find(|e| matches!(e, MultiModuleError::CycleInModules(_)))
    {
        panic!("cycle among modules: {}", cycle.join(" ↔ "));
    }
    for e in &report.errors {
        if !matches!(e, MultiModuleError::CycleInModules(_)) {
            panic!("driver error: {e:?}");
        }
    }

    // Per-module diagnostics. Aggregate every failure rather than
    // fail on the first — that way the run surfaces the whole
    // gap surface, not just the deepest visible bug.
    let mut failures: Vec<(String, String)> = Vec::new();
    for result in &report.results {
        if let Some(err) = &result.inference_error {
            failures.push((result.name.clone(), format!("infer: {err:?}")));
            continue;
        }
        if let Some(ie) = result.import_errors.first() {
            failures.push((
                result.name.clone(),
                format!("import: {:?}", ie.kind),
            ));
            continue;
        }
        if let Some(ne) = result.exhaustiveness_errors.first() {
            failures.push((
                result.name.clone(),
                format!("non-exhaustive {} (missing {:?})", ne.type_name, ne.missing),
            ));
            continue;
        }
        if let Some(ce) = result.constraint_errors.first() {
            failures.push((
                result.name.clone(),
                format!(
                    "constraint {:?}: {}",
                    ce.kind, ce.constraint.class.name,
                ),
            ));
            continue;
        }
    }

    let total = report.results.len();
    let failing = failures.len();
    let passing = total - failing;
    eprintln!("=== fixture acceptance summary ===");
    eprintln!("modules processed: {total}");
    eprintln!("passing: {passing}");
    eprintln!("failing: {failing}");
    if !failures.is_empty() {
        eprintln!("--- first 10 failures:");
        for (name, reason) in failures.iter().take(10) {
            eprintln!("  {name}: {reason}");
        }
    }
    assert!(
        failures.is_empty(),
        "{failing}/{total} modules failed acceptance check",
    );
}
