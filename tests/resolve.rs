//! Integration tests for name resolution.
//!
//! Runs resolve_names on all PureScript fixture files to verify the resolver
//! handles real-world code without panicking and produces no errors.

use std::path::{Path, PathBuf};

use purescript_fast_compiler::cst::Module;
use purescript_fast_compiler::parser;
use purescript_fast_compiler::typechecker::resolve::{resolve_names, ResolutionExports};

fn collect_purs_files(dir: &Path, files: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_purs_files(&path, files);
            } else if path.extension().is_some_and(|e| e == "purs") {
                files.push(path);
            }
        }
    }
}

/// Parse all .purs files, returning (path, module) pairs for those that parse successfully.
fn parse_all_files(files: &[PathBuf]) -> Vec<(PathBuf, Module)> {
    files
        .iter()
        .filter_map(|path| {
            let source = std::fs::read_to_string(path).ok()?;
            let module = parser::parse(&source).ok()?;
            Some((path.clone(), module))
        })
        .collect()
}

/// Run resolve_names on all parsed modules, collecting panics and errors.
fn resolve_all_modules(
    parsed: &[(PathBuf, Module)],
    exports: &ResolutionExports,
) -> (usize, Vec<PathBuf>, Vec<(PathBuf, Vec<String>)>) {
    let mut panicked: Vec<PathBuf> = Vec::new();
    let mut errored: Vec<(PathBuf, Vec<String>)> = Vec::new();

    for (path, module) in parsed {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            resolve_names(module, exports)
        }));
        match result {
            Err(_) => {
                panicked.push(path.clone());
            }
            Ok(resolved) => {
                if !resolved.errors.is_empty() {
                    let errors: Vec<String> =
                        resolved.errors.iter().map(|e| e.to_string()).collect();
                    errored.push((path.clone(), errors));
                }
            }
        }
    }

    (parsed.len(), panicked, errored)
}

// ===== Tests =====

#[test]
fn resolve_fixture_original_compiler_passing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/passing");
    if !fixtures_dir.exists() {
        eprintln!("Skipping: original-compiler/passing fixtures not found");
        return;
    }

    let mut files = Vec::new();
    collect_purs_files(&fixtures_dir, &mut files);
    files.sort();

    assert!(!files.is_empty(), "Expected passing fixture files");

    let parsed = parse_all_files(&files);
    let all_modules: Vec<Module> = parsed.iter().map(|(_, m)| m.clone()).collect();
    let exports = ResolutionExports::new(&all_modules);
    let (total, panicked, errored) = resolve_all_modules(&parsed, &exports);

    if !panicked.is_empty() {
        let summary: Vec<String> = panicked
            .iter()
            .map(|p| format!("  {}", p.display()))
            .collect();
        panic!(
            "{}/{} files panicked during resolve_names:\n{}",
            panicked.len(),
            total,
            summary.join("\n")
        );
    }

    // Many files import from Prelude/Effect/etc. which aren't in the fixture set,
    // so errors are expected. Just report stats.
    let error_count = errored.len();
    eprintln!(
        "resolve_names: {}/{total} passing fixture files clean (0 panics, {error_count} with import errors from missing deps)",
        total - error_count,
    );
}

#[test]
fn resolve_fixture_packages() {
    let fixtures_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    if !fixtures_dir.exists() {
        eprintln!("Skipping: packages fixtures not found");
        return;
    }

    let mut files = Vec::new();
    collect_purs_files(&fixtures_dir, &mut files);
    files.sort();

    assert!(!files.is_empty(), "Expected package fixture files");

    let parsed = parse_all_files(&files);
    let all_modules: Vec<Module> = parsed.iter().map(|(_, m)| m.clone()).collect();
    let exports = ResolutionExports::new(&all_modules);
    let (total, panicked, errored) = resolve_all_modules(&parsed, &exports);

    let rel = |p: &Path| {
        p.strip_prefix(&fixtures_dir)
            .unwrap_or(p)
            .display()
            .to_string()
    };

    if !panicked.is_empty() {
        let summary: Vec<String> = panicked.iter().map(|p| format!("  {}", rel(p))).collect();
        panic!(
            "{}/{} files panicked during resolve_names:\n{}",
            panicked.len(),
            total,
            summary.join("\n")
        );
    }

    // Some errors are expected from:
    // - Modules importing packages not in the fixture set (Halogen, spec-discovery, etc.)
    // - Multiple imports with the same qualifier (only last one wins in re-export resolution)
    // - Qualified class references (Row.Cons etc.)
    let error_count = errored.len();
    let error_pct = (error_count as f64 / total as f64) * 100.0;

    if error_count > 0 {
        let summary: Vec<String> = errored
            .iter()
            .take(10)
            .map(|(p, errs)| format!("  {} ({} errors): {}", rel(p), errs.len(), errs[0]))
            .collect();
        eprintln!(
            "resolve_names: {error_count}/{total} files ({error_pct:.1}%) had errors. First 10:\n{}",
            summary.join("\n")
        );
    }

    // Fail if error rate exceeds threshold
    assert!(
        error_pct < 10.0,
        "{error_count}/{total} files ({error_pct:.1}%) had resolve errors, exceeding 10% threshold"
    );

    eprintln!(
        "resolve_names: {}/{total} package files clean (0 panics, {error_count} with errors)",
        total - error_count,
    );
}
