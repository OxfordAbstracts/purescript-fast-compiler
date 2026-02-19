//! Integration tests for name resolution.
//!
//! Runs resolve_names on all PureScript fixture files to verify the resolver
//! handles real-world code without panicking and produces no errors.

use std::path::{Path, PathBuf};

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

/// Run resolve_names on all .purs files in a directory, collecting panics and errors.
fn resolve_all_files(
    files: &[PathBuf],
) -> (usize, Vec<PathBuf>, Vec<(PathBuf, Vec<String>)>) {
    let mut total = 0;
    let mut panicked: Vec<PathBuf> = Vec::new();
    let mut errored: Vec<(PathBuf, Vec<String>)> = Vec::new();

    for path in files {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let module = match parser::parse(&source) {
            Ok(m) => m,
            Err(_) => continue,
        };
        total += 1;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            resolve_names(&module, &ResolutionExports::empty())
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

    (total, panicked, errored)
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

    let (total, panicked, errored) = resolve_all_files(&files);

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

    // Known failure: TypeOperators.purs — parser doesn't handle `type (~>)` in imports
    let known_failing = "TypeOperators.purs";
    let unexpected: Vec<_> = errored
        .iter()
        .filter(|(p, _)| !p.to_string_lossy().ends_with(known_failing))
        .collect();

    if !unexpected.is_empty() {
        let summary: Vec<String> = unexpected
            .iter()
            .map(|(p, errs)| {
                format!("  {} ({} errors): {}", p.display(), errs.len(), errs[0])
            })
            .collect();
        panic!(
            "{}/{} files had unexpected resolve errors:\n{}",
            unexpected.len(),
            total,
            summary.join("\n")
        );
    }

    let known_count = errored.len();
    eprintln!(
        "resolve_names succeeded on {total} passing fixture files (0 panics, {known_count} known failures)"
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

    let (total, panicked, errored) = resolve_all_files(&files);

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

    if !errored.is_empty() {
        let summary: Vec<String> = errored
            .iter()
            .map(|(p, errs)| format!("  {} ({} errors): {}", rel(p), errs.len(), errs[0]))
            .collect();
        panic!(
            "{}/{} files had resolve errors:\n{}",
            errored.len(),
            total,
            summary.join("\n")
        );
    }

    eprintln!("resolve_names succeeded on {total} package fixture files (0 panics, 0 errors)");
}
