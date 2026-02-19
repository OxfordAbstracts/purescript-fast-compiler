//! Integration tests for name resolution.
//!
//! Runs resolve_names on all PureScript fixture files to verify the resolver
//! handles real-world code without panicking and produces no errors.

use std::path::{Path, PathBuf};

use purescript_fast_compiler::cst::Module;
use purescript_fast_compiler::parser;
use purescript_fast_compiler::typechecker::resolve::{resolve_names, ResolutionExports};

/// Support packages from tests/fixtures/packages used by the original compiler tests.
/// Same list as in tests/build.rs.
const SUPPORT_PACKAGES: &[&str] = &[
    "prelude",
    "arrays",
    "assert",
    "bifunctors",
    "catenable-lists",
    "console",
    "const",
    "contravariant",
    "control",
    "datetime",
    "distributive",
    "effect",
    "either",
    "enums",
    "exceptions",
    "exists",
    "filterable",
    "foldable-traversable",
    "foreign",
    "foreign-object",
    "free",
    "functions",
    "functors",
    "gen",
    "graphs",
    "identity",
    "integers",
    "invariant",
    "json",
    "lazy",
    "lcg",
    "lists",
    "maybe",
    "newtype",
    "nonempty",
    "numbers",
    "ordered-collections",
    "orders",
    "partial",
    "profunctor",
    "quickcheck",
    "random",
    "record",
    "refs",
    "safe-coerce",
    "semirings",
    "st",
    "strings",
    "tailrec",
    "transformers",
    "tuples",
    "type-equality",
    "typelevel-prelude",
    "unfoldable",
    "unsafe-coerce",
    "validation",
];

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

/// Parse all .purs source files from support packages.
fn parse_support_modules() -> Vec<Module> {
    let packages_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    let mut modules = Vec::new();
    for &pkg in SUPPORT_PACKAGES {
        let pkg_src = packages_dir.join(pkg).join("src");
        if !pkg_src.exists() {
            continue;
        }
        let mut files = Vec::new();
        collect_purs_files(&pkg_src, &mut files);
        for f in files {
            if let Ok(source) = std::fs::read_to_string(&f) {
                if let Ok(module) = parser::parse(&source) {
                    modules.push(module);
                }
            }
        }
    }
    modules
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

/// Discover "projects" in the original-compiler passing directory.
/// Each .purs file in the root is a project; if a matching directory exists,
/// its files are companion modules. Returns (project_name, files) pairs.
fn discover_projects(fixtures_dir: &Path) -> Vec<(String, Vec<PathBuf>)> {
    let mut projects = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(fixtures_dir)
        .unwrap()
        .flatten()
        .collect();
    entries.sort_by_key(|e| e.path());

    for entry in &entries {
        let path = entry.path();
        if path.is_file() && path.extension().is_some_and(|e| e == "purs") {
            let stem = path.file_stem().unwrap().to_string_lossy().to_string();
            let mut project_files = vec![path.clone()];
            // Check for companion directory
            let companion_dir = fixtures_dir.join(&stem);
            if companion_dir.is_dir() {
                collect_purs_files(&companion_dir, &mut project_files);
            }
            projects.push((stem, project_files));
        }
    }
    projects
}

#[test]
fn resolve_fixture_original_compiler_passing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/passing");
    if !fixtures_dir.exists() {
        eprintln!("Skipping: original-compiler/passing fixtures not found");
        return;
    }

    let support_modules = parse_support_modules();
    let projects = discover_projects(&fixtures_dir);
    assert!(!projects.is_empty(), "Expected passing fixture projects");

    let mut total = 0;
    let mut panicked: Vec<PathBuf> = Vec::new();
    let mut errored: Vec<(PathBuf, Vec<String>)> = Vec::new();

    for (_project_name, files) in &projects {
        let parsed = parse_all_files(files);
        if parsed.is_empty() {
            continue;
        }

        // Build exports from support packages + this project's modules
        let mut all_modules: Vec<Module> = support_modules.clone();
        all_modules.extend(parsed.iter().map(|(_, m)| m.clone()));
        let exports = ResolutionExports::new(&all_modules);

        let (n, p, e) = resolve_all_modules(&parsed, &exports);
        total += n;
        panicked.extend(p);
        errored.extend(e);
    }

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

    // Filter out known failures: files that use type-level operator sections (/\), (~>)
    // in type annotations, which our parser doesn't handle as type arguments.
    let known_failures: &[&str] = &["4535.purs", "TypeOperators.purs"];
    let unexpected_errors: Vec<_> = errored
        .iter()
        .filter(|(p, _)| {
            let file_name = p.file_name().unwrap().to_string_lossy();
            !known_failures.contains(&file_name.as_ref())
        })
        .collect();

    if !unexpected_errors.is_empty() {
        let summary: Vec<String> = unexpected_errors
            .iter()
            .take(20)
            .map(|(p, errs)| {
                format!("  {} ({} errors): {}", p.display(), errs.len(), errs[0])
            })
            .collect();
        panic!(
            "{}/{} files had unexpected resolve errors:\n{}",
            unexpected_errors.len(),
            total,
            summary.join("\n")
        );
    }

    let known_count = errored.len();
    eprintln!(
        "resolve_names succeeded on {}/{total} passing fixture files (0 panics, {known_count} known failures)",
        total - known_count,
    );
}

#[test]
fn resolve_fixture_packages() {
    let fixtures_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    if !fixtures_dir.exists() {
        eprintln!("Skipping: packages fixtures not found");
        return;
    }

    // Only collect from src/ directories (test/ files import test-only utilities)
    let mut files = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&fixtures_dir) {
        for entry in entries.flatten() {
            let src_dir = entry.path().join("src");
            if src_dir.is_dir() {
                collect_purs_files(&src_dir, &mut files);
            }
        }
    }
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

    eprintln!("resolve_names succeeded on {total} package files (0 panics, 0 errors)");
}
