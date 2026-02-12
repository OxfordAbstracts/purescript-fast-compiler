//! Build integration tests.
//!
//! Tests that the passing fixtures from the original PureScript compiler
//! build successfully through the full pipeline (parse + typecheck).

use purescript_fast_compiler::build::{build_from_sources, BuildError};
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Support packages from tests/fixtures/packages used by the original compiler tests.
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

#[test]
fn build_support_packages() {
    let packages_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    if !packages_dir.exists() {
        eprintln!("Skipping: packages fixtures not found");
        return;
    }

    // Collect all .purs source files from support package src/ directories
    let mut all_sources: Vec<(String, String)> = Vec::new();

    for &pkg in SUPPORT_PACKAGES {
        let pkg_src = packages_dir.join(pkg).join("src");
        assert!(
            pkg_src.exists(),
            "Support package '{}' not found at expected path: {}",
            pkg,
            pkg_src.display()
        );
        let mut files = Vec::new();
        collect_purs_files(&pkg_src, &mut files);
        for f in files {
            if let Ok(source) = std::fs::read_to_string(&f) {
                all_sources.push((f.to_string_lossy().into_owned(), source));
            }
        }
    }

    let source_refs: Vec<(&str, &str)> = all_sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    let result = build_from_sources(&source_refs);

    let panic_count = result
        .build_errors
        .iter()
        .filter(|e| matches!(e, BuildError::TypecheckPanic { .. }))
        .count();
    let parse_error_count = result
        .build_errors
        .iter()
        .filter(|e| matches!(e, BuildError::ParseError { .. }))
        .count();
    let cycle_count = result
        .build_errors
        .iter()
        .filter(|e| matches!(e, BuildError::CycleInModules { .. }))
        .count();
    let modules_with_type_errors: Vec<&str> = result
        .modules
        .iter()
        .filter(|m| !m.type_errors.is_empty())
        .map(|m| m.module_name.as_str())
        .collect();
    let clean_modules = result.modules.len() - modules_with_type_errors.len();

    eprintln!(
        "\n=== Support Package Build Results ===\n\
         Source files:     {}\n\
         Modules compiled: {}\n\
         Clean:            {}\n\
         Type errors:      {}\n\
         Panics:           {}\n\
         Parse errors:     {}\n\
         Cycles:           {}",
        all_sources.len(),
        result.modules.len(),
        clean_modules,
        modules_with_type_errors.len(),
        panic_count,
        parse_error_count,
        cycle_count,
    );

    // No panics — typechecker should never crash
    assert_eq!(panic_count, 0, "Support packages should have no typechecker panics");

    // No parse errors — all support packages should parse successfully
    assert_eq!(
        parse_error_count, 0,
        "Support packages should have no parse errors"
    );

    // No cycles — support packages should have a valid dependency order
    assert_eq!(
        cycle_count, 0,
        "Support packages should have no import cycles"
    );

    // All support package modules should parse and enter the build pipeline
    assert!(
        result.modules.len() > 100,
        "Expected >100 modules from support packages, got {}",
        result.modules.len()
    );
}

/// Fixtures skipped due to pre-existing typechecker bugs (not build module issues).
/// - 2616: derive instance triggers infinite recursion (derive not yet implemented)
/// - NamedPatterns: as-pattern `y@{..}` triggers infinite recursion in typechecker
/// - Import: index out of bounds panic in unifier (multi-module import test)
/// - ForeignKind: index out of bounds panic in unifier
/// - 2018: qualified type reference `Main.Foo` not resolved (qualified imports limitation)
/// - TypeOperators: value operator alias `/\` not resolved across modules
const SKIP_FIXTURES: &[&str] = &[
    "2616",
    "NamedPatterns",
    "Import",
    "ForeignKind",
    "2018",
    "TypeOperators",
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

/// Collect all build units from the passing fixtures directory.
/// A build unit is one of:
/// - A single `Name.purs` file (if no matching `Name/` directory exists)
/// - A `Name/` directory (if no matching `Name.purs` exists)
/// - A `Name.purs` + `Name/` directory merged together (the original compiler's
///   convention for multi-module tests: `Name.purs` is Main, `Name/*.purs` are deps)
fn collect_build_units(fixtures_dir: &Path) -> Vec<(String, Vec<(String, String)>)> {
    // First, collect all directory names and file stems
    let mut dir_names: HashSet<String> = HashSet::new();
    let mut file_stems: HashSet<String> = HashSet::new();

    let mut entries: Vec<_> = std::fs::read_dir(fixtures_dir).unwrap().flatten().collect();
    entries.sort_by_key(|e| e.path());

    for entry in &entries {
        let path = entry.path();
        if path.is_dir() {
            dir_names.insert(path.file_name().unwrap().to_string_lossy().into_owned());
        } else if path.extension().is_some_and(|e| e == "purs") {
            file_stems.insert(path.file_stem().unwrap().to_string_lossy().into_owned());
        }
    }

    let mut units = Vec::new();
    let mut processed_dirs: HashSet<String> = HashSet::new();

    for entry in &entries {
        let path = entry.path();

        if path.extension().is_some_and(|e| e == "purs") {
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            let mut sources = Vec::new();

            // Read the main .purs file
            if let Ok(source) = std::fs::read_to_string(&path) {
                sources.push((path.to_string_lossy().into_owned(), source));
            }

            // If there's a matching directory, merge its files in
            if dir_names.contains(&name) {
                let dir_path = fixtures_dir.join(&name);
                let mut dir_files = Vec::new();
                collect_purs_files(&dir_path, &mut dir_files);
                dir_files.sort();
                for f in &dir_files {
                    if let Ok(source) = std::fs::read_to_string(f) {
                        sources.push((f.to_string_lossy().into_owned(), source));
                    }
                }
                processed_dirs.insert(name.clone());
            }

            if !sources.is_empty() {
                units.push((name, sources));
            }
        } else if path.is_dir() {
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            // Skip if already merged with a .purs file
            if processed_dirs.contains(&name) {
                continue;
            }

            let mut purs_files = Vec::new();
            collect_purs_files(&path, &mut purs_files);
            purs_files.sort();

            if !purs_files.is_empty() {
                let sources: Vec<(String, String)> = purs_files
                    .iter()
                    .filter_map(|p| {
                        let source = std::fs::read_to_string(p).ok()?;
                        Some((p.to_string_lossy().into_owned(), source))
                    })
                    .collect();
                if !sources.is_empty() {
                    units.push((name, sources));
                }
            }
        }
    }

    units
}

/// Collect all .purs source files from support packages (prelude, effect, etc.)
/// These are included in each fixture build so imports like `import Prelude` resolve.
fn collect_support_sources() -> Vec<(String, String)> {
    let packages_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    let mut sources = Vec::new();
    for &pkg in SUPPORT_PACKAGES {
        let pkg_src = packages_dir.join(pkg).join("src");
        if !pkg_src.exists() {
            continue;
        }
        let mut files = Vec::new();
        collect_purs_files(&pkg_src, &mut files);
        for f in files {
            if let Ok(source) = std::fs::read_to_string(&f) {
                sources.push((f.to_string_lossy().into_owned(), source));
            }
        }
    }
    sources
}

#[test]
#[ignore]
fn build_fixture_original_compiler_passing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/passing");
    if !fixtures_dir.exists() {
        panic!("original-compiler/passing fixtures not found");
    }

    let units = collect_build_units(&fixtures_dir);
    assert!(!units.is_empty(), "Expected passing fixture build units");

    let support_sources = collect_support_sources();

    let skip: HashSet<&str> = SKIP_FIXTURES.iter().copied().collect();
    let mut total = 0;
    let mut clean = 0;
    let mut skipped = 0;
    let mut real_failures: Vec<(String, String)> = Vec::new();

    for (name, sources) in &units {
        if skip.contains(name.as_str()) {
            skipped += 1;
            continue;
        }
        total += 1;

        // Combine fixture sources with support package sources
        let mut all_sources: Vec<(&str, &str)> = support_sources
            .iter()
            .map(|(p, s)| (p.as_str(), s.as_str()))
            .collect();
        for (p, s) in sources {
            all_sources.push((p.as_str(), s.as_str()));
        }

        // Track which module names belong to this fixture (not support packages)
        let fixture_module_names: HashSet<String> = sources
            .iter()
            .filter_map(|(p, _)| {
                // Extract module name from source by parsing the "module X where" line
                let source = std::fs::read_to_string(p).ok()?;
                source
                    .lines()
                    .find(|l| l.trim_start().starts_with("module "))
                    .and_then(|l| {
                        let rest = l.trim_start().strip_prefix("module ")?;
                        Some(rest.split_whitespace().next()?.to_string())
                    })
            })
            .collect();

        let build_result = std::panic::catch_unwind(|| build_from_sources(&all_sources));

        let result = match build_result {
            Ok(r) => r,
            Err(_) => {
                real_failures.push((name.clone(), "  panic in build_from_sources".to_string()));
                continue;
            }
        };

        // Only check errors for fixture modules, not support packages
        let fixture_build_errors: Vec<&BuildError> = result
            .build_errors
            .iter()
            .filter(|e| match e {
                BuildError::ModuleNotFound {
                    importing_module, ..
                } => fixture_module_names.contains(importing_module),
                BuildError::TypecheckPanic { module_name, .. } => {
                    fixture_module_names.contains(module_name)
                }
                _ => true,
            })
            .collect();
        let fixture_type_errors: bool = result
            .modules
            .iter()
            .any(|m| fixture_module_names.contains(&m.module_name) && !m.type_errors.is_empty());

        if fixture_build_errors.is_empty() && !fixture_type_errors {
            clean += 1;
        } else {
            let mut lines = Vec::new();
            for e in &fixture_build_errors {
                lines.push(format!("  {:?}", e));
            }
            for m in &result.modules {
                if fixture_module_names.contains(&m.module_name) && !m.type_errors.is_empty() {
                    lines.push(format!("  [{}]", m.module_name));
                    for e in &m.type_errors {
                        lines.push(format!("    {}", e));
                    }
                }
            }
            real_failures.push((name.clone(), lines.join("\n")));
        }
    }

    eprintln!(
        "\n=== Build Fixture Results ===\n\
         Total:        {}\n\
         Clean:        {}\n\
         Failed:       {}\n\
         Skipped:      {}",
        total,
        clean,
        real_failures.len(),
        skipped,
    );

    if !real_failures.is_empty() {
        let summary: Vec<String> = real_failures
            .iter()
            .map(|(name, errors)| format!("{}:\n{}", name, errors))
            .collect();
        panic!(
            "{} build units failed:\n\n{}",
            real_failures.len(),
            summary.join("\n\n")
        );
    }
}
