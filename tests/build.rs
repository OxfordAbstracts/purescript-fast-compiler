//! Build integration tests.
//!
//! Tests that the passing fixtures from the original PureScript compiler
//! build successfully through the full pipeline (parse + typecheck).

use purescript_fast_compiler::build::{build_from_sources, build_from_sources_with_registry};
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
    // Collect all .purs source files from support package src/ directories
    let source_refs_string = collect_support_sources();

    eprintln!(
        "Building support packages ({} modules)...",
        source_refs_string.len()
    );

    let source_refs: Vec<(&str, &str)> = source_refs_string
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();
      

    let result = build_from_sources(&source_refs);

    assert!(
        result.build_errors.is_empty(),
        "Expected no build errors in support packages, but got:\n{}",
        result
            .build_errors
            .iter()
            .map(|e| format!(" {}", e))
            .collect::<Vec<_>>()
            .join("\n")
    );

    let mut type_errors: Vec<(String, PathBuf, String)> = Vec::new();

    let mut fails = 0;

    for m in &result.modules {
        let new_type_errors: Vec<(String, PathBuf, String)> = m
            .type_errors
            .iter()
            .map(|e| (m.module_name.clone(), m.path.clone(), e.to_string()))
            .collect();

        type_errors.extend(new_type_errors);

        if !m.type_errors.is_empty() {
            fails += 1;
        }
    }

    let type_errors_str: String = type_errors
        .iter()
        .map(|(m, p, e): &(String, PathBuf, String)| {
            format!("{} ({}): {}", m, p.to_string_lossy(), e)
        })
        .collect::<Vec<String>>()
        .join("\n");

    assert!(
        type_errors.is_empty(),
        "Type errors in support packages: {}/{} failed:\n{}",
        fails,
        SUPPORT_PACKAGES.len(),
        type_errors_str
    );
}

/// Fixtures skipped due to pre-existing typechecker limitations.
///
/// Panics (crash the typechecker):
/// - 2616: derive instance triggers infinite recursion (derive not yet implemented)
/// - NamedPatterns: as-pattern `y@{..}` triggers infinite recursion
/// - Import: index out of bounds panic in unifier
/// - ForeignKind: index out of bounds panic in unifier
///
/// Type errors (typechecker limitations, not panics):
/// - 2018: qualified type reference `Main.Foo` not resolved
/// - 2138: cannot import re-exported data constructors
/// - 2197-1: cycle detected in type synonym declarations
/// - 2197-2: type synonym `Number` not resolved
/// - 2626: boolean/int mismatch (Number type alias)
/// - 2806: unknown value in where clause
/// - 2972: missing derived instance matching
/// - 3595: cycle in type class declarations (re-export)
/// - 3957: unknown value in where clause
/// - 4179: various unresolved values / infinite type
/// - 4357: unknown value / type mismatch
/// - 4535: type-level operator `/\` not resolved across modules
/// - BigFunction: `where` clause bindings not in scope
/// - BindersInFunctions: Unit vs wildcard mismatch
/// - CSEInitialDigitSymbols: IsSymbol instance for string literals
/// - DerivingFunctor: derive Functor not implemented
/// - DuplicateProperties: duplicate record label check too strict
/// - EmptyTypeClass: Unit vs wildcard mismatch
/// - Generalization1: where-clause binding not in scope
/// - Guards: various guard-related type errors
/// - Let: Unit vs wildcard mismatch
/// - ModuleExportSelf: self-referencing module export
/// - Monad: Number/String mismatch, Id/Maybe mismatch
/// - MonadState: unknown value runState
/// - MultiArgFunctions: unknown value in where clause
/// - MutRec: mutual recursion across where clauses
/// - MutRec2: mutual recursion across where clauses
/// - NestedRecordUpdateWildcards: record update wildcard
/// - NumberLiterals: unknown value test
/// - ObjectSynonym: type synonym resolution
/// - ObjectUpdate: record update type mismatch
/// - ObjectUpdater: record update type mismatch
/// - OperatorSections: operator section type inference
/// - OptimizerBug: unknown value in where clause
/// - QualifiedOperators: qualified operator resolution
/// - RebindableSyntax: rebindable do syntax
/// - ReservedWords: Unit vs wildcard mismatch
/// - RowUnion: duplicate row label
/// - ShadowedTCOLet: Unit vs wildcard mismatch
/// - SingleInstanceFundep: functional dependency resolution
/// - SolvingAppendSymbol: type-level symbol solving
/// - SolvingReflectable: Reflectable instances
/// - StringEdgeCases: edge-case string/symbol handling
/// - TypeAnnotationPrecedence: annotation precedence
/// - TypeOperators: value operator alias `/\` not resolved across modules
/// - TypeSynonymInstance: type synonym in instance head
/// - TypeWildcards: wildcard type unification
/// - TypeWildcardsRecordExtension: wildcard in record extension
/// - TypedBinders: unknown value runState
/// - VTAsClassHeads: visible type application in class heads
/// - Where: Unit vs wildcard mismatch
/// - WildcardType: wildcard type unification
const SKIP_FIXTURES: &[&str] = &[
    // Panics
    "2616",
    "NamedPatterns",
    "Import",
    "ForeignKind",
    // Type errors
    "2018",
    "2138",
    "2197-1",
    "2197-2",
    "2626",
    "2806",
    "2972",
    "3595",
    "3957",
    "4179",
    "4357",
    "4535",
    "BigFunction",
    "BindersInFunctions",
    "CSEInitialDigitSymbols",
    "DerivingFunctor",
    "DuplicateProperties",
    "EmptyTypeClass",
    "Generalization1",
    "Guards",
    "Let",
    "ModuleExportSelf",
    "Monad",
    "MonadState",
    "MultiArgFunctions",
    "MutRec",
    "MutRec2",
    "NestedRecordUpdateWildcards",
    "NumberLiterals",
    "ObjectSynonym",
    "ObjectUpdate",
    "ObjectUpdater",
    "OperatorSections",
    "OptimizerBug",
    "QualifiedOperators",
    "RebindableSyntax",
    "ReservedWords",
    "RowUnion",
    "ShadowedTCOLet",
    "SingleInstanceFundep",
    "SolvingAppendSymbol",
    "SolvingReflectable",
    "StringEdgeCases",
    "TypeAnnotationPrecedence",
    "TypeOperators",
    "TypeSynonymInstance",
    "TypeWildcards",
    "TypeWildcardsRecordExtension",
    "TypedBinders",
    "VTAsClassHeads",
    "Where",
    "WildcardType",
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
                sources.push((f.to_string_lossy().into_owned(), source));
            }
        }
    }
    sources
}

/// Extract module name from PureScript source text (the `module X where` line).
fn extract_module_name(source: &str) -> Option<String> {
    source
        .lines()
        .find(|l| l.trim_start().starts_with("module "))
        .and_then(|l| {
            let rest = l.trim_start().strip_prefix("module ")?;
            Some(rest.split_whitespace().next()?.to_string())
        })
}

#[test]
fn build_fixture_original_compiler_passing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/passing");
    if !fixtures_dir.exists() {
        panic!("original-compiler/passing fixtures not found");
    }

    let units = collect_build_units(&fixtures_dir);
    assert!(!units.is_empty(), "Expected passing fixture build units");

    // Build support packages once to get a shared registry
    let support_sources_string = collect_support_sources();
    let support_sources: Vec<(&str, &str)> = support_sources_string
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();
    let (_, registry) = build_from_sources_with_registry(&support_sources, None);

    let skip: HashSet<&str> = SKIP_FIXTURES.iter().copied().collect();
    let mut total = 0;
    let mut clean = 0;
    let mut skipped = 0;
    let mut failures: Vec<(String, String)> = Vec::new();

    for (name, sources) in &units {
        if skip.contains(name.as_str()) {
            skipped += 1;
            continue;
        }
        total += 1;

        // Only the fixture's own sources — support modules come from the registry
        let test_sources: Vec<(&str, &str)> = sources
            .iter()
            .map(|(p, s)| (p.as_str(), s.as_str()))
            .collect();

        // Track fixture module names so we only report errors from this fixture
        let fixture_module_names: HashSet<String> = sources
            .iter()
            .filter_map(|(_, s)| extract_module_name(s))
            .collect();

        let build_result = std::panic::catch_unwind(|| {
            build_from_sources_with_registry(&test_sources, Some(registry.clone()))
        });

        let result = match build_result {
            Ok((r, _)) => r,
            Err(_) => {
                failures.push((
                    name.clone(),
                    "  panic in build_from_sources_with_registry".to_string(),
                ));
                continue;
            }
        };

        let has_build_errors = !result.build_errors.is_empty();
        let has_type_errors = result
            .modules
            .iter()
            .any(|m| fixture_module_names.contains(&m.module_name) && !m.type_errors.is_empty());

        if !has_build_errors && !has_type_errors {
            clean += 1;
        } else {
            let mut lines = Vec::new();
            for e in &result.build_errors {
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
            failures.push((name.clone(), lines.join("\n")));
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
        failures.len(),
        skipped,
    );

    if !failures.is_empty() {
        let summary: Vec<String> = failures
            .iter()
            .map(|(name, errors)| format!("{}:\n{}", name, errors))
            .collect();
        panic!(
            "{}/{} build units failed:\n\n{}",
            failures.len(),
            total,
            summary.join("\n\n")
        );
    }
}
