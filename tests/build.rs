//! Build integration tests.
//!
//! Tests that the passing fixtures from the original PureScript compiler
//! build successfully through the full pipeline (parse + typecheck).

use ntest_timeout::timeout;
use rayon::prelude::*;
use purescript_fast_compiler::build::{
    build_from_sources_with_js, build_from_sources_with_options, build_from_sources_with_registry,
    BuildError, BuildOptions, BuildResult,
};
use purescript_fast_compiler::typechecker::error::TypeError;
use purescript_fast_compiler::typechecker::ModuleRegistry;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

/// Shared support package build result. Built lazily on first access so that
/// all three tests (build_support_packages, _passing, _failing) share a single
/// build of the ~290 support modules instead of each rebuilding independently.
/// This eliminates CPU contention when tests run in parallel.
struct SupportBuild {
    sources: Vec<(String, String)>,
    result: BuildResult,
    registry: Arc<ModuleRegistry>,
}

static SUPPORT_BUILD: OnceLock<SupportBuild> = OnceLock::new();

fn get_support_build() -> &'static SupportBuild {
    SUPPORT_BUILD.get_or_init(|| {
        let sources = collect_support_sources();
        let source_refs: Vec<(&str, &str)> = sources
            .iter()
            .map(|(p, s)| (p.as_str(), s.as_str()))
            .collect();
        let (result, registry) = build_from_sources_with_registry(&source_refs, None);
        SupportBuild {
            sources,
            result,
            registry: Arc::new(registry),
        }
    })
}

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
#[timeout(6000)] // 6 second timeout to prevent infinite loops in failing fixtures. 6 seconds is far more than this test should ever need.
fn build_support_packages() {
    let support = get_support_build();
    let result = &support.result;

    eprintln!(
        "Building support packages ({} modules)...",
        support.sources.len()
    );

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

/// Collect JS companion files for a set of .purs sources.
/// For each .purs file, checks if a .js file with the same base name exists.
fn collect_js_companions(sources: &[(String, String)]) -> HashMap<String, String> {
    let mut js_sources = HashMap::new();
    for (purs_path, _) in sources {
        let p = PathBuf::from(purs_path);
        let js_path = p.with_extension("js");
        if js_path.exists() {
            if let Ok(js_source) = std::fs::read_to_string(&js_path) {
                js_sources.insert(purs_path.clone(), js_source);
            }
        }
    }
    js_sources
}

/// Collect all build units from the passing fixtures directory.
/// A build unit is one of:
/// - A single `Name.purs` file (if no matching `Name/` directory exists)
/// - A `Name/` directory (if no matching `Name.purs` exists)
/// - A `Name.purs` + `Name/` directory merged together (the original compiler's
///   convention for multi-module tests: `Name.purs` is Main, `Name/*.purs` are deps)
///
/// Returns (name, purs_sources, js_companion_sources).
fn collect_build_units(
    fixtures_dir: &Path,
) -> Vec<(String, Vec<(String, String)>, HashMap<String, String>)> {
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
                let js = collect_js_companions(&sources);
                units.push((name, sources, js));
            }
        } else if path.is_dir() {
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            // Skip if already merged with a .purs file, or if a matching .purs exists
            // (it will be processed later and will merge this directory's files)
            if processed_dirs.contains(&name) || file_stems.contains(&name) {
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
                    let js = collect_js_companions(&sources);
                    units.push((name, sources, js));
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
#[timeout(6000)] // 6 second timeout to prevent infinite loops in failing fixtures. 6 seconds is far more than this test should ever need.
fn build_fixture_original_compiler_passing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/passing");
    if !fixtures_dir.exists() {
        panic!("original-compiler/passing fixtures not found");
    }

    let units = collect_build_units(&fixtures_dir);
    assert!(!units.is_empty(), "Expected passing fixture build units");

    // Use shared support build (built lazily on first access, shared across tests)
    let registry = Arc::clone(&get_support_build().registry);

    let mut total = 0;
    let mut clean = 0;
    let mut failures: Vec<(String, String)> = Vec::new();

    for (name, sources, js_sources) in &units {
        total += 1;

        // Only the fixture's own sources — support modules come from the registry
        let test_sources: Vec<(&str, &str)> = sources
            .iter()
            .map(|(p, s)| (p.as_str(), s.as_str()))
            .collect();

        let js_refs: HashMap<&str, &str> = js_sources
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
            .collect();

        // Track fixture module names so we only report errors from this fixture
        let fixture_module_names: HashSet<String> = sources
            .iter()
            .filter_map(|(_, s)| extract_module_name(s))
            .collect();

        let registry = Arc::clone(&registry);
        let build_result = std::panic::catch_unwind(|| {
            build_from_sources_with_js(&test_sources, &Some(js_refs), Some(registry))
        });

        let result = match build_result {
            Ok((r, _)) => r,
            Err(_) => {
                failures.push((
                    name.clone(),
                    "  panic in build_from_sources_with_js".to_string(),
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
                    lines.push(format!(
                        "  [{}, {}]",
                        m.module_name,
                        m.path.to_string_lossy()
                    ));
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
         Failed:       {}",
        total,
        clean,
        failures.len(),
    );

    let summary: Vec<String> = failures
        .iter()
        .map(|(name, errors)| format!("{}:\n{}", name, errors))
        .collect();

    assert!(
        !failures.is_empty(),
        "{}/{} build units failed:\n\n{}",
        failures.len(),
        total,
        summary.join("\n\n")
    );
}

/// Extract the `-- @shouldFailWith ErrorName` annotation from the first source file.
/// Searches the first few comment lines (not just the first line).
fn extract_expected_error(sources: &[(String, String)]) -> Option<String> {
    sources.first().and_then(|(_, source)| {
        source
            .lines()
            .take_while(|line| line.trim().starts_with("--"))
            .find_map(|line| {
                line.trim()
                    .strip_prefix("-- @shouldFailWith ")
                    .map(|s| s.trim().to_string())
            })
    })
}

/// Check if any of the actual errors match the expected error category.
fn matches_expected_error(
    expected: &str,
    build_errors: &[BuildError],
    type_errors: &[TypeError],
) -> bool {
    let codes: Vec<String> = build_errors
        .iter()
        .map(|e| e.code())
        .chain(type_errors.iter().map(|e| e.code()))
        .collect();
    let has = |code: &str| {
        codes
            .iter()
            .any(|c| c == code || c.ends_with(&format!(".{}", code)))
    };

    match expected {
        "TypesDoNotUnify" => has("UnificationError"),
        "NoInstanceFound" => has("NoInstanceFound"),
        "ErrorParsingModule" => has("LexError") || has("SyntaxError"),
        "UnknownName" => has("UnknownName") || has("UndefinedVariable"),
        "HoleInferredType" => has("HoleInferredType") || has("UnificationError"),
        "InfiniteType" => has("InfiniteType"),
        "InfiniteKind" => has("InfiniteKind"),
        "DuplicateValueDeclaration" => has("DuplicateValueDeclaration"),
        "OverlappingNamesInLet" => has("OverlappingNamesInLet"),
        "CycleInTypeSynonym" => has("CycleInTypeSynonym"),
        "CycleInDeclaration" => has("CycleInDeclaration") || has("CycleInTypeClassDeclaration"),
        "CycleInTypeClassDeclaration" => has("CycleInTypeClassDeclaration"),
        "CycleInKindDeclaration" => has("CycleInKindDeclaration"),
        "UnknownImport" => has("UnknownImport"),
        "UnknownImportDataConstructor" => has("UnknownImportDataConstructor"),
        "IncorrectConstructorArity" => has("IncorrectConstructorArity"),
        "DuplicateTypeClass" => has("DuplicateTypeClass"),
        "DuplicateInstance" => has("DuplicateInstance"),
        "DuplicateTypeArgument" => has("DuplicateTypeArgument"),
        "InvalidDoBind" => has("InvalidDoBind"),
        "InvalidDoLet" => has("InvalidDoLet"),
        "CannotUseBindWithDo" => has("CannotUseBindWithDo"),
        "ModuleNotFound" => has("ModuleNotFound"),
        "DuplicateModule" => has("DuplicateModule"),
        "CycleInModules" => has("CycleInModules"),
        "MultipleValueOpFixities" => has("MultipleValueOpFixities"),
        "MultipleTypeOpFixities" => has("MultipleTypeOpFixities"),
        "OrphanTypeDeclaration" => has("OrphanTypeSignature"),
        "OrphanKindDeclaration" => has("OrphanKindDeclaration"),
        "UnknownExport" | "UnknownExportDataConstructor" => has("UnkownExport"),
        "OverlappingArgNames" => has("OverlappingArgNames") || has("OverlappingPattern"),
        "ArgListLengthsDiffer" => has("ArityMismatch"),
        "InvalidNewtypeInstance" | "CannotDeriveNewtypeForData" => {
            has("InvalidNewtypeInstance") || has("InvalidNewtypeDerivation")
        }
        "InvalidNewtypeDerivation" => has("InvalidNewtypeDerivation"),
        "OverlappingPattern" => has("OverlappingPattern"),
        "NonExhaustivePattern" => has("NonExhaustivePattern"),
        "CaseBinderLengthDiffers" => has("CaseBinderLengthDiffers"),
        "AdditionalProperty" => has("AdditionalProperty") || has("UnificationError"),
        "PropertyIsMissing" => has("PropertyIsMissing") || has("UnificationError"),
        "InvalidOperatorInBinder" => has("InvalidOperatorInBinder"),
        "IncorrectAnonymousArgument" => has("IncorrectAnonymousArgument"),
        "IntOutOfRange" => has("IntOutOfRange"),
        "UnknownClass" => has("UnknownClass"),
        "MissingClassMember" => has("MissingClassMember"),
        "ExtraneousClassMember" => has("ExtraneousClassMember"),
        "CannotGeneralizeRecursiveFunction" => has("CannotGeneralizeRecursiveFunction"),
        "CannotApplyExpressionOfTypeOnType" => has("CannotApplyExpressionOfTypeOnType"),
        "DeclConflict" => has("DeclConflict"),
        "CannotDefinePrimModules" => has("CannotDefinePrimModules"),
        "OrphanRoleDeclaration" => has("OrphanRoleDeclaration"),
        "DuplicateRoleDeclaration" => has("DuplicateRoleDeclaration"),
        "UnsupportedRoleDeclaration" => has("UnsupportedRoleDeclaration"),
        "RoleDeclarationArityMismatch" => has("RoleDeclarationArityMismatch"),
        "UndefinedTypeVariable" => has("UndefinedTypeVariable"),
        "AmbiguousTypeVariables" => has("AmbiguousTypeVariables"),
        "ExpectedType" => has("ExpectedType"),
        "ExpectedWildcard" => has("ExpectedWildcard"),
        "NonAssociativeError" => has("NonAssociativeError"),
        "MixedAssociativityError" => has("MixedAssociativityError"),
        "DeprecatedFFIPrime" => has("DeprecatedFFIPrime"),
        "ClassInstanceArityMismatch" => has("ClassInstanceArityMismatch"),
        "InvalidInstanceHead" => has("InvalidInstanceHead"),
        "PartiallyAppliedSynonym" => has("PartiallyAppliedSynonym"),
        "TransitiveExportError" | "TransitiveDctorExportError" => has("TransitiveExportError"),
        "OverlappingInstances" => has("OverlappingInstances"),
        "ExportConflict" => has("ExportConflict"),
        "ScopeConflict" => has("ScopeConflict"),
        "OrphanInstance" => has("OrphanInstance"),
        "KindsDoNotUnify" => has("KindsDoNotUnify"),
        "PossiblyInfiniteInstance" => has("PossiblyInfiniteInstance"),
        "InvalidCoercibleInstanceDeclaration" => has("InvalidCoercibleInstanceDeclaration"),
        "RoleMismatch" => has("RoleMismatch"),
        "PossiblyInfiniteCoercibleInstance" => has("PossiblyInfiniteCoercibleInstance"),
        "UnsupportedTypeInKind" => has("UnsupportedTypeInKind"),
        "CannotDeriveInvalidConstructorArg" => has("CannotDeriveInvalidConstructorArg"),
        "MissingFFIImplementations" => has("MissingFFIImplementations"),
        "UnusedFFIImplementations" => has("UnusedFFIImplementations"),
        "UnsupportedFFICommonJSExports" => has("UnsupportedFFICommonJSExports"),
        "UnsupportedFFICommonJSImports" => has("UnsupportedFFICommonJSImports"),
        "DeprecatedFFICommonJSModule" => has("DeprecatedFFICommonJSModule"),
        "MissingFFIModule" => has("MissingFFIModule"),
        "EscapedSkolem" => has("EscapedSkolem"),
        "QuantificationCheckFailureInType" => has("QuantificationCheckFailureInType"),
        "QuantificationCheckFailureInKind" => has("QuantificationCheckFailureInKind"),
        "VisibleQuantificationCheckFailureInType" => has("VisibleQuantificationCheckFailureInType"),
        "WildcardInTypeDefinition"  => has("WildcardInTypeDefinition") || has("SyntaxError"),
        "ConstraintInForeignImport"  =>  has("ConstraintInForeignImport") || has("SyntaxError"),
        "InvalidConstraintArgument"  =>  has("InvalidConstraintArgument") || has("SyntaxError"),
        _ => {
            eprintln!("Warning: Unrecognized expected error code '{}'. Add the appropriate error constructor with a matching error.code() implementation. Then add it to matches_expected_error match statement", expected);
            false
        }
    }
}

#[test]
#[timeout(30000)] // 30 second timeout — all failing fixtures are compiled without skipping.
fn build_fixture_original_compiler_failing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/failing");
    if !fixtures_dir.exists() {
        panic!("original-compiler/failing fixtures not found");
    }

    let units = collect_build_units(&fixtures_dir);
    assert!(!units.is_empty(), "Expected failing fixture build units");

    // Use shared support build (built lazily on first access, shared across tests)
    let registry = Arc::clone(&get_support_build().registry);

    let mut total = 0;
    let mut correct = 0;
    let mut wrong_errors: Vec<String>= Vec::new();
    let mut panicked = 0;
    let mut false_passes: Vec<String> = Vec::new();

    for (name, sources, js_sources) in &units {
        total += 1;

        let expected_error = extract_expected_error(sources).unwrap_or_default();

        let fixture_module_names: HashSet<String> = sources
            .iter()
            .filter_map(|(_, s)| extract_module_name(s))
            .collect();

        let registry = Arc::clone(&registry);

        // Clone sources into owned data for the spawned thread ('static requirement)
        let owned_sources: Vec<(String, String)> = sources.clone();
        let owned_js: HashMap<String, String> = js_sources.clone();
        let fixture_module_names_clone = fixture_module_names.clone();
        let expected_error_clone = expected_error.clone();

        // Run in a separate thread with a large stack to avoid stack overflows
        // from deeply recursive fixtures, and catch panics.
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024) // 64 MB stack
            .spawn(move || {
                let test_sources: Vec<(&str, &str)> = owned_sources
                    .iter()
                    .map(|(p, s)| (p.as_str(), s.as_str()))
                    .collect();
                let js_refs: HashMap<&str, &str> = owned_js
                    .iter()
                    .map(|(k, v)| (k.as_str(), v.as_str()))
                    .collect();
                let build_result = std::panic::catch_unwind(|| {
                    build_from_sources_with_js(&test_sources, &Some(js_refs), Some(registry))
                });

                match build_result {
                    Err(_) => "panicked".to_string(),
                    Ok((result, _)) => {
                        let type_errors: Vec<TypeError> = result
                            .modules
                            .iter()
                            .filter(|m| fixture_module_names_clone.contains(&m.module_name))
                            .flat_map(|m| m.type_errors.iter().cloned())
                            .collect();

                        if result.build_errors.is_empty() && type_errors.is_empty() {
                            format!("false_pass:{}", expected_error_clone)
                        } else if matches_expected_error(
                            &expected_error_clone,
                            &result.build_errors,
                            &type_errors,
                        ) {
                            "correct".to_string()
                        } else {
                            let build_codes: Vec<String> = result
                                .build_errors
                                .iter()
                                .map(|e| e.code().to_string())
                                .collect();
                            let type_codes: Vec<String> =
                                type_errors.iter().map(|e| e.code().to_string()).collect();
                            format!(
                                "wrong_error:expected={},build=[{}],type=[{}]",
                                expected_error_clone,
                                build_codes.join(","),
                                type_codes.join(",")
                            )
                        }
                    }
                }
            })
            .expect("Failed to spawn thread");

        match handle.join() {
            Ok(result) => {
                if result == "correct" {
                    correct += 1;
                } else if result.starts_with("wrong_error") {
                    eprintln!("  WRONG: {} -> {}", name, &result);
                    wrong_errors.push(result);
                } else if result.starts_with("false_pass:") {
                    let expected = result.strip_prefix("false_pass:").unwrap_or("");
                    false_passes.push(format!("{} (expected {})", name, expected));
                } else {
                    panicked += 1;
                    eprintln!(" PANIC with result: {} - {}", name, result.clone());
                }
            }
            Err(_) => {
                panicked += 1;
                eprintln!(" PANIC: {}", name);
            }
        }
    }

    eprintln!(
        "\n=== Failing Fixture Results ===\n\
         Total:        {}\n\
         Correct:      {}\n\
         WrongError:   {}\n\
         Panicked:     {}\n\
         FalsePass:    {}",
        total,
        correct,
        wrong_errors.len(),
        panicked,
        false_passes.len(),
    );


    assert!(
      panicked == 0,
      "There should be no panics"
    );

    assert!(
      false_passes.len() == 0,
      "There should be no false passes. Found:\n{}",
      false_passes.join("\n")
    );

    assert!(
      wrong_errors.len() == 0,
      "The should be no wrong errors. Found:\n{}",
      wrong_errors.join("\n")
    )

}


#[test]
#[ignore]
// Heavy test (~33s release, ~300s debug, 4859 modules)
// run with: RUST_LOG=debug cargo test --test build build_all_packages -- --exact --ignored
// for release (RECOMMENDED): cargo test --release --test build build_all_packages -- --exact --ignored
#[timeout(300000)] // 300s (5 min) timeout — debug mode is ~10x slower than release
fn build_all_packages() {
    let _ = env_logger::try_init();
    let started = std::time::Instant::now();

    let packages_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    assert!(packages_dir.exists(), "packages directory not found");

    // Per-module timeout: defaults to 10s, controlled by MODULE_TIMEOUT_SECS env var.
    let timeout_secs: u64 = std::env::var("MODULE_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(10);

    let options = BuildOptions {
        module_timeout: Some(std::time::Duration::from_secs(timeout_secs)),
        output_dir: None,
    };

    // Discover all packages with src/ directories
    let mut all_sources: Vec<(String, String)> = Vec::new();
    let mut pkg_count = 0;

    let mut entries: Vec<_> = std::fs::read_dir(&packages_dir)
        .unwrap()
        .flatten()
        .collect();
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        let src_dir = path.join("src");
        if !src_dir.exists() {
            continue;
        }
        pkg_count += 1;
        let mut files = Vec::new();
        collect_purs_files(&src_dir, &mut files);
        for f in files {
            if let Ok(source) = std::fs::read_to_string(&f) {
                all_sources.push((f.to_string_lossy().into_owned(), source));
            }
        }
    }

    eprintln!(
        "Discovered packages in {} seconds",
        started.elapsed().as_secs_f64()
    );

    eprintln!(
        "Building all packages ({} packages, {} modules, timeout={}s)...",
        pkg_count,
        all_sources.len(),
        timeout_secs,
    );

    let source_refs: Vec<(&str, &str)> = all_sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    let (result, _) = build_from_sources_with_options(&source_refs, &None, None, &options);

    eprintln!("Build completed in {:.2?}", started.elapsed());

    // Separate timeouts/panics from other build errors
    let mut timeouts: Vec<String> = Vec::new();
    let mut panics: Vec<String> = Vec::new();
    let mut other_errors: Vec<String> = Vec::new();
    for e in &result.build_errors {
        match e {
            BuildError::TypecheckTimeout { .. } => {
                timeouts.push(format!(" {}", e));
            }
            BuildError::TypecheckPanic { .. } => {
                panics.push(format!(" {}", e));
            }
            _ => {
                other_errors.push(format!("  {}", e));
            }
        }
    }

    let mut type_errors: Vec<(String, PathBuf, String)> = Vec::new();
    let mut fails = 0;

    for m in &result.modules {
        if !m.type_errors.is_empty() {
            eprintln!("Errors in {}, {}", m.path.to_string_lossy(), m.module_name);
            fails += 1;
            for e in &m.type_errors {
                eprintln!("  {}", e);
                type_errors.push((m.module_name.clone(), m.path.clone(), e.to_string()));
            }
        }
    }

    let clean = result.modules.len() - fails;
    eprintln!(
        "Results: {} clean, {} with type errors, {} timeouts, {} panics out of {} modules",
        clean,
        fails,
        timeouts.len(),
        panics.len(),
        result.modules.len()
    );

    assert!(
        timeouts.len() == 0,
        "Modules exceeded deadline:\n  {}",
        timeouts.join("\n  ")
    );

    assert!(
        panics.is_empty(),
        "Modules panicked during typechecking:\n  {}",
        panics.join("\n  ")
    );

    assert!(
        other_errors.is_empty(),
        "Unexpected build errors:\n{}",
        other_errors.join("\n")
    );

    // Categorize errors for diagnostics
    let mut error_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    for m in &result.modules {
        for e in &m.type_errors {
            *error_counts.entry(e.code()).or_default() += 1;
        }
    }
    if fails > 0 {
        let mut sorted_counts: Vec<_> = error_counts.iter().collect();
        sorted_counts.sort_by(|a, b| b.1.cmp(a.1));
        eprintln!("\nError distribution ({} modules with errors):", fails);
        for (code, count) in &sorted_counts {
            eprintln!("  {:>4} {}", count, code);
        }
        // Show modules with errors and their error code breakdown
        let mut module_errors: Vec<(String, Vec<String>)> = Vec::new();
        for m in &result.modules {
            if !m.type_errors.is_empty() {
                let codes: Vec<String> = m.type_errors.iter().map(|e| e.code()).collect();
                module_errors.push((m.module_name.clone(), codes));
            }
        }
        module_errors.sort_by(|a, b| b.1.len().cmp(&a.1.len()));
        eprintln!("\nModules with errors (by count):");
        for (module, codes) in module_errors.iter().take(40) {
            let mut code_counts: std::collections::HashMap<&str, usize> =
                std::collections::HashMap::new();
            for c in codes {
                *code_counts.entry(c.as_str()).or_default() += 1;
            }
            let summary: Vec<String> = code_counts
                .iter()
                .map(|(k, v)| format!("{}x{}", v, k))
                .collect();
            eprintln!(
                "  {:>3} errors  {}  [{}]",
                codes.len(),
                module,
                summary.join(", ")
            );
        }
    }

    assert!(
        fails == 0,
        "Type error regression: {}/{} modules had errors",
        fails,
        result.modules.len(),
    );
}


// run with: RUST_LOG=debug cargo test --test build build_from_sources -- --exact --ignored
// for release (RECOMMENDED): cargo test --release --test build build_from_sources -- --exact --ignored
#[test]
#[ignore] // This is for manually invocation with 
#[timeout(600000)] // 10 min timeout
fn build_from_sources() {
    
    let _ = env_logger::try_init();
    let started = std::time::Instant::now();

    let application_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("CARGO_MANIFEST_DIR has no parent")
        .join("application");
    assert!(
        application_dir.exists(),
        "OA application directory not found at: {}",
        application_dir.display()
    );

    let sources_txt = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/sources.txt");
    let patterns = std::fs::read_to_string(&sources_txt).expect("Failed to read sources.txt");

    let timeout_secs: u64 = std::env::var("MODULE_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);

    let options = BuildOptions {
        module_timeout: Some(std::time::Duration::from_secs(timeout_secs)),
        output_dir: None
    };

    // Step 1: Glob all patterns to collect file paths
    let step = std::time::Instant::now();
    let mut all_paths: Vec<std::path::PathBuf> = Vec::new();
    for line in patterns.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        let full_pattern = application_dir.join(line);
        let pattern_str = full_pattern.to_string_lossy();

        let matches: Vec<_> = glob::glob(&pattern_str)
            .unwrap_or_else(|e| panic!("Invalid glob pattern '{}': {}", pattern_str, e))
            .filter_map(|entry| entry.ok())
            .collect();

        all_paths.extend(matches);
    }
    eprintln!(
        "  glob: {} files in {:.2?}",
        all_paths.len(),
        step.elapsed()
    );

    // Step 2: Read all files in parallel
    let step = std::time::Instant::now();
    let all_sources: Vec<(String, String)> = all_paths
        .into_par_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|source| (path.to_string_lossy().into_owned(), source))
        })
        .collect();
    eprintln!(
        "  read: {} files in {:.2?}",
        all_sources.len(),
        step.elapsed()
    );

    eprintln!(
        "Discovered {} modules from sources.txt in {:.2?}",
        all_sources.len(),
        started.elapsed()
    );

    let source_refs: Vec<(&str, &str)> = all_sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    let (result, _) = build_from_sources_with_options(&source_refs, &None, None, &options);

    eprintln!("Build completed in {:.2?}", started.elapsed());

    let mut timeouts: Vec<String> = Vec::new();
    let mut panics: Vec<String> = Vec::new();
    let mut other_errors: Vec<String> = Vec::new();
    for e in &result.build_errors {
        match e {
            BuildError::TypecheckTimeout { .. } => {
                timeouts.push(format!("  {}", e));
            }
            BuildError::TypecheckPanic { .. } => {
                panics.push(format!("  {}", e));
            }
            _ => {
                other_errors.push(format!("  {}", e));
            }
        }
    }

    let mut type_errors: Vec<(String, PathBuf, String)> = Vec::new();
    let mut fails = 0;

    for m in &result.modules {
        if !m.type_errors.is_empty() {
            eprintln!("Errors in {}, {}", m.path.to_string_lossy(), m.module_name);
            fails += 1;
            for e in &m.type_errors {
                eprintln!("  {}", e);
                type_errors.push((m.module_name.clone(), m.path.clone(), e.to_string()));
            }
        }
    }

    let clean = result.modules.len() - fails;
    eprintln!(
        "Results: {} clean, {} with type errors, {} timeouts, {} panics out of {} modules",
        clean,
        fails,
        timeouts.len(),
        panics.len(),
        result.modules.len()
    );

    // Error distribution
    let mut error_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    for m in &result.modules {
        for e in &m.type_errors {
            *error_counts.entry(e.code()).or_default() += 1;
        }
    }
    if fails > 0 {
        let mut sorted_counts: Vec<_> = error_counts.iter().collect();
        sorted_counts.sort_by(|a, b| b.1.cmp(a.1));
        eprintln!("\nError distribution ({} modules with errors):", fails);
        for (code, count) in &sorted_counts {
            eprintln!("  {:>4} {}", count, code);
        }
    }

    assert!(
        timeouts.is_empty(),
        "Modules exceeded deadline:\n{}",
        timeouts.join("\n")
    );

    assert!(
        panics.is_empty(),
        "Modules panicked during typechecking:\n{}",
        panics.join("\n")
    );


    assert!(
        fails == 0,
        "Type errors: {} modules with errors \n\
         Error distribution:\n{}",
        fails,
        error_counts.iter()
            .map(|(code, count)| format!("  {:>4} {}", count, code))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
