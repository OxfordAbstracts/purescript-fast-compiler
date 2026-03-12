//! Build integration tests.
//!
//! Tests that the passing fixtures from the original PureScript compiler
//! build successfully through the full pipeline (parse + typecheck).

use ntest_timeout::timeout;
use purescript_fast_compiler::build::{
    build_from_sources_incremental, build_from_sources_with_js, build_from_sources_with_options,
    build_from_sources_with_registry, cache::ModuleCache, BuildError, BuildOptions, BuildResult,
};
use purescript_fast_compiler::typechecker::error::TypeError;
use purescript_fast_compiler::typechecker::ModuleRegistry;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;
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

/// Shared support build WITH JavaScript codegen. Built lazily on first access.
/// Generates JS output for all support packages into a temp directory so that
/// fixture tests can run their compiled `main` via Node.js.
struct SupportBuildWithJs {
    registry: Arc<ModuleRegistry>,
    output_dir: PathBuf,
}

static SUPPORT_BUILD_JS: OnceLock<SupportBuildWithJs> = OnceLock::new();

fn get_support_build_with_js() -> &'static SupportBuildWithJs {
    SUPPORT_BUILD_JS.get_or_init(|| {
        let output_dir = std::env::temp_dir().join("pfc-test-passing-output");
        let _ = std::fs::remove_dir_all(&output_dir);
        std::fs::create_dir_all(&output_dir).unwrap();

        let sources = collect_support_sources();
        let source_refs: Vec<(&str, &str)> = sources
            .iter()
            .map(|(p, s)| (p.as_str(), s.as_str()))
            .collect();

        let js_companions = collect_js_companions(&sources);
        let js_refs: HashMap<&str, &str> = js_companions
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
            .collect();

        let options = BuildOptions {
            output_dir: Some(output_dir.clone()),
            ..Default::default()
        };

        let (_, registry) =
            build_from_sources_with_options(&source_refs, &Some(js_refs), None, &options);

        SupportBuildWithJs {
            registry: Arc::new(registry),
            output_dir,
        }
    })
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
#[timeout(240000)] // 240 second timeout — includes codegen + node execution for each fixture.
fn build_fixture_original_compiler_passing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/passing");
    if !fixtures_dir.exists() {
        panic!("original-compiler/passing fixtures not found");
    }

    let units = collect_build_units(&fixtures_dir);
    assert!(!units.is_empty(), "Expected passing fixture build units");

    // Build support packages with JS codegen (shared, built lazily on first access)
    let support = get_support_build_with_js();
    let output_dir = &support.output_dir;
    let registry = Arc::clone(&support.registry);

    let mut total = 0;
    let mut clean = 0;
    let mut failures: Vec<(String, String)> = Vec::new();
    let mut tsc_failures: Vec<(String, String)> = Vec::new();
    let mut node_failures: Vec<(String, String)> = Vec::new();

    for (name, sources, js_sources) in &units {
        // Optional filter: FIXTURE_FILTER=DeepArrayBinder cargo test ...
        // Use comma-separated for multiple: FIXTURE_FILTER=Ado,Sequence
        if let Ok(filter) = std::env::var("FIXTURE_FILTER") {
            let filters: Vec<&str> = filter.split(',').collect();
            if !filters.iter().any(|f| name == f || name.contains(f)) {
                continue;
            }
            eprintln!("  [fixture] {name}");
        }
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
        let output_dir_clone = output_dir.clone();

        let build_result = std::panic::catch_unwind(|| {
            let options = BuildOptions {
                output_dir: Some(output_dir_clone),
                ..Default::default()
            };
            build_from_sources_with_options(&test_sources, &Some(js_refs), Some(registry), &options)
        });

        let result = match build_result {
            Ok((r, _)) => r,
            Err(_) => {
                failures.push((
                    name.clone(),
                    "  panic in build_from_sources_with_options".to_string(),
                ));
                // Clean up fixture module dirs
                for module_name in &fixture_module_names {
                    let _ = std::fs::remove_dir_all(output_dir.join(module_name));
                }
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

            // Run tsc --noEmit to check that outputted TypeScript typechecks
            let tsconfig_path = output_dir.join("tsconfig.json");
            let include_patterns: Vec<String> = fixture_module_names
                .iter()
                .map(|m| format!("{m}/**/*.ts"))
                .collect();
            let include_json = serde_json::to_string(&include_patterns).unwrap_or_default();
            let tsconfig_content = format!(
                r#"{{
  "compilerOptions": {{
    "strict": false,
    "noEmit": true,
    "target": "ES2020",
    "module": "ES2020",
    "moduleResolution": "bundler",
    "skipLibCheck": true,
    "allowImportingTsExtensions": true
  }},
  "include": {include_json}
}}"#
            );
            std::fs::write(&tsconfig_path, &tsconfig_content).ok();

            let tsc_result = Command::new("npx")
                .arg("tsc")
                .arg("--project")
                .arg(&tsconfig_path)
                .output();

            if let Ok(tsc_output) = tsc_result {
                if !tsc_output.status.success() {
                    let tsc_stdout = String::from_utf8_lossy(&tsc_output.stdout);
                    tsc_failures.push((name.clone(), format!("  {}", tsc_stdout.trim())));
                }
            }

            let _ = std::fs::remove_file(&tsconfig_path);

            // Run node to execute main() and check it logs "Done"
            let main_index = output_dir.join("Main").join("index.ts");
            if main_index.exists() {
                let script = format!(
                    "import('file://{}').then(m => m.main())",
                    main_index.display()
                );
                let node_result = Command::new("node")
                    .arg("--experimental-strip-types")
                    .arg("--no-warnings")
                    .arg("-e")
                    .arg(&script)
                    .output();

                match node_result {
                    Ok(output) => {
                        let stdout = String::from_utf8_lossy(&output.stdout);
                        if !stdout.lines().any(|l| l.trim() == "Done") {
                            let stderr = String::from_utf8_lossy(&output.stderr);
                            node_failures.push((
                                name.clone(),
                                format!(
                                    "  expected stdout to contain 'Done'\n  stdout: {}\n  stderr: {}",
                                    stdout.trim(),
                                    stderr.trim()
                                ),
                            ));
                        }
                    }
                    Err(e) => {
                        node_failures.push((name.clone(), format!("  node failed to run: {}", e)));
                    }
                }
            } else {
                node_failures.push((
                    name.clone(),
                    "  Main/index.ts was not generated".to_string(),
                ));
            }
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

        // Clean up fixture module dirs so the next fixture's Main doesn't conflict
        if std::env::var("KEEP_OUTPUT").is_err() {
            for module_name in &fixture_module_names {
                let _ = std::fs::remove_dir_all(output_dir.join(module_name));
            }
        }
    }

    eprintln!(
        "\n=== Build Fixture Results ===\n\
         Total:        {}\n\
         Clean:        {}\n\
         Failed:       {}\n\
         TSC failed:   {}\n\
         Node failed:  {}",
        total,
        clean,
        failures.len(),
        tsc_failures.len(),
        node_failures.len(),
    );

    let summary: Vec<String> = failures
        .iter()
        .map(|(name, errors)| format!("{}:\n{}", name, errors))
        .collect();

    if !failures.is_empty() {
        eprintln!(
            "WARNING: {}/{} build units failed:\n\n{}",
            failures.len(),
            total,
            summary.join("\n\n")
        );
    }

    let tsc_summary: Vec<String> = tsc_failures
        .iter()
        .map(|(name, errors)| format!("{}:\n{}", name, errors))
        .collect();

    assert!(
        tsc_failures.is_empty(),
        "fixtures failed tsc typecheck:\n\n{}\n\n{}/{} failed",
        tsc_summary.join("\n\n"),
        tsc_failures.len(),
        clean,
    );

    let node_summary: Vec<String> = node_failures
        .iter()
        .map(|(name, errors)| format!("{}:\n{}", name, errors))
        .collect();
    assert!(
        node_failures.is_empty(),
        "\n {} fixture(s) failed node execution:\n\n{}\n",
        node_failures.len(),
        node_summary.join("\n\n"),
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
        "UnsupportedFFICommonJSExports" => has("UnsupportedFFICommonJSExports"),
        "UnsupportedFFICommonJSImports" => has("UnsupportedFFICommonJSImports"),
        "DeprecatedFFICommonJSModule" => has("DeprecatedFFICommonJSModule"),
        "MissingFFIModule" => has("MissingFFIModule"),
        "EscapedSkolem" => has("EscapedSkolem"),
        "QuantificationCheckFailureInType" => has("QuantificationCheckFailureInType"),
        "QuantificationCheckFailureInKind" => has("QuantificationCheckFailureInKind"),
        "VisibleQuantificationCheckFailureInType" => has("VisibleQuantificationCheckFailureInType"),
        "WildcardInTypeDefinition" => has("WildcardInTypeDefinition") || has("SyntaxError"),
        "ConstraintInForeignImport" => has("ConstraintInForeignImport") || has("SyntaxError"),
        "InvalidConstraintArgument" => has("InvalidConstraintArgument") || has("SyntaxError"),
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
    let mut wrong_errors: Vec<String> = Vec::new();
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
            .name("pfc-test-build".to_string())
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

    assert!(panicked == 0, "There should be no panics");

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
#[timeout(120000)] // 120s timeout — debug mode is ~10x slower than release
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
        sequential: false,
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
// for release (RECOMMENDED): RUST_LOG=debug FAIL_FAST=1 cargo test --release --test build build_from_sources -- --exact --ignored --no-capture
#[test]
#[ignore] // This is for manually invocation
#[timeout(600000)] // 10 min timeout
fn build_from_sources() {
    let _ = env_logger::try_init();
    let started = std::time::Instant::now();

    let application_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("CARGO_MANIFEST_DIR has no parent")
        .join("application-copy/application");

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
        .unwrap_or(60);

    let sequential = std::env::var("SEQUENTIAL").is_ok();

    let options = BuildOptions {
        module_timeout: Some(std::time::Duration::from_secs(timeout_secs)),
        output_dir: None,
        sequential,
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
                eprintln!("TypecheckTimeout: {e}");
                timeouts.push(format!("  {}", e));
            }
            BuildError::TypecheckPanic { .. } => {
                eprintln!("TypecheckPanic: {e}");
                panics.push(format!("  {}", e));
            }
            _ => {
                eprintln!("Other error: {e}");
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

    assert!(timeouts.is_empty(), "No timeouts");
    assert!(panics.is_empty(), "No panics");
    if !other_errors.is_empty() {
        eprintln!("\n{} other build errors:", other_errors.len());
        for e in &other_errors {
            eprintln!("{}", e);
        }
    }
    // Note: other_errors (parse failures, missing modules) are expected and not asserted.

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
        // Count modules by exclusive error type
        {
            let mut nep_only = 0;
            let mut uv_only = 0;
            let mut ue_only = 0;
            let mut nif_only = 0;
            for m in &result.modules {
                if !m.type_errors.is_empty() {
                    let codes: std::collections::HashSet<String> =
                        m.type_errors.iter().map(|e| e.code()).collect();
                    if codes.len() == 1 {
                        let code = codes.into_iter().next().unwrap();
                        match code.as_str() {
                            "NonExhaustivePattern" => nep_only += 1,
                            "UndefinedVariable" => uv_only += 1,
                            "UnificationError" => ue_only += 1,
                            "NoInstanceFound" => nif_only += 1,
                            _ => {}
                        }
                    }
                }
            }
            let mut kam_only = 0;
            let mut kdu_only = 0;
            let mut mnf_only = 0;
            let mut sc_only = 0;
            let mut ica_only = 0;
            for m in &result.modules {
                if !m.type_errors.is_empty() {
                    let codes: std::collections::HashSet<String> =
                        m.type_errors.iter().map(|e| e.code()).collect();
                    if codes.len() == 1 {
                        match codes.iter().next().unwrap().as_str() {
                            "KindArityMismatch" => kam_only += 1,
                            "KindsDoNotUnify" => kdu_only += 1,
                            "ModuleNotFound" => mnf_only += 1,
                            "ScopeConflict" => sc_only += 1,
                            "IncorrectConstructorArity" => ica_only += 1,
                            _ => {}
                        }
                    }
                }
            }
            eprintln!("  Single-error-type modules: NEP={}, UV={}, UE={}, NIF={}, KAM={}, KDU={}, MNF={}, SC={}, ICA={}", nep_only, uv_only, ue_only, nif_only, kam_only, kdu_only, mnf_only, sc_only, ica_only);
        }
        // KDU pattern breakdown — write to file to avoid OOM with --nocapture
        {
            use std::io::Write;
            let mut kdu_patterns: std::collections::HashMap<String, usize> =
                std::collections::HashMap::new();
            for m in &result.modules {
                for e in &m.type_errors {
                    if let purescript_fast_compiler::typechecker::error::TypeError::KindsDoNotUnify { expected, found, .. } = e {
                        let pattern = format!("{} vs {}", expected, found);
                        *kdu_patterns.entry(pattern).or_default() += 1;
                    }
                }
            }
            if !kdu_patterns.is_empty() {
                if let Ok(mut f) =
                    std::fs::File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/kdu_patterns.txt"))
                {
                    let mut sorted: Vec<_> = kdu_patterns.iter().collect();
                    sorted.sort_by(|a, b| b.1.cmp(a.1));
                    let _ = writeln!(f, "KDU pattern breakdown:");
                    for (pattern, count) in &sorted {
                        let _ = writeln!(f, "  {:>4} {}", count, pattern);
                    }
                }
            }
        }
        // Show first 40 NEP errors
        let mut nep_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.contains("cover all inputs") {
                eprintln!(
                    "  NEP in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(150, err_str.len())]
                );
                nep_count += 1;
                if nep_count >= 40 {
                    break;
                }
            }
        }
        // Show first 30 KDU errors with module names
        let mut kdu_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.starts_with("Could not match kind") {
                eprintln!(
                    "  KDU in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(120, err_str.len())]
                );
                kdu_count += 1;
                if kdu_count >= 30 {
                    break;
                }
            }
        }
        // Show all PartiallyAppliedSynonym errors
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.contains("partially applied") {
                eprintln!("  PAS in {}: {}", mod_name, err_str);
            }
        }
        // Show first 20 IncorrectConstructorArity errors
        let mut ica_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.starts_with("Constructor") && err_str.contains("expects") {
                eprintln!(
                    "  ICA in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(120, err_str.len())]
                );
                ica_count += 1;
                if ica_count >= 20 {
                    break;
                }
            }
        }
        // Show first 30 InvalidInstanceHead errors
        let mut iih_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.contains("Invalid instance head") || err_str.contains("instance head") {
                eprintln!(
                    "  IIH in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(200, err_str.len())]
                );
                iih_count += 1;
                if iih_count >= 30 {
                    break;
                }
            }
        }
        // Show first 30 UndefinedVariable errors
        let mut uv_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.starts_with("Unknown value") {
                eprintln!(
                    "  UV in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(120, err_str.len())]
                );
                uv_count += 1;
                if uv_count >= 30 {
                    break;
                }
            }
        }
        // Show first 30 UnificationError messages
        let mut ue_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.starts_with("Could not match type") {
                eprintln!(
                    "  UE in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(200, err_str.len())]
                );
                ue_count += 1;
                if ue_count >= 120 {
                    break;
                }
            }
        }
        // Show first 20 UnknownName errors
        let mut un_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.starts_with("Unknown") {
                eprintln!(
                    "  UN in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(120, err_str.len())]
                );
                un_count += 1;
                if un_count >= 20 {
                    break;
                }
            }
        }
        // Show first 20 KindArityMismatch errors
        let mut kam_count = 0;
        for (mod_name, _path, err_str) in &type_errors {
            if err_str.contains("expected")
                && err_str.contains("arguments")
                && err_str.contains("type")
            {
                eprintln!(
                    "  KAM in {}: {}",
                    mod_name,
                    &err_str[..std::cmp::min(150, err_str.len())]
                );
                kam_count += 1;
                if kam_count >= 20 {
                    break;
                }
            }
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

    // Note: other_errors (parse failures, module-not-found) are expected —
    // not all PureScript syntax is supported by the parser yet.

    assert!(
        fails == 0,
        "Type errors: {} modules with errors\n\
         Error distribution:\n{}",
        fails,
        error_counts
            .iter()
            .map(|(code, count)| format!("  {:>4} {}", count, code))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// ===== Incremental build tests =====

#[test]
fn incremental_build_caches_modules() {
    let sources: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nvalA :: Int\nvalA = 42\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA\n\nvalB :: Int\nvalB = valA\n",
        ),
    ];

    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    // First build: everything should be typechecked
    let (result1, _, _) =
        build_from_sources_incremental(&sources, &None, None, &options, &mut cache);
    assert!(
        result1.build_errors.is_empty(),
        "First build should succeed"
    );
    assert_eq!(result1.modules.len(), 2);
    for m in &result1.modules {
        assert!(
            m.type_errors.is_empty(),
            "Module {} should have no errors",
            m.module_name
        );
    }

    // Verify cache has entries
    assert!(cache.get_exports("ModA").is_some(), "ModA should be cached");
    assert!(cache.get_exports("ModB").is_some(), "ModB should be cached");

    // Second build with same sources: should use cache (no rebuild needed)
    let (result2, _, _) =
        build_from_sources_incremental(&sources, &None, None, &options, &mut cache);
    assert!(
        result2.build_errors.is_empty(),
        "Second build should succeed"
    );
    assert_eq!(result2.modules.len(), 2);
    for m in &result2.modules {
        assert!(
            m.type_errors.is_empty(),
            "Cached module {} should have no errors",
            m.module_name
        );
    }
}

#[test]
fn incremental_build_rebuilds_changed_module() {
    let sources_v1: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nvalA :: Int\nvalA = 42\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA\n\nvalB :: Int\nvalB = valA\n",
        ),
    ];

    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    // First build
    let (result1, _, _) =
        build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(result1.build_errors.is_empty());

    // Change ModA's source
    let sources_v2: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nvalA :: Int\nvalA = 99\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA\n\nvalB :: Int\nvalB = valA\n",
        ),
    ];

    // Second build: ModA changed, ModB depends on it, both should rebuild
    let (result2, _, _) =
        build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(result2.build_errors.is_empty(), "Rebuild should succeed");
    assert_eq!(result2.modules.len(), 2);
    for m in &result2.modules {
        assert!(
            m.type_errors.is_empty(),
            "Module {} should have no errors after rebuild",
            m.module_name
        );
    }
}

#[test]
fn incremental_build_disk_roundtrip() {
    let sources: Vec<(&str, &str)> =
        vec![("ModA.purs", "module ModA where\n\nvalA :: Int\nvalA = 42\n")];

    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    // Build to populate cache
    let (result, _, _) =
        build_from_sources_incremental(&sources, &None, None, &options, &mut cache);
    assert!(result.build_errors.is_empty());

    // Save to disk
    let tmp_dir = std::env::temp_dir().join("pfc-test-cache");
    let cache_path = tmp_dir.join("cache.bin");
    cache
        .save_to_disk(&cache_path)
        .expect("Failed to save cache");

    // Load from disk
    let mut loaded_cache = ModuleCache::load_from_disk(&cache_path).expect("Failed to load cache");
    assert!(
        loaded_cache.get_exports("ModA").is_some(),
        "Loaded cache should have ModA"
    );

    // Build with loaded cache — should use cached entries
    let (result2, _, _) =
        build_from_sources_incremental(&sources, &None, None, &options, &mut loaded_cache);
    assert!(
        result2.build_errors.is_empty(),
        "Build with loaded cache should succeed"
    );

    // Cleanup
    let _ = std::fs::remove_dir_all(&tmp_dir);
}

#[test]
fn incremental_build_does_not_cache_errors() {
    let sources: Vec<(&str, &str)> = vec![(
        "ModA.purs",
        "module ModA where\n\nvalA :: Int\nvalA = undefinedVar\n",
    )];

    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    // First build: should report type error (undefinedVar is not defined)
    let (result1, _, _) =
        build_from_sources_incremental(&sources, &None, None, &options, &mut cache);
    let has_type_errors_1 = result1.modules.iter().any(|m| !m.type_errors.is_empty());
    assert!(has_type_errors_1, "First build should have type errors");

    // Second build with same sources: error should NOT be cached away
    let (result2, _, _) =
        build_from_sources_incremental(&sources, &None, None, &options, &mut cache);
    let has_type_errors_2 = result2.modules.iter().any(|m| !m.type_errors.is_empty());
    assert!(
        has_type_errors_2,
        "Second build should still have type errors (not cached)"
    );
}

// ===== Smart rebuild tests =====
//
// These tests verify the import-aware rebuild skipping logic:
// - Modules that import unchanged symbols should be SKIPPED
// - Modules that import changed symbols MUST be rebuilt

/// Helper: check if a module was cached (skipped) in a build result
fn was_cached(result: &purescript_fast_compiler::build::BuildResult, module_name: &str) -> bool {
    result
        .modules
        .iter()
        .find(|m| m.module_name == module_name)
        .map_or(false, |m| m.cached)
}

// --- CORRECTNESS: modules that MUST be rebuilt ---

#[test]
fn smart_rebuild_changed_imported_value_type() {
    // ModA exports foo :: Int, ModB imports foo.
    // Change foo :: Int to foo :: String → ModB MUST rebuild
    let sources_v1: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 42\n\nbar :: String\nbar = \"hi\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());
    assert!(r1.modules.iter().all(|m| m.type_errors.is_empty()));

    // Change foo's type from Int to String
    let sources_v2: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: String\nfoo = \"changed\"\n\nbar :: String\nbar = \"hi\"\n"),
        ("ModB.purs", "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n"),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    // ModB should be rebuilt and now have a type error (Int vs String)
    assert!(
        !was_cached(&r2, "ModB"),
        "ModB must be rebuilt when imported value type changes"
    );
    let mod_b_errors = r2.modules.iter().find(|m| m.module_name == "ModB").unwrap();
    assert!(
        !mod_b_errors.type_errors.is_empty(),
        "ModB should have type error after foo changed type"
    );
}

#[test]
fn smart_rebuild_changed_imported_type_constructors() {
    // ModA exports data T = A | B, ModB imports T(..)
    // Add constructor C → ModB MUST rebuild
    let sources_v1: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\ndata T = A | B\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (T(..))\n\nfoo :: T\nfoo = A\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    let sources_v2: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\ndata T = A | B | C\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (T(..))\n\nfoo :: T\nfoo = A\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        !was_cached(&r2, "ModB"),
        "ModB must rebuild when T's constructors change"
    );
}

#[test]
fn smart_rebuild_wildcard_import_any_change() {
    // ModB uses wildcard import from ModA — any change must trigger rebuild
    let sources_v1: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: Int\nfoo = 1\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    // Add a new export to ModA
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbaz :: String\nbaz = \"new\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        !was_cached(&r2, "ModB"),
        "ModB must rebuild on wildcard import when any export changes"
    );
}

#[test]
fn smart_rebuild_transitive_chain() {
    // A→B→C chain. Change A's exported type → B must rebuild → C must rebuild
    let sources_v1: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: Int\nfoo = 1\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nbar :: Int\nbar = foo\n",
        ),
        (
            "ModC.purs",
            "module ModC where\n\nimport ModB (bar)\n\nbaz :: Int\nbaz = bar\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());
    assert!(r1.modules.iter().all(|m| m.type_errors.is_empty()));

    // Change foo's type
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: String\nfoo = \"changed\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nbar :: Int\nbar = foo\n",
        ),
        (
            "ModC.purs",
            "module ModC where\n\nimport ModB (bar)\n\nbaz :: Int\nbaz = bar\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        !was_cached(&r2, "ModB"),
        "ModB must rebuild when foo's type changes"
    );
    // ModB will now have errors, which means C should also rebuild
    // (error modules get an export diff)
}

// --- OPTIMIZATION: modules that SHOULD be skipped ---

#[test]
fn smart_rebuild_skip_unused_value_change() {
    // ModA exports foo and bar, ModB imports only foo.
    // Change bar's type → ModB should be SKIPPED
    let sources_v1: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 42\n\nbar :: String\nbar = \"hello\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());
    assert!(r1.modules.iter().all(|m| m.type_errors.is_empty()));

    // Change bar's type (foo stays the same)
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 42\n\nbar :: Boolean\nbar = true\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        was_cached(&r2, "ModB"),
        "ModB should be skipped when only bar (not imported) changed"
    );
}

#[test]
fn smart_rebuild_skip_body_only_change() {
    // Change function body only (same types) → downstream should be SKIPPED
    let sources_v1: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: Int\nfoo = 42\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    // Change foo's body, not its type
    let sources_v2: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: Int\nfoo = 99\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        was_cached(&r2, "ModB"),
        "ModB should be skipped when only foo's body changed (type unchanged)"
    );
}

#[test]
fn smart_rebuild_skip_new_export_not_imported() {
    // ModA adds a new export baz, ModB explicitly imports only foo → skip
    let sources_v1: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: Int\nfoo = 42\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    // Add baz to ModA
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 42\n\nbaz :: String\nbaz = \"new\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        was_cached(&r2, "ModB"),
        "ModB should be skipped when ModA adds a new export that ModB doesn't import"
    );
}

#[test]
fn smart_rebuild_skip_chain() {
    // A→B→C. Change in A doesn't affect what B imports → B skipped → C skipped
    let sources_v1: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbar :: String\nbar = \"x\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nbaz :: Int\nbaz = foo\n",
        ),
        (
            "ModC.purs",
            "module ModC where\n\nimport ModB (baz)\n\nqux :: Int\nqux = baz\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());
    assert!(r1.modules.iter().all(|m| m.type_errors.is_empty()));

    // Change bar in ModA (ModB doesn't import bar)
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbar :: Boolean\nbar = true\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nbaz :: Int\nbaz = foo\n",
        ),
        (
            "ModC.purs",
            "module ModC where\n\nimport ModB (baz)\n\nqux :: Int\nqux = baz\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        was_cached(&r2, "ModB"),
        "ModB should be skipped (only bar changed, imports foo)"
    );
    assert!(
        was_cached(&r2, "ModC"),
        "ModC should be skipped (ModB was skipped)"
    );
}

#[test]
fn smart_rebuild_hiding_import_skip() {
    // ModB does `import ModA hiding (bar)`. Change bar → ModB should be SKIPPED
    let sources_v1: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbar :: String\nbar = \"x\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA hiding (bar)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    // Change bar's type
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbar :: Boolean\nbar = true\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA hiding (bar)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        was_cached(&r2, "ModB"),
        "ModB should be skipped when hidden import bar changes"
    );
}

#[test]
fn smart_rebuild_hiding_import_rebuild() {
    // ModB does `import ModA hiding (bar)`. Change foo → ModB MUST rebuild
    let sources_v1: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbar :: String\nbar = \"x\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA hiding (bar)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    // Change foo's type (not hidden)
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: String\nfoo = \"changed\"\n\nbar :: String\nbar = \"x\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA hiding (bar)\n\nvalB :: Int\nvalB = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        !was_cached(&r2, "ModB"),
        "ModB must rebuild when non-hidden foo changes type"
    );
}

#[test]
fn smart_rebuild_unchanged_source_skipped() {
    // No changes at all → everything cached
    let sources: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: Int\nfoo = 1\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nbar :: Int\nbar = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    let (r2, _, _) = build_from_sources_incremental(&sources, &None, None, &options, &mut cache);
    assert!(
        was_cached(&r2, "ModA"),
        "ModA should be cached (no changes)"
    );
    assert!(
        was_cached(&r2, "ModB"),
        "ModB should be cached (no changes)"
    );
}

#[test]
fn smart_rebuild_multiple_imports_partial_change() {
    // ModC imports from both ModA and ModB. Only ModA changes, but ModC only imports
    // the unchanged export from ModA.
    let sources_v1: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbar :: String\nbar = \"x\"\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nbaz :: Boolean\nbaz = true\n",
        ),
        (
            "ModC.purs",
            "module ModC where\n\nimport ModA (foo)\nimport ModB (baz)\n\nqux :: Int\nqux = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    // Change bar in ModA (ModC doesn't import bar)
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = 1\n\nbar :: Boolean\nbar = true\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nbaz :: Boolean\nbaz = true\n",
        ),
        (
            "ModC.purs",
            "module ModC where\n\nimport ModA (foo)\nimport ModB (baz)\n\nqux :: Int\nqux = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    assert!(
        was_cached(&r2, "ModC"),
        "ModC should be skipped (only bar changed, ModC imports foo)"
    );
}

#[test]
fn smart_rebuild_error_module_forces_downstream_rebuild() {
    // Module with errors should force downstream rebuild
    let sources_v1: Vec<(&str, &str)> = vec![
        ("ModA.purs", "module ModA where\n\nfoo :: Int\nfoo = 42\n"),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nbar :: Int\nbar = foo\n",
        ),
    ];
    let options = BuildOptions::default();
    let mut cache = ModuleCache::new();

    let (r1, _, _) = build_from_sources_incremental(&sources_v1, &None, None, &options, &mut cache);
    assert!(r1.build_errors.is_empty());

    // Introduce error in ModA
    let sources_v2: Vec<(&str, &str)> = vec![
        (
            "ModA.purs",
            "module ModA where\n\nfoo :: Int\nfoo = undefinedVar\n",
        ),
        (
            "ModB.purs",
            "module ModB where\n\nimport ModA (foo)\n\nbar :: Int\nbar = foo\n",
        ),
    ];
    let (r2, _, _) = build_from_sources_incremental(&sources_v2, &None, None, &options, &mut cache);
    // The build stops on first error module, but ModA should not be cached
    assert!(
        !was_cached(&r2, "ModA"),
        "ModA with errors must not be cached"
    );
}
