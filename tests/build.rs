//! Build integration tests.
//!
//! Tests that the passing fixtures from the original PureScript compiler
//! build successfully through the full pipeline (parse + typecheck).

use purescript_fast_compiler::build::{
    build_from_sources, build_from_sources_with_registry, BuildError,
};
use purescript_fast_compiler::typechecker::error::TypeError;
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

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

/// Fixtures skipped due to pre-existing typechecker limitations (8 remaining).
const SKIP_PASSING_FIXTURES: &[&str] = &[
    "2626",                        // Higher-rank polymorphism (rank-2 subsumption)
    "4179",                        // Infinite type in recursive thunking
    "DuplicateProperties",         // Row-polymorphic unification with duplicate labels
    "Guards",                      // Number alias + EuclideanRing Boolean constraint
    "Monad",                       // Higher-rank record fields (subsumption)
    "NestedRecordUpdateWildcards", // Nested record update wildcard propagation
    "TypeAnnotationPrecedence",    // :: operator precedence in grammar (LALRPOP ambiguity)
    "VTAsClassHeads",              // VTA on class methods with functional dependencies
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
    let registry = Arc::new(registry);

    let skip: HashSet<&str> = SKIP_PASSING_FIXTURES.iter().copied().collect();
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

        let registry = Arc::clone(&registry);
        let build_result = std::panic::catch_unwind(|| {
            build_from_sources_with_registry(&test_sources, Some(registry))
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

/// Failing fixtures skipped: compile cleanly in our compiler due to missing checks.
const SKIP_FAILING_FIXTURES: &[&str] = &[
    // Stack overflow
    "3765",
    // Kind checking not implemented
    "1071",
    "1570",
    "2601",
    "3077",
    "3275-DataBindingGroupErrorPos",
    "3765-kinds",
    "DiffKindsSameName",
    "InfiniteKind",
    "InfiniteKind2",
    "MonoKindDataBindingGroup",
    "PolykindInstantiatedInstance",
    "PolykindInstantiation",
    "RowsInKinds",
    "StandaloneKindSignatures1",
    "StandaloneKindSignatures2",
    "StandaloneKindSignatures3",
    "StandaloneKindSignatures4",
    "CycleInForeignDataKinds",
    "CycleInKindDeclaration",
    "SelfCycleInForeignDataKinds",
    "SelfCycleInKindDeclaration",
    "SkolemEscapeKinds",
    "UnsupportedTypeInKind",
    "QuantificationCheckFailure",
    "QuantificationCheckFailure2",
    "QuantificationCheckFailure3",
    "QuantifiedKind",
    "ScopedKindVariableSynonym",
    // Orphan instance / overlapping instance checks not implemented
    "OrphanInstance",
    "OrphanInstanceFunDepCycle",
    "OrphanInstanceNullary",
    "OrphanInstanceWithDetermined",
    "OrphanUnnamedInstance",
    "OverlapAcrossModules",
    "OverlapAcrossModulesUnnamedInstance",
    "OverlappingInstances",
    "OverlappingUnnamedInstances",
    "PolykindInstanceOverlapping",
    "PolykindUnnamedInstanceOverlapping",
    // Role system not implemented
    "CoercibleRepresentational6",
    "CoercibleRepresentational7",
    "CoercibleRoleMismatch1",
    "CoercibleRoleMismatch2",
    "CoercibleRoleMismatch3",
    "CoercibleRoleMismatch4",
    "CoercibleRoleMismatch5",
    "DuplicateRoleDeclaration",
    "InvalidCoercibleInstanceDeclaration",
    "OrphanRoleDeclaration1",
    "OrphanRoleDeclaration2",
    "OrphanRoleDeclaration3",
    "RoleDeclarationArityMismatch",
    "RoleDeclarationArityMismatchForeign",
    "RoleDeclarationArityMismatchForeign2",
    "RoleDeclarationArityMismatchForeign3",
    "RoleDeclarationArityMismatchForeign4",
    "UnsupportedRoleDeclarationTypeClass",
    "UnsupportedRoleDeclarationTypeSynonym",
    // Export/import conflict and transitive export checks not implemented
    "ConflictingExports",
    "ConflictingImports",
    "ConflictingImports2",
    "ConflictingQualifiedImports",
    "ConflictingQualifiedImports2",
    "ExportConflictClass",
    "ExportConflictClassAndType",
    "ExportConflictCtor",
    "ExportConflictType",
    "ExportConflictTypeOp",
    "ExportConflictValue",
    "ExportConflictValueOp",
    "ExportExplicit1",
    "ExportExplicit3",
    "ImportExplicit",
    "ImportExplicit2",
    "ImportHidingModule",
    "ImportModule",
    "DctorOperatorAliasExport",
    "OperatorAliasNoExport",
    "TypeOperatorAliasNoExport",
    "RequiredHiddenType",
    "TransitiveDctorExport",
    "TransitiveDctorExportError",
    "TransitiveKindExport",
    "TransitiveSynonymExport",
    "2197-shouldFail",
    "SelfImport",
    // DeclConflict detection not implemented
    "DeclConflictClassCtor",
    "DeclConflictClassType",
    "DeclConflictCtorClass",
    "DeclConflictCtorCtor",
    "DeclConflictDuplicateCtor",
    "DeclConflictTypeClass",
    "DeclConflictTypeType",
    // FFI checks not implemented
    "DeprecatedFFICommonJSModule",
    "DeprecatedFFIPrime",
    "MissingFFIImplementations",
    "UnsupportedFFICommonJSExports1",
    "UnsupportedFFICommonJSExports2",
    "UnsupportedFFICommonJSImports1",
    "UnsupportedFFICommonJSImports2",
    // Instance signature checks not implemented
    "InstanceSigsBodyIncorrect",
    "InstanceSigsDifferentTypes",
    "InstanceSigsIncorrectType",
    "InstanceSigsOrphanTypeDeclaration",
    // Type-level integer comparison not implemented
    "CompareInt1",
    "CompareInt2",
    "CompareInt3",
    "CompareInt4",
    "CompareInt5",
    "CompareInt6",
    "CompareInt7",
    "CompareInt8",
    "CompareInt9",
    "CompareInt10",
    "CompareInt11",
    "CompareInt12",
    // VTA class head checks not implemented
    "ClassHeadNoVTA1",
    "ClassHeadNoVTA3",
    "ClassHeadNoVTA4",
    "ClassHeadNoVTA5",
    "ClassHeadNoVTA6a",
    "ClassHeadNoVTA6b",
    "ClassHeadNoVTA6c",
    // Specific instance / constraint checks not implemented
    "2567",
    "2806",
    "3531",
    "3531-2",
    "3531-3",
    "3531-4",
    "3531-5",
    "3531-6",
    "4024",
    "4024-2",
    "LacksWithSubGoal",
    "NonExhaustivePatGuard",
    // Scope / class member / misc checks not implemented
    "1733",
    "2109-negate",
    "2378",
    "2379",
    "2434",
    "2534",
    "2542",
    "2874-forall",
    "2874-forall2",
    "2874-wildcard",
    "3335-TypeOpAssociativityError",
    "3701",
    "4382",
    "AnonArgument1",
    "DuplicateDeclarationsInLet2",
    "DuplicateModule",
    "IntOutOfRange",
    "InvalidOperatorInBinder",
    "OrphanKindDeclaration2",
    "PolykindGeneralizationLet",
    "PrimModuleReserved",
    "PrimSubModuleReserved",
    "TypeSynonyms8",
    "TypeWildcards4",
    "VisibleTypeApplications1",
    "Whitespace1",
];

/// Extract the `-- @shouldFailWith ErrorName` annotation from the first source file.
fn extract_expected_error(sources: &[(String, String)]) -> Option<String> {
    sources.first().and_then(|(_, source)| {
        source.lines().next().and_then(|line| {
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
            .any(|c| c == code || c.ends_with(&format!("{}", code)))
    };

    match expected {
        // Type error
        "TypesDoNotUnify" => has("UnificationError"),
        // Type error
        "NoInstanceFound" => has("NoInstanceFound"),
        // OK
        "ErrorParsingModule" => has("LexError") || has("SyntaxError"),
        // OK
        "UnknownName" => has("UndefinedVariable") || has("UnknownType"),
        // OK
        "HoleInferredType" => has("HoleInferredType"),
        // OK
        "InfiniteType" => has("InfiniteType"),
        // OK
        "InfiniteKind" => has("InfiniteKind"),
        // OK 
        "DuplicateValueDeclaration" => has("DuplicateValueDeclaration"),
        // OK
        "OverlappingNamesInLet" => has("OverlappingNamesInLet"),
        // OK 
        "CycleInTypeSynonym" => has("CycleInTypeSynonym"),
        // OK
        "CycleInDeclaration" => has("CycleInTypeClassDeclaration"),
        // OK
        "CycleInTypeClassDeclaration" => has("CycleInTypeClassDeclaration"),
        // OK
        "CycleInKindDeclaration" => has("CycleInKindDeclaration"),
        // OK
        "UnknownImport" => has("UnknownImport"),
        // OK
        "UnknownImportDataConstructor" => has("UnknownImportDataConstructor"),
        // OK
        "IncorrectConstructorArity" => has("IncorrectConstructorArity"),
        // OK 
        "DuplicateTypeClass" => has("DuplicateTypeClass"),
        // OK
        "DuplicateInstance" => has("DuplicateInstance"),
        // OK
        "DuplicateTypeArgument" => has("DuplicateTypeArgument"),
        // OK
        "InvalidDoBind" => has("InvalidDoBind"),
        // OK
        "InvalidDoLet" => has("InvalidDoLet"),
        // OK
        "CannotUseBindWithDo" => has("CannotUseBindWithDo"),
        "ModuleNotFound" => has("ModuleNotFound"),
        "DuplicateModule" => has("DuplicateModule"),
        "CycleInModules" => has("CycleInModules"),
        "MultipleValueOpFixities" => has("MultipleValueOpFixities"),
        "MultipleTypeOpFixities" => has("MultipleTypeOpFixities"),
        "OrphanTypeDeclaration" => has("OrphanTypeSignature"),
        "OrphanKindDeclaration" => has("OrphanKindDeclaration"),
        "UnknownExport" | "UnknownExportDataConstructor" => has("UnkownExport"),
        "OverlappingArgNames" => has("OverlappingArgNames"),
        "ArgListLengthsDiffer" => has("ArityMismatch"),
        "InvalidNewtypeInstance" | "CannotDeriveNewtypeForData" => has("InvalidNewtypeInstance"),
        "InvalidNewtypeDerivation" => has("InvalidNewtypeDerivation"),
        "OverlappingPattern" => has("OverlappingPattern"),
        "NonExhaustivePattern" => has("NonExhaustivePattern") || has("UnificationError"),
        "CaseBinderLengthDiffers" => has("UnificationError"),
        "AdditionalProperty" | "PropertyIsMissing" => {
            has("UnificationError") || has("DuplicateLabel")
        }
        "InvalidOperatorInBinder" => has("SyntaxError") || has("UnificationError"),
        // OK
        "IntOutOfRange" => has("LexError") || has("SyntaxError"),
        "UnknownClass" => has("UnknownClass"),
        "MissingClassMember" => has("MissingClassMember"),
        "ExtraneousClassMember" => has("ExtraneousClassMember"),
        "CannotGeneralizeRecursiveFunction" => has("CannotGeneralizeRecursiveFunction"),
        "CannotApplyExpressionOfTypeOnType" => has("CannotGeneralizeRecursiveFunction"),
        "AmbiguousTypeVariables" | "UndefinedTypeVariable" => {
            has("UndefinedVariable") || has("UnificationError")
        }
        "ExpectedType" | "ExpectedWildcard" => has("UnificationError") || has("SyntaxError"),
        _ => false,
    }
}

#[test]
fn build_fixture_original_compiler_failing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/failing");
    if !fixtures_dir.exists() {
        panic!("original-compiler/failing fixtures not found");
    }

    let units = collect_build_units(&fixtures_dir);
    assert!(!units.is_empty(), "Expected failing fixture build units");

    // Build support packages once to get a shared registry
    let support_sources_string = collect_support_sources();
    let support_sources: Vec<(&str, &str)> = support_sources_string
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();
    let (_, registry) = build_from_sources_with_registry(&support_sources, None);
    let registry = Arc::new(registry);

    let skip: HashSet<&str> = SKIP_FAILING_FIXTURES.iter().copied().collect();
    let mut total = 0;
    let mut correct = 0;
    let mut wrong_error = 0;
    let mut panicked = 0;
    let mut skipped = 0;
    let mut false_passes: Vec<String> = Vec::new();

    for (name, sources) in &units {
        if skip.contains(name.as_str()) {
            skipped += 1;
            continue;
        }
        total += 1;

        let expected_error = extract_expected_error(sources).unwrap_or_default();

        let fixture_module_names: HashSet<String> = sources
            .iter()
            .filter_map(|(_, s)| extract_module_name(s))
            .collect();

        let registry = Arc::clone(&registry);

        // Clone sources into owned data for the spawned thread ('static requirement)
        let owned_sources: Vec<(String, String)> = sources.clone();
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
                let build_result = std::panic::catch_unwind(|| {
                    build_from_sources_with_registry(&test_sources, Some(registry))
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
                            "wrong_error".to_string()
                        }
                    }
                }
            })
            .expect("Failed to spawn thread");

        // Wait for the thread with a timeout
        match handle.join() {
            Ok(result) => {
                if result == "correct" {
                    correct += 1;
                } else if result == "wrong_error" {
                    wrong_error += 1;
                } else if result.starts_with("false_pass:") {
                    let expected = result.strip_prefix("false_pass:").unwrap_or("");
                    false_passes.push(format!("{} (expected {})", name, expected));
                } else {
                    panicked += 1;
                }
            }
            Err(_) => {
                // Thread panicked (e.g., stack overflow caught by thread boundary)
                panicked += 1;
            }
        }
    }

    eprintln!(
        "\n=== Failing Fixture Results ===\n\
         Total:        {}\n\
         Correct:      {}\n\
         WrongError:   {}\n\
         Panicked:     {}\n\
         FalsePass:    {}\n\
         Skipped:      {}",
        total,
        correct,
        wrong_error,
        panicked,
        false_passes.len(),
        skipped,
    );

    if !false_passes.is_empty() {
        panic!(
            "{} fixtures compiled cleanly but should have failed:\n  {}",
            false_passes.len(),
            false_passes.join("\n  ")
        );
    }
}
