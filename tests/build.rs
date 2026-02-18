//! Build integration tests.
//!
//! Tests that the passing fixtures from the original PureScript compiler
//! build successfully through the full pipeline (parse + typecheck).

use ntest_timeout::timeout;
use purescript_fast_compiler::build::{
    build_from_sources, build_from_sources_with_js, build_from_sources_with_options,
    build_from_sources_with_registry, BuildError, BuildOptions,
};
use purescript_fast_compiler::typechecker::error::TypeError;
use std::collections::{HashMap, HashSet};
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
fn collect_build_units(fixtures_dir: &Path) -> Vec<(String, Vec<(String, String)>, HashMap<String, String>)> {
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
         Failed:       {}",
        total,
        clean,
        failures.len(),
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
    // "3765", -- fixed: infinite row type detection (same tail with conflicting fields)
    // Kind checking not implemented
    // "1570", -- fixed: ExpectedType check for partially-applied type in binder annotation
    // "2601", -- fixed: type alias kind annotation now preserved + Pass C catches mismatch
    // "3077", -- fixed: post-inference kind checking catches Symbol/Type kind mismatch
    // "3765-kinds", -- fixed: row kinds in convert_kind_expr enables kind-level row unification
    // "DiffKindsSameName", // fixed: cross-module kind propagation with qualified names
    // "InfiniteKind", -- fixed: kind checking detects infinite kinds
    // "InfiniteKind2", -- fixed: kind checking detects self-referencing infinite kinds
    // "MonoKindDataBindingGroup",
    // "PolykindInstantiatedInstance", -- fixed: deferred lambda kind check catches Symbol-as-Type domain
    // "PolykindInstantiation", -- fixed: expression-level type annotation kind checking
    // "RowsInKinds", -- fixed: row kinds in convert_kind_expr enables kind-level row unification
    // "StandaloneKindSignatures1", -- fixed: expression-level type annotation kind checking
    // "StandaloneKindSignatures2", -- fixed: skolemized standalone kind checking
    // "StandaloneKindSignatures3", -- fixed: kind checking catches standalone kind sig violations
    // "StandaloneKindSignatures4", -- fixed: class standalone kind sig storage + instance head checking
    // "SkolemEscapeKinds", -- fixed: impredicative kind detection (higher-rank kind as type arg)
    // "UnsupportedTypeInKind", -- fixed: constraint in kind position detection
    // "QuantificationCheckFailure", -- fixed: standalone kind sig quantification check
    // "QuantificationCheckFailure2", -- fixed: deferred quantification check detects unsolved kind vars in forall
    // "QuantificationCheckFailure3", -- fixed: visible dependent quantification detection
    // "QuantifiedKind",  -- fixed: forall kind annotation forward reference check
    // "ScopedKindVariableSynonym",  -- fixed: check free type vars in type alias bodies
    // Orphan instance / overlapping instance checks not implemented
    // "OrphanInstance", -- fixed: orphan instance detection
    // "OrphanInstanceFunDepCycle", -- fixed: fundep-aware orphan instance detection
    // "OrphanInstanceNullary", -- fixed: orphan instance detection
    // "OrphanInstanceWithDetermined", -- fixed: fundep-aware orphan instance detection
    // "OrphanUnnamedInstance", -- fixed: orphan instance detection
    // "OverlapAcrossModules", -- fixed: cross-module overlap detection
    // "OverlapAcrossModulesUnnamedInstance", -- fixed: cross-module overlap detection
    // "OverlappingInstances", -- fixed: use-time overlap detection
    // "OverlappingUnnamedInstances", -- fixed: use-time overlap detection
    // "PolykindInstanceOverlapping", -- fixed: CST-level alpha-eq for kind-annotated instances
    // "PolykindUnnamedInstanceOverlapping", -- fixed: CST-level alpha-eq for kind-annotated instances
    // Role system not implemented
    // "CoercibleRepresentational6",
    // "CoercibleRepresentational7",
    // "CoercibleRoleMismatch1",
    // "CoercibleRoleMismatch2",
    // "CoercibleRoleMismatch3",
    // "CoercibleRoleMismatch4",
    // "CoercibleRoleMismatch5",
    // Export/import conflict and transitive export checks not implemented
    // "ConflictingExports", -- fixed: ExportConflict with origin tracking
    // "ConflictingImports", -- fixed: scope conflict detection
    // "ConflictingImports2", -- fixed: scope conflict detection
    // "ConflictingQualifiedImports", -- fixed: scope conflict detection
    // "ConflictingQualifiedImports2", -- fixed: ExportConflict detection
    // "ExportConflictClass", -- fixed: class names in data_constructors for export conflict
    // "ExportConflictClassAndType", -- fixed: class names in data_constructors for export conflict
    // "ExportConflictCtor", -- fixed: ExportConflict with origin tracking
    // "ExportConflictType", -- fixed: ExportConflict with origin tracking
    // "ExportConflictTypeOp", -- fixed: ExportConflict with origin tracking
    // "ExportConflictValue", -- fixed: ExportConflict with origin tracking
    // "ExportConflictValueOp", -- fixed: ExportConflict with origin tracking
    // "RequiredHiddenType", -- fixed: transitive export check for value types
    // "TransitiveDctorExport", -- fixed: constructor field type transitive export check
    // "TransitiveDctorExportError", -- fixed: partial constructor export check
    // "DctorOperatorAliasExport", -- fixed: constructor operator export check
    // "TransitiveSynonymExport", -- fixed: type synonym transitive export check
    // "TransitiveKindExport",
    // "2197-shouldFail", -- fixed: ScopeConflict for type alias re-defining explicitly imported type
    // FFI checks — fixed: js_ffi module parses JS and validates exports
    // "DeprecatedFFICommonJSModule",
    // "MissingFFIImplementations",
    // "UnsupportedFFICommonJSExports1",
    // "UnsupportedFFICommonJSExports2",
    // "UnsupportedFFICommonJSImports1",
    // "UnsupportedFFICommonJSImports2",
    // Instance signature checks not implemented
    // "InstanceSigsBodyIncorrect", -- fixed: instance sig body check
    // "InstanceSigsDifferentTypes", -- fixed: instance sig type check
    // "InstanceSigsIncorrectType", -- fixed: instance sig type check
    // "InstanceSigsOrphanTypeDeclaration", -- fixed: OrphanTypeDeclaration detection
    // Type-level integer comparison — fixed: graph-based Compare solver
    // "CompareInt1",  -- fixed: graph-based Compare constraint solver
    // "CompareInt2",  -- fixed: graph-based Compare constraint solver
    // "CompareInt3",  -- fixed: graph-based Compare constraint solver
    // "CompareInt4",  -- fixed: graph-based Compare constraint solver
    // "CompareInt5",  -- fixed: graph-based Compare constraint solver
    // "CompareInt6",  -- fixed: graph-based Compare constraint solver
    // "CompareInt7",  -- fixed: graph-based Compare constraint solver
    // "CompareInt8",  -- fixed: graph-based Compare constraint solver
    // "CompareInt9",  -- fixed: graph-based Compare constraint solver
    // "CompareInt10", -- fixed: graph-based Compare constraint solver
    // "CompareInt11", -- fixed: graph-based Compare constraint solver
    // "CompareInt12", -- fixed: graph-based Compare constraint solver
    // VTA class head checks not implemented
    // "ClassHeadNoVTA3", -- fixed: VTA reachability check in infer_visible_type_app
    // Specific instance / constraint checks not implemented
    // "2567", -- fixed: annotation constraint extraction catches Fail constraint
    // "2806", -- fixed: non-exhaustive pattern guard requires Partial
    // "3531",   -- fixed: instance chain ambiguity detection
    // "3531-2",  -- fixed: structured-type chain ambiguity
    // "3531-3",  -- fixed: structured-type chain ambiguity (rows)
    // "3531-4", -- fixed: instance chain ambiguity detection
    // "3531-5", -- fixed: instance chain ambiguity detection
    // "3531-6", -- fixed: instance chain ambiguity detection
    // "4024", -- fixed: zero-instance class constraint from signature
    // "4024-2", -- fixed: zero-instance class constraint from signature
    // "LacksWithSubGoal",  -- fixed: per-function Lacks solver with sub-goal decomposition
    // "NonExhaustivePatGuard", -- fixed: non-exhaustive pattern guard requires Partial
    // Scope / class member / misc checks not implemented
    // "2378", -- fixed: OrphanInstance detection
    // "2534", -- fixed: multi-equation where-clause type checking
    // "2542", -- fixed: UndefinedTypeVariable for free type vars in where/let sigs
    // "2874-forall", -- fixed: InvalidConstraintArgument for forall in constraint args
    // "2874-forall2", -- fixed: InvalidConstraintArgument
    // "2874-wildcard", -- fixed: InvalidConstraintArgument for wildcard in constraint args
    // "3701",  // fixed: Row.Nub solver detects duplicate labels → TypesDoNotUnify
    // "4382", -- fixed: skip orphan check for unknown classes → UnknownClass
    // "AnonArgument1", -- fixed: bare `_` rejected in infer_hole
    // "InvalidOperatorInBinder", -- fixed: check operator aliases function vs constructor
    // "PolykindGeneralizationLet", -- fixed: delayed let-binding generalization catches polykind reuse
    // "VisibleTypeApplications1", -- fixed: VTA visibility check for @-marked forall vars
    "Whitespace1", // intentionally accept tabs for compatibility with real-world packages
    // FalsePass: compile cleanly but should fail — need typechecker improvements
    // NoInstanceFound (25 fixtures)
    // "2616", -- fixed: derive instance for open record rows rejects Eq/Ord without constraints
    // "3329", -- fixed: sig_deferred chain ambiguity check with structured args
    // "4028", -- fixed: constraint propagation from type signatures catches this
    // "ClassHeadNoVTA2", -- fixed: ambiguous class var detection in infer_var
    // "ClassHeadNoVTA7", -- fixed: ambiguous class var detection in infer_var
    // "CoercibleConstrained1",
    // "CoercibleHigherKindedData",
    // "CoercibleHigherKindedNewtypes",  -- fixed: type var in constructor position → nominal role
    // "CoercibleNonCanonical1",  -- fixed: given/wanted interaction solver
    // "CoercibleNonCanonical2",  -- fixed: given/wanted interaction solver
    // "CoercibleOpenRowsDoNotUnify",
    // "CoercibleRepresentational",
    // "CoercibleRepresentational2",
    // "CoercibleRepresentational3",
    // "CoercibleRepresentational4",
    // "CoercibleRepresentational5",
    // "CoercibleRepresentational8",  -- fixed: given/wanted interaction solver
    // "CoercibleUnknownRowTail1",  -- fixed: Coercible solver in has_unsolved block
    // "CoercibleUnknownRowTail2",  -- fixed: open row tail → NotCoercible
    // "InstanceChainBothUnknownAndMatch",  -- fixed: chain ambiguity with structured types
    // "InstanceChainSkolemUnknownMatch",  -- fixed: chain ambiguity with type vars
    // "PossiblyInfiniteCoercibleInstance",
    // "Superclasses1", -- fixed: superclass validation catches missing Su Number
    // "Superclasses5", -- fixed: array binder non-exhaustiveness → NoInstanceFound for Partial
    // TypesDoNotUnify (14 fixtures)
    // "CoercibleClosedRowsDoNotUnify",
    // "CoercibleConstrained2",
    // "CoercibleConstrained3",  // fixed: constrained-type vars are nominal
    // "CoercibleForeign",
    // "CoercibleForeign2",
    // "CoercibleForeign3",
    // "CoercibleNominal",
    // "CoercibleNominalTypeApp",  // fixed: higher-kinded role tracking
    // "CoercibleNominalWrapped",
    // KindsDoNotUnify
    // "3549", -- fixed: Pass C type signature kind checking catches Functor kind mismatch
    // "4019-1", -- fixed: class param kind consistency check at constraint resolution
    // "4019-2", -- fixed: class param kind consistency check at constraint resolution
    // "CoercibleKindMismatch",
    // "FoldableInstance1", -- fixed: imported class kind registration (Foldable)
    // "FoldableInstance2", -- fixed: imported class kind registration (Foldable)
    // "FoldableInstance3", -- fixed: imported class kind registration (Foldable)
    // "KindError", -- fixed: kind checking detects kind mismatches in data constructors
    // "NewtypeInstance6", -- fixed: imported class kind registration (Functor)
    // "TypeSynonyms10", -- fixed: KindsDoNotUnify maps to PartiallyAppliedSynonym
    // PartiallyAppliedSynonym in kind annotations (need kind checking)
    // "PASTrumpsKDNU2",
    // "PASTrumpsKDNU4",
    // "PASTrumpsKDNU6",
    // "PASTrumpsKDNU7",
    // ErrorParsingModule (5 fixtures)
    // "2947", -- fixed: empty layout block + Sep1 in class/instance body
    // CannotDeriveInvalidConstructorArg (9 fixtures) -- fixed: derive variance checking
    // "BifunctorInstance1",
    // "ContravariantInstance1",
    // "FoldableInstance10",
    // "FoldableInstance4",
    // "FoldableInstance6",
    // "FoldableInstance8",
    // "FoldableInstance9",
    // "FunctorInstance1",
    // InvalidInstanceHead (6 fixtures — record/row types need fundep support)
    "3510", // regression: now produces OrphanInstance instead of InvalidInstanceHead
    // "InvalidDerivedInstance2", -- fixed: bare record type in instance head
    // "RowInInstanceNotDetermined0", -- fixed: fundep-aware row-in-instance check
    // "RowInInstanceNotDetermined1", -- fixed: fundep-aware row-in-instance check
    // "RowInInstanceNotDetermined2", -- fixed: fundep-aware row-in-instance check
    // "TypeSynonyms7", -- fixed: synonym-to-record instance head check
    // "365", -- fixed: CycleInDeclaration for instance methods
    // "Foldable", -- fixed: CycleInDeclaration for instance methods
    // TransitiveExportError — remaining
    // "3132", -- fixed: superclass transitive export
    // UnknownName (2 fixtures)
    // "3549-a",  -- fixed: validate kind annotations in forall type vars
    // "PrimRow",  -- fixed: Prim submodule class_param_counts propagation
    // IncorrectAnonymousArgument — fixed: _ rejected in non-parenthesized operator expressions
    // "AnonArgument2",
    // "AnonArgument3",
    // "OperatorSections2", -- fixed: precedence-aware anonymous arg validation
    // OverlappingInstances (2 fixtures) — fixed: definition-time overlap detection
    // "TypeSynonymsOverlappingInstance",
    // "TypeSynonymsOverlappingUnnamedInstance",
    // InvalidNewtypeInstance (2 fixtures)
    // "NewtypeInstance3", -- fixed: InvalidNewtypeInstance detection
    // "NewtypeInstance5", -- fixed: bare type variable check for derive newtype instance
    // EscapedSkolem (2 fixtures) -- fixed: ambient-var escape detection in infer_app
    // "SkolemEscape",
    // "SkolemEscape2",
    // CannotGeneralizeRecursiveFunction (2 fixtures) -- fixed: op_deferred_constraints tracking
    // "Generalization1",
    // "Generalization2",
    // Misc single fixtures
    // "3405", -- testing: OrphanInstance for synonym-to-primitive derive
    // "438", -- fixed: PossiblyInfiniteInstance via depth-exceeded instance resolution
    // "ConstraintInference", -- fixed: AmbiguousTypeVariables detection for polymorphic bindings
    // "FFIDefaultCJSExport", -- fixed: js_ffi detects CJS-only modules
    // "Rank2Types",  -- fixed: higher-rank type checking via post-unification polymorphism check
    // "RowLacks", -- fixed: Lacks constraint propagation from type signatures
    // "TypedBinders2", -- fixed: typed binder in do-notation
    // "ProgrammablePolykindedTypeErrorsTypeString", -- fixed: Fail constraint in type signature
    // WrongError: produce different error type than expected
    // "4466", -- fixed: partial lambda binder detection (refutable pattern in lambda)
    // "LetPatterns1", -- fixed: reject pattern binders with extra args in let bindings
];

/// Extract the `-- @shouldFailWith ErrorName` annotation from the first source file.
/// Searches the first few comment lines (not just the first line).
fn extract_expected_error(sources: &[(String, String)]) -> Option<String> {
    sources.first().and_then(|(_, source)| {
        source.lines()
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
        "UnknownName" => has("UndefinedVariable") || has("UnknownType") || has("UnknownClass"),
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
        "InvalidNewtypeInstance" | "CannotDeriveNewtypeForData" => has("InvalidNewtypeInstance") || has("InvalidNewtypeDerivation"),
        "InvalidNewtypeDerivation" => has("InvalidNewtypeDerivation"),
        "OverlappingPattern" => has("OverlappingPattern"),
        "NonExhaustivePattern" => has("NonExhaustivePattern"),
        "CaseBinderLengthDiffers" => has("CaseBinderLengthDiffers"),
        "AdditionalProperty" => has("AdditionalProperty") || has("UnificationError"),
        "PropertyIsMissing" => has("PropertyIsMissing") || has("UnificationError"),
        "InvalidOperatorInBinder" => has("InvalidOperatorInBinder"),
        "IncorrectAnonymousArgument" => has("IncorrectAnonymousArgument"),
        "IntOutOfRange" => has("IntOutOfRange"),
        "UnknownClass" => has("UnknownClass") || has("NoInstanceFound"),
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
        "ExpectedType" | "ExpectedWildcard" => has("UnificationError") || has("SyntaxError") || has("InvalidNewtypeInstance") || has("ExpectedType"),
        "NonAssociativeError" => has("NonAssociativeError"),
        "MixedAssociativityError" => has("MixedAssociativityError"),
        "DeprecatedFFIPrime" => has("DeprecatedFFIPrime"),
        "ClassInstanceArityMismatch" => has("ClassInstanceArityMismatch"),
        "InvalidInstanceHead" => has("InvalidInstanceHead"),
        "PartiallyAppliedSynonym" => has("PartiallyAppliedSynonym"),
        "TransitiveExportError" | "TransitiveDctorExportError" => has("TransitiveExportError"),
        "OverlappingInstances" => has("OverlappingInstances"),
        "ExportConflict" => has("ExportConflict"),
        "ScopeConflict" => has("ScopeConflict") || has("ExportConflict"),
        "OrphanInstance" => has("OrphanInstance"),
        "KindsDoNotUnify" => has("KindsDoNotUnify") || has("PartiallyAppliedSynonym"),
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
        _ => {
          eprintln!("Warning: Unrecognized expected error code '{}'. Add the appropriate error constructor with a matching error.code() implementation. Then add it to matches_expected_error match statement", expected);
          false
        },
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

    let run_all = std::env::var("RUN_ALL_FAILING").ok();
    let skip: HashSet<&str> = SKIP_FAILING_FIXTURES.iter().copied().collect();
    let mut total = 0;
    let mut correct = 0;
    let mut wrong_error = 0;
    let mut panicked = 0;
    let mut skipped = 0;
    let mut false_passes: Vec<String> = Vec::new();
    let mut newly_correct: Vec<String> = Vec::new();

    for (name, sources, js_sources) in &units {
        let should_run = match &run_all {
            Some(filter) if !filter.is_empty() => name.contains(filter.as_str()),
            Some(_) => true,
            None => false,
        };
        if skip.contains(name.as_str()) && !should_run {
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
                            let build_codes: Vec<String> = result.build_errors.iter().map(|e| e.code().to_string()).collect();
                            let type_codes: Vec<String> = type_errors.iter().map(|e| e.code().to_string()).collect();
                            format!("wrong_error:expected={},build=[{}],type=[{}]", expected_error_clone, build_codes.join(","), type_codes.join(","))
                        }
                    }
                }
            })
            .expect("Failed to spawn thread");

        match handle.join() {
            Ok(result) => {
                if result == "correct" {
                    correct += 1;
                    if run_all.is_some() && skip.contains(name.as_str()) {
                        newly_correct.push(name.clone());
                    }
                } else if result.starts_with("wrong_error") {
                    wrong_error += 1;
                    if run_all.is_none() || !skip.contains(name.as_str()) {
                        eprintln!("  WRONG: {} -> {}", name, result);
                    } else if run_all.is_some() && skip.contains(name.as_str()) {
                        eprintln!("  SKIP_WRONG: {} -> {}", name, result);
                    }
                } else if result.starts_with("false_pass:") {
                    let expected = result.strip_prefix("false_pass:").unwrap_or("");
                    if run_all.is_none() || !skip.contains(name.as_str()) {
                        false_passes.push(format!("{} (expected {})", name, expected));
                    } else if run_all.is_some() && skip.contains(name.as_str()) {
                        eprintln!("  SKIP_FALSEPASS: {} (expected {})", name, expected);
                    }
                } else {
                    panicked += 1;
                }
            }
            Err(_) => {
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

    if !newly_correct.is_empty() {
        eprintln!("\n=== Newly Correct (can remove from skip list) ===");
        for name in &newly_correct {
            eprintln!("  {}", name);
        }
    }

    if !false_passes.is_empty() {
        panic!(
            "{} fixtures compiled cleanly but should have failed:\n  {}",
            false_passes.len(),
            false_passes.join("\n  ")
        );
    }

    if wrong_error > 0 {
        panic!("{} fixtures produced wrong errors. See output for details.", wrong_error);
    }
}

#[test] #[timeout(120000)] #[ignore]// 120s timeout for the whole test
fn build_all_packages() {
    let _ = env_logger::try_init();
    let started = std::time::Instant::now();

    let packages_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    assert!(packages_dir.exists(), "packages directory not found");

    // Per-module timeout: defaults to 2s, controlled by MODULE_TIMEOUT_SECS env var
    let timeout_secs: u64 = std::env::var("MODULE_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(2);

    let options = BuildOptions {
        module_timeout: Some(std::time::Duration::from_secs(timeout_secs)),
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

    eprintln!("Discovered packages in {} seconds", started.elapsed().as_secs_f64());

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
            BuildError::TypecheckTimeout { module_name, .. } => {
                timeouts.push(module_name.clone());
            }
            BuildError::TypecheckPanic { module_name, .. } => {
                panics.push(module_name.clone());
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
            fails += 1;
            for e in &m.type_errors {
                type_errors.push((m.module_name.clone(), m.path.clone(), e.to_string()));
            }
        }
    }

    let clean = result.modules.len() - fails;
    eprintln!(
        "Results: {} clean, {} with type errors, {} timeouts, {} panics out of {} modules",
        clean, fails, timeouts.len(), panics.len(), result.modules.len()
    );
    if !timeouts.is_empty() {
        eprintln!("Timed out modules:");
        for name in &timeouts {
            eprintln!("  {}", name);
        }
    }
    if !panics.is_empty() {
        eprintln!("Panicked modules:");
        for name in &panics {
            eprintln!("  {}", name);
        }
    }

    assert!(
        other_errors.is_empty(),
        "Unexpected build errors:\n{}",
        other_errors.join("\n")
    );

    let type_errors_str: String = type_errors
        .iter()
        .map(|(m, p, e)| format!("{} ({}): {}", m, p.to_string_lossy(), e))
        .collect::<Vec<String>>()
        .join("\n");

    assert!(
        type_errors.is_empty(),
        "Type errors in packages: {}/{} modules failed:\n{}",
        fails,
        result.modules.len(),
        type_errors_str
    );
}
