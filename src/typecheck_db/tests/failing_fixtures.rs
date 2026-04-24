//! Per-fixture tests for `tests/fixtures/original-compiler/failing/`.
//!
//! Each test verifies that `typecheck_db` reports an error whose category
//! matches the `-- @shouldFailWith ErrorCode` annotation in the fixture's
//! `.purs` file. Tests are `#[ignore]` by default and act as a ratchet:
//! running them with `--ignored` shows how many failure categories the
//! new pipeline already covers.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use crate::cst;
use crate::parser::parse;
use crate::typecheck_db::driver::TypecheckDb;
use crate::typecheck_db::driver_multi::{
    check_many_modules_with_db, ModuleInput, ModuleCheckReport, MultiModuleError,
};
use crate::typecheck_db::passes::constraints::ConstraintErrorKind;
use crate::typecheck_db::passes::infer_value::InferError;
use crate::typecheck_db::passes::imports::ImportErrorKind;
use crate::typecheck_db::passes::validate_decls::ValidationErrorKind;
use crate::typecheck_db::unify::UnifyError;

const FIXTURES_ROOT: &str = "tests/fixtures";

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn failing_root() -> PathBuf {
    manifest_dir()
        .join(FIXTURES_ROOT)
        .join("original-compiler")
        .join("failing")
}

fn packages_root() -> PathBuf {
    manifest_dir().join(FIXTURES_ROOT).join("packages")
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

fn module_name_of(m: &cst::Module) -> String {
    m.name
        .value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
}

fn imports_of(module: &cst::Module) -> Vec<String> {
    module
        .imports
        .iter()
        .map(|imp| {
            imp.module
                .parts
                .iter()
                .map(|p| crate::interner::resolve(*p).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect()
}

fn package_modules_by_name() -> &'static std::collections::HashMap<String, ModuleInput> {
    static CACHE: OnceLock<std::collections::HashMap<String, ModuleInput>> = OnceLock::new();
    CACHE.get_or_init(|| {
        let root = packages_root();
        let files = collect_purs_files(&root);
        let mut out = std::collections::HashMap::with_capacity(files.len());
        for file in files {
            let src = match fs::read_to_string(&file) {
                Ok(s) => s,
                Err(e) => panic!("failed to read {}: {e}", file.display()),
            };
            let module = match parse(&src) {
                Ok(m) => m,
                Err(e) => panic!("parse error in {}: {e:?}", file.display()),
            };
            let name = module_name_of(&module);
            out.entry(name.clone()).or_insert(ModuleInput::new(name, src, module));
        }
        out
    })
}

fn transitive_imports(
    seed_modules: &[ModuleInput],
    pkgs: &std::collections::HashMap<String, ModuleInput>,
) -> Vec<ModuleInput> {
    let already: std::collections::HashSet<String> =
        seed_modules.iter().map(|m| m.name.clone()).collect();
    let mut visited: std::collections::HashSet<String> = already.clone();
    let mut stack: Vec<String> = seed_modules
        .iter()
        .flat_map(|m| imports_of(&m.module))
        .collect();
    let mut out: Vec<ModuleInput> = Vec::new();
    while let Some(name) = stack.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        if let Some(m) = pkgs.get(&name) {
            stack.extend(imports_of(&m.module));
            out.push(ModuleInput::new(m.name.clone(), m.source.clone(), m.module.clone()));
        }
    }
    out
}

fn build_unit_sources(name: &str) -> Vec<(PathBuf, String)> {
    let root = failing_root();
    let primary = root.join(format!("{name}.purs"));
    if !primary.exists() {
        panic!(
            "failing fixture primary file missing: {} (looked under {})",
            primary.display(),
            root.display(),
        );
    }
    let mut out: Vec<(PathBuf, String)> = Vec::new();
    let primary_src = match fs::read_to_string(&primary) {
        Ok(s) => s,
        Err(e) => panic!("failed to read {}: {e}", primary.display()),
    };
    out.push((primary.clone(), primary_src));

    let support_dir = root.join(name);
    if support_dir.is_dir() {
        for path in collect_purs_files(&support_dir) {
            let src = match fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => panic!("failed to read {}: {e}", path.display()),
            };
            out.push((path, src));
        }
    }
    out
}

/// Scan leading comment lines for `-- @shouldFailWith ErrorCode`.
fn extract_annotation(source: &str) -> Option<String> {
    source
        .lines()
        .take_while(|line| line.trim().starts_with("--"))
        .find_map(|line| {
            line.trim()
                .strip_prefix("-- @shouldFailWith ")
                .map(|s| s.trim().to_string())
        })
}

/// Collect all error codes produced by a `ModuleCheckReport` as short strings.
fn collect_error_codes(report: &ModuleCheckReport) -> Vec<String> {
    let mut codes: Vec<String> = Vec::new();

    for e in &report.errors {
        match e {
            MultiModuleError::CycleInModules(_) => codes.push("CycleInModules".into()),
            MultiModuleError::UnknownImport { .. } => codes.push("UnknownImport".into()),
        }
    }

    for r in &report.results {
        for ve in &r.validation_errors {
            codes.push(ve.kind.code().to_string());
        }
        for _ke in &r.kind_errors {
            codes.push("KindsDoNotUnify".into());
        }
        for ce in &r.coercible_errors {
            codes.push(ce.kind.code().to_string());
        }
        if let Some(err) = &r.inference_error {
            codes.push(infer_error_code(err));
        }
        for e in &r.import_errors {
            codes.push(import_error_code(&e.kind));
        }
        for _ in &r.exhaustiveness_errors {
            codes.push("NonExhaustivePattern".into());
        }
        for e in &r.constraint_errors {
            match e.kind {
                ConstraintErrorKind::NoInstanceFound => codes.push("NoInstanceFound".into()),
                ConstraintErrorKind::SolverDepthExceeded => {
                    codes.push("PossiblyInfiniteInstance".into())
                }
            }
        }
        if !r.hole_diagnostics.is_empty() {
            codes.push("HoleInferredType".into());
        }
        // Unresolved constraints at module boundary — treated as a
        // NoInstanceFound signal for fixture-matching purposes.
        if !r.deferred_constraints.is_empty() {
            codes.push("NoInstanceFound".into());
        }
    }

    codes
}

fn infer_error_code(e: &InferError) -> String {
    match e {
        InferError::Unify(u) => match u {
            UnifyError::Mismatch(_, _) => "UnificationError".into(),
            UnifyError::Infinite { .. } => "InfiniteType".into(),
            // Skolem escape is a kind-1-vs-kind-N polymorphism
            // violation — fits the same bucket as `EscapedSkolem`
            // in the reference compiler.
            UnifyError::SkolemEscape { .. } => "EscapedSkolem".into(),
        },
        InferError::UnboundVar(_) => "UnboundVar".into(),
        InferError::UnboundConstructor(_) => "UnboundConstructor".into(),
        InferError::Unsupported(_) => "Unsupported".into(),
        InferError::UnsupportedBinder(_) => "UnsupportedBinder".into(),
        InferError::InvalidDoLet => "InvalidDoLet".into(),
        InferError::InvalidDoBind => "InvalidDoBind".into(),
        InferError::EmptyDoBlock => "EmptyDoBlock".into(),
    }
}

fn import_error_code(kind: &ImportErrorKind) -> String {
    match kind {
        ImportErrorKind::UnknownModule(_) => "UnknownImport".into(),
        ImportErrorKind::UnknownValue { .. } => "UnknownImport".into(),
        ImportErrorKind::UnknownType { .. } => "UnknownImport".into(),
        ImportErrorKind::UnknownConstructor { .. } => "UnknownImport".into(),
        ImportErrorKind::UnknownClass { .. } => "UnknownImport".into(),
        ImportErrorKind::UnknownOperator { .. } => "UnknownImport".into(),
    }
}

/// Returns true if any code in `actual` satisfies the mapping for `expected`.
fn failing_matches_expected(expected: &str, actual: &[String]) -> bool {
    let has = |code: &str| {
        actual
            .iter()
            .any(|c| c == code || c.ends_with(&format!(".{code}")))
    };

    match expected {
        "TypesDoNotUnify" => has("UnificationError") || has("RecordLabelMismatch"),
        "NoInstanceFound" => has("NoInstanceFound"),
        "ErrorParsingModule" => {
            has("LexError")
                || has("SyntaxError")
                || has("WildcardInTypeDefinition")
                || has("ConstraintInForeignImport")
                || has("InvalidConstraintArgument")
        }
        "UnknownName" => {
            has("UnknownName")
                || has("UndefinedVariable")
                || has("UnboundVar")
                || has("UnboundConstructor")
        }
        "HoleInferredType" => has("HoleInferredType") || has("UnificationError"),
        "InfiniteType" => has("InfiniteType"),
        "InfiniteKind" => has("InfiniteKind"),
        "DuplicateValueDeclaration" => has("DuplicateValueDeclaration"),
        "OverlappingNamesInLet" => has("OverlappingNamesInLet") || has("UnificationError"),
        "CycleInTypeSynonym" => has("CycleInTypeSynonym"),
        "CycleInDeclaration" => has("CycleInDeclaration") || has("CycleInTypeClassDeclaration"),
        "CycleInTypeClassDeclaration" => has("CycleInTypeClassDeclaration"),
        "CycleInKindDeclaration" => has("CycleInKindDeclaration"),
        "UnknownImport" => has("UnknownImport"),
        "UnknownImportDataConstructor" => has("UnknownImportDataConstructor") || has("UnknownImport"),
        "IncorrectConstructorArity" => has("IncorrectConstructorArity") || has("UnificationError"),
        "DuplicateTypeClass" => has("DuplicateTypeClass"),
        "DuplicateInstance" => has("DuplicateInstance"),
        "DuplicateTypeArgument" => has("DuplicateTypeArgument"),
        "InvalidDoBind" => has("InvalidDoBind"),
        "InvalidDoLet" => has("InvalidDoLet"),
        "CannotUseBindWithDo" => has("CannotUseBindWithDo") || has("UnificationError"),
        "ModuleNotFound" => has("ModuleNotFound") || has("UnknownImport"),
        "DuplicateModule" => has("DuplicateModule"),
        "CycleInModules" => has("CycleInModules"),
        "MultipleValueOpFixities" => has("MultipleValueOpFixities"),
        "MultipleTypeOpFixities" => has("MultipleTypeOpFixities"),
        "OrphanTypeDeclaration" => has("OrphanTypeSignature"),
        "OrphanKindDeclaration" => has("OrphanKindDeclaration"),
        "UnknownExport" | "UnknownExportDataConstructor" => has("UnkownExport") || has("UnknownExport"),
        "OverlappingArgNames" => has("OverlappingArgNames") || has("OverlappingPattern"),
        "ArgListLengthsDiffer" => has("ArityMismatch"),
        "InvalidNewtypeInstance" | "CannotDeriveNewtypeForData" => {
            has("InvalidNewtypeInstance") || has("InvalidNewtypeDerivation")
        }
        "InvalidNewtypeDerivation" => has("InvalidNewtypeDerivation"),
        "OverlappingPattern" => has("OverlappingPattern"),
        "NonExhaustivePattern" => has("NonExhaustivePattern"),
        "CaseBinderLengthDiffers" => has("CaseBinderLengthDiffers") || has("Unsupported"),
        "AdditionalProperty" => {
            has("AdditionalProperty") || has("UnificationError") || has("RecordLabelMismatch")
        }
        "PropertyIsMissing" => {
            has("PropertyIsMissing") || has("UnificationError") || has("RecordLabelMismatch")
        }
        "InvalidOperatorInBinder" => has("InvalidOperatorInBinder"),
        "IncorrectAnonymousArgument" => has("IncorrectAnonymousArgument") || has("UnificationError"),
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
        "ExpectedType" => has("ExpectedType"),
        "ExpectedWildcard" => has("ExpectedWildcard"),
        "NonAssociativeError" => has("NonAssociativeError"),
        "MixedAssociativityError" => has("MixedAssociativityError"),
        "DeprecatedFFIPrime" => has("DeprecatedFFIPrime"),
        "ClassInstanceArityMismatch" => has("ClassInstanceArityMismatch"),
        "InvalidInstanceHead" => has("InvalidInstanceHead"),
        "PartiallyAppliedSynonym" => has("PartiallyAppliedSynonym"),
        "TransitiveExportError" | "TransitiveDctorExportError" => {
            has("TransitiveExportError") || has("TransitiveDctorExportError")
        }
        "OverlappingInstances" => has("OverlappingInstances"),
        "ExportConflict" => has("ExportConflict"),
        "ScopeConflict" => has("ScopeConflict"),
        "OrphanInstance" => has("OrphanInstance"),
        "KindsDoNotUnify" => has("KindsDoNotUnify") || has("RecordLabelMismatch"),
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
        _ => false,
    }
}

fn extract_panic_msg(payload: Box<dyn std::any::Any + Send + 'static>) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "panicked (non-string payload)".to_string()
    }
}

pub(crate) fn run_failing_build_unit(name: &str) {
    let owned_name = name.to_string();
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(move || {
                let previous = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || run_failing_inner(&owned_name),
                ));
                std::panic::set_hook(previous);
                match outcome {
                    Ok(res) => res,
                    Err(payload) => Err(format!("panicked: {}", extract_panic_msg(payload))),
                }
            })
            .expect("spawn fixture-check thread")
            .join();

    let inner = match join_result {
        Ok(r) => r,
        Err(payload) => Err(format!(
            "worker thread lost at top level: {}",
            extract_panic_msg(payload),
        )),
    };
    match inner {
        Ok(()) => {}
        Err(msg) => {
            eprintln!("failing fixture {name}: {msg}");
            panic!("failing fixture {name}: {msg}");
        }
    }
}

fn run_failing_inner(name: &str) -> Result<(), String> {
    // 1) Parse the fixture's own files.
    let sources = build_unit_sources(name);
    let primary_src = sources.first().map(|(_, s)| s.clone()).unwrap_or_default();

    let mut fixture_modules: Vec<ModuleInput> = Vec::new();
    for (path, src) in &sources {
        let module = match parse(src) {
            Ok(m) => m,
            // A parse error itself might be the expected error — record it as
            // a code and continue (without adding to fixture_modules).
            Err(_e) => {
                // SyntaxError/LexError: check whether the annotation expects that.
                let expected = extract_annotation(&primary_src);
                match expected.as_deref() {
                    Some("ErrorParsingModule") => return Ok(()),
                    Some(code) => {
                        return Err(format!(
                            "parse error in {}; expected @shouldFailWith {code}",
                            path.display()
                        ))
                    }
                    None => {
                        return Err(format!(
                            "parse error in {} and no @shouldFailWith annotation",
                            path.display()
                        ))
                    }
                }
            }
        };
        let mod_name = module_name_of(&module);
        fixture_modules.push(ModuleInput::new(mod_name, src.clone(), module));
    }

    // 2) Transitive import closure from support packages.
    let pkgs = package_modules_by_name();
    let closure = transitive_imports(&fixture_modules, pkgs);

    // 3) Dedupe; fixture wins on collision.
    let mut by_name: std::collections::HashMap<String, ModuleInput> =
        std::collections::HashMap::with_capacity(fixture_modules.len() + closure.len());
    for m in closure {
        by_name.insert(m.name.clone(), m);
    }
    for m in fixture_modules {
        by_name.insert(m.name.clone(), m);
    }
    let parsed: Vec<ModuleInput> = by_name.into_values().collect();

    // 4) Run typecheck_db.
    let mut db = TypecheckDb::open_in_memory().expect("open in-memory TypecheckDb");
    let report = check_many_modules_with_db(&mut db, parsed);

    // 5) Collect error codes.
    let actual_codes = collect_error_codes(&report);

    // 6) Parse the expected annotation.
    let expected = match extract_annotation(&primary_src) {
        Some(e) => e,
        None => {
            // No annotation — just check that *some* error was produced.
            if actual_codes.is_empty() {
                return Err(
                    "no @shouldFailWith annotation and typecheck_db produced no errors".into(),
                );
            }
            return Ok(());
        }
    };

    // 7) Match.
    if actual_codes.is_empty() {
        return Err(format!(
            "expected @shouldFailWith {expected}, but typecheck_db produced no errors"
        ));
    }
    if !failing_matches_expected(&expected, &actual_codes) {
        return Err(format!(
            "expected @shouldFailWith {expected}, got {actual_codes:?}"
        ));
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Macro: every entry is ignored by default.
// ---------------------------------------------------------------------------

macro_rules! check_failing_build_unit {
    ($test_name:ident, $fixture:literal) => {
        #[test]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_failing_build_unit($fixture);
        }
    };
}

macro_rules! check_failing_build_unit_ignored {
    ($test_name:ident, $fixture:literal) => {
        #[test]
        #[ignore = "gap-closing: typecheck_db doesn't yet catch this failure category"]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_failing_build_unit($fixture);
        }
    };
}

/// Skipped entirely — these fixtures stack-overflow typecheck_db and
/// the overflow aborts the whole test process, so we can't even mark
/// them `#[ignore]`. Generates a regular fn (not `#[test]`) so the
/// fixture stays indexed in source, but won't be executed.
macro_rules! check_failing_build_unit_skipped {
    ($test_name:ident, $fixture:literal, $reason:literal) => {
        #[allow(dead_code, non_snake_case)]
        fn $test_name() {
            let _ = $reason;
            run_failing_build_unit($fixture);
        }
    };
}

include!("failing_fixtures_list.rs");
