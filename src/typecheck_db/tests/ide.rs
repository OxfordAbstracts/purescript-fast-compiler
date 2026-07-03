//! IDE-facing capabilities of `typecheck_db`: span→type recording (hover),
//! unused-import warnings, exported kinds, and the `check_module_ide` entry
//! point. These are the features the LSP consumes.

use crate::parser::parse;
use crate::typecheck_db::driver_multi::{
    check_many_modules, ModuleCheckResult, ModuleInput,
};

/// Parse + check a single module in a fresh in-memory db.
fn check_one(name: &str, src: &str) -> ModuleCheckResult {
    let module = parse(src).expect("parse");
    let report = check_many_modules(vec![ModuleInput::new(name, src, module)]);
    report
        .results
        .into_iter()
        .find(|r| r.name == name)
        .expect("result for module")
}

/// Byte offset of the first occurrence of `needle` in `src`.
fn offset_of(src: &str, needle: &str) -> usize {
    src.find(needle)
        .unwrap_or_else(|| panic!("`{needle}` not found in source"))
}

/// The recorded type whose span covers `offset` (narrowest span wins), if any.
fn ty_at(r: &ModuleCheckResult, offset: usize) -> Option<String> {
    r.span_types
        .iter()
        .filter(|(s, _)| offset >= s.start && offset < s.end)
        .min_by_key(|(s, _)| s.end - s.start)
        .map(|(_, ty)| ty.to_string())
}

// --- A2: span→type recording ------------------------------------------------

#[test]
fn span_types_record_local_variable_type() {
    // A `let`-bound local with a concrete (monomorphic) type. Hovering the
    // body use of `y` should resolve to the data type `T` (no Prelude needed).
    let src = "module Test where\n\ndata T = MkT\n\nfoo = let y = MkT in y\n";
    let r = check_one("Test", src);
    let use_off = offset_of(src, "in y") + 3; // the `y` after `in `
    let ty = ty_at(&r, use_off).expect("body use of `y` should be recorded");
    assert_eq!(ty, "T", "recorded type for local `y`: {ty}");
}

#[test]
fn span_types_record_top_level_body_type() {
    let src = "module Test where\n\nfoo = 42\n";
    let r = check_one("Test", src);
    let off = offset_of(src, "42");
    assert_eq!(ty_at(&r, off).as_deref(), Some("Int"));
}

// --- A3: unused-import warnings ---------------------------------------------

use crate::typecheck_db::passes::warnings::WarningKind;

/// Names flagged `UnusedImport` in the module named `name`.
fn unused_imports_of(name: &str, sources: &[(&str, &str)]) -> Vec<String> {
    let inputs: Vec<ModuleInput> = sources
        .iter()
        .map(|(n, src)| ModuleInput::new(*n, *src, parse(src).expect("parse")))
        .collect();
    let report = check_many_modules(inputs);
    let r = report
        .results
        .iter()
        .find(|r| r.name == name)
        .expect("result");
    r.warnings
        .iter()
        .filter_map(|w| match &w.kind {
            WarningKind::UnusedImport { name } => Some(name.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn unused_import_is_warned() {
    let lib = "module Lib where\n\nused :: Int\nused = 1\n\nunused :: Int\nunused = 2\n";
    let main = "module Main where\nimport Lib (used, unused)\nmain :: Int\nmain = used\n";
    let unused = unused_imports_of("Main", &[("Lib", lib), ("Main", main)]);
    assert!(unused.contains(&"unused".to_string()), "should warn `unused`: {unused:?}");
    assert!(!unused.contains(&"used".to_string()), "must NOT warn `used`: {unused:?}");
}

#[test]
fn type_only_used_in_signature_is_not_unused() {
    // `Lib.T` is referenced only in a signature — must not be flagged unused.
    let lib = "module Lib where\n\ndata T = T\n";
    let main = "module Main where\nimport Lib (T(..))\nmk :: T\nmk = T\n";
    let unused = unused_imports_of("Main", &[("Lib", lib), ("Main", main)]);
    assert!(unused.is_empty(), "type used in signature is not unused: {unused:?}");
}

#[test]
fn underscore_prefixed_import_is_exempt() {
    // (Constructed) — an explicitly imported but unreferenced name that starts
    // with `_` must not be warned. Uses a value name `_helper`.
    let lib = "module Lib where\n\n_helper :: Int\n_helper = 1\n\nreal :: Int\nreal = 2\n";
    let main = "module Main where\nimport Lib (_helper, real)\nmain :: Int\nmain = real\n";
    let unused = unused_imports_of("Main", &[("Lib", lib), ("Main", main)]);
    assert!(!unused.iter().any(|n| n == "_helper"), "_-prefixed exempt: {unused:?}");
}

// --- A4: exported kinds for hover -------------------------------------------

fn kind_of(name: &str, module: &str, src: &str) -> Option<String> {
    let m = parse(src).expect("parse");
    let report = check_many_modules(vec![ModuleInput::new(module, src, m)]);
    report
        .registry
        .get(module)
        .and_then(|e| e.type_kinds.get(name))
        .map(|k| k.to_string())
}

#[test]
fn exports_carry_class_and_type_kinds() {
    let src = "module Test where\n\nclass MyShow a where\n  myShow :: a -> String\n\ndata Box a = MkBox a\n\ndata Color = Red\n";
    assert_eq!(kind_of("MyShow", "Test", src).as_deref(), Some("Type -> Constraint"));
    assert_eq!(kind_of("Box", "Test", src).as_deref(), Some("Type -> Type"));
    assert_eq!(kind_of("Color", "Test", src).as_deref(), Some("Type"));
}

#[test]
fn exports_carry_higher_kinded_class_kind() {
    // `f` is applied to type args in the method, so it's `Type -> Type`.
    let src = "module Test where\n\nclass MyFunctor f where\n  mmap :: forall a b. (a -> b) -> f a -> f b\n";
    assert_eq!(
        kind_of("MyFunctor", "Test", src).as_deref(),
        Some("(Type -> Type) -> Constraint"),
    );
}

// --- B1: check_module_ide entry point ---------------------------------------

#[test]
fn check_module_ide_gives_complete_span_types_against_warm_registry() {
    use crate::typecheck_db::driver::TypecheckDb;
    use crate::typecheck_db::driver_multi::{check_many_modules_with_db, check_module_ide};

    // Warm the registry with Lib + Main, then IDE-check Main: span_types must
    // cover Main's locals across BOTH decls, and its `base` import resolves
    // against the warm registry.
    let lib = "module Lib where\n\nbase :: Int\nbase = 1\n";
    let main = "module Main where\nimport Lib (base)\n\nfirst :: Int\nfirst = base\n\nsecond :: Int -> Int\nsecond n = base\n";
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let libm = parse(lib).unwrap();
    let mainm = parse(main).unwrap();
    let report = check_many_modules_with_db(
        &mut db,
        vec![
            ModuleInput::new("Lib", lib, libm),
            ModuleInput::new("Main", main, mainm.clone()),
        ],
    );
    let mut registry = report.registry;

    let input = ModuleInput::new("Main", main, mainm);
    let r = check_module_ide(&mut db, &input, &mut registry);
    assert!(
        r.import_errors.is_empty(),
        "warm registry resolves `base`: {:?}",
        r.import_errors
    );
    // A use of `base` in the SECOND decl must be recorded (full re-inference).
    let off = offset_of(main, "second n = base") + "second n = ".len();
    assert_eq!(
        ty_at(&r, off).as_deref(),
        Some("Int"),
        "IDE check records span types for the second decl too"
    );
}
