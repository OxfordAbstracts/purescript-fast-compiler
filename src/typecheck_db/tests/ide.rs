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
