//! Tests for typechecker warnings: unused imports and unused variables.
//!
//! Warnings do not prevent building but are reported in build output and
//! LSP diagnostics so users can clean up their code.

use purescript_fast_compiler::parser;
use purescript_fast_compiler::typechecker::check_module;
use purescript_fast_compiler::typechecker::error::TypeWarning;

fn warnings_for(source: &str) -> Vec<TypeWarning> {
    let module = parser::parse(source).unwrap_or_else(|e| panic!("parse failed: {e}"));
    let result = check_module(&module);
    // Errors should still compile the module; warnings are what we're checking.
    // If an errant test case sets up a module that fails to typecheck entirely,
    // surface the errors so the test author can fix their fixture.
    if !result.errors.is_empty() {
        let lines: Vec<String> = result
            .errors
            .iter()
            .map(|e| format!("  {}", e))
            .collect();
        panic!("typecheck errors (fix fixture):\n{}", lines.join("\n"));
    }
    result.warnings
}

fn has_unused_name(warnings: &[TypeWarning], name: &str) -> bool {
    warnings.iter().any(|w| match w {
        TypeWarning::UnusedName { name: n, .. } => {
            n.resolve().unwrap_or_default().as_str() == name
        }
        _ => false,
    })
}

fn has_unused_import(warnings: &[TypeWarning], name: &str) -> bool {
    warnings.iter().any(|w| match w {
        TypeWarning::UnusedImport { name: n, .. } => {
            n.resolve().unwrap_or_default().as_str() == name
        }
        _ => false,
    })
}

// ===== Unused let bindings =====

#[test]
fn unused_let_binding_is_warned() {
    let src = r#"
module M where

f = let x = 1 in 2
"#;
    let ws = warnings_for(src);
    assert!(
        has_unused_name(&ws, "x"),
        "expected UnusedName for 'x', got: {ws:?}"
    );
}

#[test]
fn used_let_binding_is_not_warned() {
    let src = r#"
module M where

f = let x = 1 in x
"#;
    let ws = warnings_for(src);
    assert!(
        !has_unused_name(&ws, "x"),
        "unexpected UnusedName for 'x' (it IS used): {ws:?}"
    );
}

#[test]
fn underscore_prefixed_binding_is_not_warned() {
    let src = r#"
module M where

f = let _unused = 1 in 2
"#;
    let ws = warnings_for(src);
    assert!(
        !has_unused_name(&ws, "_unused"),
        "names starting with `_` should be exempt: {ws:?}"
    );
}

// ===== Unused lambda params =====

#[test]
fn unused_lambda_param_is_warned() {
    let src = r#"
module M where

f = \x -> 1
"#;
    let ws = warnings_for(src);
    assert!(
        has_unused_name(&ws, "x"),
        "expected UnusedName for lambda param 'x', got: {ws:?}"
    );
}

#[test]
fn used_lambda_param_is_not_warned() {
    let src = r#"
module M where

f = \x -> x
"#;
    let ws = warnings_for(src);
    assert!(
        !has_unused_name(&ws, "x"),
        "unexpected UnusedName for lambda param 'x' (it IS used): {ws:?}"
    );
}

#[test]
fn underscore_lambda_param_is_not_warned() {
    let src = r#"
module M where

f = \_ignored -> 1
"#;
    let ws = warnings_for(src);
    assert!(
        !has_unused_name(&ws, "_ignored"),
        "underscore-prefixed lambda params should be exempt: {ws:?}"
    );
}

// ===== Unused imports =====

fn module_warnings_in_build(sources: &[(&str, &str)], target_module: &str) -> Vec<TypeWarning> {
    use purescript_fast_compiler::build::build_from_sources;
    let result = build_from_sources(sources);
    let m = result
        .modules
        .iter()
        .find(|m| m.module_name == target_module)
        .unwrap_or_else(|| panic!("module {target_module} not found in build result"));
    m.type_warnings.clone()
}

#[test]
fn unused_import_is_warned() {
    let sources = &[
        ("src/Dep.purs", "module Dep where\nfoo :: Int\nfoo = 1\nbar :: Int\nbar = 2"),
        ("src/M.purs", "module M where\nimport Dep (foo, bar)\nx = foo"),
    ];
    let ws = module_warnings_in_build(sources, "M");
    assert!(
        has_unused_import(&ws, "bar"),
        "expected UnusedImport for 'bar', got: {ws:?}"
    );
    assert!(
        !has_unused_import(&ws, "foo"),
        "unexpected UnusedImport for 'foo' (it IS used): {ws:?}"
    );
}

#[test]
fn used_import_is_not_warned() {
    let sources = &[
        ("src/Dep.purs", "module Dep where\nfoo :: Int\nfoo = 1"),
        ("src/M.purs", "module M where\nimport Dep (foo)\nx = foo"),
    ];
    let ws = module_warnings_in_build(sources, "M");
    assert!(
        !has_unused_import(&ws, "foo"),
        "unexpected UnusedImport for 'foo' (it IS used): {ws:?}"
    );
}
