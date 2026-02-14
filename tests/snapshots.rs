//! Snapshot tests using insta.
//!
//! These capture the debug representation of CST nodes and type inference
//! results, so changes to output format are caught and reviewed explicitly.

use purescript_fast_compiler::interner;
use purescript_fast_compiler::parser;
use purescript_fast_compiler::typechecker::{check_module, infer_expr};
use string_interner::Symbol as _;

// ===== Helpers =====

fn format_type_map(source: &str) -> String {
    let module = parser::parse(source).expect("parse failed");
    let result = check_module(&module);
    assert!(result.errors.is_empty(), "typecheck errors: {:?}", result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    let mut entries: Vec<(String, String)> = result.types
        .iter()
        .map(|(sym, ty)| {
            let name = interner::resolve(*sym).unwrap_or_default();
            (name.to_string(), format!("{}", ty))
        })
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries
        .iter()
        .map(|(name, ty)| format!("{} :: {}", name, ty))
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_expr_type(source: &str) -> String {
    let expr = parser::parse_expr(source).expect("parse failed");
    match infer_expr(&expr) {
        Ok(ty) => format!("{}", ty),
        Err(e) => format!("ERROR: {}", e),
    }
}

fn format_module_error(source: &str) -> String {
    let module = parser::parse(source).expect("parse failed");
    let result = check_module(&module);
    if result.errors.is_empty() {
        "OK (no error)".to_string()
    } else {
        result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n")
    }
}

// ===== Expression type snapshots =====

#[test]
fn snap_expr_int() {
    insta::assert_snapshot!(format_expr_type("42"), @"Int");
}

#[test]
fn snap_expr_string() {
    insta::assert_snapshot!(format_expr_type(r#""hello""#), @"String");
}

#[test]
fn snap_expr_lambda_identity() {
    let ty = format_expr_type(r"\x -> x");
    // Should be something like (?0 -> ?0) — both sides same unif var
    insta::assert_snapshot!(ty);
}

#[test]
fn snap_expr_application() {
    insta::assert_snapshot!(format_expr_type(r"(\x -> x) 42"), @"Int");
}

#[test]
fn snap_expr_if() {
    insta::assert_snapshot!(format_expr_type("if true then 1 else 2"), @"Int");
}

#[test]
fn snap_expr_let_polymorphism() {
    insta::assert_snapshot!(
        format_expr_type("let\n  id = \\x -> x\nin id 42"),
        @"Int"
    );
}

#[test]
fn snap_expr_array() {
    insta::assert_snapshot!(format_expr_type("[1, 2, 3]"), @"(Array Int)");
}

#[test]
fn snap_expr_negate() {
    insta::assert_snapshot!(format_expr_type("-42"), @"Int");
}

// ===== Expression error snapshots =====

#[test]
fn snap_expr_error_branch_mismatch() {
    insta::assert_snapshot!(
        format_expr_type(r#"if true then 1 else "x""#),
        @"ERROR: Could not match type Int with type String at 0:23"
    );
}

#[test]
fn snap_expr_error_not_boolean_cond() {
    insta::assert_snapshot!(
        format_expr_type("if 42 then 1 else 2"),
        @"ERROR: Could not match type Int with type Boolean at 3:5"
    );
}

#[test]
fn snap_expr_error_undefined() {
    insta::assert_snapshot!(
        format_expr_type("undefinedVar"),
        @"ERROR: Unknown value undefinedVar at 0:12"
    );
}

#[test]
fn snap_expr_error_negate_string() {
    insta::assert_snapshot!(
        format_expr_type(r#"-"hello""#),
        @"ERROR: No type class instance was found for Ring String at 0:8"
    );
}

// ===== Module type map snapshots =====

#[test]
fn snap_module_simple() {
    insta::assert_snapshot!(
        format_type_map("module T where\nx = 42"),
        @"x :: Int"
    );
}

#[test]
fn snap_module_multiple_values() {
    insta::assert_snapshot!(format_type_map("module T where
a = 42
b = true
c = \"hello\""));
}

#[test]
fn snap_module_function_and_application() {
    insta::assert_snapshot!(format_type_map("module T where
f x = x
g = f 42"));
}

#[test]
fn snap_module_data_constructors() {
    insta::assert_snapshot!(format_type_map("module T where
data Maybe a = Just a | Nothing
x = Just 42
y = Nothing"));
}

// ===== Module error snapshots =====

#[test]
fn snap_module_error_sig_mismatch() {
    insta::assert_snapshot!(
        format_module_error("module T where\nx :: Int\nx = true"),
        @"Could not match type Boolean with type Int at 24:32"
    );
}

#[test]
fn snap_module_error_duplicate_sig() {
    insta::assert_snapshot!(
        format_module_error("module T where\nx :: Int\nx :: String\nx = 42"),
        @"Duplicate type declaration for x at 24:35"
    );
}

#[test]
fn snap_module_error_orphan_sig() {
    insta::assert_snapshot!(
        format_module_error("module T where\nx :: Int"),
        @"The type declaration for x has no corresponding value declaration at 15:23"
    );
}

// ===== Parse tree snapshots =====

/// Format debug output with resolved symbol names instead of raw SymbolU32 IDs.
fn resolve_symbols_in_debug(debug: &str) -> String {
    // Replace SymbolU32 { value: N } with the resolved string
    let re = regex::Regex::new(r"SymbolU32 \{\s*value:\s*(\d+),?\s*\}").unwrap();
    re.replace_all(debug, |caps: &regex::Captures| {
        let raw_value: usize = caps[1].parse().unwrap();
        // SymbolU32 stores NonZeroU32(index + 1), so subtract 1 to get the index
        let sym = string_interner::DefaultSymbol::try_from_usize(raw_value - 1).unwrap();
        let name = interner::resolve(sym).unwrap_or_else(|| format!("?{}", raw_value));
        format!("\"{}\"", name)
    }).to_string()
}

#[test]
fn snap_parse_expr_simple() {
    let expr = parser::parse_expr("42").unwrap();
    insta::assert_snapshot!(resolve_symbols_in_debug(&format!("{:#?}", expr)));
}

#[test]
fn snap_parse_expr_lambda() {
    let expr = parser::parse_expr(r"\x -> x + 1").unwrap();
    insta::assert_snapshot!(resolve_symbols_in_debug(&format!("{:#?}", expr)));
}

#[test]
fn snap_parse_expr_case() {
    let expr = parser::parse_expr("case x of\n  y -> y").unwrap();
    insta::assert_snapshot!(resolve_symbols_in_debug(&format!("{:#?}", expr)));
}

#[test]
fn snap_parse_module_data() {
    let module = parser::parse("module T where\ndata Either a b = Left a | Right b").unwrap();
    insta::assert_snapshot!(resolve_symbols_in_debug(&format!("{:#?}", module.decls)));
}
