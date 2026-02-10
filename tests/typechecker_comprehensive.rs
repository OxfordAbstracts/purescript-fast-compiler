//! Comprehensive typechecker test suite.
//!
//! Organized by feature category. Tests marked "NOT YET IMPLEMENTED" assert
//! that the typechecker returns `NotImplemented` — as features are added,
//! these tests should be updated to assert the correct inferred types.
//!
//! This file serves as both a test suite and a roadmap of remaining work.

use std::collections::HashMap;

use purescript_fast_compiler::interner::{self, Symbol};
use purescript_fast_compiler::parser;
use purescript_fast_compiler::typechecker::error::TypeError;
use purescript_fast_compiler::typechecker::types::Type;
use purescript_fast_compiler::typechecker::{check_module, infer_expr, infer_expr_with_env};
use purescript_fast_compiler::typechecker::env::Env;

// ===== Test Helpers =====

fn assert_expr_type(source: &str, expected: Type) {
    let expr = parser::parse_expr(source).unwrap_or_else(|e| {
        panic!("parse failed for '{}': {}", source, e)
    });
    match infer_expr(&expr) {
        Ok(ty) => assert_eq!(ty, expected, "for expression: {}", source),
        Err(e) => panic!("type error for '{}': {}", source, e),
    }
}

fn assert_expr_type_with_env(source: &str, env: &Env, expected: Type) {
    let expr = parser::parse_expr(source).unwrap_or_else(|e| {
        panic!("parse failed for '{}': {}", source, e)
    });
    match infer_expr_with_env(env, &expr) {
        Ok(ty) => assert_eq!(ty, expected, "for expression: {}", source),
        Err(e) => panic!("type error for '{}': {}", source, e),
    }
}

fn assert_expr_error(source: &str) {
    let expr = parser::parse_expr(source).unwrap_or_else(|e| {
        panic!("parse failed for '{}': {}", source, e)
    });
    assert!(
        infer_expr(&expr).is_err(),
        "expected type error for '{}', got: {:?}",
        source,
        infer_expr(&expr)
    );
}

fn assert_expr_error_kind<F: Fn(&TypeError) -> bool>(source: &str, pred: F, desc: &str) {
    let expr = parser::parse_expr(source).unwrap_or_else(|e| {
        panic!("parse failed for '{}': {}", source, e)
    });
    match infer_expr(&expr) {
        Err(ref e) if pred(e) => {}
        Err(e) => panic!("expected {} for '{}', got: {}", desc, source, e),
        Ok(ty) => panic!("expected {} for '{}', got type: {}", desc, source, ty),
    }
}

fn check_module_types(source: &str) -> Result<HashMap<Symbol, Type>, TypeError> {
    let module = parser::parse(source).unwrap_or_else(|e| {
        panic!("parse failed: {}", e)
    });
    check_module(&module)
}

fn assert_module_type(source: &str, name: &str, expected: Type) {
    let types = check_module_types(source).unwrap_or_else(|e| {
        panic!("typecheck failed for module: {}", e)
    });
    let sym = interner::intern(name);
    let ty = types.get(&sym).unwrap_or_else(|| {
        let names: Vec<_> = types.keys()
            .map(|k| interner::resolve(*k).unwrap_or_default())
            .collect();
        panic!("name '{}' not found. available: {:?}", name, names)
    });
    assert_eq!(*ty, expected, "for name '{}' in module", name);
}

fn assert_module_fn_type(source: &str, name: &str) -> Type {
    let types = check_module_types(source).unwrap_or_else(|e| {
        panic!("typecheck failed for module: {}", e)
    });
    let sym = interner::intern(name);
    types.get(&sym).unwrap_or_else(|| {
        panic!("name '{}' not found in module types", name)
    }).clone()
}

fn assert_module_error(source: &str) {
    let result = check_module_types(source);
    assert!(result.is_err(), "expected type error for module, got: {:?}", result);
}

fn assert_module_error_kind<F: Fn(&TypeError) -> bool>(source: &str, pred: F, desc: &str) {
    match check_module_types(source) {
        Err(ref e) if pred(e) => {}
        Err(e) => panic!("expected {} for module, got: {}", desc, e),
        Ok(types) => panic!("expected {} for module, got types: {:?}", desc,
            types.iter().map(|(k, v)| format!("{}: {}", interner::resolve(*k).unwrap_or_default(), v)).collect::<Vec<_>>()),
    }
}

fn assert_not_implemented_expr(source: &str) {
    let expr = parser::parse_expr(source).unwrap_or_else(|e| {
        panic!("parse failed for '{}': {}", source, e)
    });
    match infer_expr(&expr) {
        Err(TypeError::NotImplemented { .. }) => {}
        Err(e) => panic!("expected NotImplemented for '{}', got: {}", source, e),
        Ok(ty) => panic!("expected NotImplemented for '{}', got type: {}", source, ty),
    }
}

fn assert_module_not_implemented(source: &str) {
    match check_module_types(source) {
        Err(TypeError::NotImplemented { .. }) => {}
        Err(e) => panic!("expected NotImplemented for module, got: {}", e),
        Ok(_) => panic!("expected NotImplemented for module, got success"),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 1. LITERALS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn lit_int() {
    assert_expr_type("42", Type::int());
}

#[test]
fn lit_negative_int() {
    assert_expr_type("-1", Type::int());
}

#[test]
fn lit_zero() {
    assert_expr_type("0", Type::int());
}

#[test]
fn lit_float() {
    assert_expr_type("3.14", Type::float());
}

#[test]
fn lit_float_with_exponent() {
    assert_expr_type("2.0e10", Type::float());
}

#[test]
fn lit_string() {
    assert_expr_type(r#""hello world""#, Type::string());
}

#[test]
fn lit_empty_string() {
    assert_expr_type(r#""""#, Type::string());
}

#[test]
fn lit_char() {
    assert_expr_type("'a'", Type::char());
}

#[test]
fn lit_boolean_true() {
    assert_expr_type("true", Type::boolean());
}

#[test]
fn lit_boolean_false() {
    assert_expr_type("false", Type::boolean());
}

#[test]
fn lit_array_int() {
    assert_expr_type("[1, 2, 3]", Type::array(Type::int()));
}

#[test]
fn lit_array_string() {
    assert_expr_type(r#"["a", "b", "c"]"#, Type::array(Type::string()));
}

#[test]
fn lit_array_empty() {
    // Empty array should have polymorphic element type (Array ?a)
    let expr = parser::parse_expr("[]").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::App(f, _) => assert_eq!(*f, Type::Con(interner::intern("Array"))),
        other => panic!("expected Array type, got: {}", other),
    }
}

#[test]
fn lit_array_nested() {
    assert_expr_type("[[1, 2], [3, 4]]", Type::array(Type::array(Type::int())));
}

#[test]
fn lit_array_singleton() {
    assert_expr_type("[true]", Type::array(Type::boolean()));
}

// ===== Literal errors =====

#[test]
fn err_array_heterogeneous() {
    assert_expr_error("[1, true]");
}

#[test]
fn err_array_heterogeneous_string_int() {
    assert_expr_error(r#"[1, "hello"]"#);
}

// ═══════════════════════════════════════════════════════════════════════════
// 2. VARIABLES AND CONSTRUCTORS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn var_undefined() {
    assert_expr_error_kind("undefinedVar",
        |e| matches!(e, TypeError::UndefinedVariable { .. }),
        "UndefinedVariable");
}

#[test]
fn var_defined_in_module() {
    assert_module_type("module T where\nx = 42\ny = x", "y", Type::int());
}

#[test]
fn constructor_nullary() {
    assert_module_type(
        "module T where\ndata Color = Red | Green | Blue\nx = Red",
        "x", Type::Con(interner::intern("Color")));
}

#[test]
fn constructor_unary() {
    assert_module_type(
        "module T where\ndata Box a = MkBox a\nx = MkBox 42",
        "x", Type::app(Type::Con(interner::intern("Box")), Type::int()));
}

#[test]
fn constructor_binary() {
    assert_module_type(
        "module T where\ndata Pair a b = MkPair a b\nx = MkPair 42 true",
        "x", Type::app(
            Type::app(Type::Con(interner::intern("Pair")), Type::int()),
            Type::boolean()));
}

#[test]
fn constructor_nothing() {
    // Nothing :: forall a. Maybe a — should be polymorphic
    let source = "module T where\ndata Maybe a = Just a | Nothing\nx = Nothing";
    let ty = assert_module_fn_type(source, "x");
    match ty {
        Type::App(f, _) => assert_eq!(*f, Type::Con(interner::intern("Maybe"))),
        other => panic!("expected Maybe ?a, got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 3. LAMBDA ABSTRACTION
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn lambda_identity() {
    let expr = parser::parse_expr(r"\x -> x").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Fun(a, b) => assert_eq!(*a, *b, "identity should have same in/out type"),
        other => panic!("expected function type, got: {}", other),
    }
}

#[test]
fn lambda_const() {
    let expr = parser::parse_expr(r"\x -> \y -> x").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match &ty {
        Type::Fun(a, inner) => match inner.as_ref() {
            Type::Fun(_, c) => assert_eq!(**a, **c, "const returns first arg"),
            other => panic!("expected inner function, got: {}", other),
        },
        other => panic!("expected function type, got: {}", other),
    }
}

#[test]
fn lambda_multi_param() {
    let expr = parser::parse_expr(r"\x y z -> x").unwrap();
    let ty = infer_expr(&expr).unwrap();
    // Should be a -> b -> c -> a
    match &ty {
        Type::Fun(a, inner1) => match inner1.as_ref() {
            Type::Fun(_, inner2) => match inner2.as_ref() {
                Type::Fun(_, result) => assert_eq!(**a, **result),
                other => panic!("expected 3-arg function, got: {}", other),
            },
            other => panic!("expected 3-arg function, got: {}", other),
        },
        other => panic!("expected function type, got: {}", other),
    }
}

#[test]
fn lambda_wildcard_binder() {
    let expr = parser::parse_expr(r"\_ -> 42").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Fun(_, ret) => assert_eq!(*ret, Type::int()),
        other => panic!("expected function type, got: {}", other),
    }
}

#[test]
fn lambda_applied_to_int() {
    assert_expr_type(r"(\x -> x) 42", Type::int());
}

#[test]
fn lambda_applied_to_string() {
    assert_expr_type(r#"(\x -> x) "hello""#, Type::string());
}

#[test]
fn lambda_nested() {
    // (\f -> \x -> f x) (\y -> y) 42 should be Int
    assert_expr_type(r"(\f -> \x -> f x) (\y -> y) 42", Type::int());
}

#[test]
fn lambda_returns_lambda() {
    // \x -> \y -> x should be a -> b -> a
    let expr = parser::parse_expr(r"\x -> \y -> x").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match &ty {
        Type::Fun(_, inner) => assert!(matches!(inner.as_ref(), Type::Fun(_, _))),
        other => panic!("expected curried function, got: {}", other),
    }
}

#[test]
fn lambda_body_uses_if() {
    assert_expr_type(r"(\x -> if x then 1 else 0) true", Type::int());
}

// ═══════════════════════════════════════════════════════════════════════════
// 4. FUNCTION APPLICATION
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn app_identity_int() {
    assert_expr_type(r"(\x -> x) 42", Type::int());
}

#[test]
fn app_const_int_string() {
    assert_expr_type(r#"(\x -> \y -> x) 42 "ignored""#, Type::int());
}

#[test]
fn app_curried_multi() {
    // (\x -> \y -> \z -> x) 42 true "hello" should be Int
    assert_expr_type(r#"(\x -> \y -> \z -> x) 42 true "hello""#, Type::int());
}

#[test]
fn app_constructor() {
    assert_module_type(
        "module T where\ndata Maybe a = Just a | Nothing\nx = Just 42",
        "x",
        Type::app(Type::Con(interner::intern("Maybe")), Type::int()));
}

#[test]
fn err_app_non_function() {
    assert_expr_error(r#"42 "hello""#);
}

#[test]
fn err_app_wrong_arg_type() {
    // (\x -> if x then 1 else 2) expects Boolean, gets String
    assert_expr_error(r#"(\x -> if x then 1 else 2) "hello""#);
}

#[test]
fn app_nested() {
    // (\f -> f 42) (\x -> x) should be Int
    assert_expr_type(r"(\f -> f 42) (\x -> x)", Type::int());
}

// ═══════════════════════════════════════════════════════════════════════════
// 5. IF-THEN-ELSE
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn if_simple_int() {
    assert_expr_type("if true then 1 else 2", Type::int());
}

#[test]
fn if_simple_string() {
    assert_expr_type(r#"if true then "a" else "b""#, Type::string());
}

#[test]
fn if_nested_in_else() {
    assert_expr_type("if true then 1 else if false then 2 else 3", Type::int());
}

#[test]
fn if_nested_in_then() {
    assert_expr_type("if true then if false then 1 else 2 else 3", Type::int());
}

#[test]
fn if_with_application() {
    assert_expr_type(r"if true then (\x -> x) 42 else 0", Type::int());
}

#[test]
fn err_if_branch_mismatch() {
    assert_expr_error(r#"if true then 1 else "hello""#);
}

#[test]
fn err_if_condition_not_bool() {
    assert_expr_error("if 42 then 1 else 2");
}

#[test]
fn err_if_condition_string() {
    assert_expr_error(r#"if "true" then 1 else 2"#);
}

// ═══════════════════════════════════════════════════════════════════════════
// 6. LET EXPRESSIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn let_simple() {
    assert_expr_type("let\n  x = 42\nin x", Type::int());
}

#[test]
fn let_multiple_bindings() {
    assert_expr_type("let\n  x = 42\n  y = true\nin x", Type::int());
}

#[test]
fn let_polymorphism_id() {
    // id used at multiple types
    assert_expr_type(
        "let\n  id = \\x -> x\nin id 42",
        Type::int());
}

#[test]
fn let_polymorphism_multi_use() {
    assert_expr_type(
        "let\n  id = \\x -> x\nin if id true then id 1 else id 2",
        Type::int());
}

#[test]
fn let_nested() {
    assert_expr_type(
        "let\n  x = let\n    y = 42\n  in y\nin x",
        Type::int());
}

#[test]
fn let_shadowing() {
    // Inner x shadows outer x
    assert_expr_type(
        "let\n  x = true\nin let\n  x = 42\nin x",
        Type::int());
}

#[test]
fn let_body_uses_binding() {
    assert_expr_type(
        "let\n  double = \\x -> x\nin double 42",
        Type::int());
}

#[test]
fn let_const_function() {
    assert_expr_type(
        r#"let
  k = \x -> \y -> x
in k 42 "ignored""#,
        Type::int());
}

// ═══════════════════════════════════════════════════════════════════════════
// 7. CASE EXPRESSIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn case_wildcard() {
    assert_module_type(
        "module T where\nf x = case x of\n  _ -> 42",
        "f",
        // f : a -> Int (any input, returns Int)
        Type::fun(Type::Unif(purescript_fast_compiler::typechecker::types::TyVarId(0)), Type::int()));
    // We can't predict the exact TyVarId, so let's just check it's a function to Int
    let ty = assert_module_fn_type("module T where\nf x = case x of\n  _ -> 42", "f");
    match ty {
        Type::Fun(_, ret) => assert_eq!(*ret, Type::int()),
        other => panic!("expected function type, got: {}", other),
    }
}

#[test]
fn case_literal_int() {
    let source = "module T where
data MyBool = MyTrue | MyFalse
f x = case x of
  0 -> MyTrue
  _ -> MyFalse";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::int());
            assert_eq!(*to, Type::Con(interner::intern("MyBool")));
        }
        other => panic!("expected Int -> MyBool, got: {}", other),
    }
}

#[test]
fn case_constructor_patterns() {
    let source = "module T where
data MyBool = MyTrue | MyFalse
f x = case x of
  MyTrue -> 1
  MyFalse -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::Con(interner::intern("MyBool")));
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected MyBool -> Int, got: {}", other),
    }
}

#[test]
fn case_constructor_with_arg() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y -> y
  Nothing -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::app(Type::Con(interner::intern("Maybe")), Type::int()));
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected Maybe Int -> Int, got: {}", other),
    }
}

#[test]
fn case_multiple_scrutinees() {
    let source = "module T where
f x y = case x, y of
  true, true -> 1
  _, _ -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(a, inner) => {
            assert_eq!(*a, Type::boolean());
            match *inner {
                Type::Fun(b, ret) => {
                    assert_eq!(*b, Type::boolean());
                    assert_eq!(*ret, Type::int());
                }
                other => panic!("expected Bool -> Int, got: {}", other),
            }
        }
        other => panic!("expected Bool -> Bool -> Int, got: {}", other),
    }
}

#[test]
fn case_with_boolean_guard() {
    let source = "module T where
f x = case x of
  y
    | y -> 1
    | true -> 0";
    // y is matched against x, guard checks y is Boolean
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::boolean());
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected Boolean -> Int, got: {}", other),
    }
}

#[test]
fn case_as_pattern() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  y@(Just _) -> y
  Nothing -> Nothing";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, *to, "input and output should be same Maybe type");
        }
        other => panic!("expected Maybe a -> Maybe a, got: {}", other),
    }
}

#[test]
fn case_no_exhaustiveness_check() {
    // Currently no exhaustiveness checking — missing arm should still pass
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y -> y";
    // Should NOT error (no exhaustiveness check yet)
    let _ty = assert_module_fn_type(source, "f");
}

// ═══════════════════════════════════════════════════════════════════════════
// 8. OPERATORS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn op_with_env() {
    // Set up an environment with (+) :: Int -> Int -> Int
    let mut env = Env::new();
    let plus = interner::intern("+");
    env.insert_mono(plus, Type::fun(Type::int(), Type::fun(Type::int(), Type::int())));
    assert_expr_type_with_env("1 + 2", &env, Type::int());
}

#[test]
fn op_section_with_env() {
    let mut env = Env::new();
    let plus = interner::intern("+");
    let plus_ty = Type::fun(Type::int(), Type::fun(Type::int(), Type::int()));
    env.insert_mono(plus, plus_ty.clone());
    assert_expr_type_with_env("(+)", &env, plus_ty);
}

#[test]
fn op_chained() {
    let mut env = Env::new();
    let plus = interner::intern("+");
    env.insert_mono(plus, Type::fun(Type::int(), Type::fun(Type::int(), Type::int())));
    // 1 + 2 + 3 (right-associative in grammar) should still be Int
    assert_expr_type_with_env("1 + 2 + 3", &env, Type::int());
}

#[test]
fn op_different_types() {
    // (<>) :: String -> String -> String
    let mut env = Env::new();
    let append = interner::intern("<>");
    env.insert_mono(append, Type::fun(Type::string(), Type::fun(Type::string(), Type::string())));
    assert_expr_type_with_env(r#""hello" <> " world""#, &env, Type::string());
}

#[test]
fn err_op_undefined() {
    assert_expr_error("1 + 2"); // (+) not in empty env
}

#[test]
fn err_op_type_mismatch() {
    let mut env = Env::new();
    let plus = interner::intern("+");
    env.insert_mono(plus, Type::fun(Type::int(), Type::fun(Type::int(), Type::int())));
    let expr = parser::parse_expr(r#""hello" + 42"#).unwrap();
    assert!(infer_expr_with_env(&env, &expr).is_err());
}

// ═══════════════════════════════════════════════════════════════════════════
// 9. NEGATION
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn negate_int() {
    assert_expr_type("-42", Type::int());
}

#[test]
fn negate_nested() {
    assert_expr_type("-(-(42))", Type::int());
}

#[test]
fn err_negate_string() {
    assert_expr_error(r#"-"hello""#);
}

#[test]
fn err_negate_boolean() {
    assert_expr_error("-true");
}

// ═══════════════════════════════════════════════════════════════════════════
// 10. TYPE ANNOTATIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn annotation_int() {
    assert_expr_type("(42 :: Int)", Type::int());
}

#[test]
fn annotation_string() {
    assert_expr_type(r#"("hello" :: String)"#, Type::string());
}

#[test]
fn err_annotation_mismatch() {
    assert_expr_error(r#"(42 :: String)"#);
}

#[test]
fn err_annotation_bool_as_int() {
    assert_expr_error("(true :: Int)");
}

#[test]
fn annotation_nested() {
    assert_expr_type("((42 :: Int) :: Int)", Type::int());
}

// ═══════════════════════════════════════════════════════════════════════════
// 11. TYPED HOLES
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn hole_simple() {
    assert_expr_error_kind("?todo",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole");
}

#[test]
fn hole_in_application() {
    // (\x -> x) ?todo — should still be TypeHole
    assert_expr_error_kind(r"(\x -> x) ?todo",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole");
}

#[test]
fn hole_in_if_branch() {
    assert_expr_error_kind("if true then ?todo else 42",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole");
}

#[test]
fn hole_in_let() {
    assert_expr_error_kind("let\n  x = ?todo\nin x",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole");
}

// ═══════════════════════════════════════════════════════════════════════════
// 12. OCCURS CHECK (INFINITE TYPES)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn err_occurs_self_application() {
    // \x -> x x requires x : a and x : a -> b, infinite
    assert_expr_error_kind(r"\x -> x x",
        |e| matches!(e, TypeError::InfiniteType { .. }),
        "InfiniteType");
}

#[test]
fn err_occurs_f_f() {
    assert_expr_error_kind(r"\f -> f f",
        |e| matches!(e, TypeError::InfiniteType { .. }),
        "InfiniteType");
}

#[test]
fn err_occurs_y_combinator() {
    // \f -> (\x -> f (x x)) (\x -> f (x x)) — infinite type
    assert_expr_error(r"\f -> (\x -> f (x x)) (\x -> f (x x))");
}

// ═══════════════════════════════════════════════════════════════════════════
// 13. MODULE-LEVEL: SIMPLE VALUES
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn module_value_int() {
    assert_module_type("module T where\nx = 42", "x", Type::int());
}

#[test]
fn module_value_string() {
    assert_module_type(r#"module T where
x = "hello""#, "x", Type::string());
}

#[test]
fn module_value_bool() {
    assert_module_type("module T where\nx = true", "x", Type::boolean());
}

#[test]
fn module_multiple_values() {
    let source = "module T where\na = 42\nb = true\nc = \"hello\"";
    let types = check_module_types(source).unwrap();
    assert_eq!(*types.get(&interner::intern("a")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("b")).unwrap(), Type::boolean());
    assert_eq!(*types.get(&interner::intern("c")).unwrap(), Type::string());
}

#[test]
fn module_value_with_signature() {
    assert_module_type("module T where\nx :: Int\nx = 42", "x", Type::int());
}

#[test]
fn module_value_uses_prior_binding() {
    assert_module_type("module T where\nx = 42\ny = x", "y", Type::int());
}

#[test]
fn err_module_signature_mismatch() {
    assert_module_error_kind("module T where\nx :: Int\nx = true",
        |e| matches!(e, TypeError::UnificationError { .. }),
        "UnificationError");
}

#[test]
fn err_module_duplicate_signature() {
    assert_module_error_kind("module T where\nx :: Int\nx :: String\nx = 42",
        |e| matches!(e, TypeError::DuplicateTypeSignature { .. }),
        "DuplicateTypeSignature");
}

#[test]
fn err_module_orphan_signature() {
    assert_module_error_kind("module T where\nx :: Int",
        |e| matches!(e, TypeError::OrphanTypeSignature { .. }),
        "OrphanTypeSignature");
}

// ═══════════════════════════════════════════════════════════════════════════
// 14. MODULE-LEVEL: FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn module_function_identity() {
    let ty = assert_module_fn_type("module T where\nf x = x", "f");
    match ty {
        Type::Fun(a, b) => assert_eq!(*a, *b),
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn module_function_const() {
    let ty = assert_module_fn_type("module T where\nf x y = x", "f");
    match &ty {
        Type::Fun(a, inner) => match inner.as_ref() {
            Type::Fun(_, c) => assert_eq!(**a, **c),
            other => panic!("expected curried function, got: {}", other),
        },
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn module_function_applied() {
    assert_module_type("module T where\nf x = x\ng = f 42", "g", Type::int());
}

#[test]
fn module_function_polymorphic_use() {
    let source = "module T where\nf x = x\ng = f 42\nh = f true";
    let types = check_module_types(source).unwrap();
    assert_eq!(*types.get(&interner::intern("g")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("h")).unwrap(), Type::boolean());
}

#[test]
fn module_function_with_forall_sig() {
    let ty = assert_module_fn_type(
        "module T where\nid :: forall a. a -> a\nid x = x", "id");
    match ty {
        Type::Fun(a, b) => assert_eq!(*a, *b),
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn module_function_with_where() {
    assert_module_type(
        "module T where
f = y
  where
  y = 42",
        "f", Type::int());
}

#[test]
fn module_function_constrained_sig() {
    // Constraints are stripped — the function should still typecheck
    let ty = assert_module_fn_type(
        "module T where\nshow :: forall a. Show a => a -> String\nshow x = \"todo\"",
        "show");
    match ty {
        Type::Fun(_, ret) => assert_eq!(*ret, Type::string()),
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn err_module_function_wrong_return() {
    assert_module_error("module T where\nf :: Int -> String\nf x = x");
}

// ═══════════════════════════════════════════════════════════════════════════
// 15. MODULE-LEVEL: DATA TYPES
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn module_data_simple_enum() {
    let source = "module T where\ndata Color = Red | Green | Blue\nx = Green";
    assert_module_type(source, "x", Type::Con(interner::intern("Color")));
}

#[test]
fn module_data_maybe() {
    let source = "module T where\ndata Maybe a = Just a | Nothing\nx = Just 42";
    assert_module_type(source, "x",
        Type::app(Type::Con(interner::intern("Maybe")), Type::int()));
}

#[test]
fn module_data_either() {
    let source = "module T where
data Either a b = Left a | Right b
x = Left 42
y = Right true";
    let types = check_module_types(source).unwrap();

    let x_ty = types.get(&interner::intern("x")).unwrap();
    match x_ty {
        Type::App(f, _) => match f.as_ref() {
            Type::App(either, arg) => {
                assert_eq!(**either, Type::Con(interner::intern("Either")));
                assert_eq!(**arg, Type::int());
            }
            other => panic!("expected Either Int _, got: {}", other),
        },
        other => panic!("expected Either type, got: {}", other),
    }
}

#[test]
fn module_data_multi_field_constructor() {
    let source = "module T where
data Pair a b = MkPair a b
x = MkPair 42 true";
    assert_module_type(source, "x",
        Type::app(
            Type::app(Type::Con(interner::intern("Pair")), Type::int()),
            Type::boolean()));
}

#[test]
fn module_newtype() {
    let source = "module T where\nnewtype Name = Name String\nx = Name \"Alice\"";
    assert_module_type(source, "x", Type::Con(interner::intern("Name")));
}

#[test]
fn module_newtype_parameterized() {
    let source = "module T where\nnewtype Wrapper a = Wrapper a\nx = Wrapper 42";
    assert_module_type(source, "x",
        Type::app(Type::Con(interner::intern("Wrapper")), Type::int()));
}

#[test]
fn module_data_recursive() {
    // Recursive data type — constructors should work
    let source = "module T where
data List a = Nil | Cons a (List a)
x = Nil
y = Cons 1 Nil";
    let types = check_module_types(source).unwrap();

    // x = Nil :: List ?a (polymorphic)
    let x_ty = types.get(&interner::intern("x")).unwrap();
    match x_ty {
        Type::App(f, _) => assert_eq!(**f, Type::Con(interner::intern("List"))),
        other => panic!("expected List type for Nil, got: {}", other),
    }

    // y = Cons 1 Nil :: List Int
    assert_eq!(
        *types.get(&interner::intern("y")).unwrap(),
        Type::app(Type::Con(interner::intern("List")), Type::int()));
}

#[test]
fn module_data_case_deconstruct() {
    let source = "module T where
data Maybe a = Just a | Nothing
fromMaybe d x = case x of
  Just v -> v
  Nothing -> d";
    let ty = assert_module_fn_type(source, "fromMaybe");
    // Should be a -> Maybe a -> a
    match &ty {
        Type::Fun(a, inner) => match inner.as_ref() {
            Type::Fun(maybe_a, result) => {
                assert_eq!(**a, **result, "default and result should match");
                match maybe_a.as_ref() {
                    Type::App(f, elem) => {
                        assert_eq!(**f, Type::Con(interner::intern("Maybe")));
                        assert_eq!(**elem, **a, "Maybe elem should match default type");
                    }
                    other => panic!("expected Maybe type, got: {}", other),
                }
            }
            other => panic!("expected curried function, got: {}", other),
        },
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn module_foreign_import() {
    let source = "module T where
foreign import sqrt :: Number -> Number
x = sqrt 4.0";
    assert_module_type(source, "x", Type::float());
}

// ═══════════════════════════════════════════════════════════════════════════
// 16. COMPLEX / COMBINED FEATURES
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn combined_let_with_case() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = let
  g = case x of
    Just v -> v
    Nothing -> 0
in g";
    assert_module_type(source, "f",
        Type::fun(
            Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
            Type::int()));
}

#[test]
fn combined_nested_constructors() {
    let source = "module T where
data Maybe a = Just a | Nothing
x = Just (Just 42)";
    assert_module_type(source, "x",
        Type::app(
            Type::Con(interner::intern("Maybe")),
            Type::app(Type::Con(interner::intern("Maybe")), Type::int())));
}

#[test]
fn combined_higher_order_function() {
    let source = "module T where
apply f x = f x
result = apply (\\x -> x) 42";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn combined_if_with_constructors() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = if true then Just x else Nothing";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(a, result) => {
            match result.as_ref() {
                Type::App(f, elem) => {
                    assert_eq!(**f, Type::Con(interner::intern("Maybe")));
                    assert_eq!(**elem, *a, "Just x should have same type as input");
                }
                other => panic!("expected Maybe type, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn combined_array_of_constructors() {
    let source = "module T where
data Maybe a = Just a | Nothing
x = [Just 1, Just 2, Nothing]";
    assert_module_type(source, "x",
        Type::array(Type::app(Type::Con(interner::intern("Maybe")), Type::int())));
}

#[test]
fn combined_function_returning_array() {
    let source = "module T where
f x = [x, x, x]";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(a, arr) => {
            assert_eq!(*arr, Type::array((*a).clone()));
        }
        other => panic!("expected function returning array, got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 17. NOT YET IMPLEMENTED — EXPRESSIONS
// These tests serve as a roadmap. When features are implemented, update
// these to assert the correct types instead of NotImplemented.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn not_impl_record_literal() {
    assert_not_implemented_expr("{ x: 1, y: 2 }");
}

#[test]
fn not_impl_record_empty() {
    assert_not_implemented_expr("{}");
}

#[test]
fn not_impl_record_access() {
    // Record access requires record inference
    assert_not_implemented_expr("{ x: 1 }.x");
}

#[test]
fn not_impl_do_notation() {
    let source = "module T where
f = do
  pure 42";
    assert_module_not_implemented(source);
}

#[test]
fn not_impl_ado_notation() {
    let source = "module T where
f = ado
  x <- [1, 2]
  in x";
    assert_module_not_implemented(source);
}

// ═══════════════════════════════════════════════════════════════════════════
// 18. NOT YET IMPLEMENTED — MODULE-LEVEL DECLARATIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn not_impl_type_class() {
    // Type class declarations are skipped, but using class methods should fail
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
x = myEq 1 2";
    // myEq won't be in env, so UndefinedVariable
    assert_module_error(source);
}

#[test]
fn not_impl_instance() {
    // Instance declarations are skipped
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
instance MyEq Int where
  myEq x y = true
x = myEq 1 2";
    // myEq still won't be in env
    assert_module_error(source);
}

// ═══════════════════════════════════════════════════════════════════════════
// 19. NOT YET IMPLEMENTED — BINDER PATTERNS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn not_impl_array_binder() {
    let source = "module T where
f x = case x of
  [a, b] -> a
  _ -> 0";
    assert_module_not_implemented(source);
}

// ═══════════════════════════════════════════════════════════════════════════
// 20. NOT YET IMPLEMENTED — TYPE FEATURES
// ═══════════════════════════════════════════════════════════════════════════

// These test features that require type system extensions:

// Row types / records
// Type aliases (type Foo = Bar)
// Kind annotations
// Type-level operators
// Visible type application (@Type)
// Pattern guards (| Just x <- lookup key map -> ...)
// Deriving
// Foreign data

// When implementing these, add passing tests and convert the
// not_impl tests above to passing ones.
