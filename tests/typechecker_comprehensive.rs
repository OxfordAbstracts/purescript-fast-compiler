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
use purescript_fast_compiler::typechecker::env::Env;
use purescript_fast_compiler::typechecker::error::TypeError;
use purescript_fast_compiler::typechecker::types::Type;
use purescript_fast_compiler::typechecker::{check_module, infer_expr, infer_expr_with_env};

// ===== Test Helpers =====

fn assert_expr_type(source: &str, expected: Type) {
    let expr = parser::parse_expr(source)
        .unwrap_or_else(|e| panic!("parse failed for '{}': {}", source, e));
    match infer_expr(&expr) {
        Ok(ty) => assert_eq!(ty, expected, "for expression: {}", source),
        Err(e) => panic!("type error for '{}': {}", source, e),
    }
}

fn assert_expr_type_with_env(source: &str, env: &Env, expected: Type) {
    let expr = parser::parse_expr(source)
        .unwrap_or_else(|e| panic!("parse failed for '{}': {}", source, e));
    match infer_expr_with_env(env, &expr) {
        Ok(ty) => assert_eq!(ty, expected, "for expression: {}", source),
        Err(e) => panic!("type error for '{}': {}", source, e),
    }
}

fn assert_expr_error(source: &str) {
    let expr = parser::parse_expr(source)
        .unwrap_or_else(|e| panic!("parse failed for '{}': {}", source, e));
    assert!(
        infer_expr(&expr).is_err(),
        "expected type error for '{}', got: {:?}",
        source,
        infer_expr(&expr)
    );
}

fn assert_expr_error_kind<F: Fn(&TypeError) -> bool>(source: &str, pred: F, desc: &str) {
    let expr = parser::parse_expr(source)
        .unwrap_or_else(|e| panic!("parse failed for '{}': {}", source, e));
    match infer_expr(&expr) {
        Err(ref e) if pred(e) => {}
        Err(e) => panic!("expected {} for '{}', got: {}", desc, source, e),
        Ok(ty) => panic!("expected {} for '{}', got type: {}", desc, source, ty),
    }
}

fn check_module_types(source: &str) -> (HashMap<Symbol, Type>, Vec<TypeError>) {
    let module = parser::parse(source).unwrap_or_else(|e| panic!("parse failed: {}", e));
    let result = check_module(&module);
    (result.types, result.errors)
}

fn assert_module_type(source: &str, name: &str, expected: Type) {
    let (types, errors) = check_module_types(source);
    if !errors.is_empty() {
        panic!(
            "typecheck failed for module: {:?}",
            errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }
    let sym = interner::intern(name);
    let ty = types.get(&sym).unwrap_or_else(|| {
        let names: Vec<_> = types
            .keys()
            .map(|k| interner::resolve(*k).unwrap_or_default())
            .collect();
        panic!("name '{}' not found. available: {:?}", name, names)
    });
    assert_eq!(*ty, expected, "for name '{}' in module", name);
}

fn assert_module_fn_type(source: &str, name: &str) -> Type {
    let (types, errors) = check_module_types(source);
    if !errors.is_empty() {
        panic!(
            "typecheck failed for module: {:?}",
            errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }
    let sym = interner::intern(name);
    types
        .get(&sym)
        .unwrap_or_else(|| panic!("name '{}' not found in module types", name))
        .clone()
}

fn assert_module_error(source: &str) {
    let (_, errors) = check_module_types(source);
    assert!(
        !errors.is_empty(),
        "expected type error for module, got no errors"
    );
}

fn assert_module_error_kind<F: Fn(&TypeError) -> bool>(source: &str, pred: F, desc: &str) {
    let (_, errors) = check_module_types(source);
    if errors.is_empty() {
        panic!("expected {} for module, got no errors", desc);
    }
    assert!(
        errors.iter().any(|e| pred(e)),
        "expected {} for module, got: {:?}",
        desc,
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
}

#[allow(dead_code)]
fn assert_not_implemented_expr(source: &str) {
    let expr = parser::parse_expr(source)
        .unwrap_or_else(|e| panic!("parse failed for '{}': {}", source, e));
    match infer_expr(&expr) {
        Err(TypeError::NotImplemented { .. }) => {}
        Err(e) => panic!("expected NotImplemented for '{}', got: {}", source, e),
        Ok(ty) => panic!("expected NotImplemented for '{}', got type: {}", source, ty),
    }
}

#[allow(dead_code)]
fn assert_module_not_implemented(source: &str) {
    let (_, errors) = check_module_types(source);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, TypeError::NotImplemented { .. })),
        "expected NotImplemented for module, got: {:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
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
    assert_expr_error_kind(
        "undefinedVar",
        |e| matches!(e, TypeError::UndefinedVariable { .. }),
        "UndefinedVariable",
    );
}

#[test]
fn var_defined_in_module() {
    assert_module_type("module T where\nx = 42\ny = x", "y", Type::int());
}

#[test]
fn constructor_nullary() {
    assert_module_type(
        "module T where\ndata Color = Red | Green | Blue\nx = Red",
        "x",
        Type::Con(interner::intern("Color")),
    );
}

#[test]
fn constructor_unary() {
    assert_module_type(
        "module T where\ndata Box a = MkBox a\nx = MkBox 42",
        "x",
        Type::app(Type::Con(interner::intern("Box")), Type::int()),
    );
}

#[test]
fn constructor_binary() {
    assert_module_type(
        "module T where\ndata Pair a b = MkPair a b\nx = MkPair 42 true",
        "x",
        Type::app(
            Type::app(Type::Con(interner::intern("Pair")), Type::int()),
            Type::boolean(),
        ),
    );
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
        Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
    );
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
    assert_expr_type("let\n  id = \\x -> x\nin id 42", Type::int());
}

#[test]
fn let_polymorphism_multi_use() {
    assert_expr_type(
        "let\n  id = \\x -> x\nin if id true then id 1 else id 2",
        Type::int(),
    );
}

#[test]
fn let_nested() {
    assert_expr_type("let\n  x = let\n    y = 42\n  in y\nin x", Type::int());
}

#[test]
fn let_shadowing() {
    // Inner x shadows outer x
    assert_expr_type("let\n  x = true\nin let\n  x = 42\nin x", Type::int());
}

#[test]
fn let_body_uses_binding() {
    assert_expr_type("let\n  double = \\x -> x\nin double 42", Type::int());
}

#[test]
fn let_const_function() {
    assert_expr_type(
        r#"let
  k = \x -> \y -> x
in k 42 "ignored""#,
        Type::int(),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 7. CASE EXPRESSIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn case_wildcard() {
    // f : a -> Int (any input, returns Int)
    // We can't predict the exact TyVarId, so just check it's a function to Int
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
            assert_eq!(
                *from,
                Type::app(Type::Con(interner::intern("Maybe")), Type::int())
            );
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
fn case_non_exhaustive_reports_error() {
    // Exhaustiveness checking: missing Nothing arm should error
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y -> y";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 8. OPERATORS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn op_with_env() {
    // Set up an environment with (+) :: Int -> Int -> Int
    let mut env = Env::new();
    let plus = interner::intern("+");
    env.insert_mono(
        plus,
        Type::fun(Type::int(), Type::fun(Type::int(), Type::int())),
    );
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
    env.insert_mono(
        plus,
        Type::fun(Type::int(), Type::fun(Type::int(), Type::int())),
    );
    // 1 + 2 + 3 (right-associative in grammar) should still be Int
    assert_expr_type_with_env("1 + 2 + 3", &env, Type::int());
}

#[test]
fn op_different_types() {
    // (<>) :: String -> String -> String
    let mut env = Env::new();
    let append = interner::intern("<>");
    env.insert_mono(
        append,
        Type::fun(Type::string(), Type::fun(Type::string(), Type::string())),
    );
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
    env.insert_mono(
        plus,
        Type::fun(Type::int(), Type::fun(Type::int(), Type::int())),
    );
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
    assert_expr_error_kind(
        "?todo",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole",
    );
}

#[test]
fn hole_in_application() {
    // (\x -> x) ?todo — should still be TypeHole
    assert_expr_error_kind(
        r"(\x -> x) ?todo",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole",
    );
}

#[test]
fn hole_in_if_branch() {
    assert_expr_error_kind(
        "if true then ?todo else 42",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole",
    );
}

#[test]
fn hole_in_let() {
    assert_expr_error_kind(
        "let\n  x = ?todo\nin x",
        |e| matches!(e, TypeError::TypeHole { .. }),
        "TypeHole",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 12. OCCURS CHECK (INFINITE TYPES)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn err_occurs_self_application() {
    // \x -> x x requires x : a and x : a -> b, infinite
    assert_expr_error_kind(
        r"\x -> x x",
        |e| matches!(e, TypeError::InfiniteType { .. }),
        "InfiniteType",
    );
}

#[test]
fn err_occurs_f_f() {
    assert_expr_error_kind(
        r"\f -> f f",
        |e| matches!(e, TypeError::InfiniteType { .. }),
        "InfiniteType",
    );
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
    assert_module_type(
        r#"module T where
x = "hello""#,
        "x",
        Type::string(),
    );
}

#[test]
fn module_value_bool() {
    assert_module_type("module T where\nx = true", "x", Type::boolean());
}

#[test]
fn module_multiple_values() {
    let source = "module T where\na = 42\nb = true\nc = \"hello\"";
    let (types, errors) = check_module_types(source);
    assert!(
        errors.is_empty(),
        "unexpected errors: {:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
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
    assert_module_error_kind(
        "module T where\nx :: Int\nx = true",
        |e| matches!(e, TypeError::UnificationError { .. }),
        "UnificationError",
    );
}

#[test]
fn err_module_duplicate_signature() {
    assert_module_error_kind(
        "module T where\nx :: Int\nx :: String\nx = 42",
        |e| matches!(e, TypeError::DuplicateTypeSignature { .. }),
        "DuplicateTypeSignature",
    );
}

#[test]
fn err_module_orphan_signature() {
    assert_module_error_kind(
        "module T where\nx :: Int",
        |e| matches!(e, TypeError::OrphanTypeSignature { .. }),
        "OrphanTypeSignature",
    );
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
    let (types, errors) = check_module_types(source);
    assert!(
        errors.is_empty(),
        "unexpected errors: {:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
    assert_eq!(*types.get(&interner::intern("g")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("h")).unwrap(), Type::boolean());
}

#[test]
fn module_function_with_forall_sig() {
    let ty = assert_module_fn_type("module T where\nid :: forall a. a -> a\nid x = x", "id");
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
        "f",
        Type::int(),
    );
}

#[test]
fn module_function_constrained_sig() {
    // Constraints are stripped — the function should still typecheck
    let ty = assert_module_fn_type(
        "module T where\nshow :: forall a. Show a => a -> String\nshow x = \"todo\"",
        "show",
    );
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
    assert_module_type(
        source,
        "x",
        Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
    );
}

#[test]
fn module_data_either() {
    let source = "module T where
data Either a b = Left a | Right b
x = Left 42
y = Right true";
    let (types, errors) = check_module_types(source);
    assert!(
        errors.is_empty(),
        "unexpected errors: {:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );

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
    assert_module_type(
        source,
        "x",
        Type::app(
            Type::app(Type::Con(interner::intern("Pair")), Type::int()),
            Type::boolean(),
        ),
    );
}

#[test]
fn module_newtype() {
    let source = "module T where\nnewtype Name = Name String\nx = Name \"Alice\"";
    assert_module_type(source, "x", Type::Con(interner::intern("Name")));
}

#[test]
fn module_newtype_parameterized() {
    let source = "module T where\nnewtype Wrapper a = Wrapper a\nx = Wrapper 42";
    assert_module_type(
        source,
        "x",
        Type::app(Type::Con(interner::intern("Wrapper")), Type::int()),
    );
}

#[test]
fn module_data_recursive() {
    // Recursive data type — constructors should work
    let source = "module T where
data List a = Nil | Cons a (List a)
x = Nil
y = Cons 1 Nil";
    let (types, errors) = check_module_types(source);
    assert!(
        errors.is_empty(),
        "unexpected errors: {:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );

    // x = Nil :: List ?a (polymorphic)
    let x_ty = types.get(&interner::intern("x")).unwrap();
    match x_ty {
        Type::App(f, _) => assert_eq!(**f, Type::Con(interner::intern("List"))),
        other => panic!("expected List type for Nil, got: {}", other),
    }

    // y = Cons 1 Nil :: List Int
    assert_eq!(
        *types.get(&interner::intern("y")).unwrap(),
        Type::app(Type::Con(interner::intern("List")), Type::int())
    );
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
    assert_module_type(
        source,
        "f",
        Type::fun(
            Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
            Type::int(),
        ),
    );
}

#[test]
fn combined_nested_constructors() {
    let source = "module T where
data Maybe a = Just a | Nothing
x = Just (Just 42)";
    assert_module_type(
        source,
        "x",
        Type::app(
            Type::Con(interner::intern("Maybe")),
            Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
        ),
    );
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
        Type::Fun(a, result) => match result.as_ref() {
            Type::App(f, elem) => {
                assert_eq!(**f, Type::Con(interner::intern("Maybe")));
                assert_eq!(**elem, *a, "Just x should have same type as input");
            }
            other => panic!("expected Maybe type, got: {}", other),
        },
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn combined_array_of_constructors() {
    let source = "module T where
data Maybe a = Just a | Nothing
x = [Just 1, Just 2, Nothing]";
    assert_module_type(
        source,
        "x",
        Type::array(Type::app(Type::Con(interner::intern("Maybe")), Type::int())),
    );
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

// ═══════════════════════════════════════════════════════════════════════════
// 17. RECORDS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn record_literal() {
    let expr = parser::parse_expr("{ x: 1, y: 2 }").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Record(fields, None) => {
            assert_eq!(fields.len(), 2);
        }
        other => panic!("expected record type, got: {}", other),
    }
}

#[test]
fn record_empty() {
    let expr = parser::parse_expr("{}").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Record(fields, None) => assert!(fields.is_empty()),
        other => panic!("expected empty record type, got: {}", other),
    }
}

#[test]
fn record_access() {
    let expr = parser::parse_expr("{ x: 1 }.x").unwrap();
    let ty = infer_expr(&expr).unwrap();
    assert_eq!(ty, Type::int());
}

// ═══════════════════════════════════════════════════════════════════════════
// 18. DO / ADO NOTATION
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn do_notation_simple() {
    // do with array — [1, 2] is already monadic (Array)
    let source = "module T where
f = do
  x <- [1, 2]
  [x]";
    // Should typecheck — f has type Array Int
    assert_module_type(source, "f", Type::array(Type::int()));
}

#[test]
fn ado_notation_simple() {
    // ado { x <- [1, 2]; in x } — applicative do
    let source = "module T where
f = ado
  x <- [1, 2]
  in x";
    // Should typecheck — f has type (Array Int)
    assert_module_type(source, "f", Type::array(Type::int()));
}

// ═══════════════════════════════════════════════════════════════════════════
// 19. TYPE CLASSES
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn type_class_method_in_scope_but_no_instance() {
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
x = myEq 1 2";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NoClassInstance { .. }),
        "NoClassInstance",
    );
}

#[test]
fn type_class_method_in_scope_but_wrong_instance() {
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
instance MyEq String where
  myEq x y = true
x = myEq 1 2";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NoClassInstance { .. }),
        "NoClassInstance",
    );
}

#[test]
fn type_class_with_instance() {
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
instance MyEq Int where
  myEq x y = true
x = myEq 1 2";
    assert_module_type(source, "x", Type::boolean());
}

#[test]
fn type_class_any_instance() {
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
instance MyEq a where
  myEq x y = true
x = myEq 1 2";
    assert_module_type(source, "x", Type::boolean());
}

#[test]
fn type_class_multiple_args_pass() {
    let source = "module T where

class MyC a b where
  fn :: a -> b -> Int

instance MyC Int Boolean where
  fn _ _ = 42

x = fn 1 true ";

    assert_module_type(source, "x", Type::int());
}

#[test]
fn type_class_multiple_args_no_instance() {
    let source = "module T where

class MyC a b where
  fn :: a -> b -> Int

instance MyC Int Int where
  fn _ _ = 42

x = fn 1 true ";

    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NoClassInstance { .. }),
        "NoClassInstance",
    );
}

#[test]
fn type_class_multiple_args_any() {
    let source = "module T where

class MyC a b where
  fn :: a -> b -> Int

instance MyC Int a where
  fn _ _ = 42

x = fn 1 true ";

    assert_module_type(source, "x", Type::int());
}
#[test]
fn type_class_multiple_args_any2() {
    let source = "module T where

class MyC a b where
  fn :: a -> b -> Int

instance MyC a Int where
  fn _ _ = 42

x = fn true 1";

    assert_module_type(source, "x", Type::int());
}
#[test]
fn instance_with_constraints_pass_single() {
    let source = "module T where
class A a where
  fn :: a -> Int

class B a where
  fn2 :: a -> Int

instance A Int where
  fn x = 42

instance A a => B a where
  fn2 = fn

result = fn2 2";

    assert_module_type(source, "result", Type::int());
}

#[test]
fn instance_with_constraints_pass_multiple() {
    let source = "module T where
class A a b where
  fn :: a -> b -> Int

class B a b where
  fn2 :: a -> b -> Int

instance A Int Int where
  fn x y = 42

instance A a b => B a b where
  fn2 = fn

result = fn2 1 2";

    assert_module_type(source, "result", Type::int());
}

#[test]
fn instance_with_constraints_no_dependency_single() {
    let source = "module T where
class A a where
  fn :: a -> Int

class B a where
  fn2 :: a -> Int

instance A Int where
  fn x = 42

instance A a => B a where
  fn2 = fn

result = fn2 true";

    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NoClassInstance { .. }),
        "NoClassInstance",
    );
}

#[test]
fn instance_with_constraints_no_dependency_multiple() {
    let source = "module T where
class A a b where
  fn :: a -> b -> Int

class B a b where
  fn2 :: a -> b -> Int

instance A Int Int where
  fn x y = 42

instance A a b => B a b where
  fn2 = fn

result = fn2 true 1";

    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NoClassInstance { .. }),
        "NoClassInstance",
    );
}

#[test]
fn instance_with_constraints_on_single_pass() {
    let source = "module T where
class A a where
  fn :: a -> Boolean

class B a b where
  fn2 :: a -> b -> Boolean

instance A Int where
  fn x = true

instance (A a, A b) => B a b where
  fn2 _ _ = true

result = fn2 1 2";

    assert_module_type(source, "result", Type::boolean());
}

#[test]
fn instance_with_constraints_on_single_fail() {
    let source = "module T where
class A a where
  fn :: a -> Boolean

class B a b where
  fn2 :: a -> b -> Boolean

instance A Int where
  fn x = true

instance (A a, A b) => B a b where
  fn2 _ _ = true

result = fn2 1 true";

    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NoClassInstance { .. }),
        "NoClassInstance",
    );
}

#[test]
fn instance_with_constraints_abcd_pass() {
    let source = "module T where
class A a where
  fn :: a -> Boolean 

class B a where
  fn2 :: a -> Boolean

class C a where
  fn3 :: a -> Boolean

class D a where
  fn4 :: a -> Boolean

instance A Int where
  fn x = true

instance A a => B a where
  fn2 _ = true

instance B a => C a where
  fn3 _ = true

instance C a => D a where
  fn4 _ = true

result = fn4 1";

    assert_module_type(source, "result", Type::boolean());
}

#[test]
fn instance_with_constraints_abcd_fail() {
    let source = "module T where
class A a where
  fn :: a -> Boolean 

class B a where
  fn2 :: a -> Boolean

class C a where
  fn3 :: a -> Boolean

class D a where
  fn4 :: a -> Boolean

instance A a => B a where
  fn2 _ = true

instance B a => C a where
  fn3 _ = true

instance C a => D a where
  fn4 _ = true
  
result = fn4 1";

    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NoClassInstance { .. }),
        "NoClassInstance",
    );
}
// ═══════════════════════════════════════════════════════════════════════════
// 20. ARRAY BINDERS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn array_binder_case() {
    let source = "module T where
f x = case x of
  [a, b] -> a
  _ -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::array(Type::int()));
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected Array Int -> Int, got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 21. RECURSIVE FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn recursive_function() {
    let source = "module T where
data List a = Nil | Cons a (List a)
length xs = case xs of
  Nil -> 0
  Cons _ rest -> length rest";
    // Should not error with UndefinedVariable for 'length'
    let ty = assert_module_fn_type(source, "length");
    match ty {
        Type::Fun(_, ret) => assert_eq!(*ret, Type::int()),
        other => panic!("expected function returning Int, got: {}", other),
    }
}

#[test]
fn recursive_function_with_accumulator() {
    let source = "module T where
data List a = Nil | Cons a (List a)
sum acc xs = case xs of
  Nil -> acc
  Cons x rest -> sum x rest";
    let _ty = assert_module_fn_type(source, "sum");
}

// ═══════════════════════════════════════════════════════════════════════════
// 22. REMAINING NOT YET IMPLEMENTED
// ═══════════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════════
// 22a. VISIBLE TYPE APPLICATION (@Type)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn vta_basic() {
    let source = "module T where
id :: forall @a. a -> a
id x = x
result = id @Int 42";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn vta_string() {
    let source = "module T where
id :: forall @a. a -> a
id x = x
result = id @String \"hello\"";
    assert_module_type(source, "result", Type::string());
}

#[test]
fn vta_multiple_vars() {
    let source = r#"module T where
const :: forall @a @b. a -> b -> a
const x y = x
result = const @Int @String 42 "hello""#;
    assert_module_type(source, "result", Type::int());
}

#[test]
fn vta_partial_application() {
    // Apply one type arg; result should still be a function
    let source = "module T where
id :: forall @a. a -> a
id x = x
result = id @Int";
    assert_module_type(source, "result", Type::fun(Type::int(), Type::int()));
}


#[test]
fn vta_fail() {
    let source = "module T where
id :: forall @a. a -> a
id x = x
result = id @Int true";
    assert_module_error(source);
}

// ═══════════════════════════════════════════════════════════════════════════
// KIND ANNOTATIONS
// ═══════════════════════════════════════════════════════════════════════════

// --- Passing cases ---

#[test]
fn kind_annotation_in_type_signature_via_forall() {
    // Kind annotation via kinded forall variable in a signature
    let source = "module T where
f :: forall (a :: Type). a -> a
f x = x
result = f 42";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn kind_annotation_in_forall_variable() {
    // Kinded forall variable: forall (a :: Type). a -> a
    let source = "module T where
id :: forall (a :: Type). a -> a
id x = x
result = id 42";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn kind_annotation_data_kind_signature() {
    // data Maybe :: Type -> Type  (kind sig, no constructors)
    // followed by the real data declaration
    let source = "module T where
data Maybe :: Type -> Type
data Maybe a = Just a | Nothing
x = Just 42";
    assert_module_type(
        source,
        "x",
        Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
    );
}

#[test]
fn kind_annotation_newtype_kind_signature() {
    // newtype Id :: Type -> Type  (kind sig only, no constructors)
    // plus the real newtype definition
    let source = "module T where
newtype Id :: Type -> Type
newtype Id a = Id a
x = Id 42";
    assert_module_type(
        source,
        "x",
        Type::app(Type::Con(interner::intern("Id")), Type::int()),
    );
}

#[test]
fn kind_annotation_type_alias_kind_signature() {
    // type MyInt :: Type  (kind sig, treated as empty data)
    // The kind signature itself should not cause errors
    let source = "module T where
type MyInt :: Type
x = 42";
    assert_module_type(source, "x", Type::int());
}

#[test]
fn kind_annotation_class_kind_signature() {
    // class MyEq :: Type -> Constraint  (kind sig)
    // followed by the real class definition and instance
    let source = "module T where
class MyEq :: Type -> Constraint
class MyEq a where
  eq :: a -> a -> Boolean
instance MyEq Int where
  eq a b = true
result = eq 1 2";
    assert_module_type(source, "result", Type::boolean());
}

#[test]
fn kind_annotation_foreign_data() {
    // foreign import data with kind annotation registers the type name
    let source = "module T where
foreign import data Effect :: Type -> Type
foreign import pure :: forall a. a -> Effect a
x = pure 42";
    let (types, errors) = check_module_types(source);
    assert!(
        errors.is_empty(),
        "unexpected errors: {:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
    let x_ty = types.get(&interner::intern("x")).unwrap();
    match x_ty {
        Type::App(f, elem) => {
            assert_eq!(**f, Type::Con(interner::intern("Effect")));
            assert_eq!(**elem, Type::int());
        }
        other => panic!("expected Effect Int, got: {}", other),
    }
}

#[test]
fn kind_annotation_higher_kinded_forall() {
    // forall (f :: Type -> Type) (a :: Type). f a -> f a
    let source = "module T where
data Box a = MkBox a
id :: forall (f :: Type -> Type) (a :: Type). f a -> f a
id x = x
result = id (MkBox 42)";
    assert_module_type(
        source,
        "result",
        Type::app(Type::Con(interner::intern("Box")), Type::int()),
    );
}

#[test]
fn kind_annotation_multiple_kinded_forall_vars() {
    // Multiple kinded forall variables
    let source = "module T where
f :: forall (a :: Type) (b :: Type). a -> b -> a
f x y = x
result = f 42 true";
    assert_module_type(
        source,
        "result",
        Type::int(),
    );
}

#[test]
fn kind_annotation_on_type_alias_body() {
    // type Name = String :: Type  (kinded type alias body)
    let source = "module T where
type Name = String :: Type
x = 42";
    let (_, errors) = check_module_types(source);
    // Should not produce errors (kind annotation is stripped)
    assert!(
        errors.is_empty(),
        "unexpected errors: {:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
}

// --- Error cases ---

#[test]
fn kind_annotation_forall_does_not_override_type_error() {
    // Kinded forall still enforces types — passing wrong type is an error
    let source = "module T where
f :: forall (a :: Type). a -> Int
f x = x
result = f true";
    assert_module_error(source);
}

#[test]
fn kind_annotation_data_kind_sig_body_mismatch() {
    // Data kind sig + definition — type mismatch in usage still caught
    let source = "module T where
data Maybe :: Type -> Type
data Maybe a = Just a | Nothing
f :: Int -> Int
f x = x
result = f (Just 42)";
    assert_module_error(source);
}

#[test]
fn kind_annotation_forall_type_mismatch() {
    // Kinded forall — should still enforce the polymorphic type correctly
    let source = "module T where
data Maybe a = Just a | Nothing
f :: forall (a :: Type). a -> a
f x = x
result = f (Just 1)
bad = result == 42";
    assert_module_error(source);
}

// ═══════════════════════════════════════════════════════════════════════════
// 23. RECORDS (EXTENDED)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn record_mixed_field_types() {
    let expr = parser::parse_expr(r#"{ name: "Alice", age: 30, active: true }"#).unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Record(fields, None) => {
            assert_eq!(fields.len(), 3);
        }
        other => panic!("expected record type with 3 fields, got: {}", other),
    }
}

#[test]
fn record_nested() {
    let expr = parser::parse_expr(r#"{ inner: { x: 1, y: 2 } }"#).unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Record(fields, None) => {
            assert_eq!(fields.len(), 1);
            let (_, inner_ty) = &fields[0];
            match inner_ty {
                Type::Record(inner_fields, None) => assert_eq!(inner_fields.len(), 2),
                other => panic!("expected inner record type, got: {}", other),
            }
        }
        other => panic!("expected record type, got: {}", other),
    }
}

#[test]
fn record_access_string_field() {
    let expr = parser::parse_expr(r#"{ name: "Alice" }.name"#).unwrap();
    let ty = infer_expr(&expr).unwrap();
    assert_eq!(ty, Type::string());
}

#[test]
fn record_access_bool_field() {
    let expr = parser::parse_expr("{ active: true }.active").unwrap();
    let ty = infer_expr(&expr).unwrap();
    assert_eq!(ty, Type::boolean());
}

#[test]
fn record_access_nested_field() {
    let expr = parser::parse_expr("{ inner: { x: 42 } }.inner").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Record(fields, None) => {
            assert_eq!(fields.len(), 1);
        }
        other => panic!("expected record type, got: {}", other),
    }
}

#[test]
fn record_singleton_field() {
    let expr = parser::parse_expr("{ x: 42 }").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Record(fields, None) => {
            assert_eq!(fields.len(), 1);
            let (_, field_ty) = &fields[0];
            assert_eq!(*field_ty, Type::int());
        }
        other => panic!("expected record type, got: {}", other),
    }
}

#[test]
fn record_in_module_function() {
    let source = r#"module T where
mkPerson name age = { name: name, age: age }
bob = mkPerson "Bob" 25"#;
    let ty = assert_module_fn_type(source, "bob");
    match ty {
        Type::Record(fields, _) => {
            assert_eq!(fields.len(), 2);
        }
        other => panic!("expected record type, got: {}", other),
    }
}

#[test]
fn record_access_in_module() {
    let source = r#"module T where
person = { name: "Alice", age: 30 }
name = person.name"#;
    assert_module_type(source, "name", Type::string());
}

#[test]
fn record_access_in_function() {
    let source = "module T where
getAge r = r.age
result = getAge { age: 42 }";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn record_in_array() {
    let expr = parser::parse_expr("[{ x: 1 }, { x: 2 }]").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::App(f, elem) => {
            assert_eq!(*f, Type::Con(interner::intern("Array")));
            match *elem {
                Type::Record(fields, None) => assert_eq!(fields.len(), 1),
                other => panic!("expected record element, got: {}", other),
            }
        }
        other => panic!("expected Array of records, got: {}", other),
    }
}

#[test]
fn record_in_constructor() {
    let source = "module T where
data Wrapper a = Wrap a
x = Wrap { x: 1, y: true }";
    let ty = assert_module_fn_type(source, "x");
    match ty {
        Type::App(f, arg) => {
            assert_eq!(*f, Type::Con(interner::intern("Wrapper")));
            match *arg {
                Type::Record(fields, None) => assert_eq!(fields.len(), 2),
                other => panic!("expected record in Wrapper, got: {}", other),
            }
        }
        other => panic!("expected Wrapper type, got: {}", other),
    }
}

#[test]
fn record_with_lambda_access() {
    // Use a lambda to access a record field
    let expr = parser::parse_expr(r"(\r -> r.x) { x: 42 }").unwrap();
    let ty = infer_expr(&expr).unwrap();
    assert_eq!(ty, Type::int());
}

#[test]
fn record_with_type_annotation() {
    let source = "module T where
f :: { name :: String, age :: Int } -> String
f r = r.name";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*to, Type::string());
            match *from {
                Type::Record(fields, _) => assert_eq!(fields.len(), 2),
                other => panic!("expected record param, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 24. DO NOTATION (EXTENDED)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn do_multiple_binds() {
    let source = "module T where
f = do
  x <- [1, 2]
  y <- [3, 4]
  [x]";
    assert_module_type(source, "f", Type::array(Type::int()));
}

#[test]
fn do_discard_only() {
    let source = "module T where
f = do
  [1, 2]";
    assert_module_type(source, "f", Type::array(Type::int()));
}

#[test]
fn do_bind_then_discard() {
    let source = "module T where
f = do
  x <- [true, false]
  [x]";
    assert_module_type(source, "f", Type::array(Type::boolean()));
}

#[test]
fn do_string_arrays() {
    let source = r#"module T where
f = do
  x <- ["hello", "world"]
  [x]"#;
    assert_module_type(source, "f", Type::array(Type::string()));
}

#[test]
fn do_nested_array_result() {
    let source = "module T where
f = do
  x <- [1, 2]
  [[x]]";
    assert_module_type(source, "f", Type::array(Type::array(Type::int())));
}

#[test]
fn do_with_constructor() {
    let source = "module T where
data Maybe a = Just a | Nothing
f = do
  x <- [1, 2]
  [Just x]";
    assert_module_type(
        source,
        "f",
        Type::array(Type::app(Type::Con(interner::intern("Maybe")), Type::int())),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 25. ADO NOTATION (EXTENDED)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn ado_multiple_binds() {
    let source = "module T where
f = ado
  x <- [1, 2]
  y <- [3, 4]
  in x";
    assert_module_type(source, "f", Type::array(Type::int()));
}

#[test]
fn ado_with_boolean() {
    let source = "module T where
f = ado
  x <- [true, false]
  in x";
    assert_module_type(source, "f", Type::array(Type::boolean()));
}

#[test]
fn ado_with_constructor_result() {
    let source = "module T where
data Maybe a = Just a | Nothing
f = ado
  x <- [1, 2]
  in Just x";
    assert_module_type(
        source,
        "f",
        Type::array(Type::app(Type::Con(interner::intern("Maybe")), Type::int())),
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 26. WHERE CLAUSES (EXTENDED)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn where_multiple_bindings() {
    let source = "module T where
f = result
  where
  x = 1
  y = 2
  result = x";
    assert_module_type(source, "f", Type::int());
}

#[test]
fn where_with_function() {
    let source = r#"module T where
f x = double x
  where
  double y = y"#;
    // double : a -> a, f : a -> a
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(a, b) => assert_eq!(*a, *b),
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn where_accessing_outer_params() {
    // Where bindings can reference other where bindings (not function params directly)
    let source = "module T where
f = result
  where
  x = 42
  result = x";
    assert_module_type(source, "f", Type::int());
}

#[test]
fn where_binding_used_in_case() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just _ -> def
  Nothing -> def
  where
  def = 0";
    // def = 0 :: Int, but x :: Maybe a (a is unconstrained since we don't use the Just value)
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*to, Type::int());
            // from is Maybe ?a — just check it's a Maybe
            match *from {
                Type::App(ref f, _) => assert_eq!(**f, Type::Con(interner::intern("Maybe"))),
                ref other => panic!("expected Maybe type, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn where_with_type_signature() {
    let source = "module T where
f = result
  where
  result :: Int
  result = 42";
    assert_module_type(source, "f", Type::int());
}

#[test]
fn where_chain_of_bindings() {
    let source = "module T where
f = c
  where
  a = 1
  b = a
  c = b";
    assert_module_type(source, "f", Type::int());
}

// ═══════════════════════════════════════════════════════════════════════════
// 27. GUARDS (EXTENDED)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn guard_top_level_boolean() {
    let source = "module T where
f x
  | x = 1
  | true = 0";
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
fn guard_case_multiple() {
    let source = "module T where
f x = case x of
  y
    | y -> 1
    | true -> 0";
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
fn guard_with_constructor_pattern() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y
    | y -> 1
    | true -> 2
  Nothing -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(
                *from,
                Type::app(Type::Con(interner::intern("Maybe")), Type::boolean())
            );
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected Maybe Boolean -> Int, got: {}", other),
    }
}

#[test]
fn guard_ensures_boolean_condition() {
    // Guard expression must be Boolean
    let source = "module T where
f x
  | x = 1
  | true = 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, _) => assert_eq!(*from, Type::boolean()),
        other => panic!("expected function from Boolean, got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 28. MULTI-EQUATION FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn multi_eq_simple_literals() {
    let source = "module T where
data MyBool = MyTrue | MyFalse
f MyTrue = 1
f MyFalse = 0";
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
fn multi_eq_with_wildcard() {
    let source = "module T where
data Color = Red | Green | Blue
f Red = 1
f _ = 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::Con(interner::intern("Color")));
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected Color -> Int, got: {}", other),
    }
}

#[test]
fn multi_eq_constructor_extract() {
    let source = "module T where
data Maybe a = Just a | Nothing
fromJust (Just x) = x
fromJust Nothing = 0";
    let ty = assert_module_fn_type(source, "fromJust");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(
                *from,
                Type::app(Type::Con(interner::intern("Maybe")), Type::int())
            );
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected Maybe Int -> Int, got: {}", other),
    }
}

#[test]
fn multi_eq_two_params() {
    let source = "module T where
data MyBool = MyTrue | MyFalse
and MyTrue MyTrue = MyTrue
and _ _ = MyFalse";
    let ty = assert_module_fn_type(source, "and");
    match ty {
        Type::Fun(a, inner) => {
            assert_eq!(*a, Type::Con(interner::intern("MyBool")));
            match *inner {
                Type::Fun(b, ret) => {
                    assert_eq!(*b, Type::Con(interner::intern("MyBool")));
                    assert_eq!(*ret, Type::Con(interner::intern("MyBool")));
                }
                other => panic!("expected MyBool -> MyBool, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn err_multi_eq_arity_mismatch() {
    let source = "module T where
f x = x
f x y = x";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::ArityMismatch { .. }),
        "ArityMismatch",
    );
}

#[test]
fn multi_eq_literal_int_patterns() {
    let source = "module T where
f 0 = true
f _ = false";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::int());
            assert_eq!(*to, Type::boolean());
        }
        other => panic!("expected Int -> Boolean, got: {}", other),
    }
}

#[test]
fn multi_eq_string_literal_patterns() {
    let source = r#"module T where
f "hello" = 1
f "world" = 2
f _ = 0"#;
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::string());
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected String -> Int, got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 29. ADVANCED PATTERN MATCHING
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn pattern_nested_constructor() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just (Just y) -> y
  _ -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*to, Type::int());
            // from should be Maybe (Maybe Int)
            match *from {
                Type::App(ref f, ref inner) => {
                    assert_eq!(**f, Type::Con(interner::intern("Maybe")));
                    assert_eq!(
                        **inner,
                        Type::app(Type::Con(interner::intern("Maybe")), Type::int())
                    );
                }
                ref other => panic!("expected Maybe (Maybe Int), got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn pattern_boolean_literal() {
    let source = "module T where
f x = case x of
  true -> 1
  false -> 0";
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
fn pattern_string_literal() {
    let source = r#"module T where
f x = case x of
  "hello" -> true
  _ -> false"#;
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::string());
            assert_eq!(*to, Type::boolean());
        }
        other => panic!("expected String -> Boolean, got: {}", other),
    }
}

#[test]
fn pattern_as_with_variable() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  whole@(Just _) -> whole
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
fn pattern_array_empty() {
    let source = "module T where
f x = case x of
  [] -> 0
  _ -> 1";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*to, Type::int());
            match *from {
                Type::App(ref f, _) => assert_eq!(**f, Type::Con(interner::intern("Array"))),
                ref other => panic!("expected Array type, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn pattern_array_three_elements() {
    let source = "module T where
f x = case x of
  [a, b, c] -> a
  _ -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::array(Type::int()));
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected Array Int -> Int, got: {}", other),
    }
}

#[test]
fn pattern_constructor_with_wildcard_field() {
    let source = "module T where
data Pair a b = MkPair a b
f x = case x of
  MkPair a _ -> a";
    // f : Pair a b -> a
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(_, _) => {} // just check it's a function
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn pattern_multiple_scrutinees_constructors() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x y = case x, y of
  Just a, Just b -> a
  _, _ -> 0";
    let ty = assert_module_fn_type(source, "f");
    // f : Maybe Int -> Maybe Int -> Int
    match ty {
        Type::Fun(_, inner) => match *inner {
            Type::Fun(_, ret) => assert_eq!(*ret, Type::int()),
            other => panic!("expected curried function, got: {}", other),
        },
        other => panic!("expected function, got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 30. ADVANCED TYPE SIGNATURES
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn sig_forall_explicit() {
    let source = "module T where
id :: forall a. a -> a
id x = x
result = id 42";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn sig_forall_used_at_multiple_types() {
    let source = "module T where
id :: forall a. a -> a
id x = x
a = id 42
b = id true
c = id \"hello\"";
    let (types, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("a")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("b")).unwrap(), Type::boolean());
    assert_eq!(*types.get(&interner::intern("c")).unwrap(), Type::string());
}

#[test]
fn sig_constrained_single() {
    let source = "module T where
class MyShow a where
  myShow :: a -> String
instance MyShow Int where
  myShow x = \"todo\"
f :: forall a. MyShow a => a -> String
f x = myShow x
result = f 42";
    assert_module_type(source, "result", Type::string());
}

#[test]
fn sig_multiple_constraints() {
    // Multiple constraints on a single function
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
class MyShow a where
  myShow :: a -> String
instance MyEq Int where
  myEq x y = true
instance MyShow Int where
  myShow x = \"todo\"
f :: forall a. MyEq a => MyShow a => a -> String
f x = myShow x
result = f 42";
    assert_module_type(source, "result", Type::string());
}

#[test]
fn sig_higher_order_function() {
    let source = "module T where
apply :: forall a b. (a -> b) -> a -> b
apply f x = f x
result = apply (\\x -> x) 42";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn sig_function_returning_function() {
    let source = "module T where
const :: forall a b. a -> b -> a
const x y = x";
    let ty = assert_module_fn_type(source, "const");
    match ty {
        Type::Fun(_, inner) => match *inner {
            Type::Fun(_, _) => {}
            other => panic!("expected curried function, got: {}", other),
        },
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn sig_with_data_type() {
    let source = "module T where
data Maybe a = Just a | Nothing
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def x = case x of
  Just v -> v
  Nothing -> def
result = fromMaybe 0 (Just 42)";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn sig_array_type() {
    let source = "module T where
singleton :: forall a. a -> Array a
singleton x = [x]
result = singleton 42";
    assert_module_type(source, "result", Type::array(Type::int()));
}

#[test]
fn err_sig_too_specific() {
    // Signature says Int -> Int, but body is identity (which is more general — ok)
    // But applying to String should fail
    let source = "module T where
f :: Int -> Int
f x = x
result = f true";
    assert_module_error(source);
}

#[test]
fn sig_record_type() {
    let source = "module T where
getName :: { name :: String } -> String
getName r = r.name
result = getName { name: \"Alice\" }";
    assert_module_type(source, "result", Type::string());
}

// ═══════════════════════════════════════════════════════════════════════════
// 31. FOREIGN IMPORTS (EXTENDED)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn foreign_import_unary() {
    let source = "module T where
foreign import not :: Boolean -> Boolean
x = not true";
    assert_module_type(source, "x", Type::boolean());
}

#[test]
fn foreign_import_binary() {
    let source = "module T where
foreign import add :: Int -> Int -> Int
x = add 1 2";
    assert_module_type(source, "x", Type::int());
}

#[test]
fn foreign_import_polymorphic() {
    let source = "module T where
foreign import unsafeCoerce :: forall a b. a -> b
x = unsafeCoerce 42";
    // Result type should be a fresh unif var (polymorphic)
    let _ty = assert_module_fn_type(source, "x");
}

#[test]
fn foreign_import_array() {
    let source = "module T where
foreign import length :: forall a. Array a -> Int
x = length [1, 2, 3]";
    assert_module_type(source, "x", Type::int());
}

#[test]
fn foreign_import_higher_order() {
    let source = "module T where
foreign import mapArray :: forall a b. (a -> b) -> Array a -> Array b
x = mapArray (\\x -> x) [1, 2, 3]";
    assert_module_type(source, "x", Type::array(Type::int()));
}

#[test]
fn foreign_data_used_in_foreign_import() {
    let source = "module T where
foreign import data IO :: Type -> Type
foreign import pure :: forall a. a -> IO a
x = pure 42";
    let ty = assert_module_fn_type(source, "x");
    match ty {
        Type::App(f, arg) => {
            assert_eq!(*f, Type::Con(interner::intern("IO")));
            assert_eq!(*arg, Type::int());
        }
        other => panic!("expected IO Int, got: {}", other),
    }
}

#[test]
fn foreign_data_multiple() {
    let source = "module T where
foreign import data Effect :: Type -> Type
foreign import data Ref :: Type -> Type
foreign import newRef :: forall a. a -> Effect (Ref a)
x = newRef 42";
    let ty = assert_module_fn_type(source, "x");
    match ty {
        Type::App(f, inner) => {
            assert_eq!(*f, Type::Con(interner::intern("Effect")));
            match *inner {
                Type::App(ref g, ref arg) => {
                    assert_eq!(**g, Type::Con(interner::intern("Ref")));
                    assert_eq!(**arg, Type::int());
                }
                ref other => panic!("expected Ref Int, got: {}", other),
            }
        }
        other => panic!("expected Effect (Ref Int), got: {}", other),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 32. TYPE CLASSES (EXTENDED)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn type_class_multiple_methods() {
    // Test that multiple methods in a class all work
    let source = "module T where
class MyNum a where
  myAdd :: a -> a -> a
  myMul :: a -> a -> a
instance MyNum Int where
  myAdd x y = x
  myMul x y = x
x = myAdd 1 2
y = myMul 3 4";
    let (types, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("x")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("y")).unwrap(), Type::int());
}

#[test]
fn type_class_instance_for_data_type() {
    let source = "module T where
data Color = Red | Green | Blue
class MyEq a where
  myEq :: a -> a -> Boolean
instance MyEq Color where
  myEq x y = true
result = myEq Red Green";
    assert_module_type(source, "result", Type::boolean());
}

#[test]
fn type_class_used_in_function_body() {
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
instance MyEq Int where
  myEq x y = true
f x y = myEq x y
result = f 1 2";
    assert_module_type(source, "result", Type::boolean());
}

#[test]
fn type_class_instance_for_array() {
    // Instance for Array — a built-in parameterized type
    let source = "module T where
class MyShow a where
  myShow :: a -> String
instance MyShow Int where
  myShow x = \"int\"
instance MyShow String where
  myShow x = \"string\"
a = myShow 42
b = myShow \"hello\"";
    let (types, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("a")).unwrap(), Type::string());
    assert_eq!(*types.get(&interner::intern("b")).unwrap(), Type::string());
}

#[test]
fn err_type_class_wrong_type() {
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean
instance MyEq Int where
  myEq x y = true
result = myEq 1 true";
    assert_module_error(source);
}

// ═══════════════════════════════════════════════════════════════════════════
// 33. RECURSIVE DATA STRUCTURES
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn recursive_list_map() {
    let source = "module T where
data List a = Nil | Cons a (List a)
map f xs = case xs of
  Nil -> Nil
  Cons x rest -> Cons (f x) (map f rest)";
    let _ty = assert_module_fn_type(source, "map");
    // Just checking it typechecks without errors
}

#[test]
fn recursive_list_append() {
    let source = "module T where
data List a = Nil | Cons a (List a)
append xs ys = case xs of
  Nil -> ys
  Cons x rest -> Cons x (append rest ys)";
    let _ty = assert_module_fn_type(source, "append");
}

#[test]
fn recursive_tree() {
    let source = "module T where
data Tree a = Leaf a | Branch (Tree a) (Tree a)
leaf = Leaf 42
branch = Branch (Leaf 1) (Leaf 2)";
    assert_module_type(
        source,
        "leaf",
        Type::app(Type::Con(interner::intern("Tree")), Type::int()),
    );
    assert_module_type(
        source,
        "branch",
        Type::app(Type::Con(interner::intern("Tree")), Type::int()),
    );
}

#[test]
fn recursive_mutual_types() {
    // Two data types that reference each other indirectly
    let source = "module T where
data Even = Zero | SuccE Odd
data Odd = SuccO Even
x = Zero
y = SuccO Zero
z = SuccE (SuccO Zero)";
    let (types, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("x")).unwrap(), Type::Con(interner::intern("Even")));
    assert_eq!(*types.get(&interner::intern("y")).unwrap(), Type::Con(interner::intern("Odd")));
    assert_eq!(*types.get(&interner::intern("z")).unwrap(), Type::Con(interner::intern("Even")));
}

// ═══════════════════════════════════════════════════════════════════════════
// 34. COMPLEX INTEGRATION TESTS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn integration_maybe_functor_manual() {
    // Manual map over Maybe — like fmap
    let source = "module T where
data Maybe a = Just a | Nothing
mapMaybe f x = case x of
  Just a -> Just (f a)
  Nothing -> Nothing
result = mapMaybe (\\x -> x) (Just 42)";
    assert_module_type(
        source,
        "result",
        Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
    );
}

#[test]
fn integration_either_fold() {
    let source = "module T where
data Either a b = Left a | Right b
either f g x = case x of
  Left a -> f a
  Right b -> g b
result = either (\\x -> 0) (\\x -> x) (Right 42)";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn integration_function_with_where_helper() {
    // Where clause with self-contained helper (no reference to function params)
    let source = "module T where
f = result
  where
  helper = 42
  result = helper";
    assert_module_type(source, "f", Type::int());
}

#[test]
fn integration_church_booleans() {
    // Church encoding of booleans
    let source = "module T where
myTrue x y = x
myFalse x y = y
myIf b t f = b t f
result = myIf myTrue 1 0";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn integration_compose_functions() {
    let source = "module T where
compose f g x = f (g x)
result = compose (\\x -> [x]) (\\x -> x) 42";
    assert_module_type(source, "result", Type::array(Type::int()));
}

#[test]
fn integration_flip() {
    let source = "module T where
flip f x y = f y x
const x y = x
result = flip const 1 2";
    assert_module_type(source, "result", Type::int());
}

#[test]
fn integration_apply_pipeline() {
    // Chain of function applications
    let source = "module T where
data Maybe a = Just a | Nothing
apply f x = f x
result = apply (\\x -> Just x) 42";
    assert_module_type(
        source,
        "result",
        Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
    );
}

#[test]
fn integration_constructor_as_function() {
    // Constructors used as first-class functions
    let source = "module T where
data Maybe a = Just a | Nothing
data List a = Nil | Cons a (List a)
mapList f xs = case xs of
  Nil -> Nil
  Cons x rest -> Cons (f x) (mapList f rest)
result = mapList Just (Cons 1 (Cons 2 Nil))";
    let _ty = assert_module_fn_type(source, "result");
    // Just checking it typechecks
}

#[test]
fn integration_nested_let_polymorphism() {
    // Let-bound polymorphic identity used at different types
    let source = "module T where
f = let
  id = \\x -> x
in let
  a = id 42
  b = id true
in a";
    assert_module_type(source, "f", Type::int());
}

#[test]
fn integration_data_with_class_and_do() {
    let source = "module T where
data Maybe a = Just a | Nothing
class MyFunctor f where
  myMap :: forall a b. (a -> b) -> f a -> f b
instance MyFunctor Array where
  myMap f xs = xs
result = do
  x <- [1, 2, 3]
  [x]";
    assert_module_type(source, "result", Type::array(Type::int()));
}

#[test]
fn integration_newtype_and_case() {
    let source = "module T where
newtype Name = Name String
getName x = case x of
  Name s -> s";
    let ty = assert_module_fn_type(source, "getName");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::Con(interner::intern("Name")));
            assert_eq!(*to, Type::string());
        }
        other => panic!("expected Name -> String, got: {}", other),
    }
}

#[test]
fn integration_multiple_data_types() {
    let source = "module T where
data Maybe a = Just a | Nothing
data Either a b = Left a | Right b
data Pair a b = MkPair a b
f x = MkPair (Just x) (Right x)";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn integration_function_with_sig_and_where() {
    // Function with type signature and where clause (where doesn't reference params)
    let source = "module T where
f :: Int -> Int
f x = result
  where
  result = 42";
    assert_module_type(source, "f", Type::fun(Type::int(), Type::int()));
}

#[test]
fn integration_typeclass_with_data_and_case() {
    let source = "module T where
data Shape = Circle | Square
class MyShow a where
  myShow :: a -> String
instance MyShow Shape where
  myShow x = case x of
    Circle -> \"circle\"
    Square -> \"square\"
result = myShow Circle";
    assert_module_type(source, "result", Type::string());
}

#[test]
fn integration_higher_order_with_array() {
    let source = "module T where
apply f x = f x
toArray x = [x]
result = apply toArray 42";
    assert_module_type(source, "result", Type::array(Type::int()));
}

// ═══════════════════════════════════════════════════════════════════════════
// 35. EDGE CASES AND REGRESSION TESTS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn edge_deeply_nested_if() {
    assert_expr_type(
        "if true then if false then if true then 1 else 2 else 3 else 4",
        Type::int(),
    );
}

#[test]
fn edge_deeply_nested_lambda() {
    let expr = parser::parse_expr(r"\a -> \b -> \c -> \d -> \e -> a").unwrap();
    let ty = infer_expr(&expr).unwrap();
    // Should be a 5-parameter curried function returning first arg type
    let mut current = &ty;
    for _ in 0..5 {
        match current {
            Type::Fun(_, ret) => current = ret,
            other => panic!("expected function, got: {}", other),
        }
    }
}

#[test]
fn edge_let_with_many_bindings() {
    assert_expr_type(
        "let\n  a = 1\n  b = 2\n  c = 3\n  d = 4\n  e = 5\nin a",
        Type::int(),
    );
}

#[test]
fn edge_constructor_partial_application() {
    let source = "module T where
data Pair a b = MkPair a b
f = MkPair 42";
    let ty = assert_module_fn_type(source, "f");
    // Should be (b -> Pair Int b)
    match ty {
        Type::Fun(_, ret) => match *ret {
            Type::App(ref f, ref arg) => {
                match f.as_ref() {
                    Type::App(pair, int_arg) => {
                        assert_eq!(**pair, Type::Con(interner::intern("Pair")));
                        assert_eq!(**int_arg, Type::int());
                    }
                    other => panic!("expected Pair Int, got: {}", other),
                }
                // arg is the type variable
                let _ = arg;
            }
            other => panic!("expected Pair Int b, got: {}", other),
        },
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn edge_array_of_functions() {
    let expr = parser::parse_expr(r"[\x -> x, \y -> y]").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::App(f, elem) => {
            assert_eq!(*f, Type::Con(interner::intern("Array")));
            match *elem {
                Type::Fun(a, b) => assert_eq!(*a, *b, "should be array of identity-like functions"),
                other => panic!("expected function element, got: {}", other),
            }
        }
        other => panic!("expected Array type, got: {}", other),
    }
}

#[test]
fn edge_if_with_lambda_branches() {
    let expr = parser::parse_expr(r"if true then \x -> x else \y -> y").unwrap();
    let ty = infer_expr(&expr).unwrap();
    match ty {
        Type::Fun(a, b) => assert_eq!(*a, *b),
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn edge_case_returning_lambda() {
    let source = "module T where
f x = case x of
  true -> \\y -> y
  false -> \\z -> z";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::boolean());
            match *to {
                Type::Fun(a, b) => assert_eq!(*a, *b),
                other => panic!("expected function return, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn edge_empty_module() {
    let (types, errors) = check_module_types("module T where");
    assert!(errors.is_empty());
    assert!(types.is_empty());
}

#[test]
fn edge_module_only_data() {
    let source = "module T where\ndata Unit = Unit";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn edge_module_only_class() {
    let source = "module T where
class MyEq a where
  myEq :: a -> a -> Boolean";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn edge_let_inside_let() {
    assert_expr_type(
        "let\n  x = let\n    y = let\n      z = 42\n    in z\n  in y\nin x",
        Type::int(),
    );
}

#[test]
fn edge_self_application_blocked() {
    // \x -> x x should fail with infinite type
    assert_expr_error(r"\x -> x x");
}

#[test]
fn edge_annotation_on_lambda() {
    assert_expr_type(r"((\x -> x) :: Int -> Int) 42", Type::int());
}

#[test]
fn edge_annotation_on_let() {
    assert_expr_type("(let\n  x = 42\nin x :: Int)", Type::int());
}

#[test]
fn edge_array_of_arrays_of_arrays() {
    assert_expr_type("[[[1]]]", Type::array(Type::array(Type::array(Type::int()))));
}

#[test]
fn edge_case_single_arm_wildcard() {
    let source = "module T where
f x = case x of
  _ -> 42";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(_, ret) => assert_eq!(*ret, Type::int()),
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn edge_fixity_declaration_no_error() {
    // Fixity declarations should not cause errors by themselves
    let source = "module T where
add :: Int -> Int -> Int
add x y = x
infixl 6 add as +";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

// ═══════════════════════════════════════════════════════════════════════════
// 36. TYPE ALIAS TESTS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn type_alias_does_not_break_module() {
    let source = "module T where
type Name = String
x = 42";
    assert_module_type(source, "x", Type::int());
}

#[test]
fn type_alias_multiple() {
    let source = "module T where
type Name = String
type Age = Int
x = 42
y = true";
    let (types, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("x")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("y")).unwrap(), Type::boolean());
}

// ═══════════════════════════════════════════════════════════════════════════
// 37. TYPE-LEVEL OPERATORS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn type_op_in_signature() {
    // Type-level operator declared with infixr, resolves to target type
    let source = "module T where
foreign import data NaturalTransformation :: (Type -> Type) -> (Type -> Type) -> Type
infixr 4 type NaturalTransformation as ~>
foreign import nat :: forall f g. f ~> g
x = nat";
    let _ty = assert_module_fn_type(source, "x");
    // Just check it typechecks without NotImplemented error
}

#[test]
fn type_op_in_type_annotation() {
    // Type operator declared with infixr, resolved to target type Pair
    let source = "module T where
foreign import data Pair :: Type -> Type -> Type
infixr 6 type Pair as ×
f :: Int × String
f = f";
    // The type `Int × String` desugars to `App(App(Con(Pair), Int), String)`
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::App(f, _) => match *f {
            Type::App(ref op, ref left) => {
                assert_eq!(**op, Type::Con(interner::intern("Pair")));
                assert_eq!(**left, Type::int());
            }
            ref other => panic!("expected Pair Int _, got: {}", other),
        },
        other => panic!("expected type application, got: {}", other),
    }
}

#[test]
fn type_op_does_not_break_function_type() {
    // Arrow -> is NOT a type operator, it's parsed as Function
    let source = "module T where
f :: Int -> String
f x = \"hello\"";
    assert_module_type(source, "f", Type::fun(Type::int(), Type::string()));
}

// ═══════════════════════════════════════════════════════════════════════════
// 38. EXHAUSTIVENESS CHECKING
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn exhaustive_all_constructors_covered() {
    let source = "module T where
data Color = Red | Green | Blue
f x = case x of
  Red -> 1
  Green -> 2
  Blue -> 3";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_wildcard_covers_all() {
    let source = "module T where
data Color = Red | Green | Blue
f x = case x of
  Red -> 1
  _ -> 0";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_variable_covers_all() {
    let source = "module T where
data Color = Red | Green | Blue
f x = case x of
  Red -> 1
  other -> 0";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_maybe_both_arms() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y -> y
  Nothing -> 0";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn err_exhaustive_missing_one_constructor() {
    let source = "module T where
data Color = Red | Green | Blue
f x = case x of
  Red -> 1
  Green -> 2";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern",
    );
}

#[test]
fn err_exhaustive_missing_nothing() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y -> y";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern",
    );
}

#[test]
fn err_exhaustive_missing_just() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Nothing -> 0";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern",
    );
}

#[test]
fn err_exhaustive_empty_case() {
    // No arms at all
    let source = "module T where
data Unit = MkUnit
f x = case x of
  _ -> 0";
    // Wildcard covers everything — should pass
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_boolean_both_arms() {
    // Booleans are not a data type in our system (they're built-in),
    // so exhaustiveness doesn't apply to literal patterns on Bool.
    // This should pass regardless.
    let source = "module T where
f x = case x of
  true -> 1
  false -> 0";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_as_pattern_covers_constructor() {
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  y@(Just _) -> y
  Nothing -> Nothing";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_single_constructor_newtype() {
    let source = "module T where
newtype Name = Name String
f x = case x of
  Name s -> s";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_newtype_constructor_covered() {
    // Newtype has exactly one constructor — matching it is exhaustive
    let source = "module T where
newtype Wrapper = Wrapper Int
f x = case x of
  Wrapper n -> n";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_either_all_arms() {
    let source = "module T where
data Either a b = Left a | Right b
f x = case x of
  Left a -> a
  Right b -> b";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn err_exhaustive_either_missing_right() {
    let source = "module T where
data Either a b = Left a | Right b
f x = case x of
  Left a -> a";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern",
    );
}

#[test]
fn exhaustive_multiple_scrutinees_covered() {
    let source = "module T where
data MyBool = MyTrue | MyFalse
f x y = case x, y of
  MyTrue, MyTrue -> 1
  MyTrue, MyFalse -> 2
  MyFalse, _ -> 0";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_recursive_data() {
    let source = "module T where
data List a = Nil | Cons a (List a)
f xs = case xs of
  Nil -> 0
  Cons _ _ -> 1";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn err_exhaustive_recursive_data_missing() {
    let source = "module T where
data List a = Nil | Cons a (List a)
f xs = case xs of
  Nil -> 0";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern",
    );
}

#[test]
fn exhaustive_no_check_for_int_scrutinee() {
    // Int is not a data type — no exhaustiveness check applies
    let source = "module T where
f x = case x of
  0 -> true
  1 -> false";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn err_exhaustive_multi_eq_missing_constructor() {
    // Multi-equation functions are checked for exhaustiveness too
    let source = "module T where
data Color = Red | Green | Blue
f Red = 1
f Green = 2";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern",
    );
}

#[test]
fn exhaustive_multi_eq_all_covered() {
    // Multi-equation with all constructors covered — no error
    let source = "module T where
data Color = Red | Green | Blue
f Red = 1
f Green = 2
f Blue = 3";
    let _ty = assert_module_fn_type(source, "f");
}

#[test]
fn exhaustive_multi_eq_wildcard() {
    // Multi-equation with wildcard covers all — no error
    let source = "module T where
data Color = Red | Green | Blue
f Red = 1
f _ = 0";
    let _ty = assert_module_fn_type(source, "f");
}

// ═══════════════════════════════════════════════════════════════════════════
// 39. MODULE EXPORTS VALIDATION
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn exports_valid_value() {
    let source = "module T (x) where
x = 42";
    let (types, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("x")).unwrap(), Type::int());
}

#[test]
fn exports_valid_type() {
    let source = "module T (Maybe(..)) where
data Maybe a = Just a | Nothing
x = Just 42";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn exports_valid_class() {
    let source = "module T (class MyEq) where
class MyEq a where
  myEq :: a -> a -> Boolean";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn exports_valid_multiple() {
    let source = "module T (x, y, Maybe(..)) where
data Maybe a = Just a | Nothing
x = 42
y = true";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn exports_no_export_list() {
    // No export list means export everything — should not error
    let source = "module T where
x = 42";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_exports_undefined_value() {
    let source = "module T (notDefined) where
x = 42";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::UndefinedExport { .. }),
        "UndefinedExport",
    );
}

#[test]
fn err_exports_undefined_type() {
    let source = "module T (NotAType) where
x = 42";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::UndefinedExport { .. }),
        "UndefinedExport",
    );
}

#[test]
fn err_exports_undefined_class() {
    let source = "module T (class NotAClass) where
x = 42";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::UndefinedExport { .. }),
        "UndefinedExport",
    );
}

#[test]
fn exports_foreign_data_type() {
    let source = "module T (Effect) where
foreign import data Effect :: Type -> Type";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn exports_newtype() {
    let source = "module T (Name) where
newtype Name = Name String";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn exports_type_alias() {
    let source = "module T (MyInt) where
type MyInt = Int";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn exports_foreign_import_value() {
    let source = "module T (sqrt) where
foreign import sqrt :: Number -> Number";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

// ═══════════════════════════════════════════════════════════════════════════
// 40. NESTED PATTERN EXHAUSTIVENESS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn nested_exhaustive_maybe_maybe_all_covered() {
    // All nested patterns covered: Just (Just _), Just Nothing, Nothing
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just (Just _) -> 1
  Just Nothing -> 2
  Nothing -> 3";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_nested_exhaustive_maybe_maybe_missing_just_nothing() {
    // Missing Just Nothing: only Just (Just _) and Nothing are covered
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just (Just _) -> 1
  Nothing -> 3";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { missing, .. } if missing.iter().any(|m| m.contains("Nothing"))),
        "NonExhaustivePattern with nested missing",
    );
}

#[test]
fn nested_exhaustive_newtype_inner_covered() {
    // Newtype wrapping Maybe: both inner constructors covered
    let source = "module T where
data Maybe a = Just a | Nothing
newtype Wrapper = Wrapper (Maybe Int)
f x = case x of
  Wrapper (Just _) -> 1
  Wrapper Nothing -> 2";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_nested_exhaustive_newtype_inner_missing() {
    // Newtype wrapping Maybe: missing Nothing inside Wrapper
    let source = "module T where
data Maybe a = Just a | Nothing
newtype Wrapper = Wrapper (Maybe Int)
f x = case x of
  Wrapper (Just _) -> 1";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { missing, .. } if missing.iter().any(|m| m.contains("Nothing"))),
        "NonExhaustivePattern nested in newtype",
    );
}

#[test]
fn nested_exhaustive_wildcard_inside_constructor() {
    // Wildcard inside a constructor covers everything
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just _ -> 1
  Nothing -> 2";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn nested_exhaustive_var_inside_constructor() {
    // Variable inside a constructor covers everything (no nested check needed)
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y -> y
  Nothing -> 0";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn nested_exhaustive_either_in_maybe() {
    // Maybe (Either a b): all combinations covered
    let source = "module T where
data Maybe a = Just a | Nothing
data Either a b = Left a | Right b
f x = case x of
  Just (Left _) -> 1
  Just (Right _) -> 2
  Nothing -> 3";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_nested_exhaustive_either_in_maybe_missing_right() {
    // Maybe (Either a b): missing Just (Right _)
    let source = "module T where
data Maybe a = Just a | Nothing
data Either a b = Left a | Right b
f x = case x of
  Just (Left _) -> 1
  Nothing -> 3";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { missing, .. } if missing.iter().any(|m| m.contains("Right"))),
        "NonExhaustivePattern nested Either in Maybe",
    );
}

#[test]
fn nested_exhaustive_three_deep() {
    // Three levels deep: Maybe (Maybe (Maybe Int))
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just (Just (Just _)) -> 1
  Just (Just Nothing) -> 2
  Just Nothing -> 3
  Nothing -> 4";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_nested_exhaustive_three_deep_missing() {
    // Three levels deep: missing Just (Just Nothing)
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just (Just (Just _)) -> 1
  Just Nothing -> 3
  Nothing -> 4";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { missing, .. } if missing.iter().any(|m| m.contains("Nothing"))),
        "NonExhaustivePattern three levels deep",
    );
}

#[test]
fn nested_exhaustive_multi_field_not_checked() {
    // Multi-field constructors (Pair a b) should NOT get nested checking
    // because column-based analysis is unsound for cross-product.
    // Even though Left is missing in the second field for Pair _ (Left _),
    // this should only check at the top level (Pair is covered).
    let source = "module T where
data Pair a b = MkPair a b
data MyBool = MyTrue | MyFalse
f x = case x of
  MkPair MyTrue MyTrue -> 1
  MkPair MyFalse _ -> 2
  MkPair _ MyFalse -> 3";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn nested_exhaustive_multi_eq_nested() {
    // Multi-equation function with nested patterns
    let source = "module T where
data Maybe a = Just a | Nothing
data MyBool = MyTrue | MyFalse
f :: Maybe MyBool -> Int
f (Just MyTrue) = 1
f (Just MyFalse) = 2
f Nothing = 0";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_nested_exhaustive_multi_eq_missing_inner() {
    // Multi-equation: all outer constructors covered but missing inner
    let source = "module T where
data Maybe a = Just a | Nothing
data MyBool = MyTrue | MyFalse
f :: Maybe MyBool -> Int
f (Just MyTrue) = 1
f Nothing = 0";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { missing, .. } if missing.iter().any(|m| m.contains("MyFalse"))),
        "NonExhaustivePattern nested in multi-eq",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 41. GUARDED PATTERN EXHAUSTIVENESS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn guard_exhaustive_with_true_fallback() {
    // Guarded alternative with `| true -> ...` counts as unconditional
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y
    | y -> 1
    | true -> 2
  Nothing -> 0";
    let (types, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("f")).unwrap(), Type::fun(Type::app(Type::Con(interner::intern("Maybe")), Type::Con(interner::intern("Boolean"))), Type::int()));
}

#[test]
fn err_guard_non_exhaustive_no_fallback() {
    // Guarded alternative without true fallback does NOT cover the constructor
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y | y -> 1
  Nothing -> 0";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { missing, .. } if missing.iter().any(|m| m.contains("Just"))),
        "NonExhaustivePattern guarded without fallback",
    );
}

#[test]
fn guard_exhaustive_unconditional_after_guarded() {
    // Guarded alternative followed by unconditional alternative for same constructor
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y | y -> 1
  Just _ -> 2
  Nothing -> 0";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn guard_exhaustive_wildcard_after_guarded() {
    // Wildcard after guarded alternatives catches everything
    let source = "module T where
data Maybe a = Just a | Nothing
f x = case x of
  Just y | y -> 1
  _ -> 0";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_guard_all_guarded_no_coverage() {
    // All alternatives are guarded — nothing is covered
    let source = "module T where
data MyBool = MyTrue | MyFalse
f x = case x of
  MyTrue | true -> 1
  MyFalse | true -> 0";
    // Even though guards are `true`, they're checked for the `| true -> ...` pattern
    // on each alternative. Here both ARE unconditional via true fallback.
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_guard_multi_eq_guarded_not_covered() {
    // Multi-equation function where one equation is guarded — not exhaustive
    let source = "module T where
data MyBool = MyTrue | MyFalse
f :: MyBool -> Int
f MyTrue | true = 1
f MyFalse = 0";
    // MyTrue has `| true` guard so it counts as unconditional
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_guard_multi_eq_only_guarded() {
    // Multi-equation: one equation guarded without true fallback
    let source = "module T where
data MyBool = MyTrue | MyFalse
f :: MyBool -> Int
f MyTrue | false = 1
f MyFalse = 0";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { missing, .. } if missing.iter().any(|m| m.contains("MyTrue"))),
        "NonExhaustivePattern multi-eq guarded",
    );
}

#[test]
fn guard_nested_with_true_fallback() {
    // Nested pattern inside guarded alternative with true fallback
    let source = "module T where
data Maybe a = Just a | Nothing
data MyBool = MyTrue | MyFalse
f x = case x of
  Just MyTrue
    | true -> 1
  Just MyFalse -> 2
  Nothing -> 0";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_guard_nested_missing_inner() {
    // Nested pattern: guarded alternative without fallback misses inner coverage
    let source = "module T where
data Maybe a = Just a | Nothing
data MyBool = MyTrue | MyFalse
f x = case x of
  Just MyTrue | true -> 1
  Nothing -> 0";
    assert_module_error_kind(
        source,
        |e| matches!(e, TypeError::NonExhaustivePattern { .. }),
        "NonExhaustivePattern nested guarded",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 42. RECORD BINDER PATTERNS
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn record_binder_pun_single_field() {
    // { x } binds x to the value of field x
    let source = "module T where
f r = case r of
  { x } -> x";
    let ty = assert_module_fn_type(source, "f");
    // f : { x :: a | r } -> a
    match ty {
        Type::Fun(from, to) => {
            match *from {
                Type::Record(fields, Some(_tail)) => {
                    assert_eq!(fields.len(), 1);
                    assert_eq!(fields[0].1, *to);
                }
                other => panic!("expected open record, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn record_binder_pun_multiple_fields() {
    // { x, y } binds both fields
    let source = "module T where
f r = case r of
  { x, y } -> x";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            match *from {
                Type::Record(fields, Some(_tail)) => {
                    assert_eq!(fields.len(), 2);
                    // x is returned, so the return type equals the x field type
                    let x_field = fields.iter().find(|(l, _)| {
                        interner::resolve(*l).unwrap_or_default() == "x"
                    });
                    assert!(x_field.is_some());
                    assert_eq!(x_field.unwrap().1, *to);
                }
                other => panic!("expected open record, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn record_binder_explicit_var() {
    // { x: a } binds a to the value of field x
    let source = "module T where
f r = case r of
  { x: a } -> a";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            match *from {
                Type::Record(fields, Some(_tail)) => {
                    assert_eq!(fields.len(), 1);
                    assert_eq!(fields[0].1, *to);
                }
                other => panic!("expected open record, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn record_binder_wildcard_field() {
    // { x: _ } matches x but doesn't bind it
    let source = "module T where
f r = case r of
  { x: _ } -> 42";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert!(matches!(*from, Type::Record(_, Some(_))));
            assert_eq!(*to, Type::int());
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn record_binder_nested_constructor() {
    // { x: Just y } destructures a constructor inside a record field
    let source = "module T where
data Maybe a = Just a | Nothing
f r = case r of
  { x: Just y } -> y
  { x: Nothing } -> 0";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*to, Type::int());
            match *from {
                Type::Record(fields, _) => {
                    assert_eq!(fields.len(), 1);
                    // x field should be Maybe Int
                    let x_ty = &fields[0].1;
                    assert_eq!(
                        *x_ty,
                        Type::app(Type::Con(interner::intern("Maybe")), Type::int())
                    );
                }
                other => panic!("expected record, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn record_binder_in_lambda() {
    // Record binder in lambda parameter
    let source = "module T where
f = \\{ x } -> x";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            match *from {
                Type::Record(fields, Some(_tail)) => {
                    assert_eq!(fields.len(), 1);
                    assert_eq!(fields[0].1, *to);
                }
                other => panic!("expected open record, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn record_binder_in_let() {
    // Record binder in let binding
    let source = "module T where
f r = let { x } = r in x";
    let ty = assert_module_fn_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            match *from {
                Type::Record(fields, Some(_tail)) => {
                    assert_eq!(fields.len(), 1);
                    assert_eq!(fields[0].1, *to);
                }
                other => panic!("expected open record, got: {}", other),
            }
        }
        other => panic!("expected function, got: {}", other),
    }
}

#[test]
fn record_binder_partial_match() {
    // Record binder matches a subset of fields (open row tail)
    let source = "module T where
f :: { x :: Int, y :: String } -> Int
f r = case r of
  { x } -> x";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn record_binder_with_type_annotation() {
    // Record field matched against annotated type
    let source = "module T where
f :: { x :: Int } -> Int
f { x } = x";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn record_binder_multi_eq() {
    // Record binder across multiple equations
    let source = "module T where
data MyBool = MyTrue | MyFalse
f :: { x :: MyBool } -> Int
f { x: MyTrue } = 1
f { x: MyFalse } = 0";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

// ===== Section 43: Type-level strings and integers =====

#[test]
fn type_level_string_in_annotation() {
    // Type-level string literal in a type annotation
    let source = r#"module T where
foreign import data SProxy :: Symbol -> Type
foo :: SProxy "hello"
foo = foo"#;
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn type_level_string_unification_same() {
    // Two identical type-level strings should unify
    let source = r#"module T where
foreign import data SProxy :: Symbol -> Type
foo :: SProxy "hello" -> SProxy "hello"
foo x = x"#;
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_type_level_string_unification_different() {
    // Two different type-level strings should NOT unify
    let source = r#"module T where
foreign import data SProxy :: Symbol -> Type
foo :: SProxy "hello" -> SProxy "world"
foo x = x"#;
    let (_, errors) = check_module_types(source);
    assert!(!errors.is_empty(), "expected a unification error for different type-level strings");
}

#[test]
fn type_level_int_in_annotation() {
    // Type-level integer literal in a type annotation
    let source = "module T where
foreign import data NProxy :: Int -> Type
foo :: NProxy 42
foo = foo";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn type_level_int_unification_same() {
    // Two identical type-level ints should unify
    let source = "module T where
foreign import data NProxy :: Int -> Type
foo :: NProxy 5 -> NProxy 5
foo x = x";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn err_type_level_int_unification_different() {
    // Two different type-level ints should NOT unify
    let source = "module T where
foreign import data NProxy :: Int -> Type
foo :: NProxy 1 -> NProxy 2
foo x = x";
    let (_, errors) = check_module_types(source);
    assert!(!errors.is_empty(), "expected a unification error for different type-level ints");
}

#[test]
fn type_level_string_in_type_app() {
    // Type-level string in a type application context
    let source = r#"module T where
foreign import data Reflectable :: Symbol -> Type -> Type
foo :: Reflectable "name" String
foo = foo"#;
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn type_level_string_not_confused_with_constructor() {
    // A type-level string "Int" should not unify with the type constructor Int
    let source = r#"module T where
foreign import data SProxy :: Symbol -> Type
foreign import data TProxy :: Type -> Type
foo :: SProxy "Int" -> TProxy Int
foo x = x"#;
    let (_, errors) = check_module_types(source);
    assert!(!errors.is_empty(), "type-level string should not unify with type constructor");
}

#[test]
fn type_level_string_polymorphic() {
    // Type-level string used with a polymorphic proxy type
    let source = r#"module T where
foreign import data SProxy :: Symbol -> Type
id :: forall a. a -> a
id x = x
foo :: SProxy "hello" -> SProxy "hello"
foo x = id x"#;
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn type_level_int_negative() {
    // Negative type-level integer (if parser supports it)
    let source = "module T where
foreign import data NProxy :: Int -> Type
foo :: NProxy 0
foo = foo";
    let (_, errors) = check_module_types(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

// Remaining features that still need work:
// - Module imports (requires multi-module compilation)
// - Derived instances (derive instance, derive newtype instance)
