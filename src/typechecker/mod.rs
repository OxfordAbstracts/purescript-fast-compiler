pub mod types;
pub mod error;
pub mod unify;
pub mod env;
pub mod infer;
pub mod convert;
pub mod check;

use std::collections::HashMap;

use crate::cst::{Expr, Module};
use crate::interner::Symbol;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::InferCtx;
use crate::typechecker::types::Type;

/// Infer the type of an expression in an empty environment.
pub fn infer_expr(expr: &Expr) -> Result<Type, TypeError> {
    let mut ctx = InferCtx::new();
    let env = Env::new();
    let ty = ctx.infer(&env, expr)?;
    Ok(ctx.state.zonk(ty))
}

/// Infer the type of an expression with a pre-populated environment.
pub fn infer_expr_with_env(env: &Env, expr: &Expr) -> Result<Type, TypeError> {
    let mut ctx = InferCtx::new();
    let ty = ctx.infer(env, expr)?;
    Ok(ctx.state.zonk(ty))
}

/// Typecheck a full module, returning a map of top-level names to their types.
pub fn check_module(module: &Module) -> Result<HashMap<Symbol, Type>, TypeError> {
    check::check_module(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;
    use crate::interner;

    fn check_expr(source: &str) -> Result<Type, TypeError> {
        let expr = parser::parse_expr(source).expect("parsing failed");
        infer_expr(&expr)
    }

    fn assert_infers_to(source: &str, expected: Type) {
        let result = check_expr(source);
        match result {
            Ok(ty) => assert_eq!(ty, expected, "for expression: {}", source),
            Err(e) => panic!("Type error for '{}': {}", source, e),
        }
    }

    fn assert_type_error(source: &str) {
        let result = check_expr(source);
        assert!(
            result.is_err(),
            "Expected type error for '{}', got: {:?}",
            source,
            result
        );
    }

    fn check_module_types(source: &str) -> Result<HashMap<Symbol, Type>, TypeError> {
        let module = parser::parse(source).expect("parsing failed");
        check_module(&module)
    }

    fn assert_module_name_type(source: &str, name: &str, expected: Type) {
        let result = check_module_types(source);
        match result {
            Ok(types) => {
                let sym = interner::intern(name);
                let ty = types.get(&sym).unwrap_or_else(|| {
                    panic!("Name '{}' not found in module types. Available: {:?}", name,
                        types.keys().map(|k| interner::resolve(*k).unwrap_or_default()).collect::<Vec<_>>())
                });
                assert_eq!(*ty, expected, "for name '{}' in module", name);
            }
            Err(e) => panic!("Type error for module: {}", e),
        }
    }

    fn assert_module_type_error(source: &str) {
        let result = check_module_types(source);
        assert!(
            result.is_err(),
            "Expected type error for module, got: {:?}",
            result
        );
    }

    // ===== Passing tests: Literals =====

    #[test]
    fn test_infer_int_literal() {
        assert_infers_to("42", Type::int());
    }

    #[test]
    fn test_infer_float_literal() {
        assert_infers_to("3.14", Type::float());
    }

    #[test]
    fn test_infer_string_literal() {
        assert_infers_to(r#""hello""#, Type::string());
    }

    #[test]
    fn test_infer_char_literal() {
        assert_infers_to("'a'", Type::char());
    }

    #[test]
    fn test_infer_boolean_true() {
        assert_infers_to("true", Type::boolean());
    }

    #[test]
    fn test_infer_boolean_false() {
        assert_infers_to("false", Type::boolean());
    }

    // ===== Passing tests: Lambda =====

    #[test]
    fn test_infer_identity_lambda() {
        let ty = check_expr(r"\x -> x").unwrap();
        match ty {
            Type::Fun(from, to) => {
                assert_eq!(*from, *to, "identity should have same input and output type");
            }
            other => panic!("Expected function type, got: {}", other),
        }
    }

    #[test]
    fn test_infer_const_lambda() {
        let ty = check_expr(r"\x -> \y -> x").unwrap();
        match &ty {
            Type::Fun(a, inner) => match inner.as_ref() {
                Type::Fun(_, c) => {
                    assert_eq!(**a, **c, "const should return first arg type");
                }
                other => panic!("Expected inner function type, got: {}", other),
            },
            other => panic!("Expected function type, got: {}", other),
        }
    }

    // ===== Passing tests: Application =====

    #[test]
    fn test_infer_identity_applied_to_int() {
        assert_infers_to(r"(\x -> x) 42", Type::int());
    }

    #[test]
    fn test_infer_identity_applied_to_string() {
        assert_infers_to(r#"(\x -> x) "hello""#, Type::string());
    }

    // ===== Passing tests: If-then-else =====

    #[test]
    fn test_infer_if_int() {
        assert_infers_to("if true then 1 else 2", Type::int());
    }

    #[test]
    fn test_infer_if_string() {
        assert_infers_to(r#"if true then "a" else "b""#, Type::string());
    }

    // ===== Passing tests: Let =====

    #[test]
    fn test_infer_let_simple() {
        assert_infers_to(
            "let\n  x = 42\nin x",
            Type::int(),
        );
    }

    #[test]
    fn test_infer_let_polymorphism() {
        assert_infers_to(
            "let\n  id = \\x -> x\nin id 42",
            Type::int(),
        );
    }

    #[test]
    fn test_infer_let_polymorphism_multiple_uses() {
        assert_infers_to(
            "let\n  id = \\x -> x\nin if id true then id 1 else id 2",
            Type::int(),
        );
    }

    // ===== Passing tests: Type annotation =====

    #[test]
    fn test_infer_annotation() {
        assert_infers_to("(42 :: Int)", Type::int());
    }

    // ===== Passing tests: Negate =====

    #[test]
    fn test_infer_negate() {
        assert_infers_to("-42", Type::int());
    }

    // ===== Passing tests: Array =====

    #[test]
    fn test_infer_array_int() {
        assert_infers_to("[1, 2, 3]", Type::array(Type::int()));
    }

    #[test]
    fn test_infer_array_string() {
        assert_infers_to(r#"["a", "b"]"#, Type::array(Type::string()));
    }

    #[test]
    fn test_infer_array_empty() {
        // Empty array should have a polymorphic element type
        let ty = check_expr("[]").unwrap();
        match ty {
            Type::App(f, _) => {
                assert_eq!(*f, Type::Con(interner::intern("Array")));
            }
            other => panic!("Expected Array type, got: {}", other),
        }
    }

    // ===== Failing tests: Type mismatches =====

    #[test]
    fn test_error_if_branch_mismatch() {
        assert_type_error(r#"if true then 1 else "hello""#);
    }

    #[test]
    fn test_error_if_condition_not_boolean() {
        assert_type_error("if 42 then 1 else 2");
    }

    #[test]
    fn test_error_applying_non_function() {
        assert_type_error(r#"42 "hello""#);
    }

    #[test]
    fn test_error_undefined_variable() {
        assert_type_error("undefinedVar");
    }

    #[test]
    fn test_error_occurs_check() {
        assert_type_error(r"\x -> x x");
    }

    #[test]
    fn test_error_occurs_check_2() {
        assert_type_error(r"\f -> f f");
    }

    #[test]
    fn test_error_negate_string() {
        assert_type_error(r#"-"hello""#);
    }

    #[test]
    fn test_error_wrong_argument_type() {
        assert_type_error(r#"(\x -> if x then 1 else 2) "hello""#);
    }

    #[test]
    fn test_error_array_element_mismatch() {
        assert_type_error("[1, true]");
    }

    #[test]
    fn test_error_typed_hole() {
        let result = check_expr("?help");
        assert!(matches!(result, Err(TypeError::TypeHole { .. })));
    }

    // ===== Module-level tests: Passing =====

    #[test]
    fn test_module_simple_value() {
        assert_module_name_type(
            "module T where\nx = 42",
            "x",
            Type::int(),
        );
    }

    #[test]
    fn test_module_value_with_signature() {
        assert_module_name_type(
            "module T where\nx :: Int\nx = 42",
            "x",
            Type::int(),
        );
    }

    #[test]
    fn test_module_function_with_binder() {
        // f x = x should infer a polymorphic type
        let types = check_module_types("module T where\nf x = x").unwrap();
        let sym = interner::intern("f");
        let ty = types.get(&sym).unwrap();
        match ty {
            Type::Fun(from, to) => {
                assert_eq!(*from, *to, "identity function should have same input/output type");
            }
            other => panic!("Expected function type, got: {}", other),
        }
    }

    #[test]
    fn test_module_two_functions() {
        let source = "module T where\nf x = x\ng = f 42";
        let types = check_module_types(source).unwrap();
        let g_sym = interner::intern("g");
        assert_eq!(*types.get(&g_sym).unwrap(), Type::int());
    }

    #[test]
    fn test_module_data_constructor() {
        let source = "module T where\ndata MyBool = MyTrue | MyFalse\nx = MyTrue";
        let types = check_module_types(source).unwrap();
        let x_sym = interner::intern("x");
        assert_eq!(
            *types.get(&x_sym).unwrap(),
            Type::Con(interner::intern("MyBool")),
        );
    }

    #[test]
    fn test_module_data_constructor_with_field() {
        let source = "module T where\ndata Maybe a = Just a | Nothing\nx = Just 42";
        let types = check_module_types(source).unwrap();
        let x_sym = interner::intern("x");
        assert_eq!(
            *types.get(&x_sym).unwrap(),
            Type::app(Type::Con(interner::intern("Maybe")), Type::int()),
        );
    }

    #[test]
    fn test_module_case_expression() {
        let source = "module T where
data MyBool = MyTrue | MyFalse
f x = case x of
  MyTrue -> 1
  MyFalse -> 0";
        let types = check_module_types(source).unwrap();
        let f_sym = interner::intern("f");
        let f_ty = types.get(&f_sym).unwrap();
        match f_ty {
            Type::Fun(from, to) => {
                assert_eq!(**from, Type::Con(interner::intern("MyBool")));
                assert_eq!(**to, Type::int());
            }
            other => panic!("Expected function type, got: {}", other),
        }
    }

    #[test]
    fn test_module_forall_signature() {
        let source = "module T where\nid :: forall a. a -> a\nid x = x";
        let types = check_module_types(source).unwrap();
        let id_sym = interner::intern("id");
        let id_ty = types.get(&id_sym).unwrap();
        match id_ty {
            Type::Fun(from, to) => {
                assert_eq!(*from, *to, "id should have matching input/output");
            }
            other => panic!("Expected function type for id, got: {}", other),
        }
    }

    // ===== Module-level tests: Failing =====

    #[test]
    fn test_module_error_signature_mismatch() {
        assert_module_type_error("module T where\nx :: Int\nx = true");
    }

    #[test]
    fn test_module_error_duplicate_signature() {
        assert_module_type_error("module T where\nx :: Int\nx :: String\nx = 42");
    }

    #[test]
    fn test_module_error_orphan_signature() {
        assert_module_type_error("module T where\nx :: Int");
    }
}
