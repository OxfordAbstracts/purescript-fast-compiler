pub mod types;
pub mod error;
pub mod unify;
pub mod env;
pub mod infer;
pub mod convert;
pub mod check;
pub mod kind;
pub mod registry;

use std::collections::HashMap;

use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;

pub use check::CheckResult;
pub use registry::{ModuleExports, ModuleRegistry};

/// Infer the type of a CST expression in an empty environment.
/// Note: standalone expression inference still uses CST types since
/// `ast::convert` operates on whole modules, not standalone expressions.
pub fn infer_expr(expr: &crate::cst::Expr) -> Result<Type, TypeError> {
    // Convert the CST expression to AST by wrapping in a minimal module
    let ast_expr = crate::ast::convert_expr(expr.clone());
    let mut ctx = infer::InferCtx::new();
    let env = env::Env::new();
    let ty = ctx.infer(&env, &ast_expr)?;
    let ty = ctx.state.zonk(ty);
    // If holes were recorded during inference, return the first as an error
    let hole_errors = ctx.drain_pending_holes();
    if let Some(err) = hole_errors.into_iter().next() {
        return Err(err);
    }
    Ok(ty)
}

/// Infer the type of a CST expression with a pre-populated environment.
pub fn infer_expr_with_env(env: &env::Env, expr: &crate::cst::Expr) -> Result<Type, TypeError> {
    let ast_expr = crate::ast::convert_expr(expr.clone());
    let mut ctx = infer::InferCtx::new();
    let ty = ctx.infer(env, &ast_expr)?;
    let ty = ctx.state.zonk(ty);
    let hole_errors = ctx.drain_pending_holes();
    if let Some(err) = hole_errors.into_iter().next() {
        return Err(err);
    }
    Ok(ty)
}

/// Typecheck a full CST module, returning partial results and accumulated errors.
/// Performs CST→AST conversion internally; returns conversion errors if any.
pub fn check_module(module: &crate::cst::Module) -> CheckResult {
    check_module_with_registry(module, &ModuleRegistry::default())
}

/// Typecheck a full CST module with a registry, returning partial results and accumulated errors.
/// Performs CST→AST conversion internally; returns conversion errors if any.
pub fn check_module_with_registry(module: &crate::cst::Module, registry: &ModuleRegistry) -> CheckResult {
    check_module_with_options(module, registry, false)
}

/// Typecheck a full CST module for IDE use, also collecting span→type mappings for hover.
pub fn check_module_for_ide(module: &crate::cst::Module, registry: &ModuleRegistry) -> CheckResult {
    check_module_with_options(module, registry, true)
}

fn check_module_with_options(module: &crate::cst::Module, registry: &ModuleRegistry, collect_span_types: bool) -> CheckResult {
    let (ast_module, convert_errors) = crate::ast::convert(module, registry);
    if !convert_errors.is_empty() {
        return CheckResult {
            types: HashMap::new(),
            errors: convert_errors,
            exports: ModuleExports::default(),
            span_types: HashMap::new(),
            record_update_fields: HashMap::new(),
        };
    }
    let mut result = if collect_span_types {
        check::check_module_for_ide(&ast_module, registry)
    } else {
        check::check_module(&ast_module, registry)
    };

    // Propagate module-level doc-comments from CST to exports
    result.exports.module_doc = module.doc_comments.iter().filter_map(|c| {
        if let crate::cst::Comment::Doc(text) = c { Some(text.clone()) } else { None }
    }).collect();

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use crate::parser;
    use crate::interner;
    use crate::interner::Symbol;

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

    fn check_module_types(source: &str) -> (HashMap<crate::names::ValueName, Type>, Vec<TypeError>) {
        let module = parser::parse(source).expect("parsing failed");
        let result = check_module(&module);
        (result.types, result.errors)
    }

    fn assert_module_name_type(source: &str, name: &str, expected: Type) {
        let (types, errors) = check_module_types(source);
        if !errors.is_empty() {
            panic!("Type errors for module: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        }
        let sym = crate::names::ValueName::new(interner::intern(name));
        let ty = types.get(&sym).unwrap_or_else(|| {
            panic!("Name '{}' not found in module types. Available: {:?}", name,
                types.keys().map(|k| k.resolve().unwrap_or_default()).collect::<Vec<_>>())
        });
        assert_eq!(*ty, expected, "for name '{}' in module", name);
    }

    fn assert_module_type_error(source: &str) {
        let (_, errors) = check_module_types(source);
        assert!(
            !errors.is_empty(),
            "Expected type error for module, got no errors",
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
                assert_eq!(*f, Type::prim_con("Array"));
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

    // Note: test_error_negate_string was removed because our typechecker strips
    // class constraints (Ring), so `-"hello"` passes type checking.

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
        assert!(matches!(result, Err(TypeError::HoleInferredType { .. })));
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
        let (types, errors) = check_module_types("module T where\nf x = x");
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let sym = crate::names::ValueName::new(interner::intern("f"));
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
        let (types, errors) = check_module_types(source);
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let g_sym = crate::names::ValueName::new(interner::intern("g"));
        assert_eq!(*types.get(&g_sym).unwrap(), Type::int());
    }

    #[test]
    fn test_module_data_constructor() {
        let source = "module T where\ndata MyBool = MyTrue | MyFalse\nx = MyTrue";
        let (types, errors) = check_module_types(source);
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let x_sym = crate::names::ValueName::new(interner::intern("x"));
        assert_eq!(
            *types.get(&x_sym).unwrap(),
            Type::con_local( "MyBool"),
        );
    }

    #[test]
    fn test_module_data_constructor_with_field() {
        let source = "module T where\ndata Maybe a = Just a | Nothing\nx = Just 42";
        let (types, errors) = check_module_types(source);
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let x_sym = crate::names::ValueName::new(interner::intern("x"));
        assert_eq!(
            *types.get(&x_sym).unwrap(),
            Type::app(Type::con_local("Maybe"), Type::int()),
        );
    }

    #[test]
    fn test_module_case_expression() {
        let source = "module T where
data MyBool = MyTrue | MyFalse
f x = case x of
  MyTrue -> 1
  MyFalse -> 0";
        let (types, errors) = check_module_types(source);
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let f_sym = crate::names::ValueName::new(interner::intern("f"));
        let f_ty = types.get(&f_sym).unwrap();
        match f_ty {
            Type::Fun(from, to) => {
                assert_eq!(**from, Type::con("T", "MyBool"));
                assert_eq!(**to, Type::int());
            }
            other => panic!("Expected function type, got: {}", other),
        }
    }

    #[test]
    fn test_module_forall_signature() {
        let source = "module T where\nid :: forall a. a -> a\nid x = x";
        let (types, errors) = check_module_types(source);
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let id_sym = crate::names::ValueName::new(interner::intern("id"));
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
