//! Integration tests for the full compiler pipeline.
//!
//! These tests exercise the public API end-to-end:
//! source string → lex → parse → typecheck

use purescript_fast_compiler::diagnostics::CompilerError;
use purescript_fast_compiler::interner;
use purescript_fast_compiler::typechecker::check_module;
use purescript_fast_compiler::typechecker::error::TypeError;
use purescript_fast_compiler::typechecker::types::Type;
use purescript_fast_compiler::{lex, parse};

// ===== Helpers =====

fn parse_and_check(source: &str) -> Result<std::collections::HashMap<interner::Symbol, Type>, TypeError> {
    let module = parse(source).expect("parse failed");
    check_module(&module)
}

fn lookup_type(source: &str, name: &str) -> Type {
    let types = parse_and_check(source).expect("typecheck failed");
    let sym = interner::intern(name);
    types
        .get(&sym)
        .unwrap_or_else(|| panic!("name '{}' not found in module types", name))
        .clone()
}

// ===== Lexing =====

#[test]
fn lex_simple_module() {
    let tokens = lex("module Main where\nx = 42").unwrap();
    assert!(tokens.len() > 0);
}

#[test]
fn lex_error_unterminated_string() {
    let result = lex(r#""unterminated"#);
    assert!(result.is_err());
}

// ===== Parsing =====

#[test]
fn parse_minimal_module() {
    let module = parse("module Main where").unwrap();
    assert!(module.decls.is_empty());
}

#[test]
fn parse_module_with_value() {
    let module = parse("module Main where\nx = 42").unwrap();
    assert_eq!(module.decls.len(), 1);
    assert!(matches!(module.decls[0], purescript_fast_compiler::CstDecl::Value { .. }));
}

#[test]
fn parse_module_with_data_type() {
    let source = r#"
module Main where

data Maybe a = Just a | Nothing
"#;
    let module = parse(source).unwrap();
    assert_eq!(module.decls.len(), 1);
    match &module.decls[0] {
        purescript_fast_compiler::CstDecl::Data { constructors, type_vars, .. } => {
            assert_eq!(type_vars.len(), 1);
            assert_eq!(constructors.len(), 2);
        }
        other => panic!("Expected Data decl, got: {:?}", other),
    }
}

#[test]
fn parse_module_with_imports() {
    let source = r#"
module Main where

import Prelude
import Data.Maybe (Maybe(..))
"#;
    let module = parse(source).unwrap();
    assert_eq!(module.imports.len(), 2);
}

#[test]
fn parse_module_with_class_and_instance() {
    let source = r#"
module Main where

class MyEq a where
  myEq :: a -> a -> Boolean

instance MyEq Int where
  myEq x y = true
"#;
    let module = parse(source).unwrap();
    assert!(module.decls.len() >= 2);
}

#[test]
fn parse_error_missing_where() {
    let result = parse("module Main");
    assert!(result.is_err());
}

#[test]
fn parse_error_invalid_syntax() {
    let result = parse("module Main where\n= = =");
    assert!(result.is_err());
}

// ===== Full pipeline: parse + typecheck =====

#[test]
fn e2e_simple_int_value() {
    assert_eq!(
        lookup_type("module T where\nx = 42", "x"),
        Type::int(),
    );
}

#[test]
fn e2e_simple_string_value() {
    assert_eq!(
        lookup_type(r#"module T where
x = "hello""#, "x"),
        Type::string(),
    );
}

#[test]
fn e2e_function_with_signature() {
    let source = "module T where\nid :: forall a. a -> a\nid x = x";
    let ty = lookup_type(source, "id");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, *to, "id should have same input/output type");
        }
        other => panic!("Expected function type for id, got: {}", other),
    }
}

#[test]
fn e2e_data_constructor_nullary() {
    let source = "module T where\ndata Color = Red | Green | Blue\nx = Red";
    assert_eq!(
        lookup_type(source, "x"),
        Type::Con(interner::intern("Color")),
    );
}

#[test]
fn e2e_data_constructor_with_field() {
    let source = "module T where\ndata Box a = MkBox a\nx = MkBox 42";
    assert_eq!(
        lookup_type(source, "x"),
        Type::app(Type::Con(interner::intern("Box")), Type::int()),
    );
}

#[test]
fn e2e_case_expression() {
    let source = "module T where
data MyBool = MyTrue | MyFalse
f x = case x of
  MyTrue -> 1
  MyFalse -> 0";
    let ty = lookup_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::Con(interner::intern("MyBool")));
            assert_eq!(*to, Type::int());
        }
        other => panic!("Expected MyBool -> Int, got: {}", other),
    }
}

#[test]
fn e2e_let_polymorphism() {
    let source = "module T where
f = let
  id = \\x -> x
in id 42";
    assert_eq!(lookup_type(source, "f"), Type::int());
}

#[test]
fn e2e_multiple_declarations() {
    let source = "module T where
f x = x
g = f 42
h = f true";
    let types = parse_and_check(source).unwrap();
    assert_eq!(*types.get(&interner::intern("g")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("h")).unwrap(), Type::boolean());
}

#[test]
fn e2e_array_literal() {
    assert_eq!(
        lookup_type("module T where\nx = [1, 2, 3]", "x"),
        Type::array(Type::int()),
    );
}

#[test]
fn e2e_nested_if() {
    let source = r#"module T where
f x = if x then 1 else if x then 2 else 3"#;
    let ty = lookup_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::boolean());
            assert_eq!(*to, Type::int());
        }
        other => panic!("Expected Boolean -> Int, got: {}", other),
    }
}

// ===== Error cases =====

#[test]
fn e2e_error_parse_failure() {
    let result = parse("module T where\n= invalid");
    assert!(result.is_err());
    match result.unwrap_err() {
        CompilerError::SyntaxError { .. } => {}
        other => panic!("Expected SyntaxError, got: {:?}", other),
    }
}

#[test]
fn e2e_error_type_mismatch() {
    let result = parse_and_check("module T where\nx :: Int\nx = true");
    assert!(result.is_err());
    match result.unwrap_err() {
        TypeError::UnificationError { .. } => {}
        other => panic!("Expected UnificationError, got: {}", other),
    }
}

#[test]
fn e2e_error_undefined_variable() {
    let result = parse_and_check("module T where\nx = undefinedVar");
    assert!(result.is_err());
    match result.unwrap_err() {
        TypeError::UndefinedVariable { .. } => {}
        other => panic!("Expected UndefinedVariable, got: {}", other),
    }
}

#[test]
fn e2e_error_duplicate_signature() {
    let result = parse_and_check("module T where\nx :: Int\nx :: String\nx = 42");
    assert!(result.is_err());
    match result.unwrap_err() {
        TypeError::DuplicateTypeSignature { .. } => {}
        other => panic!("Expected DuplicateTypeSignature, got: {}", other),
    }
}

#[test]
fn e2e_error_orphan_signature() {
    let result = parse_and_check("module T where\nx :: Int");
    assert!(result.is_err());
    match result.unwrap_err() {
        TypeError::OrphanTypeSignature { .. } => {}
        other => panic!("Expected OrphanTypeSignature, got: {}", other),
    }
}

#[test]
fn e2e_error_if_branch_mismatch() {
    let result = parse_and_check(r#"module T where
x = if true then 1 else "hello""#);
    assert!(result.is_err());
    match result.unwrap_err() {
        TypeError::UnificationError { .. } => {}
        other => panic!("Expected UnificationError, got: {}", other),
    }
}

#[test]
fn e2e_error_array_element_mismatch() {
    let result = parse_and_check("module T where\nx = [1, true]");
    assert!(result.is_err());
    match result.unwrap_err() {
        TypeError::UnificationError { .. } => {}
        other => panic!("Expected UnificationError, got: {}", other),
    }
}
