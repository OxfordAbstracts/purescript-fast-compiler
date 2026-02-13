// Parser module - LALRPOP-generated parser with custom lexer

pub mod lexer_adapter;

// LALRPOP generates this module from grammar.lalrpop
#[allow(clippy::all, unused, unused_lifetimes)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/parser/grammar.rs"));
}

use crate::cst::Module;
use crate::diagnostics::CompilerError;
use crate::lexer::lex;
use lexer_adapter::LexerAdapter;

/// Extract a module path from a potentially nested RecordAccess chain.
/// e.g. `RecordAccess(Constructor("Foo"), "Bar")` -> intern("Foo.Bar")
/// e.g. `Constructor("Foo")` -> intern("Foo")
pub fn extract_module_path(expr: &crate::cst::Expr) -> Option<crate::interner::Symbol> {
    // Helper to get the full name of a constructor (including module qualifier)
    fn constructor_parts(name: &crate::cst::QualifiedIdent) -> Vec<String> {
        let mut parts = Vec::new();
        if let Some(m) = name.module {
            parts.push(crate::interner::resolve(m).unwrap_or_default().to_string());
        }
        parts.push(crate::interner::resolve(name.name).unwrap_or_default().to_string());
        parts
    }

    match expr {
        crate::cst::Expr::Constructor { name, .. } => {
            let parts = constructor_parts(name);
            Some(crate::interner::intern(&parts.join(".")))
        }
        crate::cst::Expr::RecordAccess { expr, field, .. } => {
            // Walk up the chain collecting parts
            let mut parts = vec![crate::interner::resolve(field.value).unwrap_or_default().to_string()];
            let mut current = expr.as_ref();
            loop {
                match current {
                    crate::cst::Expr::RecordAccess { expr, field, .. } => {
                        parts.push(crate::interner::resolve(field.value).unwrap_or_default().to_string());
                        current = expr.as_ref();
                    }
                    crate::cst::Expr::Constructor { name, .. } => {
                        let mut base = constructor_parts(name);
                        base.reverse();
                        parts.extend(base);
                        break;
                    }
                    _ => return None,
                }
            }
            parts.reverse();
            Some(crate::interner::intern(&parts.join(".")))
        }
        _ => None,
    }
}

/// Parse PureScript source code into a CST
pub fn parse(source: &str) -> Result<Module, CompilerError> {
    // Step 1: Lex the source
    let tokens = lex(source).map_err(|e| CompilerError::LexError { error: e })?;

    // Step 2: Create lexer adapter for LALRPOP
    let lexer = LexerAdapter::new(tokens);

    // Step 3: Parse with LALRPOP
    grammar::ModuleParser::new()
        .parse(lexer)
        .map_err(|e| CompilerError::SyntaxError { error: e })
}

/// Parse a PureScript expression string into a CST Expr.
pub fn parse_expr(source: &str) -> Result<crate::cst::Expr, CompilerError> {
    let tokens = lex(source).map_err(|e| CompilerError::LexError { error: e })?;
    let lexer = LexerAdapter::new(tokens);
    grammar::ExprParser::new()
        .parse(lexer)
        .map_err(|e| CompilerError::SyntaxError { error: e })
}

#[cfg(test)]
mod tests {
    use crate::cst::*;

    use super::*;

    // ===== Test Helpers =====

    fn parse_expr(source: &str) -> Result<Expr, CompilerError> {
        let tokens = lex(source).map_err(|e| CompilerError::LexError { error: e })?;
        let lexer = LexerAdapter::new(tokens);
        grammar::ExprParser::new()
            .parse(lexer)
            .map_err(|e| CompilerError::SyntaxError { error: e })
    }

    fn parse_type(source: &str) -> Result<TypeExpr, CompilerError> {
        // add the correct error span here
        let tokens = lex(source).map_err(|e| CompilerError::LexError { error: e })?;
        let lexer = LexerAdapter::new(tokens);
        grammar::TypeExprParser::new()
            .parse(lexer)
            .map_err(|e| CompilerError::SyntaxError { error: e })
    }

    // ===== Expression Tests: Literals =====

    #[test]
    fn test_expr_int_literal() {
        let result = parse_expr("42");
        assert!(
            matches!(
                result,
                Ok(Expr::Literal {
                    lit: Literal::Int(42),
                    ..
                })
            ),
            "Expected Int(42), got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_float_literal() {
        let result = parse_expr("3.14");
        assert!(
            matches!(result, Ok(Expr::Literal { lit: Literal::Float(f), .. }) if (f - 3.14).abs() < 1e-10),
            "Expected Float(3.14), got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_string_literal() {
        let result = parse_expr(r#""hello""#);
        assert!(
            matches!(result, Ok(Expr::Literal { lit: Literal::String(ref s), .. }) if s == "hello"),
            "Expected String(\"hello\"), got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_char_literal() {
        let result = parse_expr("'a'");
        assert!(
            matches!(
                result,
                Ok(Expr::Literal {
                    lit: Literal::Char('a'),
                    ..
                })
            ),
            "Expected Char('a'), got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_boolean_literals() {
        let result = parse_expr("true");
        assert!(
            matches!(
                result,
                Ok(Expr::Literal {
                    lit: Literal::Boolean(true),
                    ..
                })
            ),
            "Expected Boolean(true), got: {:?}",
            result
        );

        let result = parse_expr("false");
        assert!(
            matches!(
                result,
                Ok(Expr::Literal {
                    lit: Literal::Boolean(false),
                    ..
                })
            ),
            "Expected Boolean(false), got: {:?}",
            result
        );
    }

    // ===== Expression Tests: Variables & Constructors =====

    #[test]
    fn test_expr_variable() {
        let result = parse_expr("foo");
        assert!(
            matches!(result, Ok(Expr::Var { .. })),
            "Expected Var, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_constructor() {
        let result = parse_expr("Just");
        assert!(
            matches!(result, Ok(Expr::Constructor { .. })),
            "Expected Constructor, got: {:?}",
            result
        );
    }

    // ===== Expression Tests: Application =====

    #[test]
    fn test_expr_single_application() {
        let result = parse_expr("f x");
        assert!(
            matches!(result, Ok(Expr::App { .. })),
            "Expected App, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_multi_application_is_left_associative() {
        // f x y should parse as (f x) y
        let result = parse_expr("f x y").unwrap();
        match result {
            Expr::App { func, .. } => {
                assert!(
                    matches!(*func, Expr::App { .. }),
                    "Expected left-nested App"
                );
            }
            other => panic!("Expected App, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_constructor_application() {
        let result = parse_expr("Just 42");
        assert!(
            matches!(result, Ok(Expr::App { .. })),
            "Expected App, got: {:?}",
            result
        );

        // Verify the function is a Constructor
        if let Ok(Expr::App { func, arg, .. }) = &result {
            assert!(matches!(**func, Expr::Constructor { .. }));
            assert!(matches!(
                **arg,
                Expr::Literal {
                    lit: Literal::Int(42),
                    ..
                }
            ));
        }
    }

    // ===== Expression Tests: Lambda =====

    #[test]
    fn test_expr_lambda_single_binder() {
        let result = parse_expr(r"\x -> x");
        assert!(
            matches!(result, Ok(Expr::Lambda { .. })),
            "Expected Lambda, got: {:?}",
            result
        );

        if let Ok(Expr::Lambda { binders, .. }) = &result {
            assert_eq!(binders.len(), 1, "Expected 1 binder");
        }
    }

    #[test]
    fn test_expr_lambda_multi_binder() {
        let result = parse_expr(r"\x y z -> x");
        assert!(
            matches!(result, Ok(Expr::Lambda { .. })),
            "Expected Lambda, got: {:?}",
            result
        );

        if let Ok(Expr::Lambda { binders, .. }) = &result {
            assert_eq!(binders.len(), 3, "Expected 3 binders");
        }
    }

    #[test]
    fn test_expr_lambda_with_operator_body() {
        // \x -> x + 1 should parse as \x -> (x + 1)
        let result = parse_expr(r"\x -> x + y").unwrap();
        match result {
            Expr::Lambda { body, .. } => {
                assert!(
                    matches!(*body, Expr::Op { .. }),
                    "Expected Op in lambda body"
                );
            }
            other => panic!("Expected Lambda, got: {:?}", other),
        }
    }

    // ===== Expression Tests: If-Then-Else =====

    #[test]
    fn test_expr_if_simple() {
        let result = parse_expr("if true then 1 else 0");
        assert!(
            matches!(result, Ok(Expr::If { .. })),
            "Expected If, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_if_nested_in_else() {
        // if x then 1 else if y then 2 else 3
        let result = parse_expr("if x then 1 else if y then 2 else 3").unwrap();
        match result {
            Expr::If { else_expr, .. } => {
                assert!(
                    matches!(*else_expr, Expr::If { .. }),
                    "Expected nested If in else branch"
                );
            }
            other => panic!("Expected If, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_if_with_application_in_branches() {
        let result = parse_expr("if x then f a else g b");
        assert!(
            matches!(result, Ok(Expr::If { .. })),
            "Expected If, got: {:?}",
            result
        );

        if let Ok(Expr::If {
            then_expr,
            else_expr,
            ..
        }) = result
        {
            assert!(
                matches!(*then_expr, Expr::App { .. }),
                "Expected App in then branch"
            );
            assert!(
                matches!(*else_expr, Expr::App { .. }),
                "Expected App in else branch"
            );
        }
    }

    // ===== Expression Tests: Operators =====

    #[test]
    fn test_expr_binary_operator() {
        let result = parse_expr("x + y");
        assert!(
            matches!(result, Ok(Expr::Op { .. })),
            "Expected Op, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_operator_chaining_is_right_associative() {
        // a + b + c should parse as a + (b + c) with our grammar
        let result = parse_expr("a + b + c").unwrap();
        match result {
            Expr::Op { right, .. } => {
                assert!(
                    matches!(*right, Expr::Op { .. }),
                    "Expected right-nested Op"
                );
            }
            other => panic!("Expected Op, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_operator_with_application() {
        // f x + g y should parse as (f x) + (g y)
        let result = parse_expr("f x + g y").unwrap();
        match result {
            Expr::Op { left, right, .. } => {
                assert!(
                    matches!(*left, Expr::App { .. }),
                    "Expected App on left of Op"
                );
                assert!(
                    matches!(*right, Expr::App { .. }),
                    "Expected App on right of Op"
                );
            }
            other => panic!("Expected Op, got: {:?}", other),
        }
    }

    #[test]
    fn test_qualified_expr_operator() {
        let result = parse_expr("a OtherModule.>>> b").unwrap();
        match result {
            Expr::Op { op, .. } => {
                assert_eq!(crate::interner::resolve(op.value.name).unwrap(), ">>>");
                let module = op.value.module.unwrap();
                assert_eq!(crate::interner::resolve(module).unwrap(), "OtherModule");
            }
            other => panic!("Expected Op for qualified operator, got: {:?}", other),
        }
    }

    #[test]
    fn test_parenthesised_expr_operator() {
        let result = parse_expr("(+)").unwrap();
        match result {
            Expr::OpParens { op, .. } => {
                assert_eq!(crate::interner::resolve(op.value.name).unwrap(), "+");
            }
            other => panic!("Expected OpParens, got: {:?}", other),
        }
    }

    #[test]
    fn test_parenthesised_expr_operator_qualified() {
        let result = parse_expr("OtherModule.(+)").unwrap();
        match result {
            Expr::OpParens { op, .. } => {
                assert_eq!(crate::interner::resolve(op.value.name).unwrap(), "+");
                let module = op.value.module.unwrap();
                assert_eq!(crate::interner::resolve(module).unwrap(), "OtherModule");
            }
            other => panic!("Expected OpParens, got: {:?}", other),
        }
    }

    #[test]
    fn test_qualified_type_operator() {
        let result = parse_type("a OtherModule.>>> b").unwrap();
        match result {
            TypeExpr::TypeOp { op, .. } => {
                assert_eq!(crate::interner::resolve(op.value.name).unwrap(), ">>>");
                let module = op.value.module.unwrap();
                assert_eq!(crate::interner::resolve(module).unwrap(), "OtherModule");
            }
            other => panic!("Expected Op for qualified operator, got: {:?}", other),
        }
    }

    // ===== Expression Tests: Parentheses =====

    #[test]
    fn test_expr_parens_simple() {
        let result = parse_expr("(x)");
        assert!(
            matches!(result, Ok(Expr::Parens { .. })),
            "Expected Parens, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_parens_nested() {
        let result = parse_expr("((x))").unwrap();
        match result {
            Expr::Parens { expr, .. } => {
                assert!(
                    matches!(*expr, Expr::Parens { .. }),
                    "Expected nested Parens"
                );
            }
            other => panic!("Expected Parens, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_parens_around_operator() {
        // (a + b) applied to c: (a + b) c
        let result = parse_expr("(a + b) c").unwrap();
        match result {
            Expr::App { func, .. } => {
                assert!(
                    matches!(*func, Expr::Parens { .. }),
                    "Expected Parens as function"
                );
            }
            other => panic!("Expected App, got: {:?}", other),
        }
    }

    // ===== Expression Tests: Case =====

    #[test]
    fn test_expr_case_simple() {
        let result = parse_expr(
            "case x of 
  y -> y",
        );
        assert!(
            matches!(result, Ok(Expr::Case { .. })),
            "Expected Case, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_case_multiple_alternatives() {
        let result = parse_expr(
            "case x of 
  True -> 1
  False -> 0",
        )
        .unwrap();
        match result {
            Expr::Case { alts, .. } => {
                assert_eq!(alts.len(), 2, "Expected 2 case alternatives");
            }
            other => panic!("Expected Case, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_case_wildcard_binder() {
        let result = parse_expr(
            "case x of 
  _ -> 42",
        );
        assert!(
            matches!(result, Ok(Expr::Case { .. })),
            "Expected Case, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_case_arrow_below() {
        let result = parse_expr(
            "case x of
  y 
  -> y",
        );
        assert!(
            matches!(result, Ok(Expr::Case { .. })),
            "Expected Case, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_case_constructor_binder() {
        let result = parse_expr(
            "case x of
  Just y -> y
  Nothing -> 0",
        );
        assert!(
            matches!(result, Ok(Expr::Case { .. })),
            "Expected Case, got: {:?}",
            result
        );

        if let Ok(Expr::Case { alts, .. }) = &result {
            assert_eq!(alts.len(), 2);
            // First alt: Just y -> y (constructor binder with arg)
            assert!(matches!(alts[0].binders[0], Binder::Constructor { .. }));
            // Second alt: Nothing -> 0 (constructor binder without args)
            assert!(matches!(alts[1].binders[0], Binder::Constructor { .. }));
        }
    }
    #[test]
    fn test_expr_case_multiple_values() {
        let result = parse_expr(
            "case x, y of
  True, False -> 1
  False, True -> 2",
        )
        .unwrap();
        match result {
            Expr::Case { alts, .. } => {
                assert_eq!(alts.len(), 2);
                // First alt: True, False -> 1 (two constructor binders)
                assert!(matches!(alts[0].binders[0], Binder::Constructor { .. }));
                assert!(matches!(alts[0].binders[1], Binder::Constructor { .. }));
                // Second alt: False, True -> 2 (two constructor binders)
                assert!(matches!(alts[1].binders[0], Binder::Constructor { .. }));
                assert!(matches!(alts[1].binders[1], Binder::Constructor { .. }));
            }
            other => panic!("Expected Case, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_case_multiple_values_multiple_lines() {
        let result = parse_expr(
            "case x, y of
  true,
  false -> 1
  false,
  true -> 2",
        )
        .unwrap();
        match result {
            Expr::Case { alts, .. } => {
                assert_eq!(alts.len(), 2);
                // First alt: true, false -> 1 (two literal binders)
                assert!(matches!(
                    alts[0].binders[0],
                    Binder::Literal {
                        lit: Literal::Boolean(true),
                        ..
                    }
                ));
                assert!(matches!(
                    alts[0].binders[1],
                    Binder::Literal {
                        lit: Literal::Boolean(false),
                        ..
                    }
                ));
                // Second alt: false, true -> 2 (two literal binders)
                assert!(matches!(
                    alts[1].binders[0],
                    Binder::Literal {
                        lit: Literal::Boolean(false),
                        ..
                    }
                ));
                assert!(matches!(
                    alts[1].binders[1],
                    Binder::Literal {
                        lit: Literal::Boolean(true),
                        ..
                    }
                ));
            }
            other => panic!("Expected Case, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_case_with_guard() {
        let result = parse_expr(
            "case x of
  y
    | y > 0 -> 1
    | y == 0 -> 2
  _ -> 0",
        )
        .unwrap();
        match result {
            Expr::Case { alts, .. } => {
                assert_eq!(alts.len(), 2);
                assert!(matches!(alts[0].binders[0], Binder::Var { .. }));
                assert!(matches!(alts[0].result, GuardedExpr::Guarded(..)));
                assert!(matches!(alts[1].binders[0], Binder::Wildcard { .. }));
                assert!(matches!(alts[1].result, GuardedExpr::Unconditional(..)));
            }
            other => panic!("Expected Case, got: {:?}", other),
        }
    }
    // ===== Expression Tests: Let =====

    #[test]
    fn test_expr_let_single_binding() {
        let result = parse_expr(
            "let
  x = 1 
in x",
        );
        assert!(
            matches!(result, Ok(Expr::Let { .. })),
            "Expected Let, got: {:?}",
            result
        );

        if let Ok(Expr::Let { bindings, .. }) = &result {
            assert_eq!(bindings.len(), 1, "Expected 1 binding");
        }
    }

    #[test]
    fn test_expr_let_multiple_bindings() {
        let result = parse_expr(
            "let 
  x = 1
  y = 2 
in x",
        )
        .unwrap();
        match result {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 2, "Expected 2 bindings");
            }
            other => panic!("Expected Let, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_let_with_type_signature() {
        let result = parse_expr(
            "let 
  x :: Int 
  x = 42  
in x",
        )
        .unwrap();
        match result {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 2);
                assert!(matches!(bindings[0], LetBinding::Signature { .. }));
                assert!(matches!(bindings[1], LetBinding::Value { .. }));
            }
            other => panic!("Expected Let, got: {:?}", other),
        }
    }

    // ===== Expression Tests: Do =====

    #[test]
    fn test_expr_do_simple() {
        let result = parse_expr(
            "do 
          x <- action
          pure x",
        );
        assert!(
            matches!(result, Ok(Expr::Do { .. })),
            "Expected Do, got: {:?}",
            result
        );

        if let Ok(Expr::Do { statements, .. }) = &result {
            assert_eq!(statements.len(), 2, "Expected 2 statements");
            assert!(matches!(statements[0], DoStatement::Bind { .. }));
            assert!(matches!(statements[1], DoStatement::Discard { .. }));
        }
    }

    #[test]
    fn test_expr_do_discard_only() {
        let result = parse_expr(
            "do
          action1
          action2",
        )
        .unwrap();
        match result {
            Expr::Do { statements, .. } => {
                assert_eq!(statements.len(), 2);
                assert!(matches!(statements[0], DoStatement::Discard { .. }));
                assert!(matches!(statements[1], DoStatement::Discard { .. }));
            }
            other => panic!("Expected Do, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_do_with_let() {
        let result = parse_expr(
            "do 
         let x = 1
         pure x",
        )
        .unwrap();
        match result {
            Expr::Do { statements, .. } => {
                assert_eq!(statements.len(), 2);
                assert!(matches!(statements[0], DoStatement::Let { .. }));
                assert!(matches!(statements[1], DoStatement::Discard { .. }));
            }
            other => panic!("Expected Do, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_do_qualified() {
        let result = parse_expr(
            "OtherModule.do
  x <- action
  pure x",
        )
        .unwrap();
        match result {
            Expr::Do { module, statements, .. } => {
                assert_eq!(module, Some(crate::interner::intern("OtherModule")));
                assert_eq!(statements.len(), 2);
                assert!(matches!(statements[0], DoStatement::Bind { .. }));
                assert!(matches!(statements[1], DoStatement::Discard { .. }));  
            }
            other => panic!("Expected Do, got: {:?}", other),
        }
    }
    #[test]
    fn test_expr_ado_simple() {
        let result = parse_expr(
            "ado 
          x <- action
          in x",
        );
        assert!(
            matches!(result, Ok(Expr::Ado { .. })),
            "Expected Ado, got: {:?}",
            result
        );

        if let Ok(Expr::Ado { statements, module, result, .. }) = &result {
            assert!(module.is_none(), "Expected unqualified ado");
            assert_eq!(statements.len(), 1, "Expected 1 statement");
            assert!(matches!(statements[0], DoStatement::Bind { .. }));
            assert!(matches!(**result, Expr::Var { .. }));
        }
    }
    #[test]
    fn test_expr_ado_qualified() {
        let parse_result = parse_expr(
            "OtherModule.ado
  x <- action
  in x",
        )
        .unwrap();
        match parse_result {
            Expr::Ado { module, statements, .. } => { 
                assert_eq!(module, Some(crate::interner::intern("OtherModule")));
                assert_eq!(statements.len(), 1);
                assert!(matches!(statements[0], DoStatement::Bind { .. }));
            }
            other => panic!("Expected Ado, got: {:?}", other),
        }
    } 

    // ===== Expression Tests: Records =====

    #[test]
    fn test_expr_record_simple() {
        let result = parse_expr("{ x: 1, y: 2 }");
        assert!(
            matches!(result, Ok(Expr::Record { .. })),
            "Expected Record, got: {:?}",
            result
        );

        if let Ok(Expr::Record { fields, .. }) = &result {
            assert_eq!(fields.len(), 2, "Expected 2 fields");
        }
    }

    #[test]
    fn test_expr_record_single_field() {
        let result = parse_expr("{ name: x }");
        assert!(
            matches!(result, Ok(Expr::Record { .. })),
            "Expected Record, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_record_empty() {
        let result = parse_expr("{}");
        assert!(
            matches!(result, Ok(Expr::Record { .. })),
            "Expected Record, got: {:?}",
            result
        );

        if let Ok(Expr::Record { fields, .. }) = &result {
            assert_eq!(fields.len(), 0, "Expected empty record");
        }
    }

    // ===== Expression Tests: Combinations =====

    #[test]
    fn test_expr_lambda_returning_if() {
        let result = parse_expr(r"\x -> if x then 1 else 0").unwrap();
        match result {
            Expr::Lambda { body, .. } => {
                assert!(
                    matches!(*body, Expr::If { .. }),
                    "Expected If in lambda body"
                );
            }
            other => panic!("Expected Lambda, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_application_of_case() {
        // f (case x of { y -> y }) — case in parens as argument
        let result = parse_expr("f (case x of\n  y -> y )").unwrap();
        match result {
            Expr::App { arg, .. } => match *arg {
                Expr::Parens { expr, .. } => {
                    assert!(matches!(*expr, Expr::Case { .. }));
                }
                other => panic!("Expected Parens around Case, got: {:?}", other),
            },
            other => panic!("Expected App, got: {:?}", other),
        }
    }

    #[test]
    fn test_expr_operator_with_lambda_on_right() {
        // x + \y -> y should parse as x + (\y -> y)
        let result = parse_expr(r"x + \y -> y").unwrap();
        match result {
            Expr::Op { right, .. } => {
                assert!(
                    matches!(*right, Expr::Lambda { .. }),
                    "Expected Lambda on right of Op"
                );
            }
            other => panic!("Expected Op, got: {:?}", other),
        }
    }

    // Unusual but valid keyword placements

    #[test]
    fn test_keyword_in_record_access() {
        let result = parse_expr("letIn.in.value");
        assert!(
            matches!(result, Ok(Expr::RecordAccess { .. })),
            "Expected RecordAccess, got: {:?}",
            result
        );
    }

    #[test]
    fn test_keyword_record_labels() {
        let result = parse_expr("{ let: 1, in: 2, of: 3, do: 4 }");
        assert!(
            matches!(result, Ok(Expr::Record { .. })),
            "Expected Record, got: {:?}",
            result
        );
    }
    #[test]
    fn test_keyword_record_labels_in_types() {
        let result = parse_type("{ let :: Int, in :: String, of :: Boolean, do :: Number }");
        assert!(
            matches!(result, Ok(TypeExpr::Record { .. })),
            "Expected Record, got: {:?}",
            result
        );
    }

    // ===== Expression Tests: Visible Type Application =====

    #[test]
    fn test_expr_visible_type_application() {
        let result = parse_expr("f @Int");
        assert!(
            matches!(
                result,
                Ok(Expr::VisibleTypeApp {
                    ty: TypeExpr::Constructor { .. },
                    ..
                })
            ),
            "Expected VisibleTypeApp(Constructor ..), got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_visible_type_application_with_parens() {
        let result = parse_expr("f @(Maybe Int)");
        assert!(
            matches!(
                result,
                Ok(Expr::VisibleTypeApp {
                    ty: TypeExpr::Parens { .. },
                    ..
                })
            ),
            "Expected VisibleTypeApp, got: {:?}",
            result
        );
    }

    #[test]
    fn test_expr_visible_type_application_with_empty_row_type() {
        let result = parse_expr("f @()");
        if let Ok(Expr::VisibleTypeApp {
            ty: TypeExpr::Row {
                fields, tail: None, ..
            },
            ..
        }) = &result
        {
            assert!(
                fields.is_empty(),
                "Expected VisibleTypeApp with empty Row, got: {:?}",
                result
            );
        } else {
            panic!("Expected VisibleTypeApp with empty Row, got: {:?}", result);
        }
    }
    #[test]
    fn test_expr_visible_type_application_with_empty_row_type_application() {
        let result = parse_expr("f @(P () a)");
        assert!(
            matches!(result, Ok(Expr::VisibleTypeApp { .. })),
            "Expected VisibleTypeApp, got: {:?}",
            result
        );
    }
    #[test]
    fn test_expr_visible_type_application_with_record() {
        let result = parse_expr("f @{ x :: Int, y :: String }");
        assert!(
            matches!(
                result,
                Ok(Expr::VisibleTypeApp {
                    ty: TypeExpr::Record { .. },
                    ..
                })
            ),
            "Expected VisibleTypeApp with Record type, got: {:?}",
            result
        );
    }

    // ===== Type Tests: Atomic =====

    #[test]
    fn test_type_variable() {
        let result = parse_type("a");
        assert!(
            matches!(result, Ok(TypeExpr::Var { .. })),
            "Expected Var, got: {:?}",
            result
        );
    }

    #[test]
    fn test_type_constructor() {
        let result = parse_type("Int");
        assert!(
            matches!(result, Ok(TypeExpr::Constructor { .. })),
            "Expected Constructor, got: {:?}",
            result
        );
    }

    #[test]
    fn test_type_parens() {
        let result = parse_type("(Int)");
        assert!(
            matches!(result, Ok(TypeExpr::Parens { .. })),
            "Expected Parens, got: {:?}",
            result
        );
    }

    // ===== Type Tests: Function Types =====

    #[test]
    fn test_type_function_simple() {
        let result = parse_type("Int -> String");
        assert!(
            matches!(result, Ok(TypeExpr::Function { .. })),
            "Expected Function, got: {:?}",
            result
        );
    }

    #[test]
    fn test_type_function_chained_right_associative() {
        // Int -> String -> Bool should parse as Int -> (String -> Bool)
        let result = parse_type("Int -> String -> Bool").unwrap();
        match result {
            TypeExpr::Function { to, .. } => {
                assert!(
                    matches!(*to, TypeExpr::Function { .. }),
                    "Expected right-nested Function"
                );
            }
            other => panic!("Expected Function, got: {:?}", other),
        }
    }

    #[test]
    fn test_type_function_with_parens() {
        // (Int -> String) -> Bool — parens change associativity
        let result = parse_type("(Int -> String) -> Bool").unwrap();
        match result {
            TypeExpr::Function { from, .. } => match *from {
                TypeExpr::Parens { ty, .. } => {
                    assert!(matches!(*ty, TypeExpr::Function { .. }));
                }
                other => panic!("Expected Parens, got: {:?}", other),
            },
            other => panic!("Expected Function, got: {:?}", other),
        }
    }

    // ===== Type Tests: Type Application =====

    #[test]
    fn test_type_application_simple() {
        let result = parse_type("Array Int");
        assert!(
            matches!(result, Ok(TypeExpr::App { .. })),
            "Expected App, got: {:?}",
            result
        );
    }

    #[test]
    fn test_type_application_multi_arg() {
        // Map String Int should parse as (Map String) Int
        let result = parse_type("Map String Int").unwrap();
        match result {
            TypeExpr::App { constructor, .. } => {
                assert!(
                    matches!(*constructor, TypeExpr::App { .. }),
                    "Expected left-nested App"
                );
            }
            other => panic!("Expected App, got: {:?}", other),
        }
    }

    #[test]
    fn test_type_application_nested() {
        // Array (Maybe Int) — application with parenthesized argument
        let result = parse_type("Array (Maybe Int)").unwrap();
        match result {
            TypeExpr::App { arg, .. } => {
                assert!(
                    matches!(*arg, TypeExpr::Parens { .. }),
                    "Expected Parens as arg"
                );
            }
            other => panic!("Expected App, got: {:?}", other),
        }
    }

    // ===== Type Tests: Mixed =====

    #[test]
    fn test_type_application_with_function() {
        // Array Int -> String: (Array Int) -> String
        let result = parse_type("Array Int -> String").unwrap();
        match result {
            TypeExpr::Function { from, .. } => {
                assert!(
                    matches!(*from, TypeExpr::App { .. }),
                    "Expected App as from"
                );
            }
            other => panic!("Expected Function, got: {:?}", other),
        }
    }

    // ===== Declaration Tests =====

    #[test]
    fn test_decl_type_signature_simple() {
        let source = "module Test where\nx :: Int";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        assert!(matches!(result.decls[0], Decl::TypeSignature { .. }));
    }

    #[test]
    fn test_decl_type_signature_function_type() {
        let source = "module Test where\nf :: Int -> String -> Bool";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        if let Decl::TypeSignature { ty, .. } = &result.decls[0] {
            assert!(matches!(ty, TypeExpr::Function { .. }));
        } else {
            panic!("Expected TypeSignature");
        }
    }

    #[test]
    fn test_decl_value_no_binders() {
        let source = "module Test where\nx = 42";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        assert!(matches!(result.decls[0], Decl::Value { .. }));
    }

    #[test]
    fn test_decl_value_with_binders() {
        let source = "module Test where\nf x y = x";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        if let Decl::Value { binders, .. } = &result.decls[0] {
            assert_eq!(binders.len(), 2, "Expected 2 binders");
        } else {
            panic!("Expected Value decl");
        }
    }

    #[test]
    fn test_decl_value_with_wildcard_binder() {
        let source = "module Test where\nf _ = 42";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        if let Decl::Value { binders, .. } = &result.decls[0] {
            assert_eq!(binders.len(), 1);
            assert!(matches!(binders[0], Binder::Wildcard { .. }));
        } else {
            panic!("Expected Value decl");
        }
    }

    #[test]
    fn test_decl_data_simple() {
        let source = "module Test where\ndata Bool = True | False";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        if let Decl::Data { constructors, .. } = &result.decls[0] {
            assert_eq!(constructors.len(), 2, "Expected 2 constructors");
        } else {
            panic!("Expected Data decl");
        }
    }

    #[test]
    fn test_decl_data_with_type_vars() {
        let source = "module Test where\ndata Maybe a = Just a | Nothing";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        if let Decl::Data {
            type_vars,
            constructors,
            ..
        } = &result.decls[0]
        {
            assert_eq!(type_vars.len(), 1, "Expected 1 type var");
            assert_eq!(constructors.len(), 2, "Expected 2 constructors");
            // Just has 1 field, Nothing has 0
            assert_eq!(constructors[0].fields.len(), 1);
            assert_eq!(constructors[1].fields.len(), 0);
        } else {
            panic!("Expected Data decl");
        }
    }

    #[test]
    fn test_decl_data_with_multiple_type_vars() {
        let source = "module Test where\ndata Either a b = Left a | Right b";
        let result = parse(source).unwrap();
        if let Decl::Data {
            type_vars,
            constructors,
            ..
        } = &result.decls[0]
        {
            assert_eq!(type_vars.len(), 2, "Expected 2 type vars");
            assert_eq!(constructors.len(), 2, "Expected 2 constructors");
        } else {
            panic!("Expected Data decl");
        }
    }

    #[test]
    fn test_decl_type_alias() {
        let source = "module Test where\ntype Name = String";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        assert!(matches!(result.decls[0], Decl::TypeAlias { .. }));
    }

    #[test]
    fn test_decl_fixity() {
        let source = "module Test where\ninfixl 6 add as +";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
        if let Decl::Fixity {
            associativity,
            precedence,
            ..
        } = &result.decls[0]
        {
            assert_eq!(*associativity, Associativity::Left);
            assert_eq!(*precedence, 6);
        } else {
            panic!("Expected Fixity decl");
        }
    }

    #[test]
    fn test_decl_fixity_right() {
        let source = "module Test where\ninfixr 0 apply as $";
        let result = parse(source).unwrap();
        if let Decl::Fixity {
            associativity,
            precedence,
            ..
        } = &result.decls[0]
        {
            assert_eq!(*associativity, Associativity::Right);
            assert_eq!(*precedence, 0);
        } else {
            panic!("Expected Fixity decl");
        }
    }

    // ===== Module Tests =====

    #[test]
    fn test_module_minimal() {
        let source = "module Test where";
        let result = parse(source);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        assert_eq!(result.unwrap().decls.len(), 0);
    }

    #[test]
    fn test_module_single_decl() {
        let source = "module Test where\nx = 42";
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 1);
    }

    #[test]
    fn test_module_multiple_decls() {
        let source = r#"
module Test where

x :: Int
x = 42
y :: String
y = "hello"
"#;
        let result = parse(source).unwrap();
        assert_eq!(
            result.decls.len(),
            4,
            "Expected 4 decls (2 type sigs + 2 value decls)"
        );
    }

    #[test]
    fn test_module_dotted_name() {
        let source = "module Data.Array where";
        let result = parse(source).unwrap();
        assert_eq!(
            result.name.value.parts.len(),
            2,
            "Expected 2 module name parts"
        );
    }

    #[test]
    fn test_module_deeply_dotted_name() {
        let source = "module Data.Array.Internal where";
        let result = parse(source).unwrap();
        assert_eq!(
            result.name.value.parts.len(),
            3,
            "Expected 3 module name parts"
        );
    }

    #[test]
    fn test_module_mixed_declarations() {
        let source = r#"
module Test where

data Color = Red | Green | Blue
type Name = String
identity :: a -> a
identity x = x
"#;
        let result = parse(source).unwrap();
        assert_eq!(result.decls.len(), 4);
        assert!(matches!(result.decls[0], Decl::Data { .. }));
        assert!(matches!(result.decls[1], Decl::TypeAlias { .. }));
        assert!(matches!(result.decls[2], Decl::TypeSignature { .. }));
        assert!(matches!(result.decls[3], Decl::Value { .. }));
    }

    // ===== Existing Tests (preserved) =====

    #[test]
    fn test_parse_simple_module() {
        let source = r#"
module Test where

factorial :: Int -> Int
factorial n = n
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    }

    #[test]
    fn test_parse_syntax_error() {
        let source = r#"
module Test where
factorial :: Int -> Int
factorial n = n
unexpected_token
"#;
        let result = parse(source);
        assert!(
            result.is_err(),
            "Expected syntax error, but got: {:?}",
            result.ok()
        );
    }

    // ===== Error Cases =====

    #[test]
    fn test_error_missing_where() {
        let source = "module Test";
        let result = parse(source);
        assert!(result.is_err(), "Expected error for missing 'where'");
    }

    #[test]
    fn test_error_unclosed_paren() {
        let result = parse_expr("(x + y");
        assert!(result.is_err(), "Expected error for unclosed paren");
    }

    #[test]
    fn test_error_empty_input() {
        let result = parse("");
        assert!(result.is_err(), "Expected error for empty input");
    }

    #[test]
    fn test_error_incomplete_lambda() {
        let result = parse_expr(r"\x ->");
        assert!(result.is_err(), "Expected error for incomplete lambda");
    }

    // ===== Span Correctness =====

    #[test]
    fn test_span_ordering() {
        // Spans should have start <= end for all parsed expressions
        let result = parse_expr("f x + g y").unwrap();
        let span = result.span();
        assert!(
            span.start <= span.end,
            "Span start should be <= end: {:?}",
            span
        );
    }

    #[test]
    fn test_span_coverage() {
        // For "42", the literal should span the entire input
        let result = parse_expr("42").unwrap();
        let span = result.span();
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 2);
    }

    #[test]
    fn test_expr_hole() {
        let result = parse_expr("?hole").unwrap();
        let span = result.span();
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 5);
        assert!(
            matches!(result, Expr::Hole { .. }),
            "Expected Hole expression, got: {:?}",
            result
        );
    }

    #[test]
    fn test_type_hole() {
        let result = parse_type("?Hole").unwrap();
        let span = result.span();
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 5);
        assert!(
            matches!(result, TypeExpr::Hole { .. }),
            "Expected Hole type expression, got: {:?}",
            result
        );
    }

    #[test]
    fn test_span_nested_expression() {
        // For "(42)", the parens should span the entire input
        let result = parse_expr("(42)").unwrap();
        let span = result.span();
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 4);

        // The inner expr should have tighter span
        if let Expr::Parens { expr, .. } = result {
            let inner_span = expr.span();
            assert_eq!(inner_span.start, 1);
            assert_eq!(inner_span.end, 3);
        }
    }

}
