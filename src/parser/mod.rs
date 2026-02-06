// Parser module - LALRPOP-generated parser with custom lexer

pub mod lexer_adapter;

// LALRPOP generates this module from grammar.lalrpop
#[allow(clippy::all, unused, unused_lifetimes)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/parser/grammar.rs"));
}

use crate::cst::Module;
use crate::diagnostics::ParseError;
use crate::lexer::lex;
use lexer_adapter::LexerAdapter;

/// Parse PureScript source code into a CST
pub fn parse(source: &str) -> Result<Module, ParseError> {
    // Step 1: Lex the source
    let tokens = lex(source).map_err(|e| ParseError::LexError { pos: 0, message: e })?;

    // Step 2: Create lexer adapter for LALRPOP
    let lexer = LexerAdapter::new(tokens);

    // Step 3: Parse with LALRPOP
    grammar::ModuleParser::new()
        .parse(lexer)
        .map_err(|e| ParseError::SyntaxError {
            span: crate::ast::span::Span::new(0, 0),
            message: format!("{:?}", e),
        })
}

#[cfg(test)]
mod tests {
    use crate::cst::Literal;

    use super::*;
    fn parse_expr(source: &str) -> Result<crate::cst::Expr, ParseError> {
        let tokens = lex(source).map_err(|e| ParseError::LexError { pos: 0, message: e })?;

        let lexer = LexerAdapter::new(tokens);

        grammar::ExprParser::new()
            .parse(lexer)
            .map_err(|e| ParseError::SyntaxError {
                span: crate::ast::span::Span::new(0, 0),
                message: format!("{:?}", e),
            })
    }

    fn parse_type(source: &str) -> Result<crate::cst::TypeExpr, ParseError> {
        let tokens = lex(source).map_err(|e| ParseError::LexError { pos: 0, message: e })?;

        let lexer = LexerAdapter::new(tokens);

        grammar::TypeExprParser::new()
            .parse(lexer)
            .map_err(|e| ParseError::SyntaxError {
                span: crate::ast::span::Span::new(0, 0),
                message: format!("{:?}", e),
            })
    }

    #[test]
    fn test_parse_simple_expr() {
        let result = parse_expr("42");
        assert!(matches!(
            result,
            Ok(crate::cst::Expr::Literal {
                lit: Literal::Int(42),
                ..
            })
        ));

        let result = parse_expr("foo");
        assert!(matches!(result, Ok(crate::cst::Expr::Var { .. })));

        let result = parse_expr("foo bar");
        assert!(matches!(result, Ok(crate::cst::Expr::App { .. })));
    }

    #[test]
    fn test_parse_lambda() {
        let result = parse_expr(r"\x -> x");
        assert!(matches!(result, Ok(crate::cst::Expr::Lambda { .. })));

        let result = parse_expr(r"\x y -> x + y");
        assert!(matches!(result, Ok(crate::cst::Expr::Lambda { .. })));
    }

    #[test]
    fn test_parse_if_expr() {
        let result = parse_expr("if true then 1 else 0");
        println!("Parsed if expression: {:?}", result);
        assert!(matches!(result, Ok(crate::cst::Expr::If { .. })));
    }
    #[test]
    fn test_parse_type() {
        let result = parse_type("Int");
        // println!("Parsed type: {:?}", result);
        assert!(matches!(
            result,
            Ok(crate::cst::TypeExpr::Constructor { .. })
        ));

        // assert!(result.is_ok(), "Failed to parse type: {:?}", result.err());

        let result = parse_type("Int -> String");
        assert!(matches!(result, Ok(crate::cst::TypeExpr::Function { .. })));

        let result = parse_type("Array Int");
        assert!(matches!(result, Ok(crate::cst::TypeExpr::App { .. })));
    }

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
}
