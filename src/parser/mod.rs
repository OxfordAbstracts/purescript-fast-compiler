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
    let tokens = lex(source).map_err(|e| ParseError::LexError {
        pos: 0,
        message: e,
    })?;

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

/// Parse a single expression (for REPL/testing)
pub fn parse_expr(source: &str) -> Result<crate::cst::Expr, ParseError> {
    let tokens = lex(source).map_err(|e| ParseError::LexError {
        pos: 0,
        message: e,
    })?;

    let lexer = LexerAdapter::new(tokens);

    grammar::ExprParser::new()
        .parse(lexer)
        .map_err(|e| ParseError::SyntaxError {
            span: crate::ast::span::Span::new(0, 0),
            message: format!("{:?}", e),
        })
}

/// Parse a type expression (for testing)
pub fn parse_type(source: &str) -> Result<crate::cst::TypeExpr, ParseError> {
    let tokens = lex(source).map_err(|e| ParseError::LexError {
        pos: 0,
        message: e,
    })?;

    let lexer = LexerAdapter::new(tokens);

    grammar::TypeExprParser::new()
        .parse(lexer)
        .map_err(|e| ParseError::SyntaxError {
            span: crate::ast::span::Span::new(0, 0),
            message: format!("{:?}", e),
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_expr() {
        let result = parse_expr("42");
        assert!(result.is_ok());

        let result = parse_expr("foo");
        assert!(result.is_ok());

        let result = parse_expr("foo bar");
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_lambda() {
        let result = parse_expr(r"\x -> x");
        assert!(result.is_ok());

        let result = parse_expr(r"\x y -> x + y");
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_if_expr() {
        let result = parse_expr("if true then 1 else 0");
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_type() {
        let result = parse_type("Int");
        assert!(result.is_ok());

        let result = parse_type("Int -> String");
        assert!(result.is_ok());

        let result = parse_type("Array Int");
        assert!(result.is_ok());
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
}
