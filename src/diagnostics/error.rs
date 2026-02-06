use crate::ast::span::Span;
use thiserror::Error;

/// Parse errors
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("Lexical error at position {pos}: {message}")]
    LexError { pos: usize, message: String },

    #[error("Parse error at {span:?}: {message}")]
    SyntaxError { span: Span, message: String },

    #[error("Not yet implemented")]
    NotImplemented,
}
