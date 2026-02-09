use crate::ast::span::Span;
use thiserror::Error;

/// Parse errors
#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("Lexical error at position {span:?}: {message}")]
    LexError { span: Span, message: String },

    #[error("Parse error: {message}")]
    SyntaxError { message: String },

    #[error("Not yet implemented")]
    NotImplemented,
}
