use lalrpop_util::ParseError;

use thiserror::Error;

use crate::{Token, ast::Span, lexer::logos_lexer::LexError};

/// Parse errors
#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("Lex error: {error}")]
    LexError { error: LexError },

    #[error("Parse error: {error}")]
    SyntaxError { error: ParseError<usize, Token, String> },


    #[error("Type error: {error}")]
    TypeError { error: crate::typechecker::error::TypeError },

    #[error("Not yet implemented")]
    NotImplemented,
}


impl CompilerError {
    pub fn get_message(&self) -> String {
        match self {
            CompilerError::LexError { error } => error.0.clone(),
            CompilerError::SyntaxError { error } => format!("{}", error),
            CompilerError::TypeError { error } => format!("{}", error),
            CompilerError::NotImplemented => "Not yet implemented".to_string(),
        }
    }
    pub fn get_span(&self) -> Option<Span> {
        match self {
            CompilerError::LexError { error } => Some(error.1.clone()),
            CompilerError::SyntaxError { error } => match error {
                ParseError::InvalidToken { location } => Some(Span::new(*location, *location)),
                ParseError::UnrecognizedToken { token: (start, _, end), expected: _ } => Some(Span::new(*start, *end)),
                ParseError::ExtraToken { token: (start, _, end) } => Some(Span::new(*start, *end)),
                ParseError::UnrecognizedEof { location, .. } => Some(Span::new(*location, *location)),
                ParseError::User { error: _ } => None,
            },
            CompilerError::TypeError { error } => Some(error.span()),
            CompilerError::NotImplemented => None,
        }
    }
}

