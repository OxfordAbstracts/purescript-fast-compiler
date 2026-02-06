//! Production-grade PureScript parser
//!
//! High-performance parser for the PureScript programming language.
//! Uses a three-stage architecture:
//! 1. Logos-based lexer for fast tokenization
//! 2. Layout processor for handling indentation-sensitive syntax
//! 3. LALRPOP-based parser with declarative grammar

pub mod lexer;
pub mod ast;
pub mod parser;
pub mod arena;
pub mod interner;
pub mod diagnostics;

// Re-export main types
pub use lexer::{Token, lex};
pub use ast::{Expr, Decl, Type, Pattern, Module};
pub use parser::parse;
pub use diagnostics::ParseError;
