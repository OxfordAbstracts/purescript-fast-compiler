use crate::ast::span::Span;
use crate::lexer::token::Ident;
use std::marker::PhantomData;

/// Expression AST nodes (Phase 3 - stub for now)
#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'ast> {
    /// Variable reference
    Var(Ident, Span),

    /// Integer literal
    IntLit(i64, Span),

    /// Placeholder for other expression types
    /// TODO: Add Lambda, App, Let, Case, If, etc. in Phase 3
    _Phantom(PhantomData<&'ast ()>),
}
