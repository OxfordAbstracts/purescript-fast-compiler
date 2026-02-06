use crate::ast::decl::Decl;
use crate::lexer::token::Ident;

/// Module structure (Phase 3 - stub for now)
#[derive(Debug, Clone, PartialEq)]
pub struct Module<'ast> {
    pub name: Ident,
    pub decls: Vec<Decl<'ast>>,
}
