// Parser module (Phase 3 - stub for now)
use crate::ast::Module;
use crate::diagnostics::ParseError;

/// Parse source code into AST
/// TODO: Implement full parser in Phase 3
pub fn parse<'ast>(_source: &str) -> Result<Module<'ast>, ParseError> {
    Err(ParseError::NotImplemented)
}
