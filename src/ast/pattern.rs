use std::marker::PhantomData;

/// Pattern AST nodes (Phase 3 - stub for now)
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern<'ast> {
    /// Placeholder
    /// TODO: Add VarPat, LitPat, ConsPat, etc. in Phase 3
    _Phantom(PhantomData<&'ast ()>),
}
