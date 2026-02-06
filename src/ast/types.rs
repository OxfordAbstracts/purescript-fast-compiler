use std::marker::PhantomData;

/// Type AST nodes (Phase 5 - stub for now)
#[derive(Debug, Clone, PartialEq)]
pub enum Type<'ast> {
    /// Placeholder
    /// TODO: Add TyVar, TyCon, TyApp, TyForall, etc. in Phase 5
    _Phantom(PhantomData<&'ast ()>),
}
