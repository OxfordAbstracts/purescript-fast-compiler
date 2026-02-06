use std::marker::PhantomData;

/// Declaration AST nodes (Phase 3 - stub for now)
#[derive(Debug, Clone, PartialEq)]
pub enum Decl<'ast> {
    /// Placeholder
    /// TODO: Add ValueDecl, TypeDecl, etc. in Phase 3
    _Phantom(PhantomData<&'ast ()>),
}
