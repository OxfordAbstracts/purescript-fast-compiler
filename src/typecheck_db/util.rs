//! Small shared helpers for the incremental typechecker passes.
//!
//! Everything here is intentionally tiny. The point is to centralize
//! invariants so we get uniform panic messages and can't accidentally
//! introduce silent fallbacks one file at a time.

use crate::interner::Symbol;

/// Resolve an interned `Symbol` back to its string, panicking if the
/// interner doesn't know it.
///
/// Rationale: every `Symbol` in the CST was produced by interning a
/// source-code identifier, so a `None` from `interner::resolve` can
/// only mean the interner is corrupt or the Symbol came from a
/// different interner instance. Either way it's a bug — not a data
/// problem — and we want the panic to fire at the first site that
/// notices, rather than silently propagating an empty string through
/// the rest of the pipeline.
pub fn resolve_symbol(sym: Symbol) -> String {
    crate::interner::resolve(sym)
        .expect("interned Symbol must resolve (interner corrupt or cross-interner Symbol)")
}
