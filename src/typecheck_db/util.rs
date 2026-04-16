//! Small shared helpers for the incremental typechecker passes.
//!
//! Everything here is intentionally tiny. The point is to centralize
//! invariants so we get uniform panic messages and can't accidentally
//! introduce silent fallbacks one file at a time.

use string_interner::Symbol as _;

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

// ---------------------------------------------------------------------------
// Hasher helpers — collapse-proof encodings for Option-shaped fields.
//
// The naive `as_deref().unwrap_or("")` pattern makes `None` and
// `Some("")` hash identically. Same story for `Option<Symbol>` folded
// through `unwrap_or(0)`: a real symbol whose internal u32 is zero
// aliases with `None`. Prefixing a one-byte discriminator (0 for
// `None`, 1 for `Some`) kills the ambiguity in every case.
// ---------------------------------------------------------------------------

pub fn hash_opt_str(h: &mut blake3::Hasher, s: Option<&str>) {
    match s {
        None => {
            h.update(&[0u8]);
        }
        Some(s) => {
            h.update(&[1u8]);
            h.update(&(s.len() as u32).to_le_bytes());
            h.update(s.as_bytes());
        }
    }
}

pub fn hash_opt_symbol(h: &mut blake3::Hasher, sym: Option<Symbol>) {
    match sym {
        None => {
            h.update(&[0u8]);
        }
        Some(s) => {
            h.update(&[1u8]);
            h.update(&(s.to_usize() as u32).to_le_bytes());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finalize(h: blake3::Hasher) -> [u8; 32] {
        *h.finalize().as_bytes()
    }

    #[test]
    fn hash_opt_str_distinguishes_none_from_empty_some() {
        let mut a = blake3::Hasher::new();
        hash_opt_str(&mut a, None);
        let mut b = blake3::Hasher::new();
        hash_opt_str(&mut b, Some(""));
        assert_ne!(finalize(a), finalize(b));
    }

    #[test]
    fn hash_opt_symbol_distinguishes_none_from_zero_symbol() {
        // Intern any string; the first interned symbol gets a small
        // internal u32 — often 0 — which is exactly the case the old
        // encoding collided with.
        let s = crate::interner::intern("x");
        let mut a = blake3::Hasher::new();
        hash_opt_symbol(&mut a, None);
        let mut b = blake3::Hasher::new();
        hash_opt_symbol(&mut b, Some(s));
        assert_ne!(
            finalize(a),
            finalize(b),
            "None must not hash the same as Some(first-interned-symbol)",
        );
    }
}
