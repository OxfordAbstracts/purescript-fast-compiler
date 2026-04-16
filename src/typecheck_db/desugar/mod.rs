//! Desugar stage: normalizes the surface CST into a reduced form before the
//! typechecker consumes it.
//!
//! The pipeline runs as a **single** cached pass (see
//! [`crate::typecheck_db::passes::desugar_decl`]); the sub-transforms are
//! cheap and don't benefit from individual caching.
//!
//! Ordering (per the design doc):
//! 1. Signed literals → `negate` app.
//! 2. Record wildcard literals → lambda.
//! 3. Operator sections → lambda.
//! 4. Do / Ado → bind / apply.
//! 5. Multi-equation function decls → one `case` body.
//! 6. Operator rebracket by fixity.
//!
//! After desugar, the resulting [`Decl`] is guaranteed to not contain any of
//! these forms, and downstream passes can rely on that invariant.
//!
//! **Current state (MDb)**: signed literals, operator sections, and
//! record-literal wildcards are lowered. Do/ado, multi-equation, and
//! operator rebracketing remain for MDc..MDe.

use crate::cst::Decl;

pub mod walk;
pub mod signed;
pub mod sections;
pub mod records;

/// Module-scoped inputs that can steer the desugar pipeline.
///
/// `module_fixity_hash` folds in every `Decl::Fixity` (local and imported)
/// that's visible when this decl is being desugared. MDa doesn't read it
/// yet — the field is carried so the cache-key machinery is already in the
/// right shape when MDe wires up the rebracketer.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DesugarContext {
    pub module_fixity_hash: [u8; 32],
}

/// Apply every sub-transform to `decl` in pipeline order and return the
/// normalized decl.
///
/// Determinism is a load-bearing invariant: for fixed inputs, `desugar`
/// must always produce the same output (bit-for-bit), because downstream
/// cache keys depend on the output's content hash.
pub fn desugar(decl: &Decl, _ctx: &DesugarContext) -> Decl {
    let d = decl.clone();
    // Order matters: handle sections first so that wildcards inside
    // operator / backtick / app positions become lambdas before
    // `records` looks for record-literal wildcards (it should only see
    // wildcards that were still sitting in a `Record { .. }` value slot).
    let d = sections::desugar_decl(d);
    let d = records::desugar_decl(d);
    let d = signed::desugar_decl(d);
    d
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn first_decl(src: &str) -> Decl {
        let m = parse(src).unwrap();
        m.decls
            .into_iter()
            .next()
            .expect("module has at least one decl")
    }

    #[test]
    fn identity_desugar_preserves_value_decl() {
        let d = first_decl("module M where\nfoo = 1\n");
        let ctx = DesugarContext::default();
        assert_eq!(desugar(&d, &ctx), d);
    }

    #[test]
    fn identity_desugar_is_idempotent() {
        let d = first_decl("module M where\nfoo x = x\n");
        let ctx = DesugarContext::default();
        let d1 = desugar(&d, &ctx);
        let d2 = desugar(&d1, &ctx);
        assert_eq!(d1, d2);
    }
}
