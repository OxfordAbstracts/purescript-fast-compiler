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
//! **Current state (MDe)**: signed literals, operator sections,
//! record-literal wildcards, do/ado, multi-equation merging, and
//! operator rebracketing (with Op→App lowering against a fixity table)
//! are all lowered. The MD stage is feature-complete.

use crate::cst::Decl;

pub mod walk;
pub mod signed;
pub mod sections;
pub mod records;
pub mod do_notation;
pub mod multi_eq;
pub mod rebracket;

pub use rebracket::{
    fixity_table_from_decls, FixityInfo, FixityTable, QualifiedFixityTable,
};

/// Module-scoped inputs that steer the desugar pipeline.
///
/// * `module_fixity_hash` — a stable digest of `fixity_table`, used by
///   the caching layer to invalidate downstream results when the
///   visible fixity set changes.
/// * `fixity_table` — every value-level `Decl::Fixity` (local + imported)
///   currently in scope, keyed by operator symbol. The rebracketer
///   consults this to reassociate operator chains and to lower each
///   operator to its declared target function.
///
/// Use [`rebracket::fixity_table_from_decls`] to build the table + hash
/// together from a module's decls.
#[derive(Debug, Default, Clone)]
pub struct DesugarContext {
    pub module_fixity_hash: [u8; 32],
    pub fixity_table: FixityTable,
    /// Operators reached only via qualified imports (`import M as
    /// Q` brings `Q.(:)` into scope but not bare `(:)`). Keyed by
    /// `(qualifier, op_symbol)` so `Q.op` can pick up its source
    /// module's `infixr N` declaration even when no
    /// unqualified-equivalent is in scope. The rebracketer
    /// consults this on a fallback path when the bare-op lookup
    /// misses.
    pub qualified_fixity_table: rebracket::QualifiedFixityTable,
}

/// Apply every sub-transform to `decl` in pipeline order and return the
/// normalized decl.
///
/// Determinism is a load-bearing invariant: for fixed inputs, `desugar`
/// must always produce the same output (bit-for-bit), because downstream
/// cache keys depend on the output's content hash.
pub fn desugar(decl: &Decl, ctx: &DesugarContext) -> Decl {
    let d = decl.clone();
    // Order matters:
    // 1. `sections` first — eliminate wildcards in Op/App/BacktickApp so
    //    later passes see clean shapes. Critical: runs *before*
    //    `rebracket`, because sections depend on the original chain
    //    shape (direct wildcard in an operand position).
    // 2. `records` — eliminate wildcards inside record literals.
    // 3. `signed` — Expr::Negate → negate application.
    // 4. `do_notation` — do/ado statements → bind / map / apply.
    // 5. `rebracket` — reassociate Op / BacktickApp chains by fixity,
    //    and lower known operators to plain function applications.
    let d = sections::desugar_decl(d);
    let d = records::desugar_decl(d);
    let d = signed::desugar_decl(d);
    let d = do_notation::desugar_decl(d);
    let d = rebracket::desugar_decl(d, &ctx.fixity_table, &ctx.qualified_fixity_table);
    d
}

/// Module-level entry point.
///
/// Runs the multi-equation merger (which changes the decl count) first,
/// then applies the per-decl pipeline to each resulting decl. This is
/// the right order: merging produces a single `case`-bodied decl per
/// function name, and the inner expressions (including the synthesized
/// case) then flow through the normal per-decl transforms.
pub fn desugar_module(decls: Vec<Decl>, ctx: &DesugarContext) -> Vec<Decl> {
    multi_eq::merge(decls)
        .into_iter()
        .map(|d| desugar(&d, ctx))
        .collect()
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
