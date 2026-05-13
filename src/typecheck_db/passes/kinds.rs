//! M3 pass: produce a kind for each `data` / `newtype` / `type` / `class`
//! declaration.
//!
//! This is the *structural* kind: every type var contributes one kind arrow,
//! defaulting to `Type` unless the var carries an explicit kind annotation.
//! `data Foo a b = ...` becomes `Type -> Type -> Type`, `class C a b where`
//! becomes `Type -> Type -> Constraint`, and a bare `type T = T'` keeps its
//! parent kind at `Type`.
//!
//! True kind-polymorphism inference is left to a later milestone once the
//! full bidirectional inference (M4/M5) is in place and can share state
//! with the kind solver. For the cache invariant M3 needs to demonstrate —
//! "body-only edits don't touch downstream kinds" — structural kinding is
//! sufficient and much cheaper.

use serde::{Deserialize, Serialize};

use crate::cst::{Decl, KindSigSource};
use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::key::{InputHash, InputHasher, OutputHash, PassKey};
use crate::typecheck_db::types::{convert_type_expr, hash_type_ops, QName, Type, TypeOpMap};

pub const PASS_NAME: &str = "kind_of_type_decl";
// v2: `hash_type_ops` encoding changed, invalidating v1 cache rows.
pub const PASS_VERSION: u32 = 2;

/// Output of this pass. A standalone kind signature (`data Foo :: Type -> Type`)
/// overrides the structural kind; we surface it unchanged.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum KindOutput {
    /// Declared kind (either structural or from an explicit `:: kind`).
    Kind(Type),
    /// The decl doesn't introduce a type constructor — nothing to kind.
    NotApplicable,
}

pub fn compute(decl: &Decl, type_ops: &TypeOpMap) -> KindOutput {
    match decl {
        Decl::Data { type_vars, type_var_kind_anns, kind_type, kind_sig, is_role_decl, .. } => {
            if *is_role_decl {
                return KindOutput::NotApplicable;
            }
            if !matches!(kind_sig, KindSigSource::None) {
                // Standalone kind signature — use its declared kind.
                if let Some(k) = kind_type {
                    return KindOutput::Kind(convert_type_expr(k, type_ops));
                }
            }
            KindOutput::Kind(structural_kind(
                type_vars.len(),
                type_var_kind_anns,
                type_ops,
                Type::kind_type(),
            ))
        }
        Decl::Newtype { type_vars, type_var_kind_anns, .. } => {
            KindOutput::Kind(structural_kind(
                type_vars.len(),
                type_var_kind_anns,
                type_ops,
                Type::kind_type(),
            ))
        }
        Decl::TypeAlias { type_vars, type_var_kind_anns, .. } => {
            // Alias kinds default to `... -> Type`. A more accurate kind
            // would inspect the RHS, but structural is enough for caching.
            KindOutput::Kind(structural_kind(
                type_vars.len(),
                type_var_kind_anns,
                type_ops,
                Type::kind_type(),
            ))
        }
        Decl::Class { type_vars, type_var_kind_anns, kind_type, is_kind_sig, .. } => {
            if *is_kind_sig {
                if let Some(k) = kind_type {
                    return KindOutput::Kind(convert_type_expr(k, type_ops));
                }
            }
            KindOutput::Kind(structural_kind(
                type_vars.len(),
                type_var_kind_anns,
                type_ops,
                crate::typecheck_db::types::prim_constraint(),
            ))
        }
        Decl::ForeignData { kind, .. } => KindOutput::Kind(convert_type_expr(kind, type_ops)),
        _ => KindOutput::NotApplicable,
    }
}

fn structural_kind(
    num_vars: usize,
    kind_anns: &[Option<Box<crate::cst::TypeExpr>>],
    type_ops: &TypeOpMap,
    result_kind: Type,
) -> Type {
    let mut out = result_kind;
    for i in (0..num_vars).rev() {
        let k = kind_anns
            .get(i)
            .and_then(|opt| opt.as_ref())
            .map(|te| convert_type_expr(te, type_ops))
            .unwrap_or_else(Type::kind_type);
        out = Type::fun(k, out);
    }
    out
}

pub fn run(
    db: &mut TypecheckDb,
    module: &str,
    decl_key: &str,
    decl_source_hash: [u8; 32],
    decl: &Decl,
    type_ops: &TypeOpMap,
) -> Result<(KindOutput, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(module, decl_key, PASS_NAME);
    let input_hash = kind_input_hash(decl_source_hash, type_ops);
    if let Some((v, oh)) = db.get_cached::<KindOutput>(&key, input_hash)? {
        return Ok((v, oh, CacheOutcome::Hit));
    }
    let value = compute(decl, type_ops);
    let oh = db.put(&key, input_hash, &value)?;
    Ok((value, oh, CacheOutcome::Miss))
}

fn kind_input_hash(decl_source_hash: [u8; 32], type_ops: &TypeOpMap) -> InputHash {
    let mut h = InputHasher::new(PASS_NAME, PASS_VERSION).with_source_hash(decl_source_hash);
    h.add_dep("_type_ops", "", PASS_NAME, hash_type_ops(type_ops));
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::passes::names::hash_decl_source;

    fn first_decl(src: &str) -> Decl {
        parse(src).unwrap().decls.into_iter().next().unwrap()
    }

    #[test]
    fn kind_of_zero_arity_data() {
        let d = first_decl("module M where\ndata Unit = Unit\n");
        let out = compute(&d, &TypeOpMap::default());
        assert_eq!(out, KindOutput::Kind(Type::kind_type()));
    }

    #[test]
    fn kind_of_two_arity_data_defaults_type_arrows() {
        let d = first_decl("module M where\ndata Either a b = Left a | Right b\n");
        let out = compute(&d, &TypeOpMap::default());
        assert_eq!(
            out,
            KindOutput::Kind(Type::fun(
                Type::kind_type(),
                Type::fun(Type::kind_type(), Type::kind_type()),
            ))
        );
    }

    #[test]
    fn kind_of_newtype() {
        let d = first_decl("module M where\nnewtype Age = Age Int\n");
        let out = compute(&d, &TypeOpMap::default());
        assert_eq!(out, KindOutput::Kind(Type::kind_type()));
    }

    #[test]
    fn kind_of_class_ends_in_constraint() {
        let d = first_decl("module M where\nclass Eq a where\n  eq :: a -> a -> Boolean\n");
        let out = compute(&d, &TypeOpMap::default());
        assert_eq!(
            out,
            KindOutput::Kind(Type::fun(
                Type::kind_type(),
                crate::typecheck_db::types::prim_constraint(),
            ))
        );
    }

    #[test]
    fn kind_respects_explicit_kind_annotation_on_type_var() {
        // `data Functor (f :: Type -> Type) = ...`
        let d = first_decl(
            "module M where\ndata Box (f :: Type -> Type) = Box (f Int)\n",
        );
        let out = compute(&d, &TypeOpMap::default());
        let inner = Type::fun(Type::kind_type(), Type::kind_type());
        assert_eq!(out, KindOutput::Kind(Type::fun(inner, Type::kind_type())));
    }

    // ---- caching invariants -------------------------------------------------

    #[test]
    fn data_ctor_body_only_edit_doesnt_change_kind_output_hash() {
        // The parent's `data` declaration includes its constructors in
        // source, so a ctor-field edit *does* change the source hash. But
        // for a zero-arity edit that leaves the type vars unchanged, the
        // structural kind is the same — so the output value and its
        // output_hash match across revisions.
        //
        // Demonstrates the M3 invariant: structural kind is stable under
        // any edit that doesn't touch the type vars or their kind
        // annotations.
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let ops = TypeOpMap::default();

        let d1 = first_decl("module M where\ndata Maybe a = Nothing | Just a\n");
        let h1 = hash_decl_source("data Maybe a = Nothing | Just a");
        let (_, k_hash_1, _) = run(&mut db, "M", "Maybe", h1, &d1, &ops).unwrap();

        // Reshape ctors without changing arity or type vars.
        let d2 = first_decl("module M where\ndata Maybe a = Just a | Nothing\n");
        let h2 = hash_decl_source("data Maybe a = Just a | Nothing");
        assert_ne!(h1, h2);
        let (_, k_hash_2, outcome) = run(&mut db, "M", "Maybe", h2, &d2, &ops).unwrap();
        assert_eq!(outcome, CacheOutcome::Miss);
        // But the output payload — and therefore its hash — is unchanged.
        assert_eq!(k_hash_1, k_hash_2);
    }

    #[test]
    fn adding_a_type_var_changes_kind_output_hash() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let ops = TypeOpMap::default();

        let d1 = first_decl("module M where\ndata Foo a = Foo a\n");
        let h1 = hash_decl_source("data Foo a = Foo a");
        let (_, kh1, _) = run(&mut db, "M", "Foo", h1, &d1, &ops).unwrap();

        let d2 = first_decl("module M where\ndata Foo a b = Foo a b\n");
        let h2 = hash_decl_source("data Foo a b = Foo a b");
        let (_, kh2, _) = run(&mut db, "M", "Foo", h2, &d2, &ops).unwrap();

        assert_ne!(kh1, kh2);
    }
}
