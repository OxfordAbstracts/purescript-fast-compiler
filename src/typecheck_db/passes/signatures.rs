//! M3 pass: convert a `TypeSignature` declaration to a serializable
//! [`Scheme`].
//!
//! This is a structural conversion — no kind checking, no polymorphism
//! inference. A signature like `foo :: forall a. a -> a` already carries its
//! quantification in the CST; we just mirror it into the wire type.
//!
//! Dependencies: this pass depends on *every* type constructor named in the
//! signature, captured through a caller-supplied [`TypeOpMap`] (for
//! resolving type-level operators to their canonical target types) plus a
//! hash of that map folded into the input hash. Source-hash invalidation
//! covers the rest: if the signature text changes at all, the output is
//! recomputed.

use serde::{Deserialize, Serialize};

use crate::cst::Decl;
use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::key::{InputHash, InputHasher, OutputHash, PassKey};
use crate::typecheck_db::types::{convert_type_expr, hash_type_ops, Scheme, Type, TypeOpMap};

pub const PASS_NAME: &str = "convert_signature";
pub const PASS_VERSION: u32 = 1;

/// Output of this pass: either the converted signature or a marker that
/// the decl wasn't a type signature at all.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SignatureOutput {
    Scheme(Scheme),
    NotASignature,
}

pub fn compute(decl: &Decl, type_ops: &TypeOpMap) -> SignatureOutput {
    match decl {
        Decl::TypeSignature { ty, .. } => {
            SignatureOutput::Scheme(scheme_of(convert_type_expr(ty, type_ops)))
        }
        Decl::Foreign { ty, .. } => {
            SignatureOutput::Scheme(scheme_of(convert_type_expr(ty, type_ops)))
        }
        _ => SignatureOutput::NotASignature,
    }
}

/// If the converted type is a top-level `forall`, lift its vars into the
/// scheme. Nested quantification stays in the body.
fn scheme_of(ty: Type) -> Scheme {
    match ty {
        Type::Forall(vars, body) => Scheme {
            vars: vars.into_iter().map(|(n, _, _)| n).collect(),
            ty: *body,
        },
        other => Scheme::mono(other),
    }
}

pub fn run(
    db: &mut TypecheckDb,
    module: &str,
    decl_key: &str,
    decl_source_hash: [u8; 32],
    decl: &Decl,
    type_ops: &TypeOpMap,
) -> Result<(SignatureOutput, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(module, decl_key, PASS_NAME);
    let input_hash = sig_input_hash(decl_source_hash, type_ops);

    if let Some((v, oh)) = db.get_cached::<SignatureOutput>(&key, input_hash)? {
        return Ok((v, oh, CacheOutcome::Hit));
    }
    let value = compute(decl, type_ops);
    let oh = db.put(&key, input_hash, &value)?;
    Ok((value, oh, CacheOutcome::Miss))
}

fn sig_input_hash(decl_source_hash: [u8; 32], type_ops: &TypeOpMap) -> InputHash {
    let mut h = InputHasher::new(PASS_NAME, PASS_VERSION).with_source_hash(decl_source_hash);
    h.add_dep("_type_ops", "", PASS_NAME, hash_type_ops(type_ops));
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::types::QName;

    fn sig_decl(src: &str) -> Decl {
        let m = parse(src).unwrap();
        m.decls
            .into_iter()
            .find(|d| matches!(d, Decl::TypeSignature { .. }))
            .expect("type signature")
    }

    #[test]
    fn converts_simple_signature() {
        let decl = sig_decl("module M where\nfoo :: Int -> Int\nfoo x = x\n");
        let out = compute(&decl, &TypeOpMap::default());
        let scheme = match out {
            SignatureOutput::Scheme(s) => s,
            _ => panic!(),
        };
        assert!(scheme.vars.is_empty());
        assert_eq!(
            scheme.ty,
            Type::fun(
                Type::Con(QName::unqualified("Int")),
                Type::Con(QName::unqualified("Int")),
            )
        );
    }

    #[test]
    fn lifts_outer_forall_into_scheme() {
        let decl = sig_decl(
            "module M where\nfoo :: forall a b. a -> b -> a\nfoo x _ = x\n",
        );
        let out = compute(&decl, &TypeOpMap::default());
        let scheme = match out {
            SignatureOutput::Scheme(s) => s,
            _ => panic!(),
        };
        assert_eq!(scheme.vars, vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn non_signature_decl_returns_not_a_signature() {
        let m = parse("module M where\nfoo = 1\n").unwrap();
        let value_decl = m.decls.into_iter().next().unwrap();
        let out = compute(&value_decl, &TypeOpMap::default());
        assert!(matches!(out, SignatureOutput::NotASignature));
    }

    // ---- caching invariants --------------------------------------------------

    fn hash_of_src(src: &str, decl_src: &str) -> (Decl, [u8; 32]) {
        let decl = sig_decl(src);
        let h = crate::typecheck_db::passes::names::hash_decl_source(decl_src);
        (decl, h)
    }

    #[test]
    fn body_only_edit_doesnt_touch_signature_output() {
        // Two revisions of the same module: only the value equation changes.
        // The signature decl's source hash is stable, so its cached output
        // stays put — and any downstream pass keyed on its output_hash would
        // continue to hit cache.
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let ops = TypeOpMap::default();

        let (decl_v1, sig_hash) = hash_of_src(
            "module M where\nfoo :: Int -> Int\nfoo x = x\n",
            "foo :: Int -> Int",
        );
        let (v1, h1, o1) =
            run(&mut db, "M", "foo", sig_hash, &decl_v1, &ops).unwrap();
        assert_eq!(o1, CacheOutcome::Miss);

        // Edit the body of foo; the signature decl itself is unchanged.
        let (decl_v2, sig_hash_v2) = hash_of_src(
            "module M where\nfoo :: Int -> Int\nfoo x = x + 1\n",
            "foo :: Int -> Int",
        );
        assert_eq!(sig_hash, sig_hash_v2);
        let (v2, h2, o2) =
            run(&mut db, "M", "foo", sig_hash_v2, &decl_v2, &ops).unwrap();
        assert_eq!(o2, CacheOutcome::Hit);
        assert_eq!(v1, v2);
        assert_eq!(h1, h2);
    }

    #[test]
    fn signature_edit_changes_output_hash() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let ops = TypeOpMap::default();

        let (decl_v1, h_v1) = hash_of_src(
            "module M where\nfoo :: Int -> Int\nfoo x = x\n",
            "foo :: Int -> Int",
        );
        let (_, sig_out_1, _) = run(&mut db, "M", "foo", h_v1, &decl_v1, &ops).unwrap();

        // Change the signature itself.
        let (decl_v2, h_v2) = hash_of_src(
            "module M where\nfoo :: String -> Int\nfoo _ = 0\n",
            "foo :: String -> Int",
        );
        assert_ne!(h_v1, h_v2);
        let (_, sig_out_2, o2) = run(&mut db, "M", "foo", h_v2, &decl_v2, &ops).unwrap();
        assert_eq!(o2, CacheOutcome::Miss);
        assert_ne!(sig_out_1, sig_out_2);
    }

    #[test]
    fn type_ops_map_change_invalidates_cache() {
        let mut db = TypecheckDb::open_in_memory().unwrap();

        // A signature using a type-level operator.
        let src = "module M where\nfoo :: Int ~> Boolean\nfoo _ = identity\n";
        let (decl, h) = hash_of_src(src, "foo :: Int ~> Boolean");

        let ops_empty = TypeOpMap::default();
        let (_, out_1, _) = run(&mut db, "M", "foo", h, &decl, &ops_empty).unwrap();

        let mut ops_with = TypeOpMap::default();
        ops_with.insert(
            (None, "~>".into()),
            QName::qualified("Data.NaturalTransformation", "NT"),
        );
        let (_, out_2, o) = run(&mut db, "M", "foo", h, &decl, &ops_with).unwrap();
        assert_eq!(o, CacheOutcome::Miss);
        assert_ne!(out_1, out_2);
    }
}
