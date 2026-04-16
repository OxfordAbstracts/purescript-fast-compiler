//! M3 pass: extract per-constructor field types from a `data`/`newtype`.
//!
//! Output: for each constructor in the decl, the ordered list of field
//! [`Type`]s and the type parameters of the parent type. The parent's type
//! vars are stored so later passes (exhaustiveness, pattern synthesis) can
//! instantiate the constructor's result type.

use serde::{Deserialize, Serialize};

use crate::cst::Decl;
use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::key::{InputHash, InputHasher, OutputHash, PassKey};
use crate::typecheck_db::types::{convert_type_expr, hash_type_ops, Type, TypeOpMap};

pub const PASS_NAME: &str = "ctor_details";
pub const PASS_VERSION: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CtorDetails {
    /// Type vars declared on the parent `data`/`newtype`.
    pub type_vars: Vec<String>,
    /// Per-constructor: (ctor_name, field_types).
    pub constructors: Vec<(String, Vec<Type>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CtorDetailsOutput {
    Data(CtorDetails),
    /// The decl isn't a `data` or `newtype` — ctor-detail extraction is a
    /// no-op for every other decl form.
    NotApplicable,
}

pub fn compute(decl: &Decl, type_ops: &TypeOpMap) -> CtorDetailsOutput {
    match decl {
        Decl::Data { type_vars, constructors, is_role_decl, kind_sig, .. } => {
            if *is_role_decl || !matches!(kind_sig, crate::cst::KindSigSource::None) {
                return CtorDetailsOutput::NotApplicable;
            }
            let vars = type_vars
                .iter()
                .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                .collect();
            let ctors = constructors
                .iter()
                .map(|c| {
                    let name = crate::typecheck_db::util::resolve_symbol(c.name.value.symbol());
                    let fields: Vec<Type> =
                        c.fields.iter().map(|f| convert_type_expr(f, type_ops)).collect();
                    (name, fields)
                })
                .collect();
            CtorDetailsOutput::Data(CtorDetails { type_vars: vars, constructors: ctors })
        }
        Decl::Newtype { type_vars, constructor, ty, .. } => {
            let vars = type_vars
                .iter()
                .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                .collect();
            let ctor_name =
                crate::typecheck_db::util::resolve_symbol(constructor.value.symbol());
            let field = convert_type_expr(ty, type_ops);
            CtorDetailsOutput::Data(CtorDetails {
                type_vars: vars,
                constructors: vec![(ctor_name, vec![field])],
            })
        }
        _ => CtorDetailsOutput::NotApplicable,
    }
}

pub fn run(
    db: &mut TypecheckDb,
    module: &str,
    decl_key: &str,
    decl_source_hash: [u8; 32],
    decl: &Decl,
    type_ops: &TypeOpMap,
) -> Result<(CtorDetailsOutput, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(module, decl_key, PASS_NAME);
    let input_hash = ctor_input_hash(decl_source_hash, type_ops);
    if let Some((v, oh)) = db.get_cached::<CtorDetailsOutput>(&key, input_hash)? {
        return Ok((v, oh, CacheOutcome::Hit));
    }
    let value = compute(decl, type_ops);
    let oh = db.put(&key, input_hash, &value)?;
    Ok((value, oh, CacheOutcome::Miss))
}

fn ctor_input_hash(decl_source_hash: [u8; 32], type_ops: &TypeOpMap) -> InputHash {
    let mut h = InputHasher::new(PASS_NAME, PASS_VERSION).with_source_hash(decl_source_hash);
    h.add_dep("_type_ops", "", PASS_NAME, hash_type_ops(type_ops));
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::passes::names::hash_decl_source;
    use crate::typecheck_db::types::QName;

    fn first_decl(src: &str) -> Decl {
        parse(src).unwrap().decls.into_iter().next().unwrap()
    }

    #[test]
    fn extracts_maybe_constructors() {
        let decl = first_decl("module M where\ndata Maybe a = Nothing | Just a\n");
        let out = compute(&decl, &TypeOpMap::default());
        let d = match out {
            CtorDetailsOutput::Data(d) => d,
            _ => panic!(),
        };
        assert_eq!(d.type_vars, vec!["a".to_string()]);
        assert_eq!(d.constructors.len(), 2);
        assert_eq!(d.constructors[0].0, "Nothing");
        assert!(d.constructors[0].1.is_empty());
        assert_eq!(d.constructors[1].0, "Just");
        assert_eq!(d.constructors[1].1, vec![Type::Var("a".into())]);
    }

    #[test]
    fn extracts_newtype_field() {
        let decl = first_decl("module M where\nnewtype Age = Age Int\n");
        let out = compute(&decl, &TypeOpMap::default());
        let d = match out {
            CtorDetailsOutput::Data(d) => d,
            _ => panic!(),
        };
        assert_eq!(d.type_vars, Vec::<String>::new());
        assert_eq!(d.constructors.len(), 1);
        assert_eq!(d.constructors[0].0, "Age");
        assert_eq!(d.constructors[0].1, vec![Type::Con(QName::unqualified("Int"))]);
    }

    #[test]
    fn not_applicable_for_type_alias() {
        let decl = first_decl("module M where\ntype Name = String\n");
        assert!(matches!(
            compute(&decl, &TypeOpMap::default()),
            CtorDetailsOutput::NotApplicable
        ));
    }

    #[test]
    fn ctor_details_round_trips_through_cache() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let decl = first_decl("module M where\ndata Maybe a = Nothing | Just a\n");
        let src_hash = hash_decl_source("data Maybe a = Nothing | Just a");
        let ops = TypeOpMap::default();

        let (v1, h1, o1) =
            run(&mut db, "M", "Maybe", src_hash, &decl, &ops).unwrap();
        assert_eq!(o1, CacheOutcome::Miss);

        let (v2, h2, o2) =
            run(&mut db, "M", "Maybe", src_hash, &decl, &ops).unwrap();
        assert_eq!(o2, CacheOutcome::Hit);
        assert_eq!(v1, v2);
        assert_eq!(h1, h2);
    }
}
