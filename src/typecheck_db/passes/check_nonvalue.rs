//! Per-decl cached "check" passes for every non-value decl kind.
//!
//! Each kind has one `Shape` struct (its stable structural surface)
//! and one `check_*` function that caches the shape keyed by the
//! decl's source hash. Output hashes capture only the structural
//! form — body-level diagnostics and anything a downstream dep
//! shouldn't care about are excluded.
//!
//! These per-decl cache entries are what the value-SCC driver folds
//! into its `dep_output_hashes` to get fine-grained invalidation: a
//! value SCC depends only on the specific non-value decls it
//! references, not on a bulk module-context fingerprint.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::cst;
use crate::typecheck_db::ir::Decl;
use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::key::{hash_bytes, InputHasher, OutputHash, PassKey};
use crate::typecheck_db::passes::exhaustiveness::CtorInfo;
use crate::typecheck_db::passes::instance_index::{ClassInfo, FunDep};
use crate::typecheck_db::types::{convert_type_expr, Constraint, QName, Scheme, Type, TypeOpMap};
use crate::typecheck_db::util;

// ============================================================================
// Shape structs — the structural output of each kind's check pass
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataShape {
    pub name: String,
    pub type_vars: Vec<String>,
    /// Each ctor carries its own field types in declaration order.
    pub ctors: Vec<(String, Vec<Type>)>,
    pub is_newtype: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AliasShape {
    pub name: String,
    pub type_vars: Vec<String>,
    pub body: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassShape {
    pub name: String,
    pub type_vars: Vec<String>,
    pub fundeps: Vec<FunDep>,
    pub superclasses: Vec<Constraint>,
    /// Methods in declaration order. Each carries its full
    /// constrained scheme — the class itself is folded into the
    /// scheme as a leading `Constrained` layer so downstream
    /// `infer_var` can peel it uniformly.
    pub methods: Vec<(String, Scheme)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InstanceShape {
    pub class: QName,
    pub types: Vec<Type>,
    pub context: Vec<Constraint>,
    pub vars: Vec<String>,
    pub chained: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixityShape {
    pub assoc: u8, // repr of cst::Associativity
    pub precedence: u8,
    pub target_module: Option<String>,
    pub target_name: String,
    pub is_type: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignShape {
    pub name: String,
    pub scheme: Scheme,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignDataShape {
    pub name: String,
    /// The declared kind. Stored as `Type` (our serializable rep).
    pub kind: Type,
}

// ============================================================================
// Common helpers
// ============================================================================

fn strip_forall(ty: Type) -> (Vec<String>, Type) {
    match ty {
        Type::Forall(qs, body) => {
            let names: Vec<String> = qs.into_iter().map(|(n, _, _)| n).collect();
            (names, *body)
        }
        other => (Vec::new(), other),
    }
}

/// Hash the serialized bytes of a shape — produces the stable
/// output hash downstream deps key on.
fn hash_shape<T: Serialize>(shape: &T) -> OutputHash {
    let bytes = bincode::serialize(shape).expect("shape serialization");
    hash_bytes(&bytes)
}

/// Fold dep hashes into a shape's output hash. Two shapes with the
/// same bytes but different dep sets produce different hashes —
/// letting transitive changes (e.g. a type alias's target
/// retargeting) propagate without changing every intermediate
/// decl's source.
fn hash_shape_with_deps<T: Serialize>(shape: &T, dep_hashes: &[OutputHash]) -> OutputHash {
    let mut h = blake3::Hasher::new();
    let body = bincode::serialize(shape).expect("shape serialization");
    h.update(b"shape_with_deps_v1");
    h.update(&(body.len() as u32).to_le_bytes());
    h.update(&body);
    let mut sorted: Vec<OutputHash> = dep_hashes.to_vec();
    sorted.sort();
    h.update(&(sorted.len() as u32).to_le_bytes());
    for d in sorted {
        h.update(&d);
    }
    *h.finalize().as_bytes()
}

/// Fold dep hashes into a check pass's input hash.
fn input_hash_with_deps(
    pass_name: &'static str,
    pass_version: u32,
    source_hash: [u8; 32],
    dep_hashes: &[OutputHash],
) -> [u8; 32] {
    let base = InputHasher::new(pass_name, pass_version)
        .with_source_hash(source_hash)
        .finish();
    let mut h = blake3::Hasher::new();
    h.update(b"input_hash_with_deps_v1");
    h.update(&base);
    let mut sorted: Vec<OutputHash> = dep_hashes.to_vec();
    sorted.sort();
    h.update(&(sorted.len() as u32).to_le_bytes());
    for d in sorted {
        h.update(&d);
    }
    *h.finalize().as_bytes()
}

// ============================================================================
// check_data / check_newtype
// ============================================================================

pub mod check_data {
    use super::*;

    pub const PASS_NAME: &str = "check_data";
    pub const PASS_VERSION: u32 = 1;

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_debug: &str,
        _source_hash: [u8; 32],
        dep_hashes: &[OutputHash],
        decl: &Decl,
        type_ops: &TypeOpMap,
    ) -> Result<(DataShape, OutputHash, CacheOutcome), DriverError> {
        // Compute the shape first so the input_hash is derived from
        // structural content rather than from the decl's source span
        // (some spans are broken — e.g. class bodies come back as
        // `15..0`, which would make distinct classes hash-collide).
        let shape = compute(decl, type_ops);
        let shape_bytes = bincode::serialize(&shape).expect("shape serialization");
        let source_hash = hash_bytes(&shape_bytes);
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash =
            input_hash_with_deps(PASS_NAME, PASS_VERSION, source_hash, dep_hashes);
        if let Some((cached, _)) = db.get_cached::<DataShape>(&key, input_hash)? {
            let oh = hash_shape_with_deps(&cached, dep_hashes);
            return Ok((cached, oh, CacheOutcome::Hit));
        }
        db.put_with_debug(&key, input_hash, &shape, decl_debug)?;
        let oh = hash_shape_with_deps(&shape, dep_hashes);
        Ok((shape, oh, CacheOutcome::Miss))
    }

    fn compute(decl: &Decl, type_ops: &TypeOpMap) -> DataShape {
        match decl {
            Decl::Data { name, type_vars, constructors, .. } => {
                let type_name = util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| util::resolve_symbol(v.value.symbol()))
                    .collect();
                let ctors: Vec<(String, Vec<Type>)> = constructors
                    .iter()
                    .map(|c| {
                        let cname = util::resolve_symbol(c.name.value.symbol());
                        let fields: Vec<Type> = c
                            .fields
                            .iter()
                            .map(|f| convert_type_expr(f, type_ops))
                            .collect();
                        (cname, fields)
                    })
                    .collect();
                DataShape { name: type_name, type_vars: tvars, ctors, is_newtype: false }
            }
            Decl::Newtype { name, type_vars, constructor, ty, .. } => {
                let type_name = util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| util::resolve_symbol(v.value.symbol()))
                    .collect();
                let cname = util::resolve_symbol(constructor.value.symbol());
                let field = convert_type_expr(ty, type_ops);
                DataShape {
                    name: type_name,
                    type_vars: tvars,
                    ctors: vec![(cname, vec![field])],
                    is_newtype: true,
                }
            }
            _ => unreachable!("check_data only handles Data/Newtype"),
        }
    }
}

// ============================================================================
// check_type_alias
// ============================================================================

pub mod check_type_alias {
    use super::*;

    pub const PASS_NAME: &str = "check_type_alias";
    pub const PASS_VERSION: u32 = 1;

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_debug: &str,
        _source_hash: [u8; 32],
        dep_hashes: &[OutputHash],
        decl: &Decl,
        type_ops: &TypeOpMap,
    ) -> Result<(AliasShape, OutputHash, CacheOutcome), DriverError> {
        let shape = match decl {
            Decl::TypeAlias { name, type_vars, ty, .. } => AliasShape {
                name: util::resolve_symbol(name.value.symbol()),
                type_vars: type_vars
                    .iter()
                    .map(|v| util::resolve_symbol(v.value.symbol()))
                    .collect(),
                body: convert_type_expr(ty, type_ops),
            },
            _ => unreachable!("check_type_alias only handles TypeAlias"),
        };
        let shape_bytes = bincode::serialize(&shape).expect("shape serialization");
        let source_hash = hash_bytes(&shape_bytes);
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash =
            input_hash_with_deps(PASS_NAME, PASS_VERSION, source_hash, dep_hashes);
        if let Some((cached, _)) = db.get_cached::<AliasShape>(&key, input_hash)? {
            let oh = hash_shape_with_deps(&cached, dep_hashes);
            return Ok((cached, oh, CacheOutcome::Hit));
        }
        db.put_with_debug(&key, input_hash, &shape, decl_debug)?;
        let oh = hash_shape_with_deps(&shape, dep_hashes);
        Ok((shape, oh, CacheOutcome::Miss))
    }
}

// ============================================================================
// check_class
// ============================================================================

pub mod check_class {
    use super::*;

    pub const PASS_NAME: &str = "check_class";
    pub const PASS_VERSION: u32 = 1;

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_debug: &str,
        _source_hash: [u8; 32],
        dep_hashes: &[OutputHash],
        decl: &Decl,
        type_ops: &TypeOpMap,
    ) -> Result<(ClassShape, OutputHash, CacheOutcome), DriverError> {
        let shape = match decl {
            Decl::Class { name, type_vars, fundeps, constraints, members, .. } => {
                let class_name = util::resolve_symbol(name.value.symbol());
                let vars: Vec<String> = type_vars
                    .iter()
                    .map(|v| util::resolve_symbol(v.value.symbol()))
                    .collect();
                let fundeps_pos: Vec<FunDep> = fundeps
                    .iter()
                    .map(|fd| FunDep {
                        determiners: fd
                            .lhs
                            .iter()
                            .filter_map(|v| position_of(&vars, v))
                            .collect(),
                        determined: fd
                            .rhs
                            .iter()
                            .filter_map(|v| position_of(&vars, v))
                            .collect(),
                    })
                    .collect();
                let superclasses: Vec<Constraint> = constraints
                    .iter()
                    .map(|c| Constraint {
                        class: cst_constraint_qname(&c.class),
                        args: c
                            .args
                            .iter()
                            .map(|a| convert_type_expr(a, type_ops))
                            .collect(),
                    })
                    .collect();
                let methods: Vec<(String, Scheme)> = members
                    .iter()
                    .map(|m| {
                        let mname = util::resolve_symbol(m.name.value.symbol());
                        let method_ty = convert_type_expr(&m.ty, type_ops);
                        let (method_vars, method_body) = strip_forall(method_ty);
                        let constraint = Constraint {
                            class: QName::unqualified(&class_name),
                            args: vars
                                .iter()
                                .map(|v| Type::Var(v.clone()))
                                .collect(),
                        };
                        let constrained =
                            Type::Constrained(vec![constraint], Box::new(method_body));
                        let mut all_vars = vars.clone();
                        all_vars.extend(method_vars);
                        (mname, Scheme { vars: all_vars, ty: constrained })
                    })
                    .collect();
                ClassShape {
                    name: class_name,
                    type_vars: vars,
                    fundeps: fundeps_pos,
                    superclasses,
                    methods,
                }
            }
            _ => unreachable!("check_class only handles Class"),
        };
        let shape_bytes = bincode::serialize(&shape).expect("shape serialization");
        let source_hash = hash_bytes(&shape_bytes);
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash =
            input_hash_with_deps(PASS_NAME, PASS_VERSION, source_hash, dep_hashes);
        if let Some((cached, _)) = db.get_cached::<ClassShape>(&key, input_hash)? {
            let oh = hash_shape_with_deps(&cached, dep_hashes);
            return Ok((cached, oh, CacheOutcome::Hit));
        }
        db.put_with_debug(&key, input_hash, &shape, decl_debug)?;
        let oh = hash_shape_with_deps(&shape, dep_hashes);
        Ok((shape, oh, CacheOutcome::Miss))
    }

    fn position_of(vars: &[String], needle: &crate::names::TypeVarName) -> Option<usize> {
        let sym = util::resolve_symbol(needle.symbol());
        vars.iter().position(|v| v == &sym)
    }

    fn cst_constraint_qname(q: &crate::names::Qualified<crate::names::ClassName>) -> QName {
        let qi = q.to_qi();
        QName {
            module: qi.module.map(util::resolve_symbol),
            name: util::resolve_symbol(qi.name),
        }
    }
}

// ============================================================================
// check_instance (handles both Instance and Derive)
// ============================================================================

pub mod check_instance {
    use super::*;

    pub const PASS_NAME: &str = "check_instance";
    pub const PASS_VERSION: u32 = 1;

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_debug: &str,
        _source_hash: [u8; 32],
        dep_hashes: &[OutputHash],
        decl: &Decl,
        type_ops: &TypeOpMap,
    ) -> Result<(InstanceShape, OutputHash, CacheOutcome), DriverError> {
        let shape = extract_shape(decl, type_ops);
        let shape_bytes = bincode::serialize(&shape).expect("shape serialization");
        let source_hash = hash_bytes(&shape_bytes);
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash =
            input_hash_with_deps(PASS_NAME, PASS_VERSION, source_hash, dep_hashes);
        if let Some((cached, _)) = db.get_cached::<InstanceShape>(&key, input_hash)? {
            let oh = hash_shape_with_deps(&cached, dep_hashes);
            return Ok((cached, oh, CacheOutcome::Hit));
        }
        db.put_with_debug(&key, input_hash, &shape, decl_debug)?;
        let oh = hash_shape_with_deps(&shape, dep_hashes);
        Ok((shape, oh, CacheOutcome::Miss))
    }

    fn extract_shape(decl: &Decl, type_ops: &TypeOpMap) -> InstanceShape {
        let (class_name, types, constraints, chained) = match decl {
            Decl::Instance { class_name, types, constraints, chain, .. } => {
                (class_name, types, constraints, *chain)
            }
            Decl::Derive { class_name, types, constraints, .. } => {
                (class_name, types, constraints, false)
            }
            _ => unreachable!("check_instance only handles Instance/Derive"),
        };
        let class = {
            let qi = class_name.to_qi();
            QName {
                module: qi.module.map(util::resolve_symbol),
                name: util::resolve_symbol(qi.name),
            }
        };
        let head_tys: Vec<Type> = types.iter().map(|t| convert_type_expr(t, type_ops)).collect();
        let context: Vec<Constraint> = constraints
            .iter()
            .map(|c| {
                let qi = c.class.to_qi();
                Constraint {
                    class: QName {
                        module: qi.module.map(util::resolve_symbol),
                        name: util::resolve_symbol(qi.name),
                    },
                    args: c
                        .args
                        .iter()
                        .map(|a| convert_type_expr(a, type_ops))
                        .collect(),
                }
            })
            .collect();
        // Vars: every distinct type variable appearing in head or context,
        // in first-occurrence order.
        let mut vars: Vec<String> = Vec::new();
        for t in &head_tys {
            collect_vars(t, &mut vars);
        }
        for c in &context {
            for a in &c.args {
                collect_vars(a, &mut vars);
            }
        }
        InstanceShape {
            class,
            types: head_tys,
            context,
            vars,
            chained,
        }
    }

    fn collect_vars(ty: &Type, out: &mut Vec<String>) {
        match ty {
            Type::Var(n) => {
                if !out.iter().any(|v| v == n) {
                    out.push(n.clone());
                }
            }
            Type::App(f, a) => {
                collect_vars(f, out);
                collect_vars(a, out);
            }
            Type::Fun(a, b) => {
                collect_vars(a, out);
                collect_vars(b, out);
            }
            Type::Forall(_, body) => collect_vars(body, out),
            Type::Constrained(cs, body) => {
                for c in cs {
                    for a in &c.args {
                        collect_vars(a, out);
                    }
                }
                collect_vars(body, out);
            }
            Type::Record(fields, tail) => {
                for (_, t) in fields {
                    collect_vars(t, out);
                }
                if let Some(t) = tail {
                    collect_vars(t, out);
                }
            }
            Type::Kinded(t, k) => {
                collect_vars(t, out);
                collect_vars(k, out);
            }
            _ => {}
        }
    }
}

// ============================================================================
// check_fixity
// ============================================================================

pub mod check_fixity {
    use super::*;

    pub const PASS_NAME: &str = "check_fixity";
    pub const PASS_VERSION: u32 = 1;

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_debug: &str,
        _source_hash: [u8; 32],
        dep_hashes: &[OutputHash],
        decl: &Decl,
    ) -> Result<(FixityShape, OutputHash, CacheOutcome), DriverError> {
        let shape = match decl {
            Decl::Fixity { associativity, precedence, target, is_type, .. } => FixityShape {
                assoc: *associativity as u8,
                precedence: *precedence,
                target_module: target.module.map(util::resolve_symbol),
                target_name: util::resolve_symbol(target.name),
                is_type: *is_type,
            },
            _ => unreachable!("check_fixity only handles Fixity"),
        };
        let shape_bytes = bincode::serialize(&shape).expect("shape serialization");
        let source_hash = hash_bytes(&shape_bytes);
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash =
            input_hash_with_deps(PASS_NAME, PASS_VERSION, source_hash, dep_hashes);
        if let Some((cached, _)) = db.get_cached::<FixityShape>(&key, input_hash)? {
            let oh = hash_shape_with_deps(&cached, dep_hashes);
            return Ok((cached, oh, CacheOutcome::Hit));
        }
        db.put_with_debug(&key, input_hash, &shape, decl_debug)?;
        let oh = hash_shape_with_deps(&shape, dep_hashes);
        Ok((shape, oh, CacheOutcome::Miss))
    }
}

// ============================================================================
// check_foreign + check_foreign_data
// ============================================================================

pub mod check_foreign {
    use super::*;

    pub const PASS_NAME: &str = "check_foreign";
    pub const PASS_VERSION: u32 = 1;

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_debug: &str,
        _source_hash: [u8; 32],
        dep_hashes: &[OutputHash],
        decl: &Decl,
        type_ops: &TypeOpMap,
    ) -> Result<(ForeignShape, OutputHash, CacheOutcome), DriverError> {
        let shape = match decl {
            Decl::Foreign { name, ty, .. } => {
                let n = util::resolve_symbol(name.value.symbol());
                let declared = convert_type_expr(ty, type_ops);
                let (vars, body) = strip_forall(declared);
                ForeignShape { name: n, scheme: Scheme { vars, ty: body } }
            }
            _ => unreachable!("check_foreign only handles Foreign"),
        };
        let shape_bytes = bincode::serialize(&shape).expect("shape serialization");
        let source_hash = hash_bytes(&shape_bytes);
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash =
            input_hash_with_deps(PASS_NAME, PASS_VERSION, source_hash, dep_hashes);
        if let Some((cached, _)) = db.get_cached::<ForeignShape>(&key, input_hash)? {
            let oh = hash_shape_with_deps(&cached, dep_hashes);
            return Ok((cached, oh, CacheOutcome::Hit));
        }
        db.put_with_debug(&key, input_hash, &shape, decl_debug)?;
        let oh = hash_shape_with_deps(&shape, dep_hashes);
        Ok((shape, oh, CacheOutcome::Miss))
    }
}

pub mod check_foreign_data {
    use super::*;

    pub const PASS_NAME: &str = "check_foreign_data";
    pub const PASS_VERSION: u32 = 1;

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_debug: &str,
        _source_hash: [u8; 32],
        dep_hashes: &[OutputHash],
        decl: &Decl,
        type_ops: &TypeOpMap,
    ) -> Result<(ForeignDataShape, OutputHash, CacheOutcome), DriverError> {
        let shape = match decl {
            Decl::ForeignData { name, kind, .. } => ForeignDataShape {
                name: util::resolve_symbol(name.value.symbol()),
                kind: convert_type_expr(kind, type_ops),
            },
            _ => unreachable!("check_foreign_data only handles ForeignData"),
        };
        let shape_bytes = bincode::serialize(&shape).expect("shape serialization");
        let source_hash = hash_bytes(&shape_bytes);
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash =
            input_hash_with_deps(PASS_NAME, PASS_VERSION, source_hash, dep_hashes);
        if let Some((cached, _)) = db.get_cached::<ForeignDataShape>(&key, input_hash)? {
            let oh = hash_shape_with_deps(&cached, dep_hashes);
            return Ok((cached, oh, CacheOutcome::Hit));
        }
        db.put_with_debug(&key, input_hash, &shape, decl_debug)?;
        let oh = hash_shape_with_deps(&shape, dep_hashes);
        Ok((shape, oh, CacheOutcome::Miss))
    }
}

// ============================================================================
// Shape → legacy-consumer adapters
//
// Lots of existing code (infer_value, exhaustiveness, instance_index
// consumers) expects the pre-graph formats: HashMap<name, CtorInfo>,
// DataConstructors, ClassInfo, Instance, etc. The helpers below let the
// driver rebuild those views on top of cached shapes with zero change
// to the downstream consumers.
// ============================================================================

pub fn ctor_info_from_data_shape(shape: &DataShape) -> HashMap<String, CtorInfo> {
    let mut out = HashMap::new();
    for (cname, fields) in &shape.ctors {
        out.insert(
            cname.clone(),
            CtorInfo {
                parent_type: shape.name.clone(),
                type_vars: shape.type_vars.clone(),
                fields: fields.clone(),
            },
        );
    }
    out
}

pub fn class_info_from_class_shape(shape: &ClassShape) -> ClassInfo {
    ClassInfo {
        type_vars: shape.type_vars.clone(),
        fundeps: shape.fundeps.clone(),
        superclasses: shape.superclasses.clone(),
    }
}

pub fn instance_from_shape(
    shape: &InstanceShape,
) -> crate::typecheck_db::passes::instance_index::Instance {
    crate::typecheck_db::passes::instance_index::Instance {
        class: shape.class.clone(),
        types: shape.types.clone(),
        context: shape.context.clone(),
        vars: shape.vars.clone(),
        chained: shape.chained,
    }
}

// ============================================================================
// decl_key helpers
// ============================================================================

/// Stable kind-prefixed decl key for a non-value decl. Instances and
/// derives (which have no user-given name) get content-hashed keys.
pub fn decl_key_for_nonvalue(decl: &Decl) -> (String, String) {
    match decl {
        Decl::Data { name, .. } => {
            let n = util::resolve_symbol(name.value.symbol());
            (format!("d__{n}"), format!("data {n}"))
        }
        Decl::Newtype { name, .. } => {
            let n = util::resolve_symbol(name.value.symbol());
            (format!("n__{n}"), format!("newtype {n}"))
        }
        Decl::TypeAlias { name, .. } => {
            let n = util::resolve_symbol(name.value.symbol());
            (format!("ta__{n}"), format!("type {n}"))
        }
        Decl::Class { name, .. } => {
            let n = util::resolve_symbol(name.value.symbol());
            (format!("c__{n}"), format!("class {n}"))
        }
        Decl::Instance { class_name, types, .. } | Decl::Derive { class_name, types, .. } => {
            let class_qi = class_name.to_qi();
            let class_debug = format!(
                "{}{}",
                class_qi
                    .module
                    .map(util::resolve_symbol)
                    .map(|m| format!("{m}."))
                    .unwrap_or_default(),
                util::resolve_symbol(class_qi.name),
            );
            // Hash the class + head types for a stable, content-derived
            // key.
            let type_ops = TypeOpMap::default();
            let type_tys: Vec<Type> =
                types.iter().map(|t| convert_type_expr(t, &type_ops)).collect();
            let mut h = blake3::Hasher::new();
            h.update(b"instance_key_v1");
            h.update(class_debug.as_bytes());
            h.update(&[0u8]);
            let types_bytes = bincode::serialize(&type_tys).unwrap_or_default();
            h.update(&(types_bytes.len() as u32).to_le_bytes());
            h.update(&types_bytes);
            let digest = h.finalize();
            let hex: String = digest.as_bytes().iter().take(8).map(|b| format!("{b:02x}")).collect();

            let types_debug: Vec<String> =
                type_tys.iter().map(|t| format!("{t}")).collect();
            let debug = format!("instance {class_debug} {}", types_debug.join(" "));
            (format!("i__{hex}"), debug)
        }
        Decl::Fixity { operator, .. } => {
            let op = util::resolve_symbol(operator.value.symbol());
            (format!("f__{op}"), format!("fixity {op}"))
        }
        Decl::Foreign { name, .. } => {
            let n = util::resolve_symbol(name.value.symbol());
            (format!("fv__{n}"), format!("foreign import {n}"))
        }
        Decl::ForeignData { name, .. } => {
            let n = util::resolve_symbol(name.value.symbol());
            (format!("ft__{n}"), format!("foreign data {n}"))
        }
        Decl::Value { .. } | Decl::TypeSignature { .. } => {
            unreachable!("decl_key_for_nonvalue called on value-kind decl")
        }
    }
}

/// Hash the decl's source-text slice. Caller provides the full
/// module source; this helper slices by span.
pub fn decl_source_hash(source: &str, decl: &Decl) -> [u8; 32] {
    let span = decl.span();
    let slice = source.get(span.start..span.end).unwrap_or("");
    hash_bytes(slice.as_bytes())
}

/// Did this decl kind emit a non-value cache entry? Used by the
/// driver to skip dispatch when encountering Value or TypeSignature.
pub fn is_nonvalue_kind(decl: &Decl) -> bool {
    !matches!(decl, Decl::Value { .. } | Decl::TypeSignature { .. })
}

#[allow(dead_code)]
pub fn _touch(_: &cst::Module) {}
