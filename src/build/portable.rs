//! Portable (serializable) representations of typechecker types.
//!
//! These mirror the core types but use `String` instead of `Symbol`
//! (which is process-local). Used for on-disk caching of ModuleExports.

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::cst::{Associativity, QualifiedIdent};
use crate::interner;
use crate::typechecker::registry::ModuleExports;
use crate::typechecker::types::{Role, Scheme, TyVarId, Type};

// ===== Helper conversions =====

fn sym_to_s(s: interner::Symbol) -> String {
    interner::resolve(s).unwrap_or_default().to_string()
}

fn s_to_sym(s: &str) -> interner::Symbol {
    interner::intern(s)
}

// ===== Portable QualifiedIdent =====

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PQI {
    pub module: Option<String>,
    pub name: String,
}

impl From<&QualifiedIdent> for PQI {
    fn from(qi: &QualifiedIdent) -> Self {
        PQI {
            module: qi.module.map(sym_to_s),
            name: sym_to_s(qi.name),
        }
    }
}

impl From<&PQI> for QualifiedIdent {
    fn from(p: &PQI) -> Self {
        QualifiedIdent {
            module: p.module.as_ref().map(|s| s_to_sym(s)),
            name: s_to_sym(&p.name),
        }
    }
}

// ===== Portable Type =====

#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum PType {
    Unif(u32),
    Var(String),
    Con(PQI),
    App(Box<PType>, Box<PType>),
    Fun(Box<PType>, Box<PType>),
    Forall(Vec<(String, bool)>, Box<PType>),
    Record(Vec<(String, PType)>, Option<Box<PType>>),
    TypeString(String),
    TypeInt(i64),
}

impl From<&Type> for PType {
    fn from(t: &Type) -> Self {
        match t {
            Type::Unif(id) => PType::Unif(id.0),
            Type::Var(s) => PType::Var(sym_to_s(*s)),
            Type::Con(qi) => PType::Con(qi.into()),
            Type::App(f, a) => PType::App(Box::new(f.as_ref().into()), Box::new(a.as_ref().into())),
            Type::Fun(a, b) => PType::Fun(Box::new(a.as_ref().into()), Box::new(b.as_ref().into())),
            Type::Forall(vars, body) => PType::Forall(
                vars.iter().map(|(s, v)| (sym_to_s(*s), *v)).collect(),
                Box::new(body.as_ref().into()),
            ),
            Type::Record(fields, tail) => PType::Record(
                fields.iter().map(|(s, t)| (sym_to_s(*s), t.into())).collect(),
                tail.as_ref().map(|t| Box::new(t.as_ref().into())),
            ),
            Type::TypeString(s) => PType::TypeString(sym_to_s(*s)),
            Type::TypeInt(i) => PType::TypeInt(*i),
        }
    }
}

impl From<&PType> for Type {
    fn from(p: &PType) -> Self {
        match p {
            PType::Unif(id) => Type::Unif(TyVarId(*id)),
            PType::Var(s) => Type::Var(s_to_sym(s)),
            PType::Con(qi) => Type::Con(qi.into()),
            PType::App(f, a) => Type::App(Box::new(f.as_ref().into()), Box::new(a.as_ref().into())),
            PType::Fun(a, b) => Type::Fun(Box::new(a.as_ref().into()), Box::new(b.as_ref().into())),
            PType::Forall(vars, body) => Type::Forall(
                vars.iter().map(|(s, v)| (s_to_sym(s), *v)).collect(),
                Box::new(body.as_ref().into()),
            ),
            PType::Record(fields, tail) => Type::Record(
                fields.iter().map(|(s, t)| (s_to_sym(s), t.into())).collect(),
                tail.as_ref().map(|t| Box::new(t.as_ref().into())),
            ),
            PType::TypeString(s) => Type::TypeString(s_to_sym(s)),
            PType::TypeInt(i) => Type::TypeInt(*i),
        }
    }
}

// ===== Portable Scheme =====

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PScheme {
    pub forall_vars: Vec<String>,
    pub ty: PType,
}

impl From<&Scheme> for PScheme {
    fn from(s: &Scheme) -> Self {
        PScheme {
            forall_vars: s.forall_vars.iter().map(|v| sym_to_s(*v)).collect(),
            ty: (&s.ty).into(),
        }
    }
}

impl From<&PScheme> for Scheme {
    fn from(p: &PScheme) -> Self {
        Scheme {
            forall_vars: p.forall_vars.iter().map(|s| s_to_sym(s)).collect(),
            ty: (&p.ty).into(),
        }
    }
}

// ===== Portable Associativity =====

#[derive(Serialize, Deserialize, Clone, Copy, Debug)]
pub enum PAssociativity {
    Left,
    Right,
    None,
}

impl From<&Associativity> for PAssociativity {
    fn from(a: &Associativity) -> Self {
        match a {
            Associativity::Left => PAssociativity::Left,
            Associativity::Right => PAssociativity::Right,
            Associativity::None => PAssociativity::None,
        }
    }
}

impl From<&PAssociativity> for Associativity {
    fn from(p: &PAssociativity) -> Self {
        match p {
            PAssociativity::Left => Associativity::Left,
            PAssociativity::Right => Associativity::Right,
            PAssociativity::None => Associativity::None,
        }
    }
}

// ===== Portable Role =====

#[derive(Serialize, Deserialize, Clone, Copy, Debug)]
pub enum PRole {
    Phantom,
    Representational,
    Nominal,
}

impl From<&Role> for PRole {
    fn from(r: &Role) -> Self {
        match r {
            Role::Phantom => PRole::Phantom,
            Role::Representational => PRole::Representational,
            Role::Nominal => PRole::Nominal,
        }
    }
}

impl From<&PRole> for Role {
    fn from(p: &PRole) -> Self {
        match p {
            PRole::Phantom => Role::Phantom,
            PRole::Representational => Role::Representational,
            PRole::Nominal => Role::Nominal,
        }
    }
}

// ===== Collection conversion helpers =====

fn map_qi_scheme(m: &HashMap<QualifiedIdent, Scheme>) -> HashMap<PQI, PScheme> {
    m.iter().map(|(k, v)| (k.into(), v.into())).collect()
}

fn unmap_qi_scheme(m: &HashMap<PQI, PScheme>) -> HashMap<QualifiedIdent, Scheme> {
    m.iter().map(|(k, v)| (k.into(), v.into())).collect()
}

fn map_qi_qi(m: &HashMap<QualifiedIdent, QualifiedIdent>) -> HashMap<PQI, PQI> {
    m.iter().map(|(k, v)| (k.into(), v.into())).collect()
}

fn unmap_qi_qi(m: &HashMap<PQI, PQI>) -> HashMap<QualifiedIdent, QualifiedIdent> {
    m.iter().map(|(k, v)| (k.into(), v.into())).collect()
}

fn map_qi_vec_qi(m: &HashMap<QualifiedIdent, Vec<QualifiedIdent>>) -> HashMap<PQI, Vec<PQI>> {
    m.iter().map(|(k, v)| (k.into(), v.iter().map(|qi| qi.into()).collect())).collect()
}

fn unmap_qi_vec_qi(m: &HashMap<PQI, Vec<PQI>>) -> HashMap<QualifiedIdent, Vec<QualifiedIdent>> {
    m.iter().map(|(k, v)| (k.into(), v.iter().map(|qi| qi.into()).collect())).collect()
}

fn map_set_qi(s: &HashSet<QualifiedIdent>) -> HashSet<PQI> {
    s.iter().map(|qi| qi.into()).collect()
}

fn unmap_set_qi(s: &HashSet<PQI>) -> HashSet<QualifiedIdent> {
    s.iter().map(|qi| qi.into()).collect()
}

fn map_qi_usize(m: &HashMap<QualifiedIdent, usize>) -> HashMap<PQI, usize> {
    m.iter().map(|(k, v)| (k.into(), *v)).collect()
}

fn unmap_qi_usize(m: &HashMap<PQI, usize>) -> HashMap<QualifiedIdent, usize> {
    m.iter().map(|(k, v)| (k.into(), *v)).collect()
}

fn map_sym_sym(m: &HashMap<interner::Symbol, interner::Symbol>) -> HashMap<String, String> {
    m.iter().map(|(k, v)| (sym_to_s(*k), sym_to_s(*v))).collect()
}

fn unmap_sym_sym(m: &HashMap<String, String>) -> HashMap<interner::Symbol, interner::Symbol> {
    m.iter().map(|(k, v)| (s_to_sym(k), s_to_sym(v))).collect()
}

fn map_set_sym(s: &HashSet<interner::Symbol>) -> HashSet<String> {
    s.iter().map(|sym| sym_to_s(*sym)).collect()
}

fn unmap_set_sym(s: &HashSet<String>) -> HashSet<interner::Symbol> {
    s.iter().map(|s| s_to_sym(s)).collect()
}

fn map_sym_type(m: &HashMap<interner::Symbol, Type>) -> HashMap<String, PType> {
    m.iter().map(|(k, v)| (sym_to_s(*k), v.into())).collect()
}

fn unmap_sym_type(m: &HashMap<String, PType>) -> HashMap<interner::Symbol, Type> {
    m.iter().map(|(k, v)| (s_to_sym(k), v.into())).collect()
}

fn map_sym_roles(m: &HashMap<interner::Symbol, Vec<Role>>) -> HashMap<String, Vec<PRole>> {
    m.iter().map(|(k, v)| (sym_to_s(*k), v.iter().map(|r| r.into()).collect())).collect()
}

fn unmap_sym_roles(m: &HashMap<String, Vec<PRole>>) -> HashMap<interner::Symbol, Vec<Role>> {
    m.iter().map(|(k, v)| (s_to_sym(k), v.iter().map(|r| r.into()).collect())).collect()
}

// ===== Portable ModuleExports =====

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PModuleExports {
    pub values: HashMap<PQI, PScheme>,
    pub class_methods: HashMap<PQI, (PQI, Vec<PQI>)>,
    pub data_constructors: HashMap<PQI, Vec<PQI>>,
    pub ctor_details: HashMap<PQI, (PQI, Vec<PQI>, Vec<PType>)>,
    pub instances: HashMap<PQI, Vec<(Vec<PType>, Vec<(PQI, Vec<PType>)>)>>,
    pub type_operators: HashMap<PQI, PQI>,
    pub value_fixities: HashMap<PQI, (PAssociativity, u8)>,
    pub type_fixities: HashMap<PQI, (PAssociativity, u8)>,
    pub function_op_aliases: HashSet<PQI>,
    pub value_operator_targets: HashMap<PQI, PQI>,
    pub constrained_class_methods: HashSet<PQI>,
    pub type_aliases: HashMap<PQI, (Vec<PQI>, PType)>,
    pub class_param_counts: HashMap<PQI, usize>,
    pub value_origins: HashMap<String, String>,
    pub type_origins: HashMap<String, String>,
    pub class_origins: HashMap<String, String>,
    pub operator_class_targets: HashMap<String, String>,
    pub class_fundeps: HashMap<String, (Vec<String>, Vec<(Vec<usize>, Vec<usize>)>)>,
    pub type_con_arities: HashMap<PQI, usize>,
    pub type_roles: HashMap<String, Vec<PRole>>,
    pub newtype_names: HashSet<String>,
    pub signature_constraints: HashMap<PQI, Vec<(PQI, Vec<PType>)>>,
    pub type_kinds: HashMap<String, PType>,
    pub class_type_kinds: HashMap<String, PType>,
    pub partial_dischargers: HashSet<String>,
    pub self_referential_aliases: HashSet<String>,
    pub class_superclasses: HashMap<PQI, (Vec<String>, Vec<(PQI, Vec<PType>)>)>,
    pub method_own_constraints: HashMap<PQI, Vec<String>>,
}

impl From<&ModuleExports> for PModuleExports {
    fn from(e: &ModuleExports) -> Self {
        PModuleExports {
            values: map_qi_scheme(&e.values),
            class_methods: e.class_methods.iter().map(|(k, (c, vs))| {
                (k.into(), (c.into(), vs.iter().map(|v| v.into()).collect()))
            }).collect(),
            data_constructors: map_qi_vec_qi(&e.data_constructors),
            ctor_details: e.ctor_details.iter().map(|(k, (p, vs, ts))| {
                (k.into(), (p.into(), vs.iter().map(|v| v.into()).collect(), ts.iter().map(|t| t.into()).collect()))
            }).collect(),
            instances: e.instances.iter().map(|(k, v)| {
                (k.into(), v.iter().map(|(ts, cs)| {
                    (ts.iter().map(|t| t.into()).collect(), cs.iter().map(|(c, ts2)| {
                        (c.into(), ts2.iter().map(|t| t.into()).collect())
                    }).collect())
                }).collect())
            }).collect(),
            type_operators: map_qi_qi(&e.type_operators),
            value_fixities: e.value_fixities.iter().map(|(k, (a, p))| (k.into(), (a.into(), *p))).collect(),
            type_fixities: e.type_fixities.iter().map(|(k, (a, p))| (k.into(), (a.into(), *p))).collect(),
            function_op_aliases: map_set_qi(&e.function_op_aliases),
            value_operator_targets: map_qi_qi(&e.value_operator_targets),
            constrained_class_methods: map_set_qi(&e.constrained_class_methods),
            type_aliases: e.type_aliases.iter().map(|(k, (ps, ty))| {
                (k.into(), (ps.iter().map(|p| p.into()).collect(), ty.into()))
            }).collect(),
            class_param_counts: map_qi_usize(&e.class_param_counts),
            value_origins: map_sym_sym(&e.value_origins),
            type_origins: map_sym_sym(&e.type_origins),
            class_origins: map_sym_sym(&e.class_origins),
            operator_class_targets: map_sym_sym(&e.operator_class_targets),
            class_fundeps: e.class_fundeps.iter().map(|(k, (vs, fs))| {
                (sym_to_s(*k), (vs.iter().map(|v| sym_to_s(*v)).collect(), fs.clone()))
            }).collect(),
            type_con_arities: map_qi_usize(&e.type_con_arities),
            type_roles: map_sym_roles(&e.type_roles),
            newtype_names: map_set_sym(&e.newtype_names),
            signature_constraints: e.signature_constraints.iter().map(|(k, v)| {
                (k.into(), v.iter().map(|(c, ts)| {
                    (c.into(), ts.iter().map(|t| t.into()).collect())
                }).collect())
            }).collect(),
            type_kinds: map_sym_type(&e.type_kinds),
            class_type_kinds: map_sym_type(&e.class_type_kinds),
            partial_dischargers: map_set_sym(&e.partial_dischargers),
            self_referential_aliases: map_set_sym(&e.self_referential_aliases),
            class_superclasses: e.class_superclasses.iter().map(|(k, (vs, cs))| {
                (k.into(), (vs.iter().map(|v| sym_to_s(*v)).collect(), cs.iter().map(|(c, ts)| {
                    (c.into(), ts.iter().map(|t| t.into()).collect())
                }).collect()))
            }).collect(),
            method_own_constraints: e.method_own_constraints.iter().map(|(k, v)| {
                (k.into(), v.iter().map(|s| sym_to_s(*s)).collect())
            }).collect(),
        }
    }
}

impl From<PModuleExports> for ModuleExports {
    fn from(p: PModuleExports) -> Self {
        ModuleExports {
            values: unmap_qi_scheme(&p.values),
            class_methods: p.class_methods.iter().map(|(k, (c, vs))| {
                (k.into(), (c.into(), vs.iter().map(|v| v.into()).collect()))
            }).collect(),
            data_constructors: unmap_qi_vec_qi(&p.data_constructors),
            ctor_details: p.ctor_details.iter().map(|(k, (par, vs, ts))| {
                (k.into(), (par.into(), vs.iter().map(|v| v.into()).collect(), ts.iter().map(|t| t.into()).collect()))
            }).collect(),
            instances: p.instances.iter().map(|(k, v)| {
                (k.into(), v.iter().map(|(ts, cs)| {
                    (ts.iter().map(|t| t.into()).collect(), cs.iter().map(|(c, ts2)| {
                        (c.into(), ts2.iter().map(|t| t.into()).collect())
                    }).collect())
                }).collect())
            }).collect(),
            type_operators: unmap_qi_qi(&p.type_operators),
            value_fixities: p.value_fixities.iter().map(|(k, (a, pr))| (k.into(), (a.into(), *pr))).collect(),
            type_fixities: p.type_fixities.iter().map(|(k, (a, pr))| (k.into(), (a.into(), *pr))).collect(),
            function_op_aliases: unmap_set_qi(&p.function_op_aliases),
            value_operator_targets: unmap_qi_qi(&p.value_operator_targets),
            constrained_class_methods: unmap_set_qi(&p.constrained_class_methods),
            type_aliases: p.type_aliases.iter().map(|(k, (ps, ty))| {
                (k.into(), (ps.iter().map(|p| p.into()).collect(), ty.into()))
            }).collect(),
            class_param_counts: unmap_qi_usize(&p.class_param_counts),
            value_origins: unmap_sym_sym(&p.value_origins),
            type_origins: unmap_sym_sym(&p.type_origins),
            class_origins: unmap_sym_sym(&p.class_origins),
            operator_class_targets: unmap_sym_sym(&p.operator_class_targets),
            class_fundeps: p.class_fundeps.iter().map(|(k, (vs, fs))| {
                (s_to_sym(k), (vs.iter().map(|v| s_to_sym(v)).collect(), fs.clone()))
            }).collect(),
            type_con_arities: unmap_qi_usize(&p.type_con_arities),
            type_roles: unmap_sym_roles(&p.type_roles),
            newtype_names: unmap_set_sym(&p.newtype_names),
            signature_constraints: p.signature_constraints.iter().map(|(k, v)| {
                (k.into(), v.iter().map(|(c, ts)| {
                    (c.into(), ts.iter().map(|t| t.into()).collect())
                }).collect())
            }).collect(),
            type_kinds: unmap_sym_type(&p.type_kinds),
            class_type_kinds: unmap_sym_type(&p.class_type_kinds),
            partial_dischargers: unmap_set_sym(&p.partial_dischargers),
            self_referential_aliases: unmap_set_sym(&p.self_referential_aliases),
            class_superclasses: p.class_superclasses.iter().map(|(k, (vs, cs))| {
                (k.into(), (vs.iter().map(|v| s_to_sym(v)).collect(), cs.iter().map(|(c, ts)| {
                    (c.into(), ts.iter().map(|t| t.into()).collect())
                }).collect()))
            }).collect(),
            method_own_constraints: p.method_own_constraints.iter().map(|(k, v)| {
                (k.into(), v.iter().map(|s| s_to_sym(s)).collect())
            }).collect(),
        }
    }
}

// ===== Portable Cache File =====

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PortableCacheFile {
    pub modules: HashMap<String, PortableCachedModule>,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PortableCachedModule {
    pub content_hash: u64,
    pub exports: PModuleExports,
    pub imports: Vec<String>,
}
