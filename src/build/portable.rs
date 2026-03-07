//! Portable (serializable) representations of typechecker types.
//!
//! Uses a deduplicated string table so each symbol is stored once.
//! Symbol references are u32 indices into the string table.

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::cst::{Associativity, QualifiedIdent};
use crate::interner;
use crate::typechecker::registry::ModuleExports;
use crate::typechecker::types::{Role, Scheme, TyVarId, Type};

// ===== String Table =====

/// Builds a deduplicated string table during serialization.
/// Each unique Symbol is resolved exactly once.
pub struct StringTableBuilder {
    strings: Vec<String>,
    sym_to_idx: HashMap<interner::Symbol, u32>,
}

impl StringTableBuilder {
    pub fn new() -> Self {
        Self {
            strings: Vec::new(),
            sym_to_idx: HashMap::new(),
        }
    }

    pub fn add(&mut self, sym: interner::Symbol) -> u32 {
        if let Some(&idx) = self.sym_to_idx.get(&sym) {
            return idx;
        }
        let s = interner::resolve(sym).unwrap_or_default();
        let idx = self.strings.len() as u32;
        self.strings.push(s);
        self.sym_to_idx.insert(sym, idx);
        idx
    }

    pub fn into_table(self) -> Vec<String> {
        self.strings
    }
}

/// Reads from a string table during deserialization.
/// All strings are interned in one batch.
pub struct StringTableReader {
    symbols: Vec<interner::Symbol>,
}

impl StringTableReader {
    pub fn new(table: Vec<String>) -> Self {
        let symbols = interner::intern_batch(&table);
        Self { symbols }
    }

    pub fn sym(&self, idx: u32) -> interner::Symbol {
        self.symbols[idx as usize]
    }
}

// ===== Portable QualifiedIdent =====

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PQI {
    pub module: Option<u32>,
    pub name: u32,
}

fn conv_qi(qi: &QualifiedIdent, st: &mut StringTableBuilder) -> PQI {
    PQI {
        module: qi.module.map(|s| st.add(s)),
        name: st.add(qi.name),
    }
}

fn rest_qi(p: &PQI, st: &StringTableReader) -> QualifiedIdent {
    QualifiedIdent {
        module: p.module.map(|i| st.sym(i)),
        name: st.sym(p.name),
    }
}

// ===== Portable Type =====

#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum PType {
    Unif(u32),
    Var(u32),
    Con(PQI),
    App(Box<PType>, Box<PType>),
    Fun(Box<PType>, Box<PType>),
    Forall(Vec<(u32, bool)>, Box<PType>),
    Record(Vec<(u32, PType)>, Option<Box<PType>>),
    TypeString(u32),
    TypeInt(i64),
}

fn conv_type(t: &Type, st: &mut StringTableBuilder) -> PType {
    match t {
        Type::Unif(id) => PType::Unif(id.0),
        Type::Var(s) => PType::Var(st.add(*s)),
        Type::Con(qi) => PType::Con(conv_qi(qi, st)),
        Type::App(f, a) => PType::App(
            Box::new(conv_type(f, st)),
            Box::new(conv_type(a, st)),
        ),
        Type::Fun(a, b) => PType::Fun(
            Box::new(conv_type(a, st)),
            Box::new(conv_type(b, st)),
        ),
        Type::Forall(vars, body) => PType::Forall(
            vars.iter().map(|(s, v)| (st.add(*s), *v)).collect(),
            Box::new(conv_type(body, st)),
        ),
        Type::Record(fields, tail) => PType::Record(
            fields.iter().map(|(s, t)| (st.add(*s), conv_type(t, st))).collect(),
            tail.as_ref().map(|t| Box::new(conv_type(t, st))),
        ),
        Type::TypeString(s) => PType::TypeString(st.add(*s)),
        Type::TypeInt(i) => PType::TypeInt(*i),
    }
}

fn rest_type(p: &PType, st: &StringTableReader) -> Type {
    match p {
        PType::Unif(id) => Type::Unif(TyVarId(*id)),
        PType::Var(s) => Type::Var(st.sym(*s)),
        PType::Con(qi) => Type::Con(rest_qi(qi, st)),
        PType::App(f, a) => Type::App(
            Box::new(rest_type(f, st)),
            Box::new(rest_type(a, st)),
        ),
        PType::Fun(a, b) => Type::Fun(
            Box::new(rest_type(a, st)),
            Box::new(rest_type(b, st)),
        ),
        PType::Forall(vars, body) => Type::Forall(
            vars.iter().map(|(s, v)| (st.sym(*s), *v)).collect(),
            Box::new(rest_type(body, st)),
        ),
        PType::Record(fields, tail) => Type::Record(
            fields.iter().map(|(s, t)| (st.sym(*s), rest_type(t, st))).collect(),
            tail.as_ref().map(|t| Box::new(rest_type(t, st))),
        ),
        PType::TypeString(s) => Type::TypeString(st.sym(*s)),
        PType::TypeInt(i) => Type::TypeInt(*i),
    }
}

// ===== Portable Scheme =====

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PScheme {
    pub forall_vars: Vec<u32>,
    pub ty: PType,
}

fn conv_scheme(s: &Scheme, st: &mut StringTableBuilder) -> PScheme {
    PScheme {
        forall_vars: s.forall_vars.iter().map(|v| st.add(*v)).collect(),
        ty: conv_type(&s.ty, st),
    }
}

fn rest_scheme(p: &PScheme, st: &StringTableReader) -> Scheme {
    Scheme {
        forall_vars: p.forall_vars.iter().map(|v| st.sym(*v)).collect(),
        ty: rest_type(&p.ty, st),
    }
}

// ===== Portable Associativity =====

#[derive(Serialize, Deserialize, Clone, Copy, Debug)]
pub enum PAssociativity {
    Left,
    Right,
    None,
}

fn conv_assoc(a: &Associativity) -> PAssociativity {
    match a {
        Associativity::Left => PAssociativity::Left,
        Associativity::Right => PAssociativity::Right,
        Associativity::None => PAssociativity::None,
    }
}

fn rest_assoc(p: &PAssociativity) -> Associativity {
    match p {
        PAssociativity::Left => Associativity::Left,
        PAssociativity::Right => Associativity::Right,
        PAssociativity::None => Associativity::None,
    }
}

// ===== Portable Role =====

#[derive(Serialize, Deserialize, Clone, Copy, Debug)]
pub enum PRole {
    Phantom,
    Representational,
    Nominal,
}

fn conv_role(r: &Role) -> PRole {
    match r {
        Role::Phantom => PRole::Phantom,
        Role::Representational => PRole::Representational,
        Role::Nominal => PRole::Nominal,
    }
}

fn rest_role(p: &PRole) -> Role {
    match p {
        PRole::Phantom => Role::Phantom,
        PRole::Representational => Role::Representational,
        PRole::Nominal => Role::Nominal,
    }
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
    pub value_origins: HashMap<u32, u32>,
    pub type_origins: HashMap<u32, u32>,
    pub class_origins: HashMap<u32, u32>,
    pub operator_class_targets: HashMap<u32, u32>,
    pub class_fundeps: HashMap<u32, (Vec<u32>, Vec<(Vec<usize>, Vec<usize>)>)>,
    pub type_con_arities: HashMap<PQI, usize>,
    pub type_roles: HashMap<u32, Vec<PRole>>,
    pub newtype_names: HashSet<u32>,
    pub signature_constraints: HashMap<PQI, Vec<(PQI, Vec<PType>)>>,
    pub type_kinds: HashMap<u32, PType>,
    pub class_type_kinds: HashMap<u32, PType>,
    pub partial_dischargers: HashSet<u32>,
    pub self_referential_aliases: HashSet<u32>,
    pub class_superclasses: HashMap<PQI, (Vec<u32>, Vec<(PQI, Vec<PType>)>)>,
    pub method_own_constraints: HashMap<PQI, Vec<u32>>,
}

impl PModuleExports {
    pub fn from_exports(e: &ModuleExports, st: &mut StringTableBuilder) -> Self {
        PModuleExports {
            values: e.values.iter().map(|(k, v)| (conv_qi(k, st), conv_scheme(v, st))).collect(),
            class_methods: e.class_methods.iter().map(|(k, (c, vs))| {
                (conv_qi(k, st), (conv_qi(c, st), vs.iter().map(|v| conv_qi(v, st)).collect()))
            }).collect(),
            data_constructors: e.data_constructors.iter().map(|(k, v)| {
                (conv_qi(k, st), v.iter().map(|qi| conv_qi(qi, st)).collect())
            }).collect(),
            ctor_details: e.ctor_details.iter().map(|(k, (p, vs, ts))| {
                (conv_qi(k, st), (conv_qi(p, st), vs.iter().map(|v| conv_qi(v, st)).collect(), ts.iter().map(|t| conv_type(t, st)).collect()))
            }).collect(),
            instances: e.instances.iter().map(|(k, v)| {
                (conv_qi(k, st), v.iter().map(|(ts, cs)| {
                    (ts.iter().map(|t| conv_type(t, st)).collect(), cs.iter().map(|(c, ts2)| {
                        (conv_qi(c, st), ts2.iter().map(|t| conv_type(t, st)).collect())
                    }).collect())
                }).collect())
            }).collect(),
            type_operators: e.type_operators.iter().map(|(k, v)| (conv_qi(k, st), conv_qi(v, st))).collect(),
            value_fixities: e.value_fixities.iter().map(|(k, (a, p))| (conv_qi(k, st), (conv_assoc(a), *p))).collect(),
            type_fixities: e.type_fixities.iter().map(|(k, (a, p))| (conv_qi(k, st), (conv_assoc(a), *p))).collect(),
            function_op_aliases: e.function_op_aliases.iter().map(|qi| conv_qi(qi, st)).collect(),
            value_operator_targets: e.value_operator_targets.iter().map(|(k, v)| (conv_qi(k, st), conv_qi(v, st))).collect(),
            constrained_class_methods: e.constrained_class_methods.iter().map(|qi| conv_qi(qi, st)).collect(),
            type_aliases: e.type_aliases.iter().map(|(k, (ps, ty))| {
                (conv_qi(k, st), (ps.iter().map(|p| conv_qi(p, st)).collect(), conv_type(ty, st)))
            }).collect(),
            class_param_counts: e.class_param_counts.iter().map(|(k, v)| (conv_qi(k, st), *v)).collect(),
            value_origins: e.value_origins.iter().map(|(k, v)| (st.add(*k), st.add(*v))).collect(),
            type_origins: e.type_origins.iter().map(|(k, v)| (st.add(*k), st.add(*v))).collect(),
            class_origins: e.class_origins.iter().map(|(k, v)| (st.add(*k), st.add(*v))).collect(),
            operator_class_targets: e.operator_class_targets.iter().map(|(k, v)| (st.add(*k), st.add(*v))).collect(),
            class_fundeps: e.class_fundeps.iter().map(|(k, (vs, fs))| {
                (st.add(*k), (vs.iter().map(|v| st.add(*v)).collect(), fs.clone()))
            }).collect(),
            type_con_arities: e.type_con_arities.iter().map(|(k, v)| (conv_qi(k, st), *v)).collect(),
            type_roles: e.type_roles.iter().map(|(k, v)| (st.add(*k), v.iter().map(conv_role).collect())).collect(),
            newtype_names: e.newtype_names.iter().map(|s| st.add(*s)).collect(),
            signature_constraints: e.signature_constraints.iter().map(|(k, v)| {
                (conv_qi(k, st), v.iter().map(|(c, ts)| {
                    (conv_qi(c, st), ts.iter().map(|t| conv_type(t, st)).collect())
                }).collect())
            }).collect(),
            type_kinds: e.type_kinds.iter().map(|(k, v)| (st.add(*k), conv_type(v, st))).collect(),
            class_type_kinds: e.class_type_kinds.iter().map(|(k, v)| (st.add(*k), conv_type(v, st))).collect(),
            partial_dischargers: e.partial_dischargers.iter().map(|s| st.add(*s)).collect(),
            self_referential_aliases: e.self_referential_aliases.iter().map(|s| st.add(*s)).collect(),
            class_superclasses: e.class_superclasses.iter().map(|(k, (vs, cs))| {
                (conv_qi(k, st), (vs.iter().map(|v| st.add(*v)).collect(), cs.iter().map(|(c, ts)| {
                    (conv_qi(c, st), ts.iter().map(|t| conv_type(t, st)).collect())
                }).collect()))
            }).collect(),
            method_own_constraints: e.method_own_constraints.iter().map(|(k, v)| {
                (conv_qi(k, st), v.iter().map(|s| st.add(*s)).collect())
            }).collect(),
        }
    }

    pub fn to_exports(&self, st: &StringTableReader) -> ModuleExports {
        ModuleExports {
            values: self.values.iter().map(|(k, v)| (rest_qi(k, st), rest_scheme(v, st))).collect(),
            class_methods: self.class_methods.iter().map(|(k, (c, vs))| {
                (rest_qi(k, st), (rest_qi(c, st), vs.iter().map(|v| rest_qi(v, st)).collect()))
            }).collect(),
            data_constructors: self.data_constructors.iter().map(|(k, v)| {
                (rest_qi(k, st), v.iter().map(|qi| rest_qi(qi, st)).collect())
            }).collect(),
            ctor_details: self.ctor_details.iter().map(|(k, (p, vs, ts))| {
                (rest_qi(k, st), (rest_qi(p, st), vs.iter().map(|v| rest_qi(v, st)).collect(), ts.iter().map(|t| rest_type(t, st)).collect()))
            }).collect(),
            instances: self.instances.iter().map(|(k, v)| {
                (rest_qi(k, st), v.iter().map(|(ts, cs)| {
                    (ts.iter().map(|t| rest_type(t, st)).collect(), cs.iter().map(|(c, ts2)| {
                        (rest_qi(c, st), ts2.iter().map(|t| rest_type(t, st)).collect())
                    }).collect())
                }).collect())
            }).collect(),
            type_operators: self.type_operators.iter().map(|(k, v)| (rest_qi(k, st), rest_qi(v, st))).collect(),
            value_fixities: self.value_fixities.iter().map(|(k, (a, p))| (rest_qi(k, st), (rest_assoc(a), *p))).collect(),
            type_fixities: self.type_fixities.iter().map(|(k, (a, p))| (rest_qi(k, st), (rest_assoc(a), *p))).collect(),
            function_op_aliases: self.function_op_aliases.iter().map(|qi| rest_qi(qi, st)).collect(),
            value_operator_targets: self.value_operator_targets.iter().map(|(k, v)| (rest_qi(k, st), rest_qi(v, st))).collect(),
            constrained_class_methods: self.constrained_class_methods.iter().map(|qi| rest_qi(qi, st)).collect(),
            type_aliases: self.type_aliases.iter().map(|(k, (ps, ty))| {
                (rest_qi(k, st), (ps.iter().map(|p| rest_qi(p, st)).collect(), rest_type(ty, st)))
            }).collect(),
            class_param_counts: self.class_param_counts.iter().map(|(k, v)| (rest_qi(k, st), *v)).collect(),
            value_origins: self.value_origins.iter().map(|(k, v)| (st.sym(*k), st.sym(*v))).collect(),
            type_origins: self.type_origins.iter().map(|(k, v)| (st.sym(*k), st.sym(*v))).collect(),
            class_origins: self.class_origins.iter().map(|(k, v)| (st.sym(*k), st.sym(*v))).collect(),
            operator_class_targets: self.operator_class_targets.iter().map(|(k, v)| (st.sym(*k), st.sym(*v))).collect(),
            class_fundeps: self.class_fundeps.iter().map(|(k, (vs, fs))| {
                (st.sym(*k), (vs.iter().map(|v| st.sym(*v)).collect(), fs.clone()))
            }).collect(),
            type_con_arities: self.type_con_arities.iter().map(|(k, v)| (rest_qi(k, st), *v)).collect(),
            type_roles: self.type_roles.iter().map(|(k, v)| (st.sym(*k), v.iter().map(rest_role).collect())).collect(),
            newtype_names: self.newtype_names.iter().map(|s| st.sym(*s)).collect(),
            signature_constraints: self.signature_constraints.iter().map(|(k, v)| {
                (rest_qi(k, st), v.iter().map(|(c, ts)| {
                    (rest_qi(c, st), ts.iter().map(|t| rest_type(t, st)).collect())
                }).collect())
            }).collect(),
            type_kinds: self.type_kinds.iter().map(|(k, v)| (st.sym(*k), rest_type(v, st))).collect(),
            class_type_kinds: self.class_type_kinds.iter().map(|(k, v)| (st.sym(*k), rest_type(v, st))).collect(),
            partial_dischargers: self.partial_dischargers.iter().map(|s| st.sym(*s)).collect(),
            self_referential_aliases: self.self_referential_aliases.iter().map(|s| st.sym(*s)).collect(),
            class_superclasses: self.class_superclasses.iter().map(|(k, (vs, cs))| {
                (rest_qi(k, st), (vs.iter().map(|v| st.sym(*v)).collect(), cs.iter().map(|(c, ts)| {
                    (rest_qi(c, st), ts.iter().map(|t| rest_type(t, st)).collect())
                }).collect()))
            }).collect(),
            method_own_constraints: self.method_own_constraints.iter().map(|(k, v)| {
                (rest_qi(k, st), v.iter().map(|s| st.sym(*s)).collect())
            }).collect(),
        }
    }
}

