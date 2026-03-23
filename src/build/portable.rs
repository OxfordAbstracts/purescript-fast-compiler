//! Portable (serializable) representations of typechecker types.
//!
//! Uses a deduplicated string table so each symbol is stored once.
//! Symbol references are u32 indices into the string table.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use serde::{Deserialize, Serialize};

use crate::cst::{Associativity, QualifiedIdent};
use crate::interner;
use crate::names::{
    ClassName, ConstructorName, LabelName, NameLike, OpName, Qualified, TypeName, TypeOpName,
    TypeVarName, ValueName,
};
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

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

/// Convert a typed Qualified<N> to PQI for serialization.
fn conv_qn<N: NameLike>(q: &Qualified<N>, st: &mut StringTableBuilder) -> PQI {
    conv_qi(&q.to_qi(), st)
}

/// Convert PQI back to a typed Qualified<N> for deserialization.
fn rest_qn<N: NameLike>(p: &PQI, st: &StringTableReader) -> Qualified<N> {
    Qualified::from_qi(&rest_qi(p, st))
}

/// Convert a typed name wrapper (ValueName, TypeName, etc.) to a string table index.
fn conv_name<N: NameLike>(n: &N, st: &mut StringTableBuilder) -> u32 {
    st.add(n.symbol())
}

/// Convert a string table index back to a typed name wrapper.
fn rest_name<N: NameLike>(idx: u32, st: &StringTableReader) -> N {
    N::from_symbol(st.sym(idx))
}

fn conv_dict_expr(d: &crate::typechecker::registry::DictExpr, st: &mut StringTableBuilder) -> PDictExpr {
    use crate::typechecker::registry::DictExpr;
    match d {
        DictExpr::Var(name) => PDictExpr::Var(st.add(*name)),
        DictExpr::App(name, subs) => PDictExpr::App(
            st.add(*name),
            subs.iter().map(|s| conv_dict_expr(s, st)).collect(),
        ),
        DictExpr::ConstraintArg(_) => {
            // ConstraintArg is only used within a single module's codegen;
            // it should not appear in serialized portable format.
            PDictExpr::Var(st.add(crate::interner::intern("__constraint_arg")))
        }
        DictExpr::InlineIsSymbol(_) => {
            // InlineIsSymbol is only used within a single module's codegen;
            // it should not appear in serialized portable format.
            PDictExpr::Var(st.add(crate::interner::intern("__is_symbol")))
        }
        DictExpr::InlineReflectable(_) => {
            PDictExpr::Var(st.add(crate::interner::intern("__reflectable")))
        }
        DictExpr::ZeroCost => {
            PDictExpr::Var(st.add(crate::interner::intern("__zero_cost")))
        }
    }
}

fn rest_dict_expr(p: &PDictExpr, st: &StringTableReader) -> crate::typechecker::registry::DictExpr {
    use crate::typechecker::registry::DictExpr;
    match p {
        PDictExpr::Var(idx) => DictExpr::Var(st.sym(*idx)),
        PDictExpr::App(idx, subs) => DictExpr::App(
            st.sym(*idx),
            subs.iter().map(|s| rest_dict_expr(s, st)).collect(),
        ),
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
        Type::Var(s) => PType::Var(st.add(s.symbol())),
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
            vars.iter().map(|(s, v)| (st.add(s.symbol()), *v)).collect(),
            Box::new(conv_type(body, st)),
        ),
        Type::Record(fields, tail) => PType::Record(
            fields.iter().map(|(s, t)| (st.add(s.symbol()), conv_type(t, st))).collect(),
            tail.as_ref().map(|t| Box::new(conv_type(t, st))),
        ),
        Type::TypeString(s) => PType::TypeString(st.add(*s)),
        Type::TypeInt(i) => PType::TypeInt(*i),
    }
}

fn rest_type(p: &PType, st: &StringTableReader) -> Type {
    match p {
        PType::Unif(id) => Type::Unif(TyVarId(*id)),
        PType::Var(s) => Type::Var(TypeVarName::new(st.sym(*s))),
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
            vars.iter().map(|(s, v)| (TypeVarName::new(st.sym(*s)), *v)).collect(),
            Box::new(rest_type(body, st)),
        ),
        PType::Record(fields, tail) => Type::Record(
            fields.iter().map(|(s, t)| (LabelName::new(st.sym(*s)), rest_type(t, st))).collect(),
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
        forall_vars: s.forall_vars.iter().map(|v| st.add(v.symbol())).collect(),
        ty: conv_type(&s.ty, st),
    }
}

fn rest_scheme(p: &PScheme, st: &StringTableReader) -> Scheme {
    Scheme {
        forall_vars: p.forall_vars.iter().map(|v| TypeVarName::new(st.sym(*v))).collect(),
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

/// Portable DictExpr for serialization.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PDictExpr {
    Var(u32),
    App(u32, Vec<PDictExpr>),
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PModuleExports {
    pub values: BTreeMap<PQI, PScheme>,
    pub class_methods: BTreeMap<PQI, (PQI, Vec<PQI>)>,
    pub data_constructors: BTreeMap<PQI, Vec<PQI>>,
    pub ctor_details: BTreeMap<PQI, (PQI, Vec<PQI>, Vec<PType>)>,
    pub instances: BTreeMap<PQI, Vec<(Vec<PType>, Vec<(PQI, Vec<PType>)>, Option<u32>)>>,
    pub type_operators: BTreeMap<PQI, PQI>,
    pub value_fixities: BTreeMap<PQI, (PAssociativity, u8)>,
    pub type_fixities: BTreeMap<PQI, (PAssociativity, u8)>,
    pub function_op_aliases: BTreeSet<PQI>,
    pub value_operator_targets: BTreeMap<PQI, PQI>,
    pub constrained_class_methods: BTreeSet<PQI>,
    pub type_aliases: BTreeMap<PQI, (Vec<PQI>, PType)>,
    pub class_param_counts: BTreeMap<PQI, usize>,
    pub value_origins: BTreeMap<u32, u32>,
    pub type_origins: BTreeMap<u32, u32>,
    pub class_origins: BTreeMap<u32, u32>,
    pub operator_class_targets: BTreeMap<u32, u32>,
    pub class_fundeps: BTreeMap<u32, (Vec<u32>, Vec<(Vec<usize>, Vec<usize>)>)>,
    pub type_con_arities: BTreeMap<PQI, usize>,
    pub type_roles: BTreeMap<u32, Vec<PRole>>,
    pub newtype_names: BTreeSet<u32>,
    pub signature_constraints: BTreeMap<PQI, Vec<(PQI, Vec<PType>)>>,
    pub type_kinds: BTreeMap<u32, PType>,
    pub class_type_kinds: BTreeMap<u32, PType>,
    pub partial_dischargers: BTreeSet<u32>,
    #[serde(default)]
    pub partial_value_names: BTreeSet<u32>,
    pub self_referential_aliases: BTreeSet<u32>,
    pub class_superclasses: BTreeMap<PQI, (Vec<u32>, Vec<(PQI, Vec<PType>)>)>,
    pub method_own_constraints: BTreeMap<PQI, Vec<u32>>,
    /// Resolved dicts: span (start, end) → [(class_name, dict_expr)]
    #[serde(default)]
    pub resolved_dicts: Vec<((u64, u64), Vec<(u32, PDictExpr)>)>,
    /// Instance registry: (class_name, head_type_con) → instance_name
    #[serde(default)]
    pub instance_registry: Vec<((u32, u32), u32)>,
    /// Class method declaration order: class_name → [method_name, ...]
    #[serde(default)]
    pub class_method_order: BTreeMap<u32, Vec<u32>>,
}

impl PModuleExports {
    pub fn from_exports(e: &ModuleExports, st: &mut StringTableBuilder) -> Self {
        PModuleExports {
            values: e.values.iter().map(|(k, v)| (conv_qn(k, st), conv_scheme(v, st))).collect(),
            class_methods: e.class_methods.iter().map(|(k, (c, vs))| {
                (conv_qn(k, st), (conv_qn(c, st), vs.iter().map(|v| PQI { module: None, name: conv_name(v, st) }).collect()))
            }).collect(),
            data_constructors: e.data_constructors.iter().map(|(k, v)| {
                (conv_qn(k, st), v.iter().map(|qi| conv_qn(qi, st)).collect())
            }).collect(),
            ctor_details: e.ctor_details.iter().map(|(k, (p, vs, ts))| {
                (conv_qn(k, st), (conv_qn(p, st), vs.iter().map(|v| PQI { module: None, name: conv_name(v, st) }).collect(), ts.iter().map(|t| conv_type(t, st)).collect()))
            }).collect(),
            instances: e.instances.iter().map(|(k, v)| {
                (conv_qn(k, st), v.iter().map(|(ts, cs, inst_name)| {
                    (ts.iter().map(|t| conv_type(t, st)).collect(), cs.iter().map(|(c, ts2)| {
                        (conv_qn(c, st), ts2.iter().map(|t| conv_type(t, st)).collect())
                    }).collect(), inst_name.map(|s| st.add(s)))
                }).collect())
            }).collect(),
            type_operators: e.type_operators.iter().map(|(k, v)| (conv_qn(k, st), conv_qn(v, st))).collect(),
            value_fixities: e.value_fixities.iter().map(|(k, (a, p))| (conv_qn(k, st), (conv_assoc(a), *p))).collect(),
            type_fixities: e.type_fixities.iter().map(|(k, (a, p))| (conv_qn(k, st), (conv_assoc(a), *p))).collect(),
            function_op_aliases: e.function_op_aliases.iter().map(|qi| conv_qn(qi, st)).collect(),
            value_operator_targets: e.value_operator_targets.iter().map(|(k, v)| (conv_qn(k, st), conv_qn(v, st))).collect(),
            constrained_class_methods: e.constrained_class_methods.iter().map(|qi| conv_qn(qi, st)).collect(),
            type_aliases: e.type_aliases.iter().map(|(k, (ps, ty))| {
                (conv_qn(k, st), (ps.iter().map(|p| PQI { module: None, name: conv_name(p, st) }).collect(), conv_type(ty, st)))
            }).collect(),
            class_param_counts: e.class_param_counts.iter().map(|(k, v)| (conv_qn(k, st), *v)).collect(),
            value_origins: e.value_origins.iter().map(|(k, v)| (conv_name(k, st), st.add(*v))).collect(),
            type_origins: e.type_origins.iter().map(|(k, v)| (conv_name(k, st), st.add(*v))).collect(),
            class_origins: e.class_origins.iter().map(|(k, v)| (conv_name(k, st), st.add(*v))).collect(),
            operator_class_targets: e.operator_class_targets.iter().map(|(k, v)| (conv_name(k, st), conv_name(v, st))).collect(),
            class_fundeps: e.class_fundeps.iter().map(|(k, (vs, fs))| {
                (conv_name(k, st), (vs.iter().map(|v| conv_name(v, st)).collect(), fs.clone()))
            }).collect(),
            type_con_arities: e.type_con_arities.iter().map(|(k, v)| (conv_qn(k, st), *v)).collect(),
            type_roles: e.type_roles.iter().map(|(k, v)| (conv_name(k, st), v.iter().map(conv_role).collect())).collect(),
            newtype_names: e.newtype_names.iter().map(|s| conv_name(s, st)).collect(),
            signature_constraints: e.signature_constraints.iter().map(|(k, v)| {
                (conv_qn(k, st), v.iter().map(|(c, ts)| {
                    (conv_qn(c, st), ts.iter().map(|t| conv_type(t, st)).collect())
                }).collect())
            }).collect(),
            type_kinds: e.type_kinds.iter().map(|(k, v)| (conv_name(k, st), conv_type(v, st))).collect(),
            class_type_kinds: e.class_type_kinds.iter().map(|(k, v)| (conv_name(k, st), conv_type(v, st))).collect(),
            partial_dischargers: e.partial_dischargers.iter().map(|s| conv_name(s, st)).collect(),
            partial_value_names: e.partial_value_names.iter().map(|s| conv_name(s, st)).collect(),
            self_referential_aliases: e.self_referential_aliases.iter().map(|s| conv_name(s, st)).collect(),
            class_superclasses: e.class_superclasses.iter().map(|(k, (vs, cs))| {
                (conv_qn(k, st), (vs.iter().map(|v| conv_name(v, st)).collect(), cs.iter().map(|(c, ts)| {
                    (conv_qn(c, st), ts.iter().map(|t| conv_type(t, st)).collect())
                }).collect()))
            }).collect(),
            method_own_constraints: e.method_own_constraints.iter().map(|(k, v)| {
                (conv_qn(k, st), v.iter().map(|s| conv_name(s, st)).collect())
            }).collect(),
            resolved_dicts: e.resolved_dicts.iter().map(|(span, dicts)| {
                ((span.start as u64, span.end as u64), dicts.iter().map(|(class_name, dict_expr)| {
                    (st.add(*class_name), conv_dict_expr(dict_expr, st))
                }).collect())
            }).collect(),
            instance_registry: e.instance_registry.iter().map(|((class, head), inst)| {
                ((st.add(*class), st.add(*head)), st.add(*inst))
            }).collect(),
            class_method_order: e.class_method_order.iter().map(|(k, v)| {
                (conv_name(k, st), v.iter().map(|s| conv_name(s, st)).collect())
            }).collect(),
        }
    }

    pub fn to_exports(&self, st: &StringTableReader) -> ModuleExports {
        ModuleExports {
            values: self.values.iter().map(|(k, v)| (rest_qn::<ValueName>(k, st), rest_scheme(v, st))).collect(),
            class_methods: self.class_methods.iter().map(|(k, (c, vs))| {
                (rest_qn::<ValueName>(k, st), (rest_qn::<ClassName>(c, st), vs.iter().map(|v| rest_name::<TypeVarName>(v.name, st)).collect()))
            }).collect(),
            data_constructors: self.data_constructors.iter().map(|(k, v)| {
                (rest_qn::<TypeName>(k, st), v.iter().map(|qi| rest_qn::<ConstructorName>(qi, st)).collect())
            }).collect(),
            ctor_details: self.ctor_details.iter().map(|(k, (p, vs, ts))| {
                (rest_qn::<ConstructorName>(k, st), (rest_qn::<TypeName>(p, st), vs.iter().map(|v| rest_name::<TypeVarName>(v.name, st)).collect(), ts.iter().map(|t| rest_type(t, st)).collect()))
            }).collect(),
            instances: self.instances.iter().map(|(k, v)| {
                (rest_qn::<ClassName>(k, st), v.iter().map(|(ts, cs, inst_name)| {
                    (ts.iter().map(|t| rest_type(t, st)).collect(), cs.iter().map(|(c, ts2)| {
                        (rest_qn::<ClassName>(c, st), ts2.iter().map(|t| rest_type(t, st)).collect())
                    }).collect(), inst_name.as_ref().map(|s| st.sym(*s)))
                }).collect())
            }).collect(),
            type_operators: self.type_operators.iter().map(|(k, v)| (rest_qn::<TypeOpName>(k, st), rest_qn::<TypeName>(v, st))).collect(),
            value_fixities: self.value_fixities.iter().map(|(k, (a, p))| (rest_qn::<OpName>(k, st), (rest_assoc(a), *p))).collect(),
            type_fixities: self.type_fixities.iter().map(|(k, (a, p))| (rest_qn::<TypeOpName>(k, st), (rest_assoc(a), *p))).collect(),
            function_op_aliases: self.function_op_aliases.iter().map(|qi| rest_qn::<OpName>(qi, st)).collect(),
            value_operator_targets: self.value_operator_targets.iter().map(|(k, v)| (rest_qn::<OpName>(k, st), rest_qn::<ValueName>(v, st))).collect(),
            constrained_class_methods: self.constrained_class_methods.iter().map(|qi| rest_qn::<ValueName>(qi, st)).collect(),
            type_aliases: self.type_aliases.iter().map(|(k, (ps, ty))| {
                (rest_qn::<TypeName>(k, st), (ps.iter().map(|p| rest_name::<TypeVarName>(p.name, st)).collect(), rest_type(ty, st)))
            }).collect(),
            class_param_counts: self.class_param_counts.iter().map(|(k, v)| (rest_qn::<ClassName>(k, st), *v)).collect(),
            value_origins: self.value_origins.iter().map(|(k, v)| (rest_name::<ValueName>(*k, st), st.sym(*v))).collect(),
            type_origins: self.type_origins.iter().map(|(k, v)| (rest_name::<TypeName>(*k, st), st.sym(*v))).collect(),
            class_origins: self.class_origins.iter().map(|(k, v)| (rest_name::<ClassName>(*k, st), st.sym(*v))).collect(),
            operator_class_targets: self.operator_class_targets.iter().map(|(k, v)| (rest_name::<OpName>(*k, st), rest_name::<ValueName>(*v, st))).collect(),
            class_fundeps: self.class_fundeps.iter().map(|(k, (vs, fs))| {
                (rest_name::<ClassName>(*k, st), (vs.iter().map(|v| rest_name::<TypeVarName>(*v, st)).collect(), fs.clone()))
            }).collect(),
            type_con_arities: self.type_con_arities.iter().map(|(k, v)| (rest_qn::<TypeName>(k, st), *v)).collect(),
            type_roles: self.type_roles.iter().map(|(k, v)| (rest_name::<TypeName>(*k, st), v.iter().map(rest_role).collect())).collect(),
            newtype_names: self.newtype_names.iter().map(|s| rest_name::<TypeName>(*s, st)).collect(),
            signature_constraints: self.signature_constraints.iter().map(|(k, v)| {
                (rest_qn::<ValueName>(k, st), v.iter().map(|(c, ts)| {
                    (rest_qn::<ClassName>(c, st), ts.iter().map(|t| rest_type(t, st)).collect())
                }).collect())
            }).collect(),
            type_kinds: self.type_kinds.iter().map(|(k, v)| (rest_name::<TypeName>(*k, st), rest_type(v, st))).collect(),
            class_type_kinds: self.class_type_kinds.iter().map(|(k, v)| (rest_name::<ClassName>(*k, st), rest_type(v, st))).collect(),
            partial_dischargers: self.partial_dischargers.iter().map(|s| rest_name::<ValueName>(*s, st)).collect(),
            partial_value_names: self.partial_value_names.iter().map(|s| rest_name::<ValueName>(*s, st)).collect(),
            self_referential_aliases: self.self_referential_aliases.iter().map(|s| rest_name::<TypeName>(*s, st)).collect(),
            class_superclasses: self.class_superclasses.iter().map(|(k, (vs, cs))| {
                (rest_qn::<ClassName>(k, st), (vs.iter().map(|v| rest_name::<TypeVarName>(*v, st)).collect(), cs.iter().map(|(c, ts)| {
                    (rest_qn::<ClassName>(c, st), ts.iter().map(|t| rest_type(t, st)).collect())
                }).collect()))
            }).collect(),
            method_own_constraints: self.method_own_constraints.iter().map(|(k, v)| {
                (rest_qn::<ValueName>(k, st), v.iter().map(|s| rest_name::<ClassName>(*s, st)).collect())
            }).collect(),
            method_own_constraint_details: std::collections::HashMap::new(), // not persisted in portable format yet
            module_doc: Vec::new(), // not persisted in portable format
            instance_registry: self.instance_registry.iter().map(|((class, head), inst)| {
                ((st.sym(*class), st.sym(*head)), st.sym(*inst))
            }).collect(),
            instance_modules: std::collections::HashMap::new(),
            resolved_dicts: self.resolved_dicts.iter().map(|((start, end), dicts)| {
                (crate::span::Span { start: *start as usize, end: *end as usize }, dicts.iter().map(|(class_name, dict_expr)| {
                    (st.sym(*class_name), rest_dict_expr(dict_expr, st))
                }).collect())
            }).collect(),
            let_binding_constraints: std::collections::HashMap::new(),
            record_update_fields: std::collections::HashMap::new(),
            class_method_order: self.class_method_order.iter().map(|(&k, v)| {
                (rest_name::<ClassName>(k, st), v.iter().map(|s| rest_name::<ValueName>(*s, st)).collect())
            }).collect(),
            return_type_constraints: std::collections::HashMap::new(), // not persisted
            return_type_arrow_depth: std::collections::HashMap::new(), // not persisted
            instance_var_kinds: std::collections::HashMap::new(), // not persisted in portable format
        }
    }
}

