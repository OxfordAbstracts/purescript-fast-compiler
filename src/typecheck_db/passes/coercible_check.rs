//! Coercible-related structural checks.
//!
//! Runs as its own pass after import resolution. Detects:
//!
//! - **RoleMismatch**: `type role Foo r1 r2 …` declares roles that
//!   are more permissive than what the data/newtype's constructor
//!   fields actually allow. For each type var, declared must be
//!   `>=` inferred on the role lattice (Phantom < Representational
//!   < Nominal).
//!
//! - **InvalidCoercibleInstanceDeclaration**: user-written
//!   `instance Coercible a b` declarations are disallowed by
//!   PureScript — the Coercible class is solver-generated only.
//!
//! Does NOT perform general Coercible solving (newtype unwrapping,
//! same-ctor role decomposition, function decomposition). That's a
//! much larger pass that would need its own role environment in
//! the constraint solver; this pass limits itself to the
//! decidable-from-CST checks.

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::cst;
use crate::interner::Symbol;
use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Role {
    Phantom = 0,
    Representational = 1,
    Nominal = 2,
}

impl Role {
    /// Role composition: flow a type var's role through a nested
    /// position. Position Phantom absorbs everything; otherwise take
    /// the more-restrictive (max).
    fn compose(outer: Role, inner: Role) -> Role {
        if outer == Role::Phantom || inner == Role::Phantom {
            if outer == Role::Phantom && inner == Role::Phantom {
                Role::Phantom
            } else {
                // One is Phantom, the other isn't — preserves the
                // non-phantom. Matches old compiler semantics.
                if outer == Role::Phantom { inner } else { outer }
            }
        } else {
            std::cmp::max(outer, inner)
        }
    }

    fn from_ident(sym: Symbol) -> Option<Role> {
        match crate::interner::resolve(sym).as_deref() {
            Some("phantom") => Some(Role::Phantom),
            Some("representational") => Some(Role::Representational),
            Some("nominal") => Some(Role::Nominal),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoercibleError {
    pub span: Span,
    pub kind: CoercibleErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoercibleErrorKind {
    RoleMismatch(String),
    InvalidCoercibleInstanceDeclaration,
}

impl CoercibleErrorKind {
    pub fn code(&self) -> &'static str {
        match self {
            Self::RoleMismatch(_) => "RoleMismatch",
            Self::InvalidCoercibleInstanceDeclaration => "InvalidCoercibleInstanceDeclaration",
        }
    }
}

/// Per-type-constructor data used for role inference. Collected once
/// from the CST and shared between inference iterations.
struct DataInfo {
    /// Names of the type parameters (in declaration order).
    type_vars: Vec<Symbol>,
    /// Type expressions used as constructor field types. One entry
    /// per constructor field across every constructor of the decl.
    fields: Vec<cst::TypeExpr>,
}

pub fn check_module(module: &cst::Module) -> Vec<CoercibleError> {
    let mut errors: Vec<CoercibleError> = Vec::new();

    // Collect data / newtype bodies so role inference can walk their
    // fields. Standalone-kind-signed and role decls are stored
    // separately.
    let mut data: HashMap<Symbol, DataInfo> = HashMap::new();
    let mut declared: HashMap<Symbol, (Span, Vec<Role>)> = HashMap::new();
    let mut foreign_nominal: HashSet<Symbol> = HashSet::new();

    for d in &module.decls {
        match d {
            cst::Decl::Data {
                name,
                type_vars,
                constructors,
                kind_sig: cst::KindSigSource::None,
                is_role_decl: false,
                ..
            } => {
                let vars: Vec<Symbol> = type_vars.iter().map(|v| v.value.symbol()).collect();
                let fields: Vec<cst::TypeExpr> = constructors
                    .iter()
                    .flat_map(|c| c.fields.iter().cloned())
                    .collect();
                data.insert(name.value.symbol(), DataInfo { type_vars: vars, fields });
            }
            cst::Decl::Newtype { name, type_vars, ty, .. } => {
                let vars: Vec<Symbol> = type_vars.iter().map(|v| v.value.symbol()).collect();
                data.insert(
                    name.value.symbol(),
                    DataInfo { type_vars: vars, fields: vec![ty.clone()] },
                );
            }
            cst::Decl::Data { name, type_vars, is_role_decl: true, .. } => {
                // `type role Foo r1 r2 …` — type_vars here carry the
                // role keywords ("phantom", "representational",
                // "nominal") as TypeVarName symbols.
                let roles: Option<Vec<Role>> = type_vars
                    .iter()
                    .map(|v| Role::from_ident(v.value.symbol()))
                    .collect();
                if let Some(roles) = roles {
                    declared.insert(name.value.symbol(), (name.span, roles));
                }
                // If any role name is unrecognised we skip — a
                // parser-level rejection would have caught it.
            }
            cst::Decl::ForeignData { name, .. } => {
                // Foreign data types have Nominal role for every
                // arrow in their kind by default.
                foreign_nominal.insert(name.value.symbol());
            }
            cst::Decl::Instance { span, class_name, .. }
            | cst::Decl::Derive { span, class_name, .. } => {
                // User instance declarations for Coercible are
                // forbidden.
                if is_coercible_class(class_name) {
                    errors.push(CoercibleError {
                        span: *span,
                        kind: CoercibleErrorKind::InvalidCoercibleInstanceDeclaration,
                    });
                }
            }
            _ => {}
        }
    }

    // Role env used during inference. Starts with declared roles;
    // undeclared types start all-Phantom and are iterated.
    let mut role_env: HashMap<Symbol, Vec<Role>> = HashMap::new();
    for (name, info) in &data {
        let roles = declared
            .get(name)
            .map(|(_, r)| r.clone())
            .unwrap_or_else(|| vec![Role::Phantom; info.type_vars.len()]);
        role_env.insert(*name, roles);
    }

    // Fixed-point: re-infer roles for every NON-declared type until
    // nothing changes. Declared roles are stable — they're what we
    // validate against afterwards.
    loop {
        let mut changed = false;
        for (name, info) in &data {
            if declared.contains_key(name) {
                continue;
            }
            let inferred = infer_data_roles(info, &role_env, &foreign_nominal);
            if role_env.get(name) != Some(&inferred) {
                role_env.insert(*name, inferred);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Validate: each declared role must be at least as restrictive as
    // what the fields require.
    for (name, (span, decl_roles)) in &declared {
        let info = match data.get(name) {
            Some(i) => i,
            None => continue,
        };
        // Compute what roles would be inferred if this type were not
        // declared. Use the current role_env — any other declared
        // type is still pinned, so the inference sees "what my
        // fields require, given everyone else's declared/inferred
        // roles".
        let without_self = {
            let mut env = role_env.clone();
            env.insert(*name, vec![Role::Phantom; info.type_vars.len()]);
            infer_data_roles(info, &env, &foreign_nominal)
        };
        let min_len = std::cmp::min(decl_roles.len(), without_self.len());
        for i in 0..min_len {
            if decl_roles[i] < without_self[i] {
                errors.push(CoercibleError {
                    span: *span,
                    kind: CoercibleErrorKind::RoleMismatch(resolve(*name)),
                });
                break;
            }
        }
    }

    errors
}

fn is_coercible_class(class_name: &crate::names::Qualified<crate::names::ClassName>) -> bool {
    let name = crate::interner::resolve(class_name.name.symbol()).unwrap_or_default();
    name == "Coercible"
}

/// Infer roles for each of `info.type_vars` based on where they
/// appear in the decl's constructor fields.
fn infer_data_roles(
    info: &DataInfo,
    role_env: &HashMap<Symbol, Vec<Role>>,
    foreign_nominal: &HashSet<Symbol>,
) -> Vec<Role> {
    let mut roles = vec![Role::Phantom; info.type_vars.len()];
    for f in &info.fields {
        update_roles_from_type(
            f,
            &info.type_vars,
            &mut roles,
            role_env,
            foreign_nominal,
            Role::Representational,
            &HashSet::new(),
        );
    }
    roles
}

/// Walk a type expression, updating the per-parameter roles based on
/// where each type variable of `type_vars` appears. `position_role`
/// is the role flowing into this position from the surrounding
/// context.
fn update_roles_from_type(
    te: &cst::TypeExpr,
    type_vars: &[Symbol],
    roles: &mut [Role],
    role_env: &HashMap<Symbol, Vec<Role>>,
    foreign_nominal: &HashSet<Symbol>,
    position_role: Role,
    bound: &HashSet<Symbol>,
) {
    match te {
        cst::TypeExpr::Var { name, .. } => {
            let sym = name.value.symbol();
            if bound.contains(&sym) {
                return;
            }
            if let Some(i) = type_vars.iter().position(|v| *v == sym) {
                roles[i] = std::cmp::max(roles[i], position_role);
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            let (head, args) = peel_app(te);
            match head {
                cst::TypeExpr::Constructor { name, .. } if name.module.is_none() => {
                    let hsym = name.name.symbol();
                    if let Some(head_roles) = role_env.get(&hsym) {
                        for (i, a) in args.iter().enumerate() {
                            let r = head_roles.get(i).copied().unwrap_or(Role::Representational);
                            update_roles_from_type(
                                a,
                                type_vars,
                                roles,
                                role_env,
                                foreign_nominal,
                                Role::compose(position_role, r),
                                bound,
                            );
                        }
                    } else if foreign_nominal.contains(&hsym) {
                        for a in &args {
                            update_roles_from_type(
                                a,
                                type_vars,
                                roles,
                                role_env,
                                foreign_nominal,
                                Role::Nominal,
                                bound,
                            );
                        }
                    } else {
                        // Unknown constructor — conservatively treat
                        // all arg positions as Representational (the
                        // default for imported nominal types in the
                        // old compiler was Nominal, but that would
                        // be too strict here without knowing types
                        // from other modules).
                        for a in &args {
                            update_roles_from_type(
                                a,
                                type_vars,
                                roles,
                                role_env,
                                foreign_nominal,
                                Role::Representational,
                                bound,
                            );
                        }
                    }
                }
                cst::TypeExpr::Var { .. } => {
                    // Type var used as a ctor — conservatively mark
                    // every type var in the args as Nominal.
                    update_roles_from_type(
                        head,
                        type_vars,
                        roles,
                        role_env,
                        foreign_nominal,
                        position_role,
                        bound,
                    );
                    for a in &args {
                        mark_vars_nominal(a, type_vars, roles, bound);
                    }
                }
                _ => {
                    // Fallback: recurse into every sub-expression
                    // with the same role.
                    update_roles_from_type(
                        constructor,
                        type_vars,
                        roles,
                        role_env,
                        foreign_nominal,
                        position_role,
                        bound,
                    );
                    update_roles_from_type(
                        arg,
                        type_vars,
                        roles,
                        role_env,
                        foreign_nominal,
                        position_role,
                        bound,
                    );
                }
            }
        }
        cst::TypeExpr::Function { from, to, .. } => {
            update_roles_from_type(
                from,
                type_vars,
                roles,
                role_env,
                foreign_nominal,
                Role::Representational,
                bound,
            );
            update_roles_from_type(
                to,
                type_vars,
                roles,
                role_env,
                foreign_nominal,
                Role::Representational,
                bound,
            );
        }
        cst::TypeExpr::Forall { ty, vars, .. } => {
            let mut new_bound = bound.clone();
            for (v, _, _) in vars {
                new_bound.insert(v.value.symbol());
            }
            update_roles_from_type(
                ty,
                type_vars,
                roles,
                role_env,
                foreign_nominal,
                position_role,
                &new_bound,
            );
        }
        cst::TypeExpr::Constrained { ty, .. } => {
            update_roles_from_type(
                ty,
                type_vars,
                roles,
                role_env,
                foreign_nominal,
                position_role,
                bound,
            );
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                update_roles_from_type(
                    &f.ty,
                    type_vars,
                    roles,
                    role_env,
                    foreign_nominal,
                    position_role,
                    bound,
                );
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                update_roles_from_type(
                    &f.ty,
                    type_vars,
                    roles,
                    role_env,
                    foreign_nominal,
                    position_role,
                    bound,
                );
            }
            if let Some(t) = tail {
                update_roles_from_type(
                    t,
                    type_vars,
                    roles,
                    role_env,
                    foreign_nominal,
                    position_role,
                    bound,
                );
            }
        }
        cst::TypeExpr::Parens { ty, .. } => update_roles_from_type(
            ty,
            type_vars,
            roles,
            role_env,
            foreign_nominal,
            position_role,
            bound,
        ),
        cst::TypeExpr::Kinded { ty, .. } => update_roles_from_type(
            ty,
            type_vars,
            roles,
            role_env,
            foreign_nominal,
            position_role,
            bound,
        ),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            update_roles_from_type(
                left,
                type_vars,
                roles,
                role_env,
                foreign_nominal,
                position_role,
                bound,
            );
            update_roles_from_type(
                right,
                type_vars,
                roles,
                role_env,
                foreign_nominal,
                position_role,
                bound,
            );
        }
        _ => {}
    }
}

fn mark_vars_nominal(
    te: &cst::TypeExpr,
    type_vars: &[Symbol],
    roles: &mut [Role],
    bound: &HashSet<Symbol>,
) {
    match te {
        cst::TypeExpr::Var { name, .. } => {
            let sym = name.value.symbol();
            if bound.contains(&sym) {
                return;
            }
            if let Some(i) = type_vars.iter().position(|v| *v == sym) {
                roles[i] = Role::Nominal;
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            mark_vars_nominal(constructor, type_vars, roles, bound);
            mark_vars_nominal(arg, type_vars, roles, bound);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            mark_vars_nominal(from, type_vars, roles, bound);
            mark_vars_nominal(to, type_vars, roles, bound);
        }
        cst::TypeExpr::Parens { ty, .. } | cst::TypeExpr::Kinded { ty, .. } => {
            mark_vars_nominal(ty, type_vars, roles, bound);
        }
        cst::TypeExpr::Record { fields, .. } | cst::TypeExpr::Row { fields, .. } => {
            for f in fields {
                mark_vars_nominal(&f.ty, type_vars, roles, bound);
            }
        }
        _ => {}
    }
}

fn peel_app(te: &cst::TypeExpr) -> (&cst::TypeExpr, Vec<&cst::TypeExpr>) {
    let mut args: Vec<&cst::TypeExpr> = Vec::new();
    let mut cur = te;
    loop {
        match cur {
            cst::TypeExpr::App { constructor, arg, .. } => {
                args.push(arg);
                cur = constructor;
            }
            cst::TypeExpr::Parens { ty, .. } => cur = ty,
            _ => break,
        }
    }
    args.reverse();
    (cur, args)
}

fn resolve(sym: Symbol) -> String {
    crate::interner::resolve(sym).unwrap_or_default()
}
