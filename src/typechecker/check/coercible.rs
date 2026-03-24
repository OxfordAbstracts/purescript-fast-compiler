use std::collections::{HashMap, HashSet};

use crate::interner::Symbol;
use crate::names::{Qualified, TypeName, ConstructorName, TypeVarName, LabelName};
use crate::typechecker::types::{Role, Type};

use super::{
    apply_var_subst, expand_type_aliases,
    type_var_occurs_in,
};

/// This implements a simplified version of the original PureScript compiler's
/// interaction system. For canonical givens (where LHS is a type var that
/// doesn't occur in the RHS), we can rewrite the wanted by substituting
/// the type var. For transitive cases (Coercible a b, Coercible b c => Coercible a c),
/// we also try combining canonical givens that share a type var.
pub(crate) fn try_solve_coercible_with_interactions(
    wanted_a: &Type,
    wanted_b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    newtype_names: &HashSet<Qualified<TypeName>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
) -> CoercibleResult {
    // First try direct solve with givens (Rule 0)
    let result = solve_coercible(
        wanted_a,
        wanted_b,
        givens,
        type_roles,
        newtype_names,
        type_aliases,
        ctor_details,
        0,
    );
    if result == CoercibleResult::Solved || result == CoercibleResult::DepthExceeded {
        return result;
    }

    // Build canonical substitution from givens:
    // A given Coercible(Var(v), T) where v does not occur in T is canonical.
    // We treat both directions: Var on left or Var on right.
    let mut canonical_subst: HashMap<TypeVarName, Type> = HashMap::new();
    for (ga, gb) in givens {
        if let Type::Var(v) = ga {
            if !type_var_occurs_in(*v, gb) {
                canonical_subst.insert(*v, gb.clone());
            }
        }
        if let Type::Var(v) = gb {
            if !type_var_occurs_in(*v, ga) {
                canonical_subst.entry(*v).or_insert_with(|| ga.clone());
            }
        }
    }

    if canonical_subst.is_empty() {
        return result;
    }

    // Apply canonical substitution to the wanted constraint
    let rewritten_a = apply_var_subst(&canonical_subst, wanted_a);
    let rewritten_b = apply_var_subst(&canonical_subst, wanted_b);

    // Only try if rewriting changed something
    if !types_structurally_equal(&rewritten_a, wanted_a)
        || !types_structurally_equal(&rewritten_b, wanted_b)
    {
        let result2 = solve_coercible(
            &rewritten_a,
            &rewritten_b,
            givens,
            type_roles,
            newtype_names,
            type_aliases,
            ctor_details,
            0,
        );
        if result2 == CoercibleResult::Solved || result2 == CoercibleResult::DepthExceeded {
            return result2;
        }

        // Try second round of substitution (for transitive cases)
        let rewritten2_a = apply_var_subst(&canonical_subst, &rewritten_a);
        let rewritten2_b = apply_var_subst(&canonical_subst, &rewritten_b);
        if !types_structurally_equal(&rewritten2_a, &rewritten_a)
            || !types_structurally_equal(&rewritten2_b, &rewritten_b)
        {
            let result3 = solve_coercible(
                &rewritten2_a,
                &rewritten2_b,
                givens,
                type_roles,
                newtype_names,
                type_aliases,
                ctor_details,
                0,
            );
            if result3 == CoercibleResult::Solved || result3 == CoercibleResult::DepthExceeded {
                return result3;
            }
        }
    }

    // Also try interactSameTyVar: if two canonical givens share the same LHS var,
    // derive a new constraint from their RHS values, then decompose derived constraints.
    let mut derived_pairs: Vec<(Type, Type)> = Vec::new();
    for i in 0..givens.len() {
        for j in (i + 1)..givens.len() {
            let vars_i = canonical_lhs_var(&givens[i]);
            let vars_j = canonical_lhs_var(&givens[j]);
            for (vi, ti) in &vars_i {
                for (vj, tj) in &vars_j {
                    if vi == vj {
                        derived_pairs.push((ti.clone(), tj.clone()));
                    }
                }
            }
        }
    }
    if !derived_pairs.is_empty() {
        // Decompose derived pairs: if (D b c, D d e) with D having roles [repr, phantom],
        // extract sub-givens like (b, d) from representational positions.
        let mut all_givens = givens.to_vec();
        for (da, db) in &derived_pairs {
            all_givens.push((da.clone(), db.clone()));
            decompose_given_pair(da, db, type_roles, &mut all_givens);
        }
        let result4 = solve_coercible(
            wanted_a,
            wanted_b,
            &all_givens,
            type_roles,
            newtype_names,
            type_aliases,
            ctor_details,
            0,
        );
        if result4 == CoercibleResult::Solved || result4 == CoercibleResult::DepthExceeded {
            return result4;
        }
    }

    result
}

/// Extract canonical (var, type) pairs from a given, where the var doesn't occur in the type.
pub(crate) fn canonical_lhs_var(given: &(Type, Type)) -> Vec<(TypeVarName, Type)> {
    let mut result = Vec::new();
    if let Type::Var(v) = &given.0 {
        if !type_var_occurs_in(*v, &given.1) {
            result.push((*v, given.1.clone()));
        }
    }
    if let Type::Var(v) = &given.1 {
        if !type_var_occurs_in(*v, &given.0) {
            result.push((*v, given.0.clone()));
        }
    }
    result
}

/// Decompose a derived given pair into sub-givens based on role decomposition.
/// E.g. (D b c, D d e) with D having roles [representational, phantom]
/// produces sub-given (b, d) from the representational position.
pub(crate) fn decompose_given_pair(
    a: &Type,
    b: &Type,
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    out: &mut Vec<(Type, Type)>,
) {
    let (head_a, args_a) = unapply_type(a);
    let (head_b, args_b) = unapply_type(b);
    if let (Type::Con(con_a), Type::Con(con_b)) = (&head_a, &head_b) {
        if con_a.name == con_b.name && args_a.len() == args_b.len() {
            let roles = type_roles.get(&con_a.name);
            for (i, (arg_a, arg_b)) in args_a.iter().zip(args_b.iter()).enumerate() {
                let role = roles
                    .and_then(|r| r.get(i))
                    .copied()
                    .unwrap_or(Role::Representational);
                match role {
                    Role::Representational => {
                        out.push(((*arg_a).clone(), (*arg_b).clone()));
                    }
                    Role::Phantom | Role::Nominal => {
                        // Phantom: no constraint needed. Nominal: must be equal (not a coercible sub-given).
                    }
                }
            }
        }
    }
}

/// Collect free named type variables (Type::Var) from a type, excluding those
/// bound by inner Type::Forall. Used to validate type alias bodies.
pub(crate) fn free_named_type_vars(ty: &Type) -> HashSet<TypeVarName> {
    let mut vars = HashSet::new();
    collect_free_named_vars(ty, &HashSet::new(), &mut vars);
    vars
}

pub(crate) fn collect_free_named_vars(ty: &Type, bound: &HashSet<TypeVarName>, vars: &mut HashSet<TypeVarName>) {
    match ty {
        Type::Var(sym) => {
            if !bound.contains(sym) {
                vars.insert(*sym);
            }
        }
        Type::Fun(from, to) => {
            collect_free_named_vars(from, bound, vars);
            collect_free_named_vars(to, bound, vars);
        }
        Type::App(f, a) => {
            collect_free_named_vars(f, bound, vars);
            collect_free_named_vars(a, bound, vars);
        }
        Type::Forall(forall_vars, body) => {
            let mut inner_bound = bound.clone();
            for (v, _) in forall_vars {
                inner_bound.insert(*v);
            }
            collect_free_named_vars(body, &inner_bound, vars);
        }
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                collect_free_named_vars(t, bound, vars);
            }
            if let Some(tail) = tail {
                collect_free_named_vars(tail, bound, vars);
            }
        }
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => {}
    }
}

/// Infer roles for a type's parameters based on how they're used in constructor fields.
/// For each type variable, compute the most restrictive role required by any field.
pub(crate) fn infer_roles_from_fields(
    type_vars: &[Symbol],
    constructor_fields: &[Vec<Type>],
    known_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
) -> Vec<Role> {
    let mut roles = vec![Role::Phantom; type_vars.len()];
    for fields in constructor_fields {
        for field_ty in fields {
            update_roles_from_type(
                field_ty,
                type_vars,
                &mut roles,
                known_roles,
                Role::Representational,
            );
        }
    }
    roles
}


/// Extract the head and arguments from a chain of TypeApp nodes.
/// Returns the head type and a vector of arguments (outermost last → reversed then returned in order).
pub(crate) fn unapply_type_args(ty: &Type) -> (&Type, Vec<&Type>) {
    let mut args = Vec::new();
    let mut current = ty;
    loop {
        match current {
            Type::App(f, a) => {
                args.push(a.as_ref());
                current = f.as_ref();
            }
            _ => {
                args.reverse();
                return (current, args);
            }
        }
    }
}

/// Mark ALL type variables in a type as Nominal (used for arguments of TypeVar-head applications).
/// When a type variable is used as a type constructor (e.g., `f a b`), we don't know what `f`
/// will be instantiated to, so all type variables in the arguments must be conservatively
/// treated as Nominal. Respects forall-bound variable shadowing.
pub(crate) fn mark_all_type_vars_nominal(
    ty: &Type,
    type_vars: &[Symbol],
    roles: &mut [Role],
    bound: &HashSet<TypeVarName>,
) {
    match ty {
        Type::Var(v) => {
            if !bound.contains(v) {
                if let Some(idx) = type_vars.iter().position(|tv| v.matches_ident(*tv)) {
                    roles[idx] = Role::Nominal;
                }
            }
        }
        Type::App(f, a) => {
            mark_all_type_vars_nominal(f, type_vars, roles, bound);
            mark_all_type_vars_nominal(a, type_vars, roles, bound);
        }
        Type::Fun(a, b) => {
            mark_all_type_vars_nominal(a, type_vars, roles, bound);
            mark_all_type_vars_nominal(b, type_vars, roles, bound);
        }
        Type::Record(fields, tail) => {
            for (_, field_ty) in fields {
                mark_all_type_vars_nominal(field_ty, type_vars, roles, bound);
            }
            if let Some(t) = tail {
                mark_all_type_vars_nominal(t, type_vars, roles, bound);
            }
        }
        Type::Forall(vars, body) => {
            let mut new_bound = bound.clone();
            for (v, _) in vars {
                new_bound.insert(*v);
            }
            mark_all_type_vars_nominal(body, type_vars, roles, &new_bound);
        }
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => {}
    }
}

/// Recursively walk a type and update roles for type variables found within.
/// Matches PureScript's `walkType` algorithm from Types/Roles.hs:
/// - For TypeApp chains with a known constructor head: compose position_role with
///   the constructor's declared roles for each argument position.
/// - For TypeApp chains with a TypeVar head: the head var gets position_role,
///   but ALL type vars in the arguments are marked Nominal (conservative — we don't
///   know what the type variable will be instantiated to).
/// - For TypeApp chains with unknown head: generic walk.
/// - TypeVar: report the variable's role.
/// - Fun: both sides get position_role.compose(Representational) (Function is Representational).
pub(crate) fn update_roles_from_type(
    ty: &Type,
    type_vars: &[Symbol],
    roles: &mut [Role],
    known_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    position_role: Role,
) {
    // For App chains, extract the head and all arguments
    if matches!(ty, Type::App(..)) {
        let (head, args) = unapply_type_args(ty);

        // Case 1: Known type constructor head — use declared roles
        if let Type::Con(name) = head {
            if let Some(head_roles) = known_roles.get(&name.name) {
                for (i, arg) in args.iter().enumerate() {
                    let arg_role = if let Some(r) = head_roles.get(i) {
                        position_role.compose(*r)
                    } else {
                        position_role.compose(Role::Representational)
                    };
                    update_roles_from_type(arg, type_vars, roles, known_roles, arg_role);
                }
                return;
            }
        }

        // Case 2: Type variable head — head gets position_role, args get Nominal treatment
        if let Type::Var(v) = head {
            // The head type variable gets the current position role
            if let Some(idx) = type_vars.iter().position(|tv| v.matches_ident(*tv)) {
                roles[idx] = roles[idx].max(position_role);
            }
            // All type variables in the arguments are marked Nominal
            let bound = HashSet::new();
            for arg in &args {
                mark_all_type_vars_nominal(arg, type_vars, roles, &bound);
            }
            return;
        }

        // Case 3: Unknown head — generic walk
        update_roles_from_type(head, type_vars, roles, known_roles, position_role);
        for arg in &args {
            update_roles_from_type(arg, type_vars, roles, known_roles, Role::Representational);
        }
        return;
    }

    // Non-App types
    match ty {
        Type::Var(v) => {
            if let Some(idx) = type_vars.iter().position(|tv| v.matches_ident(*tv)) {
                roles[idx] = roles[idx].max(position_role);
            }
        }
        Type::Fun(a, b) => {
            // Function is Representational in both positions
            let arg_role = position_role.compose(Role::Representational);
            update_roles_from_type(a, type_vars, roles, known_roles, arg_role);
            update_roles_from_type(b, type_vars, roles, known_roles, arg_role);
        }
        Type::Record(fields, tail) => {
            for (_, field_ty) in fields {
                update_roles_from_type(field_ty, type_vars, roles, known_roles, position_role);
            }
            if let Some(t) = tail {
                update_roles_from_type(t, type_vars, roles, known_roles, position_role);
            }
        }
        Type::Forall(vars, body) => {
            let bound: HashSet<TypeVarName> = vars.iter().map(|(v, _)| *v).collect();
            if !type_vars.iter().any(|tv| bound.iter().any(|b| b.matches_ident(*tv))) {
                update_roles_from_type(body, type_vars, roles, known_roles, position_role);
            }
        }
        Type::App(..) => unreachable!(), // handled above
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => {}
    }
}

/// Walk a CST TypeExpr and mark type variables inside constraint positions as nominal.
/// This handles `data D a = D (C a => a)` — the `a` in `C a` must be nominal because
/// constraints cannot be coerced. Respects forall-bound variable shadowing.
pub(crate) fn mark_constrained_vars_nominal_cst(
    te: &crate::ast::TypeExpr,
    type_vars: &[Symbol],
    roles: &mut [Role],
    bound: &HashSet<Symbol>,
) {
    use crate::ast::TypeExpr;
    match te {
        TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            // All type vars in constraints are nominal (unless shadowed by forall)
            for c in constraints {
                for arg in &c.args {
                    mark_all_cst_vars_nominal(arg, type_vars, roles, bound);
                }
            }
            mark_constrained_vars_nominal_cst(ty, type_vars, roles, bound);
        }
        TypeExpr::App {
            constructor, arg, ..
        } => {
            mark_constrained_vars_nominal_cst(constructor, type_vars, roles, bound);
            mark_constrained_vars_nominal_cst(arg, type_vars, roles, bound);
        }
        TypeExpr::Function { from, to, .. } => {
            mark_constrained_vars_nominal_cst(from, type_vars, roles, bound);
            mark_constrained_vars_nominal_cst(to, type_vars, roles, bound);
        }
        TypeExpr::Forall { vars, ty, .. } => {
            let mut new_bound = bound.clone();
            for (v, _, _) in vars {
                new_bound.insert(v.value);
            }
            mark_constrained_vars_nominal_cst(ty, type_vars, roles, &new_bound);
        }
        TypeExpr::Record { fields, .. } => {
            for f in fields {
                mark_constrained_vars_nominal_cst(&f.ty, type_vars, roles, bound);
            }
        }
        TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                mark_constrained_vars_nominal_cst(&f.ty, type_vars, roles, bound);
            }
            if let Some(t) = tail {
                mark_constrained_vars_nominal_cst(t, type_vars, roles, bound);
            }
        }
        TypeExpr::Kinded { ty, .. } => {
            mark_constrained_vars_nominal_cst(ty, type_vars, roles, bound);
        }
        _ => {} // Var, Constructor, StringLiteral, IntLiteral, Wildcard, Hole
    }
}

/// Mark all type variables in a CST TypeExpr as nominal (respecting forall shadowing).
pub(crate) fn mark_all_cst_vars_nominal(
    te: &crate::ast::TypeExpr,
    type_vars: &[Symbol],
    roles: &mut [Role],
    bound: &HashSet<Symbol>,
) {
    use crate::ast::TypeExpr;
    match te {
        TypeExpr::Var { name, .. } => {
            if !bound.contains(&name.value) {
                if let Some(idx) = type_vars.iter().position(|tv| *tv == name.value) {
                    roles[idx] = Role::Nominal;
                }
            }
        }
        TypeExpr::App {
            constructor, arg, ..
        } => {
            mark_all_cst_vars_nominal(constructor, type_vars, roles, bound);
            mark_all_cst_vars_nominal(arg, type_vars, roles, bound);
        }
        TypeExpr::Function { from, to, .. } => {
            mark_all_cst_vars_nominal(from, type_vars, roles, bound);
            mark_all_cst_vars_nominal(to, type_vars, roles, bound);
        }
        TypeExpr::Forall { vars, ty, .. } => {
            let mut new_bound = bound.clone();
            for (v, _, _) in vars {
                new_bound.insert(v.value);
            }
            mark_all_cst_vars_nominal(ty, type_vars, roles, &new_bound);
        }
        TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            for c in constraints {
                for arg in &c.args {
                    mark_all_cst_vars_nominal(arg, type_vars, roles, bound);
                }
            }
            mark_all_cst_vars_nominal(ty, type_vars, roles, bound);
        }
        TypeExpr::Record { fields, .. } => {
            for f in fields {
                mark_all_cst_vars_nominal(&f.ty, type_vars, roles, bound);
            }
        }
        TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                mark_all_cst_vars_nominal(&f.ty, type_vars, roles, bound);
            }
            if let Some(t) = tail {
                mark_all_cst_vars_nominal(t, type_vars, roles, bound);
            }
        }
        TypeExpr::Kinded { ty, .. } => {
            mark_all_cst_vars_nominal(ty, type_vars, roles, bound);
        }
        _ => {} // Constructor, StringLiteral, IntLiteral, Wildcard, Hole
    }
}

/// Unapply a type: `App(App(Con(T), a), b)` → `(Con(T), [a, b])`.
pub(crate) fn unapply_type(ty: &Type) -> (Type, Vec<&Type>) {
    let mut head = ty;
    let mut args = Vec::new();
    while let Type::App(f, arg) = head {
        args.push(arg.as_ref());
        head = f.as_ref();
    }
    args.reverse();
    (head.clone(), args)
}

/// Result of attempting to solve a Coercible constraint.
#[derive(Debug, PartialEq)]
pub(crate) enum CoercibleResult {
    /// The constraint is satisfied.
    Solved,
    /// The types are not coercible — produce NoInstanceFound.
    NotCoercible,
    /// Types don't unify under nominal roles — produce TypesDoNotUnify.
    TypesDoNotUnify,
    /// Depth limit exceeded — produce PossiblyInfiniteCoercibleInstance.
    DepthExceeded,
    /// Types have different kinds — produce KindArityMismatch.
    KindMismatch,
}

/// Returns true if the type has unif vars outside of record row tail positions.
/// Used to decide whether to skip Coercible solving in the has_unsolved block:
/// - Unif vars in structural positions (bare, App args) → skip (can't solve yet)
/// - Unif vars only in row tails → don't skip (solver can still determine coercibility)
pub(crate) fn has_unif_outside_row_tails(ty: &Type) -> bool {
    match ty {
        Type::Unif(_) => true,
        Type::Con(_) | Type::Var(_) | Type::TypeString(_) | Type::TypeInt(_) => false,
        Type::App(f, a) => has_unif_outside_row_tails(f) || has_unif_outside_row_tails(a),
        Type::Fun(a, b) => has_unif_outside_row_tails(a) || has_unif_outside_row_tails(b),
        Type::Record(fields, _tail) => {
            // Fields must not have unif vars in structural positions.
            // The tail itself is a row tail position, so unif vars there are fine.
            fields.iter().any(|(_, ft)| has_unif_outside_row_tails(ft))
        }
        Type::Forall(_, body) => has_unif_outside_row_tails(body),
    }
}

/// Solve a `Coercible a b` constraint.
/// Uses role-based decomposition and newtype unwrapping.
/// `givens` are Coercible pairs assumed to hold (from the function's signature constraints).
pub(crate) fn solve_coercible(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    newtype_names: &HashSet<Qualified<TypeName>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    depth: u32,
) -> CoercibleResult {
    let mut visited = HashSet::new();
    solve_coercible_with_visited(
        a,
        b,
        givens,
        type_roles,
        newtype_names,
        type_aliases,
        ctor_details,
        depth,
        &mut visited,
    )
}

pub(crate) fn solve_coercible_with_visited(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    newtype_names: &HashSet<Qualified<TypeName>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    depth: u32,
    visited: &mut HashSet<(String, String)>,
) -> CoercibleResult {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    solve_coercible_with_visited_impl(a, b, givens, type_roles, newtype_names, type_aliases, ctor_details, depth, visited)
    })
}

pub(crate) fn solve_coercible_with_visited_impl(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    newtype_names: &HashSet<Qualified<TypeName>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    depth: u32,
    visited: &mut HashSet<(String, String)>,
) -> CoercibleResult {
    if depth > 50 {
        return CoercibleResult::DepthExceeded;
    }

    // Expand type aliases on both sides
    let a_expanded = expand_type_aliases(a, type_aliases);
    let b_expanded = expand_type_aliases(b, type_aliases);

    solve_coercible_inner(
        &a_expanded,
        &b_expanded,
        givens,
        type_roles,
        newtype_names,
        type_aliases,
        ctor_details,
        depth,
        visited,
    )
}

pub(crate) fn solve_coercible_inner(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    newtype_names: &HashSet<Qualified<TypeName>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    depth: u32,
    visited: &mut HashSet<(String, String)>,
) -> CoercibleResult {
    // Cycle detection: if we've seen this exact goal on the current call path, it's infinite
    let goal_key = (format!("{}", a), format!("{}", b));
    if visited.contains(&goal_key) {
        return CoercibleResult::DepthExceeded;
    }
    visited.insert(goal_key.clone());

    let result = solve_coercible_inner_impl(
        a,
        b,
        givens,
        type_roles,
        newtype_names,
        type_aliases,
        ctor_details,
        depth,
        visited,
    );

    // Remove from visited set — only track goals on current call path
    visited.remove(&goal_key);

    result
}

pub(crate) fn solve_coercible_inner_impl(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    newtype_names: &HashSet<Qualified<TypeName>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    depth: u32,
    visited: &mut HashSet<(String, String)>,
) -> CoercibleResult {
    // Rule 0: Check given Coercible constraints (symmetric)
    for (ga, gb) in givens {
        if (types_structurally_equal(a, ga) && types_structurally_equal(b, gb))
            || (types_structurally_equal(a, gb) && types_structurally_equal(b, ga))
        {
            return CoercibleResult::Solved;
        }
        // Extended matching: allow type variables in the given to match concrete
        // types in the wanted. This handles cases like:
        //   given: Coercible (f payload) (Element ... payload)
        //   wanted: Coercible (Element ... payload) (Geometry payload)
        // where f=Geometry satisfies the match via symmetry.
        let mut subst = HashMap::new();
        if types_match_up_to_vars(ga, a, &mut subst) && types_match_up_to_vars(gb, b, &mut subst) {
            return CoercibleResult::Solved;
        }
        subst.clear();
        if types_match_up_to_vars(ga, b, &mut subst) && types_match_up_to_vars(gb, a, &mut subst) {
            return CoercibleResult::Solved;
        }
    }

    // Rule 1: Reflexivity
    if types_structurally_equal(a, b) {
        return CoercibleResult::Solved;
    }

    // Rule 2: Record decomposition
    if let (Type::Record(fields_a, tail_a), Type::Record(fields_b, tail_b)) = (a, b) {
        return solve_coercible_records(
            fields_a,
            tail_a,
            fields_b,
            tail_b,
            givens,
            type_roles,
            newtype_names,
            type_aliases,
            ctor_details,
            depth,
            visited,
        );
    }

    let (head_a, args_a) = unapply_type(a);
    let (head_b, args_b) = unapply_type(b);

    // Rule 3 (newtypes first): Unwrap newtypes before role-based decomposition.
    // The original PureScript compiler does this because it solves more constraints —
    // e.g. when a newtype has nominal parameters, unwrapping may still succeed.
    let is_newtype = |c: &Qualified<TypeName>| -> bool {
        newtype_names.contains(c) || newtype_names.iter().any(|n| n.name == c.name)
    };
    let a_is_newtype = matches!(&head_a, Type::Con(c) if is_newtype(c));
    let b_is_newtype = matches!(&head_b, Type::Con(c) if is_newtype(c));
    // Track if newtype unwrapping hit DepthExceeded; if Rule 4 also fails,
    // propagate DepthExceeded (PossiblyInfiniteCoercibleInstance) instead of NotCoercible.
    let mut newtype_depth_exceeded = false;

    if a_is_newtype || b_is_newtype {
        // Try unwrapping both sides first if same constructor
        if let (Type::Con(con_a), Type::Con(con_b)) = (&head_a, &head_b) {
            if con_a.name == con_b.name && a_is_newtype {
                if let (Some(unwrapped_a), Some(unwrapped_b)) = (
                    unwrap_newtype(con_a, &args_a, ctor_details),
                    unwrap_newtype(con_b, &args_b, ctor_details),
                ) {
                    let unwrapped_a = expand_type_aliases(&unwrapped_a, type_aliases);
                    let unwrapped_b = expand_type_aliases(&unwrapped_b, type_aliases);
                    let result = solve_coercible_inner(
                        &unwrapped_a,
                        &unwrapped_b,
                        givens,
                        type_roles,
                        newtype_names,
                        type_aliases,
                        ctor_details,
                        depth + 1,
                        visited,
                    );
                    match result {
                        CoercibleResult::Solved
                        | CoercibleResult::NotCoercible
                        | CoercibleResult::TypesDoNotUnify
                        | CoercibleResult::KindMismatch => {
                            // For same-constructor newtypes, unwrapping is the definitive path.
                            // Only DepthExceeded falls through to role-based decomposition
                            // (for recursive newtypes solvable via given constraints).
                            return result;
                        }
                        CoercibleResult::DepthExceeded => {
                            newtype_depth_exceeded = true;
                        }
                    }
                }
            }
        }

        // Try unwrapping left side only
        if a_is_newtype {
            if let Type::Con(con_a) = &head_a {
                if let Some(unwrapped) = unwrap_newtype(con_a, &args_a, ctor_details) {
                    let unwrapped = expand_type_aliases(&unwrapped, type_aliases);
                    let result = solve_coercible_inner(
                        &unwrapped,
                        b,
                        givens,
                        type_roles,
                        newtype_names,
                        type_aliases,
                        ctor_details,
                        depth + 1,
                        visited,
                    );
                    if result == CoercibleResult::Solved {
                        return result;
                    }
                    if result == CoercibleResult::DepthExceeded {
                        newtype_depth_exceeded = true;
                    }
                }
            }
        }

        // Try unwrapping right side only
        if b_is_newtype {
            if let Type::Con(con_b) = &head_b {
                if let Some(unwrapped) = unwrap_newtype(con_b, &args_b, ctor_details) {
                    let unwrapped = expand_type_aliases(&unwrapped, type_aliases);
                    let result = solve_coercible_inner(
                        a,
                        &unwrapped,
                        givens,
                        type_roles,
                        newtype_names,
                        type_aliases,
                        ctor_details,
                        depth + 1,
                        visited,
                    );
                    if result == CoercibleResult::Solved {
                        return result;
                    }
                    if result == CoercibleResult::DepthExceeded {
                        newtype_depth_exceeded = true;
                    }
                }
            }
        }
    }

    // Rule 4: Same type constructor — decompose with roles
    if let (Type::Con(con_a), Type::Con(con_b)) = (&head_a, &head_b) {
        if con_a.name == con_b.name && args_a.len() == args_b.len() {
            let roles = type_roles.get(&con_a.name);
            for (i, (arg_a, arg_b)) in args_a.iter().zip(args_b.iter()).enumerate() {
                let role = roles
                    .and_then(|r| r.get(i))
                    .copied()
                    .unwrap_or(Role::Representational);
                match role {
                    Role::Phantom => {
                        // Phantom args can differ freely
                        continue;
                    }
                    Role::Nominal => {
                        // Nominal args must be exactly equal
                        if !types_structurally_equal(arg_a, arg_b) {
                            if newtype_depth_exceeded {
                                return CoercibleResult::DepthExceeded;
                            }
                            return CoercibleResult::TypesDoNotUnify;
                        }
                    }
                    Role::Representational => {
                        // Representational args must be Coercible
                        match solve_coercible_with_visited(
                            arg_a,
                            arg_b,
                            givens,
                            type_roles,
                            newtype_names,
                            type_aliases,
                            ctor_details,
                            depth + 1,
                            visited,
                        ) {
                            CoercibleResult::Solved => continue,
                            other => {
                                if newtype_depth_exceeded {
                                    return CoercibleResult::DepthExceeded;
                                }
                                return other;
                            }
                        }
                    }
                }
            }
            return CoercibleResult::Solved;
        }
    }

    // Rule 5: Newtype unwrapping for non-same-constructor cases (already tried same-constructor above)
    if !a_is_newtype && !b_is_newtype {
        // Skip — already tried above for newtypes
    } else {
        // Already tried in the newtype-first section above
    }

    // Rule 6: Function decomposition — both sides are functions
    if let (Type::Fun(a1, a2), Type::Fun(b1, b2)) = (a, b) {
        // Check both sub-goals, propagating DepthExceeded even if one fails
        let result1 = solve_coercible_with_visited(
            a1,
            b1,
            givens,
            type_roles,
            newtype_names,
            type_aliases,
            ctor_details,
            depth + 1,
            visited,
        );
        let result2 = solve_coercible_with_visited(
            a2,
            b2,
            givens,
            type_roles,
            newtype_names,
            type_aliases,
            ctor_details,
            depth + 1,
            visited,
        );
        return match (result1, result2) {
            (CoercibleResult::Solved, CoercibleResult::Solved) => CoercibleResult::Solved,
            (CoercibleResult::DepthExceeded, _) | (_, CoercibleResult::DepthExceeded) => {
                CoercibleResult::DepthExceeded
            }
            (CoercibleResult::TypesDoNotUnify, _) | (_, CoercibleResult::TypesDoNotUnify) => {
                CoercibleResult::TypesDoNotUnify
            }
            _ => CoercibleResult::NotCoercible,
        };
    }

    // Rule 7: Forall types — structurally match quantifiers
    if let (Type::Forall(vars_a, body_a), Type::Forall(vars_b, body_b)) = (a, b) {
        if vars_a.len() == vars_b.len() {
            // Rename vars_b to match vars_a for structural comparison
            let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
            for ((va, _), (vb, _)) in vars_a.iter().zip(vars_b.iter()) {
                if va != vb {
                    subst.insert(*vb, Type::Var(*va));
                }
            }
            let body_b_renamed = if subst.is_empty() {
                body_b.as_ref().clone()
            } else {
                apply_var_subst(&subst, body_b)
            };
            return solve_coercible_inner(
                body_a,
                &body_b_renamed,
                givens,
                type_roles,
                newtype_names,
                type_aliases,
                ctor_details,
                depth + 1,
                visited,
            );
        }
    }

    // No rule applies — if newtype unwrapping hit infinite recursion, report that
    if newtype_depth_exceeded {
        return CoercibleResult::DepthExceeded;
    }

    // Check for kind mismatch: two different type constructors with different remaining
    // arities after accounting for partial application.
    // (e.g. bare Unary vs bare Binary → remaining arity 1 vs 2 → kind mismatch)
    // (but Unary vs Binary a → remaining arity 1 vs 1 → no kind mismatch, just not coercible)
    let (final_head_a, final_args_a) = unapply_type(a);
    let (final_head_b, final_args_b) = unapply_type(b);
    if let (Type::Con(a_con), Type::Con(b_con)) = (&final_head_a, &final_head_b) {
        if a_con.name != b_con.name {
            let a_remaining = type_roles
                .get(&a_con.name)
                .map(|r| r.len().saturating_sub(final_args_a.len()));
            let b_remaining = type_roles
                .get(&b_con.name)
                .map(|r| r.len().saturating_sub(final_args_b.len()));
            if let (Some(a_n), Some(b_n)) = (a_remaining, b_remaining) {
                if a_n != b_n {
                    return CoercibleResult::KindMismatch;
                }
            }
        }
    }

    CoercibleResult::NotCoercible
}

/// Solve Coercible for record types.
pub(crate) fn solve_coercible_records(
    fields_a: &[(crate::names::LabelName, Type)],
    tail_a: &Option<Box<Type>>,
    fields_b: &[(crate::names::LabelName, Type)],
    tail_b: &Option<Box<Type>>,
    givens: &[(Type, Type)],
    type_roles: &HashMap<crate::names::TypeName, Vec<Role>>,
    newtype_names: &HashSet<Qualified<TypeName>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    depth: u32,
    visited: &mut HashSet<(String, String)>,
) -> CoercibleResult {
    // Build label maps
    let map_a: HashMap<LabelName, &Type> = fields_a.iter().map(|(l, t)| (*l, t)).collect();
    let map_b: HashMap<LabelName, &Type> = fields_b.iter().map(|(l, t)| (*l, t)).collect();

    // Check all fields in a exist in b with coercible types
    for (label, ty_a) in &map_a {
        match map_b.get(label) {
            Some(ty_b) => {
                match solve_coercible_with_visited(
                    ty_a,
                    ty_b,
                    givens,
                    type_roles,
                    newtype_names,
                    type_aliases,
                    ctor_details,
                    depth + 1,
                    visited,
                ) {
                    CoercibleResult::Solved => continue,
                    other => return other,
                }
            }
            None => {
                // If the other side has an open tail, the missing field might be in the tail.
                // We can't prove coercibility with an unknown tail → NotCoercible.
                if tail_b.is_some() {
                    return CoercibleResult::NotCoercible;
                }
                return CoercibleResult::TypesDoNotUnify;
            }
        }
    }

    // Check all fields in b exist in a
    for label in map_b.keys() {
        if !map_a.contains_key(label) {
            if tail_a.is_some() {
                return CoercibleResult::NotCoercible;
            }
            return CoercibleResult::TypesDoNotUnify;
        }
    }

    // Check tails
    match (tail_a, tail_b) {
        (None, None) => CoercibleResult::Solved,
        (Some(ta), Some(tb)) => {
            // When both tails are bare unif vars, they represent unknown row
            // extensions that will be unified elsewhere. The coercible solver
            // can't unify them, but the field structure is sufficient to
            // determine coercibility.
            if matches!(ta.as_ref(), Type::Unif(_)) && matches!(tb.as_ref(), Type::Unif(_)) {
                return CoercibleResult::Solved;
            }
            solve_coercible_with_visited(
                ta,
                tb,
                givens,
                type_roles,
                newtype_names,
                type_aliases,
                ctor_details,
                depth + 1,
                visited,
            )
        }
        // Open vs closed — can't coerce
        _ => CoercibleResult::NotCoercible,
    }
}

/// Unwrap a newtype: given `N a1 a2 ...`, substitute the type vars in the wrapped type.
pub(crate) fn unwrap_newtype(
    type_name: &Qualified<TypeName>,
    args: &[&Type],
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
) -> Option<Type> {
    // Find a constructor for this newtype.
    // Match by name only (ignoring module qualifier) to handle qualified vs
    // unqualified references to the same type (e.g., C.Node vs Node).
    for (_, (parent, type_vars, field_types)) in ctor_details {
        if parent.name == type_name.name && field_types.len() == 1 {
            // Single-field constructor = newtype
            let wrapped_ty = &field_types[0];
            let subst: HashMap<TypeVarName, Type> = type_vars
                .iter()
                .zip(args.iter())
                .map(|(tv, arg)| (*tv, (*arg).clone()))
                .collect();
            return Some(apply_var_subst(&subst, wrapped_ty));
        }
    }
    None
}

/// Check structural equality of two types (without unification).
pub(crate) fn types_structurally_equal(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Con(a), Type::Con(b)) => a.name == b.name,
        (Type::Var(a), Type::Var(b)) => a == b,
        (Type::Unif(a), Type::Unif(b)) => a == b,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            types_structurally_equal(f1, f2) && types_structurally_equal(a1, a2)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            types_structurally_equal(a1, a2) && types_structurally_equal(b1, b2)
        }
        (Type::TypeString(a), Type::TypeString(b)) => a == b,
        (Type::TypeInt(a), Type::TypeInt(b)) => a == b,
        (Type::Record(fa, ta), Type::Record(fb, tb)) => {
            if fa.len() != fb.len() {
                return false;
            }
            let all_fields_eq = fa
                .iter()
                .zip(fb.iter())
                .all(|((la, ta), (lb, tb))| la == lb && types_structurally_equal(ta, tb));
            if !all_fields_eq {
                return false;
            }
            match (ta, tb) {
                (None, None) => true,
                (Some(a), Some(b)) => types_structurally_equal(a, b),
                _ => false,
            }
        }
        (Type::Forall(va, ba), Type::Forall(vb, bb)) => {
            if va.len() != vb.len() {
                return false;
            }
            // Simple check: same var names and same body
            let vars_eq = va.iter().zip(vb.iter()).all(|((a, _), (b, _))| a == b);
            vars_eq && types_structurally_equal(ba, bb)
        }
        _ => false,
    }
}

/// Match a pattern type against a target type, allowing type variables in the
/// pattern to match any type in the target. Returns true if the match succeeds
/// with a consistent substitution. Used in Coercible Rule 0 to match given
/// constraints (which may contain abstract type variables) against wanted constraints.
pub(crate) fn types_match_up_to_vars(pattern: &Type, target: &Type, subst: &mut HashMap<TypeVarName, Type>) -> bool {
    match (pattern, target) {
        // Type variables in the pattern can match anything
        (Type::Var(v), _) => {
            if let Some(existing) = subst.get(v) {
                types_structurally_equal(existing, target)
            } else {
                subst.insert(*v, target.clone());
                true
            }
        }
        // Concrete types must match structurally
        (Type::Con(a), Type::Con(b)) => a.name == b.name,
        (Type::Unif(a), Type::Unif(b)) => a == b,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            types_match_up_to_vars(f1, f2, subst) && types_match_up_to_vars(a1, a2, subst)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            types_match_up_to_vars(a1, a2, subst) && types_match_up_to_vars(b1, b2, subst)
        }
        (Type::TypeString(a), Type::TypeString(b)) => a == b,
        (Type::TypeInt(a), Type::TypeInt(b)) => a == b,
        (Type::Record(fa, ta), Type::Record(fb, tb)) => {
            if fa.len() != fb.len() {
                return false;
            }
            let all_fields = fa.iter().zip(fb.iter())
                .all(|((la, ta), (lb, tb))| la == lb && types_match_up_to_vars(ta, tb, subst));
            if !all_fields {
                return false;
            }
            match (ta, tb) {
                (None, None) => true,
                (Some(a), Some(b)) => types_match_up_to_vars(a, b, subst),
                _ => false,
            }
        }
        (Type::Forall(va, ba), Type::Forall(vb, bb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let vars_eq = va.iter().zip(vb.iter()).all(|((a, _), (b, _))| a == b);
            vars_eq && types_match_up_to_vars(ba, bb, subst)
        }
        _ => false,
    }
}
