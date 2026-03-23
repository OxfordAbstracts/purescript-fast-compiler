use std::collections::{HashMap, HashSet};

use crate::ast::TypeExpr;
use crate::cst::QualifiedIdent;
use crate::interner::{intern, Symbol};
use crate::typechecker::registry::DictExpr;
use crate::typechecker::types::Type;

use crate::cst::unqualified_ident;
use crate::names::TypeVarName;

use super::{
    apply_var_subst, contains_type_var, contains_type_var_or_unif, expand_type_aliases_inner,
    expand_type_aliases_limited_inner, extract_head_from_type_tc,
    lookup_instances, prim_qi, qi,
};


/// Result of instance resolution with depth tracking.
pub(crate) enum InstanceResult {
    Match,
    NoMatch,
    DepthExceeded,
    UnknownClass(QualifiedIdent),
}

/// Like `has_matching_instance_depth` but returns a tri-state result to distinguish
/// "no instance found" from "possibly infinite instance" (depth exceeded).
pub(crate) fn check_instance_depth(
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    class_name: &QualifiedIdent,
    concrete_args: &[Type],
    depth: u32,
    known_classes: Option<&HashSet<QualifiedIdent>>,
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
) -> InstanceResult {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    check_instance_depth_impl(instances, type_aliases, class_name, concrete_args, depth, known_classes, type_con_arities)
    })
}

pub(crate) fn check_instance_depth_impl(
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    class_name: &QualifiedIdent,
    concrete_args: &[Type],
    depth: u32,
    known_classes: Option<&HashSet<QualifiedIdent>>,
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
) -> InstanceResult {
    if depth > 200 {
        return InstanceResult::DepthExceeded;
    }

    // Check if the class is in scope (only for sub-constraints at depth > 0)
    // Also accept classes that have instances (covers Prim built-in classes like Nub)
    // Use lookup_instances for qualified fallback (e.g. SimpleJson.WriteForeign → WriteForeign).
    if depth > 0 {
        if let Some(kc) = known_classes {
            let kc_known = kc.contains(class_name) || (class_name.module.is_some() && kc.iter().any(|k| k.name == class_name.name));
            if !kc_known && lookup_instances(instances, class_name).is_none() {
                return InstanceResult::UnknownClass(*class_name);
            }
        }
    }

    // Built-in solver instances for compiler-magic type classes.
    let class_str = crate::interner::resolve(class_name.name)
        .unwrap_or_default()
        .to_string();
    match class_str.as_str() {
        "IsSymbol" => {
            if concrete_args.len() == 1 {
                if let Type::TypeString(_) = &concrete_args[0] {
                    return InstanceResult::Match;
                }
            }
        }
        "Reflectable" => {
            if concrete_args.len() == 2 {
                let matches = match (&concrete_args[0], &concrete_args[1]) {
                    (Type::TypeString(_), Type::Con(s)) => {
                        crate::interner::resolve(s.name).unwrap_or_default() == "String"
                    }
                    (Type::TypeInt(_), Type::Con(s)) => {
                        crate::interner::resolve(s.name).unwrap_or_default() == "Int"
                    }
                    (Type::Con(c), Type::Con(s)) => {
                        let c_str = crate::interner::resolve(c.name).unwrap_or_default().to_string();
                        let s_str = crate::interner::resolve(s.name).unwrap_or_default().to_string();
                        (c_str == "True" || c_str == "False") && s_str == "Boolean"
                            || (c_str == "LT" || c_str == "EQ" || c_str == "GT")
                                && s_str == "Ordering"
                    }
                    _ => false,
                };
                if matches {
                    return InstanceResult::Match;
                }
            }
        }
        "Append" => {
            if concrete_args.len() == 3 {
                match (&concrete_args[0], &concrete_args[1], &concrete_args[2]) {
                    (Type::TypeString(a), Type::TypeString(b), Type::TypeString(c)) => {
                        let a_str = crate::interner::resolve(*a).unwrap_or_default().to_string();
                        let b_str = crate::interner::resolve(*b).unwrap_or_default().to_string();
                        let c_str = crate::interner::resolve(*c).unwrap_or_default().to_string();
                        if format!("{}{}", a_str, b_str) == c_str {
                            return InstanceResult::Match;
                        }
                    }
                    _ => {}
                }
            }
        }
        "Lacks" => {
            // Lacks label row: the label must NOT appear in the row
            if concrete_args.len() == 2 {
                if let Type::TypeString(label_sym) = &concrete_args[0] {
                    let label_str = crate::interner::resolve(*label_sym)
                        .unwrap_or_default()
                        .to_string();
                    match &concrete_args[1] {
                        Type::Record(fields, tail) => {
                            let has_label = fields.iter().any(|(f, _)| {
                                f.eq_str(&label_str)
                            });
                            if has_label {
                                return InstanceResult::NoMatch;
                            }
                            match tail {
                                None => return InstanceResult::Match,
                                Some(t) => {
                                    if matches!(t.as_ref(), Type::Record(f, None) if f.is_empty()) {
                                        return InstanceResult::Match;
                                    }
                                    return InstanceResult::NoMatch;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        "RowToList" | "Nub" | "Union" | "Cons" | "Coercible" | "Partial"
        | "Warn" | "CompareSymbol" | "Compare" | "Add" | "Mul"
        | "ToString" | "Reifiable" => {
            return InstanceResult::Match;
        }
        "Fail" => {
            // Fail always fails — it's a compile-time error mechanism
            return InstanceResult::NoMatch;
        }
        _ => {}
    }

    let expanded_args: Vec<Type> = concrete_args
        .iter()
        .map(|t| {
            let mut expanding = HashSet::new();
            expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None)
        })
        .collect();

    let known = match lookup_instances(instances, class_name) {
        Some(k) => k,
        None => return InstanceResult::NoMatch,
    };

    let mut any_depth_exceeded = false;
    for (inst_types, inst_constraints, _inst_name) in known {
        let expanded_inst_types: Vec<Type> = inst_types
            .iter()
            .map(|t| {
                let mut expanding = HashSet::new();
                expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None)
            })
            .collect();
        if expanded_inst_types.len() != expanded_args.len() {
            continue;
        }

        let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
        let matched = expanded_inst_types
            .iter()
            .zip(expanded_args.iter())
            .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst));

        if !matched {
            continue;
        }

        if inst_constraints.is_empty() {
            return InstanceResult::Match;
        }

        let mut all_ok = true;
        for (c_class, c_args) in inst_constraints {
            let substituted_args: Vec<Type> =
                c_args.iter().map(|t| apply_var_subst(&subst, t)).collect();
            let has_unbound_vars = substituted_args.iter().any(|t| {
                fn has_var_or_unif(ty: &Type, subst: &HashMap<TypeVarName, Type>) -> bool {
                    match ty {
                        Type::Var(v) => !subst.contains_key(v),
                        // Unification variables are unresolved — can't check constraints involving them
                        Type::Unif(_) => true,
                        Type::App(f, a) => {
                            has_var_or_unif(f, subst) || has_var_or_unif(a, subst)
                        }
                        Type::Fun(a, b) => {
                            has_var_or_unif(a, subst) || has_var_or_unif(b, subst)
                        }
                        Type::Forall(_, body) => has_var_or_unif(body, subst),
                        Type::Record(fields, tail) => {
                            fields.iter().any(|(_, t)| has_var_or_unif(t, subst))
                                || tail
                                    .as_ref()
                                    .map_or(false, |t| has_var_or_unif(t, subst))
                        }
                        _ => false,
                    }
                }
                has_var_or_unif(t, &subst)
            });
            if has_unbound_vars {
                continue;
            }
            match check_instance_depth(
                instances,
                type_aliases,
                c_class,
                &substituted_args,
                depth + 1,
                known_classes,
                type_con_arities,
            ) {
                InstanceResult::Match => {}
                InstanceResult::DepthExceeded => {
                    any_depth_exceeded = true;
                    all_ok = false;
                    break;
                }
                InstanceResult::NoMatch => {
                    all_ok = false;
                    break;
                }
                r @ InstanceResult::UnknownClass(_) => return r,
            }
        }
        if all_ok {
            return InstanceResult::Match;
        }
    }

    if any_depth_exceeded {
        InstanceResult::DepthExceeded
    } else {
        InstanceResult::NoMatch
    }
}

pub(crate) fn has_matching_instance_depth(
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    class_name: &QualifiedIdent,
    concrete_args: &[Type],
    depth: u32,
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
) -> bool {
    if depth > 20 {
        // Avoid infinite recursion on circular constraint chains
        return false;
    }

    // Built-in solver instances for compiler-magic type classes.
    let class_str = crate::interner::resolve(class_name.name)
        .unwrap_or_default()
        .to_string();
    match class_str.as_str() {
        // IsSymbol "foo" always holds for any type-level string literal
        "IsSymbol" => {
            if concrete_args.len() == 1 {
                if let Type::TypeString(_) = &concrete_args[0] {
                    return true;
                }
            }
        }
        // Reflectable: literal types can be reflected to their value types
        "Reflectable" => {
            if concrete_args.len() == 2 {
                let matches = match (&concrete_args[0], &concrete_args[1]) {
                    (Type::TypeString(_), Type::Con(s)) => {
                        crate::interner::resolve(s.name).unwrap_or_default() == "String"
                    }
                    (Type::TypeInt(_), Type::Con(s)) => {
                        crate::interner::resolve(s.name).unwrap_or_default() == "Int"
                    }
                    (Type::Con(c), Type::Con(s)) => {
                        let c_str = crate::interner::resolve(c.name).unwrap_or_default().to_string();
                        let s_str = crate::interner::resolve(s.name).unwrap_or_default().to_string();
                        (c_str == "True" || c_str == "False") && s_str == "Boolean"
                            || (c_str == "LT" || c_str == "EQ" || c_str == "GT")
                                && s_str == "Ordering"
                    }
                    _ => false,
                };
                if matches {
                    return true;
                }
            }
        }
        // Append "A" "B" "AB" holds when the third argument is the concatenation
        "Append" => {
            if concrete_args.len() == 3 {
                match (&concrete_args[0], &concrete_args[1], &concrete_args[2]) {
                    (Type::TypeString(a), Type::TypeString(b), Type::TypeString(c)) => {
                        let a_str = crate::interner::resolve(*a).unwrap_or_default().to_string();
                        let b_str = crate::interner::resolve(*b).unwrap_or_default().to_string();
                        let c_str = crate::interner::resolve(*c).unwrap_or_default().to_string();
                        if format!("{}{}", a_str, b_str) == c_str {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
        "RowToList" | "Nub" | "Union" | "Cons" | "Lacks" | "Coercible" | "Partial"
        | "Warn" | "Fail" | "CompareSymbol" | "Compare" | "Add" | "Mul"
        | "ToString" | "Reifiable" => {
            return true;
        }
        _ => {}
    }

    // Expand type aliases in concrete args before matching (with over-saturated support)
    let expanded_args: Vec<Type> = concrete_args
        .iter()
        .map(|t| {
            let mut expanding = HashSet::new();
            expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None)
        })
        .collect();

    let known = match lookup_instances(instances, class_name) {
        Some(k) => k,
        None => {
            return false;
        }
    };

    known.iter().any(|(inst_types, inst_constraints, _)| {
        // Also expand aliases in instance types
        let expanded_inst_types: Vec<Type> = inst_types
            .iter()
            .map(|t| {
                let mut expanding = HashSet::new();
                expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None)
            })
            .collect();
        if expanded_inst_types.len() != expanded_args.len() {
            return false;
        }

        // Try to match instance types against concrete args, building a substitution
        let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
        let matched = expanded_inst_types
            .iter()
            .zip(expanded_args.iter())
            .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst));

        if !matched {
            return false;
        }

        // If there are no constraints, we're done
        if inst_constraints.is_empty() {
            return true;
        }

        inst_constraints.iter().all(|(c_class, c_args)| {
            let substituted_args: Vec<Type> =
                c_args.iter().map(|t| apply_var_subst(&subst, t)).collect();
            let has_vars = substituted_args.iter().any(|t| contains_type_var_or_unif(t));
            if has_vars {
                return true;
            }
            let result = has_matching_instance_depth(
                instances,
                type_aliases,
                c_class,
                &substituted_args,
                depth + 1,
                type_con_arities,
            );
            result
        })
    })
}

/// Recursively match an instance type pattern against a concrete type, building a substitution.
/// E.g. matches `App(Array, Var(a))` against `App(Array, JSON)` with subst {a → JSON}.
/// Check if a CST TypeExpr contains a Kinded annotation (type :: kind).
/// Check if a Type contains any type constructor that is in the given set of local type names.
/// Used for orphan instance detection: at least one type in the instance head must be local.
/// Collect all type constructor names (Type::Con) referenced in a type.
pub(crate) fn collect_type_constructors(ty: &Type, out: &mut Vec<Symbol>) {
    match ty {
        Type::Con(name) => {
            // Skip qualified type references (e.g. Subject.Checkbox) — they are imported
            // and do not require local export validation.
            if name.module.is_none() {
                out.push(name.name);
            }
        }
        Type::App(f, arg) => {
            collect_type_constructors(f, out);
            collect_type_constructors(arg, out);
        }
        Type::Fun(a, b) => {
            collect_type_constructors(a, out);
            collect_type_constructors(b, out);
        }
        Type::Forall(_, body) => collect_type_constructors(body, out),
        Type::Record(fields, tail) => {
            for (_, ty) in fields {
                collect_type_constructors(ty, out);
            }
            if let Some(t) = tail {
                collect_type_constructors(t, out);
            }
        }
        _ => {}
    }
}

pub(crate) fn type_has_vars(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::App(f, arg) => type_has_vars(f) || type_has_vars(arg),
        Type::Fun(a, b) => type_has_vars(a) || type_has_vars(b),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_has_vars(t))
                || tail.as_ref().map_or(false, |t| type_has_vars(t))
        }
        Type::Forall(_, body) => type_has_vars(body),
        _ => false,
    }
}

pub(crate) fn type_contains_record(ty: &Type) -> bool {
    // Flag record types at the top level that have concrete fields or are closed.
    // Open records like `{ | r }` are fine (equivalent to `Record r` which is nominal).
    // Records nested inside type constructors (e.g. `Maybe { x :: Int }`) are also fine.
    match ty {
        Type::Record(fields, tail) => !fields.is_empty() || tail.is_none(),
        _ => false,
    }
}

pub(crate) fn type_has_local_con(ty: &Type, local_types: &HashSet<Symbol>) -> bool {
    match ty {
        Type::Con(name) => local_types.contains(&name.name),
        Type::App(f, arg) => {
            type_has_local_con(f, local_types) || type_has_local_con(arg, local_types)
        }
        _ => false,
    }
}

/// Check if an instance is orphan, considering functional dependencies.
/// With fundeps, every covering set must have at least one locally-defined type.
/// Without fundeps, at least one type in the instance head must be local.
pub(crate) fn check_orphan_with_fundeps(
    inst_types: &[Type],
    class_name: &QualifiedIdent,
    class_fundeps: &HashMap<QualifiedIdent, (Vec<Symbol>, Vec<(Vec<usize>, Vec<usize>)>)>,
    local_type_names: &HashSet<Symbol>,
) -> bool {
    if inst_types.is_empty() {
        return true; // Nullary classes are always orphan if class is imported
    }

    // Check which parameter positions have local types
    let local_positions: Vec<bool> = inst_types
        .iter()
        .map(|ty| type_has_local_con(ty, local_type_names))
        .collect();

    // If no fundeps, use simple check: any position has local type
    let fundeps = match class_fundeps.get(class_name) {
        Some((_, fds)) if !fds.is_empty() => fds,
        _ => return !local_positions.iter().any(|&x| x),
    };

    // Compute covering sets and check each one
    let n = inst_types.len();
    let covering_sets = compute_covering_sets(n, fundeps);

    // Every covering set must have at least one local type.
    // Empty covering sets (from `| -> r` fundeps) trivially satisfy this
    // since they need no types to determine the instance.
    for covering_set in &covering_sets {
        if covering_set.is_empty() {
            continue; // Empty covering set: always determined, no local type needed
        }
        let has_local = covering_set
            .iter()
            .any(|&idx| idx < n && local_positions[idx]);
        if !has_local {
            return true; // This covering set has no local type → orphan
        }
    }
    false
}

/// Compute minimal covering sets from functional dependencies.
/// A covering set is a minimal subset of parameter indices whose functional closure
/// equals all parameter indices.
pub(crate) fn compute_covering_sets(n: usize, fundeps: &[(Vec<usize>, Vec<usize>)]) -> Vec<Vec<usize>> {
    let all: HashSet<usize> = (0..n).collect();
    let mut covering: Vec<Vec<usize>> = Vec::new();

    // Try all subsets from smallest to largest (including empty set for `| -> r` fundeps)
    let empty_closure = fundep_closure(&[], fundeps);
    if empty_closure == all {
        covering.push(vec![]);
    }
    for size in 1..=n {
        for subset in combinations(n, size) {
            // Skip if any existing covering set is a subset of this one
            if covering
                .iter()
                .any(|cs| cs.iter().all(|x| subset.contains(x)))
            {
                continue;
            }
            let closure = fundep_closure(&subset, fundeps);
            if closure == all {
                covering.push(subset);
            }
        }
    }
    covering
}

/// Compute the functional dependency closure of a set of parameter indices.
pub(crate) fn fundep_closure(initial: &[usize], fundeps: &[(Vec<usize>, Vec<usize>)]) -> HashSet<usize> {
    let mut result: HashSet<usize> = initial.iter().copied().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for (lhs, rhs) in fundeps {
            if lhs.iter().all(|x| result.contains(x)) {
                for &r in rhs {
                    if result.insert(r) {
                        changed = true;
                    }
                }
            }
        }
    }
    result
}

/// Generate all combinations of `size` elements from 0..n.
pub(crate) fn combinations(n: usize, size: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    let mut current = Vec::new();
    fn helper(
        start: usize,
        n: usize,
        remaining: usize,
        current: &mut Vec<usize>,
        result: &mut Vec<Vec<usize>>,
    ) {
        if remaining == 0 {
            result.push(current.clone());
            return;
        }
        for i in start..n {
            current.push(i);
            helper(i + 1, n, remaining - 1, current, result);
            current.pop();
        }
    }
    helper(0, n, size, &mut current, &mut result);
    result
}

pub(crate) fn type_expr_has_kinded(ty: &crate::ast::TypeExpr) -> bool {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Kinded { .. } => true,
        TypeExpr::App {
            constructor, arg, ..
        } => type_expr_has_kinded(constructor) || type_expr_has_kinded(arg),
        TypeExpr::Function { from, to, .. } => {
            type_expr_has_kinded(from) || type_expr_has_kinded(to)
        }
        TypeExpr::Forall { ty, .. } => type_expr_has_kinded(ty),
        TypeExpr::Constrained { ty, .. } => type_expr_has_kinded(ty),
        _ => false,
    }
}

/// Extract kind annotations from CST type expressions.
/// Returns a map from type variable name → kind name (e.g. "Type", "Symbol").
/// Used for polykinded instance dispatch.
pub(crate) fn extract_kind_annotations(types: &[TypeExpr]) -> HashMap<Symbol, Symbol> {
    let mut result = HashMap::new();
    fn walk(ty: &TypeExpr, result: &mut HashMap<Symbol, Symbol>) {
        match ty {
            TypeExpr::Kinded { ty, kind, .. } => {
                // If the inner type is a variable, record its kind
                if let TypeExpr::Var { name, .. } = ty.as_ref() {
                    if let Some(kind_name) = extract_kind_name_ast(kind) {
                        result.insert(name.value, kind_name);
                    }
                }
                walk(ty, result);
            }
            TypeExpr::App { constructor, arg, .. } => {
                walk(constructor, result);
                walk(arg, result);
            }
            TypeExpr::Function { from, to, .. } => {
                walk(from, result);
                walk(to, result);
            }
            TypeExpr::Forall { ty, .. } => walk(ty, result),
            TypeExpr::Constrained { ty, .. } => walk(ty, result),
            _ => {}
        }
    }
    for ty in types {
        walk(ty, &mut result);
    }
    result
}

/// Extract a simple kind name from an AST kind expression.
pub(crate) fn extract_kind_name_ast(kind: &TypeExpr) -> Option<Symbol> {
    match kind {
        TypeExpr::Constructor { name, .. } => Some(name.name),
        TypeExpr::Var { name, .. } => Some(name.value),
        _ => None,
    }
}

/// Check if two lists of CST TypeExprs are alpha-equivalent (including kind annotations).
/// Used for overlap detection when kind annotations are present, since the internal Type
/// representation strips kind info.
pub(crate) fn type_exprs_alpha_eq_list(a: &[crate::ast::TypeExpr], b: &[crate::ast::TypeExpr]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut var_map: HashMap<Symbol, Symbol> = HashMap::new();
    a.iter()
        .zip(b.iter())
        .all(|(x, y)| type_expr_alpha_eq(x, y, &mut var_map))
}

/// Check if two CST TypeExprs are alpha-equivalent (variables map consistently).
pub(crate) fn type_expr_alpha_eq(
    a: &crate::ast::TypeExpr,
    b: &crate::ast::TypeExpr,
    var_map: &mut HashMap<Symbol, Symbol>,
) -> bool {
    use crate::ast::TypeExpr;
    match (a, b) {
        (TypeExpr::Var { name: na, .. }, TypeExpr::Var { name: nb, .. }) => {
            if let Some(mapped) = var_map.get(&na.value) {
                *mapped == nb.value
            } else {
                var_map.insert(na.value, nb.value);
                true
            }
        }
        (TypeExpr::Constructor { name: na, .. }, TypeExpr::Constructor { name: nb, .. }) => {
            na.name == nb.name && na.module == nb.module
        }
        (
            TypeExpr::App {
                constructor: ca,
                arg: aa,
                ..
            },
            TypeExpr::App {
                constructor: cb,
                arg: ab,
                ..
            },
        ) => type_expr_alpha_eq(ca, cb, var_map) && type_expr_alpha_eq(aa, ab, var_map),
        (
            TypeExpr::Function {
                from: fa, to: ta, ..
            },
            TypeExpr::Function {
                from: fb, to: tb, ..
            },
        ) => type_expr_alpha_eq(fa, fb, var_map) && type_expr_alpha_eq(ta, tb, var_map),
        (
            TypeExpr::Kinded {
                ty: ta, kind: ka, ..
            },
            TypeExpr::Kinded {
                ty: tb, kind: kb, ..
            },
        ) => type_expr_alpha_eq(ta, tb, var_map) && type_expr_alpha_eq(ka, kb, var_map),
        (
            TypeExpr::Forall {
                vars: va, ty: ta, ..
            },
            TypeExpr::Forall {
                vars: vb, ty: tb, ..
            },
        ) => {
            if va.len() != vb.len() {
                return false;
            }
            for ((a_var, a_vis, _a_kind), (b_var, b_vis, _b_kind)) in va.iter().zip(vb.iter()) {
                if a_vis != b_vis {
                    return false;
                }
                var_map.insert(a_var.value, b_var.value);
            }
            type_expr_alpha_eq(ta, tb, var_map)
        }
        (TypeExpr::StringLiteral { value: va, .. }, TypeExpr::StringLiteral { value: vb, .. }) => {
            va == vb
        }
        (TypeExpr::IntLiteral { value: va, .. }, TypeExpr::IntLiteral { value: vb, .. }) => {
            va == vb
        }
        _ => false,
    }
}

/// Check if two instance heads are identical (alpha-equivalent after alias expansion).
/// This catches cases like `Convert String Bar` vs `Convert String String` (when Bar = String).
/// Does NOT match `Foo a` vs `Foo Int` — those are "overlapping" but valid at definition time.
/// `no_expand` names are excluded from alias expansion — used for locally-defined data/newtypes
/// whose names might collide with imported type aliases from other modules.
pub(crate) fn instance_heads_overlap(
    types_a: &[Type],
    types_b: &[Type],
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    no_expand: &HashSet<Symbol>,
) -> bool {
    if types_a.len() != types_b.len() {
        return false;
    }
    // Pre-seed the expanding set with locally-defined data/newtype names
    // to prevent alias expansion for those names (avoids false overlaps
    // e.g. newtype Thread matching Record via imported Thread alias).
    let seed: HashSet<QualifiedIdent> = no_expand.iter().map(|s| qi(*s)).collect();
    let expanded_a: Vec<Type> = types_a
        .iter()
        .map(|t| {
            let mut expanding = seed.clone();
            expand_type_aliases_inner(t, type_aliases, 0, &mut expanding)
        })
        .collect();
    let expanded_b: Vec<Type> = types_b
        .iter()
        .map(|t| {
            let mut expanding = seed.clone();
            expand_type_aliases_inner(t, type_aliases, 0, &mut expanding)
        })
        .collect();
    // Check alpha-equivalence: type variables match other type variables (positionally),
    // but concrete types must be structurally identical.
    let mut var_map: HashMap<TypeVarName, TypeVarName> = HashMap::new();
    if expanded_a
        .iter()
        .zip(expanded_b.iter())
        .all(|(a, b)| instance_types_alpha_eq(a, b, &mut var_map))
    {
        return true;
    }
    // Also check subsumption: if one instance head is strictly more general than the other,
    // they overlap. E.g. `instance Test a` subsumes `instance Test Int`.
    // Check both directions: A subsumes B, or B subsumes A.
    // Use strict constructor comparison to avoid false positives when types from
    // different modules share the same unqualified name (e.g. List vs Lazy.List).
    let mut subst_ab: HashMap<TypeVarName, Type> = HashMap::new();
    let a_subsumes_b = expanded_a
        .iter()
        .zip(expanded_b.iter())
        .all(|(a, b)| match_instance_type_strict(a, b, &mut subst_ab));
    if a_subsumes_b {
        return true;
    }
    let mut subst_ba: HashMap<TypeVarName, Type> = HashMap::new();
    expanded_b
        .iter()
        .zip(expanded_a.iter())
        .all(|(b, a)| match_instance_type_strict(b, a, &mut subst_ba))
}

/// Check if two instance types are alpha-equivalent (identical up to variable renaming).
/// Var matches Var (with consistent renaming), Con matches Con, but Var does NOT match Con.
pub(crate) fn instance_types_alpha_eq(a: &Type, b: &Type, var_map: &mut HashMap<TypeVarName, TypeVarName>) -> bool {
    match (a, b) {
        (Type::Var(x), Type::Var(y)) => {
            // Variables must map consistently
            if let Some(mapped) = var_map.get(x) {
                *mapped == *y
            } else {
                var_map.insert(*x, *y);
                true
            }
        }
        (Type::Con(x), Type::Con(y)) => x == y,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            instance_types_alpha_eq(f1, f2, var_map) && instance_types_alpha_eq(a1, a2, var_map)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            instance_types_alpha_eq(a1, a2, var_map) && instance_types_alpha_eq(b1, b2, var_map)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            if f1.len() != f2.len() {
                return false;
            }
            for ((l1, ty1), (l2, ty2)) in f1.iter().zip(f2.iter()) {
                if l1 != l2 || !instance_types_alpha_eq(ty1, ty2, var_map) {
                    return false;
                }
            }
            match (t1, t2) {
                (None, None) => true,
                (Some(a), Some(b)) => instance_types_alpha_eq(a, b, var_map),
                _ => false,
            }
        }
        (Type::TypeString(x), Type::TypeString(y)) => x == y,
        (Type::TypeInt(x), Type::TypeInt(y)) => x == y,
        _ => a == b,
    }
}

/// Check if two type constructor names are equivalent, accounting for
/// the `(->)` / `Function` alias (they're the same type in PureScript).
pub(crate) fn type_con_names_eq(a: Symbol, b: Symbol) -> bool {
    a == b || {
        let a_str = crate::interner::resolve(a).unwrap_or_default();
        let b_str = crate::interner::resolve(b).unwrap_or_default();
        (a_str == "->" || a_str == "Function") && (b_str == "->" || b_str == "Function")
    }
}

/// Module-aware type constructor comparison.
/// When both types have module qualifiers and they differ, the types are distinct
/// (e.g., `List.List` vs `LazyList.List` are different types even though both are named "List").
/// When either type has no module qualifier, falls back to name-only comparison.
pub(crate) fn type_con_qi_eq(a: &QualifiedIdent, b: &QualifiedIdent) -> bool {
    // When both have module qualifiers and they match, that's a strong positive.
    // When they differ, DON'T return false — the difference may be due to
    // import aliases vs canonical module names (e.g., "FO" vs "Foreign.Object"
    // both referring to Foreign.Object.Object). Always fall back to name comparison.
    type_con_names_eq(a.name, b.name)
}

/// Strict module-aware type constructor comparison for overlap checking.
/// Unlike `type_con_qi_eq`, when one type has a module qualifier and the other
/// doesn't, treats them as distinct (e.g., `List` vs `Lazy.List`).
pub(crate) fn type_con_qi_eq_strict(a: &QualifiedIdent, b: &QualifiedIdent) -> bool {
    match (a.module, b.module) {
        (Some(ma), Some(mb)) => {
            if ma != mb {
                return false;
            }
        }
        (Some(_), None) | (None, Some(_)) => {
            return false;
        }
        (None, None) => {}
    }
    type_con_names_eq(a.name, b.name)
}

/// Compare two types for equality, using lenient module-qualifier comparison for type constructors.
/// This handles cases where the same type is referenced as `DecodeError` (unqualified) and
/// `Error.DecodeError` (qualified through an import alias).
pub(crate) fn types_eq_lenient(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Con(ca), Type::Con(cb)) => type_con_qi_eq(ca, cb),
        (Type::App(f1, a1), Type::App(f2, a2)) => types_eq_lenient(f1, f2) && types_eq_lenient(a1, a2),
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => types_eq_lenient(a1, a2) && types_eq_lenient(b1, b2),
        (Type::Forall(v1, body1), Type::Forall(v2, body2)) => {
            v1.len() == v2.len() && types_eq_lenient(body1, body2)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            f1.len() == f2.len()
                && f1.iter().zip(f2.iter()).all(|((l1, ty1), (l2, ty2))| l1 == l2 && types_eq_lenient(ty1, ty2))
                && match (t1, t2) {
                    (None, None) => true,
                    (Some(a), Some(b)) => types_eq_lenient(a, b),
                    _ => false,
                }
        }
        _ => a == b,
    }
}

/// Recursively match an instance type pattern against a concrete type, building a substitution.
/// E.g. matches `App(Array, Var(a))` against `App(Array, JSON)` with subst {a → JSON}.
pub(crate) fn match_instance_type(inst_ty: &Type, concrete: &Type, subst: &mut HashMap<TypeVarName, Type>) -> bool {
    match (inst_ty, concrete) {
        (Type::Var(v), _) => {
            if let Some(existing) = subst.get(v) {
                // Use lenient comparison that ignores module qualifiers on type constructors.
                // This handles cases like `DecodeError` vs `Error.DecodeError` referring to
                // the same type through different import paths.
                types_eq_lenient(existing, concrete)
            } else {
                subst.insert(*v, concrete.clone());
                true
            }
        }
        // Unif in concrete position: treat as wildcard match (after Var binding).
        // Handles functional-dependency output params (like `rep` in `Generic a rep`)
        // where codegen deferred constraints have unsolved unif vars.
        (_, Type::Unif(_)) => true,
        (Type::Con(a), Type::Con(b)) => type_con_qi_eq(a, b),
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            match_instance_type(f1, f2, subst) && match_instance_type(a1, a2, subst)
        }
        // Fun(a, b) is equivalent to App(App(Con(Function), a), b) in PureScript.
        // Allow App patterns to match Fun types and vice versa.
        (Type::App(_, _), Type::Fun(a, b)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type(inst_ty, &desugared, subst)
        }
        (Type::Fun(a, b), Type::App(_, _)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type(&desugared, concrete, subst)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            match_instance_type(a1, a2, subst) && match_instance_type(b1, b2, subst)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            let mut remaining2: Vec<(crate::names::LabelName, Type)> = f2.to_vec();
            for (l1, ty1) in f1 {
                if let Some(idx) = remaining2.iter().position(|(l, _)| l == l1) {
                    let (_, ty2) = remaining2.remove(idx);
                    if !match_instance_type(ty1, &ty2, subst) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            match (t1, remaining2.is_empty(), t2) {
                (None, true, None) => true,
                (None, true, Some(_)) => false,
                (None, false, _) => false,
                (Some(tail), _, _) => {
                    let residual = Type::Record(remaining2, t2.clone());
                    match_instance_type(tail, &residual, subst)
                }
            }
        }
        // App(Con("Record"), row) vs Record(fields, tail): `Record row` matches any record
        (Type::App(f, inst_row), Type::Record(..)) => {
            if let Type::Con(sym) = f.as_ref() {
                let name = crate::interner::resolve(sym.name).unwrap_or_default();
                if name == "Record" {
                    return match_instance_type(inst_row, concrete, subst);
                }
            }
            inst_ty == concrete
        }
        (Type::Record(..), Type::App(f, concrete_row)) => {
            if let Type::Con(sym) = f.as_ref() {
                let name = crate::interner::resolve(sym.name).unwrap_or_default();
                if name == "Record" {
                    return match_instance_type(inst_ty, concrete_row, subst);
                }
            }
            inst_ty == concrete
        }
        (Type::TypeString(a), Type::TypeString(b)) => a == b,
        (Type::TypeInt(a), Type::TypeInt(b)) => a == b,
        _ => inst_ty == concrete,
    }
}

/// Check if a concrete type is compatible with the named kind.
/// Used for polykinded instance dispatch to reject kind mismatches.
pub(crate) fn type_matches_kind(ty: &Type, kind_name: &str) -> bool {
    match kind_name {
        "Symbol" => {
            // Only TypeString values have kind Symbol
            matches!(ty, Type::TypeString(_))
        }
        "Int" => {
            // Only TypeInt values have kind Int
            matches!(ty, Type::TypeInt(_))
        }
        "Type" => {
            // Regular types: Con, App, Fun, Record, Forall, Var, Unif
            // Specifically NOT TypeString or TypeInt
            !matches!(ty, Type::TypeString(_) | Type::TypeInt(_))
        }
        _ => {
            // Unknown kind — don't restrict matching
            true
        }
    }
}

/// Like `match_instance_type` but uses strict module-aware constructor comparison.
/// Used for overlap checking where `List` (unqualified) and `Lazy.List` (qualified)
/// must be treated as distinct types.
pub(crate) fn match_instance_type_strict(inst_ty: &Type, concrete: &Type, subst: &mut HashMap<TypeVarName, Type>) -> bool {
    match (inst_ty, concrete) {
        (Type::Var(v), _) => {
            if let Some(existing) = subst.get(v) {
                existing == concrete
            } else {
                subst.insert(*v, concrete.clone());
                true
            }
        }
        (Type::Con(a), Type::Con(b)) => type_con_qi_eq_strict(a, b),
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            match_instance_type_strict(f1, f2, subst) && match_instance_type_strict(a1, a2, subst)
        }
        (Type::App(_, _), Type::Fun(a, b)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type_strict(inst_ty, &desugared, subst)
        }
        (Type::Fun(a, b), Type::App(_, _)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type_strict(&desugared, concrete, subst)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            match_instance_type_strict(a1, a2, subst) && match_instance_type_strict(b1, b2, subst)
        }
        _ => inst_ty == concrete,
    }
}

/// Check if a type variable occurs in a type — used for infinite type detection.
pub(crate) fn occurs_var(v: TypeVarName, ty: &Type) -> bool {
    match ty {
        Type::Var(w) => v == *w,
        Type::App(f, a) => occurs_var(v, f) || occurs_var(v, a),
        Type::Fun(a, b) => occurs_var(v, a) || occurs_var(v, b),
        Type::Forall(_, body) => occurs_var(v, body),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| occurs_var(v, t))
                || tail.as_ref().map_or(false, |t| occurs_var(v, t))
        }
        _ => false,
    }
}

/// Check if two types could potentially be unified, treating Type::Var and Type::Unif
/// as "could be anything" (but checking for infinite types via occurs check).
pub(crate) fn could_unify_types(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Var(v), t) | (t, Type::Var(v)) => !occurs_var(*v, t),
        (Type::Unif(_), _) | (_, Type::Unif(_)) => true,
        (Type::Con(x), Type::Con(y)) => x == y,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            could_unify_types(f1, f2) && could_unify_types(a1, a2)
        }
        (app @ Type::App(_, _), Type::Fun(fa, fb)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi(function_sym))), fa.clone())),
                fb.clone(),
            );
            could_unify_types(app, &desugared)
        }
        (Type::Fun(fa, fb), app @ Type::App(_, _)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi(function_sym))), fa.clone())),
                fb.clone(),
            );
            could_unify_types(&desugared, app)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            could_unify_types(a1, a2) && could_unify_types(b1, b2)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            if f1.len() != f2.len() {
                return false;
            }
            for ((l1, ty1), (l2, ty2)) in f1.iter().zip(f2.iter()) {
                if l1 != l2 || !could_unify_types(ty1, ty2) {
                    return false;
                }
            }
            match (t1, t2) {
                (None, None) => true,
                (Some(a), Some(b)) => could_unify_types(a, b),
                _ => false,
            }
        }
        (Type::TypeString(x), Type::TypeString(y)) => x == y,
        (Type::TypeInt(x), Type::TypeInt(y)) => x == y,
        _ => a == b,
    }
}

/// Liberal version of match_instance_type for chain ambiguity checking.
/// Treats Type::Var and Type::Unif in the concrete type as "could be anything".
/// Returns true if the instance COULD POSSIBLY match the concrete args.
pub(crate) fn could_match_instance_type(
    inst_ty: &Type,
    concrete: &Type,
    subst: &mut HashMap<TypeVarName, Type>,
) -> bool {
    match (inst_ty, concrete) {
        // Instance type variable matches anything
        (Type::Var(v), _) => {
            if let Some(existing) = subst.get(v).cloned() {
                could_unify_types(&existing, concrete)
            } else {
                subst.insert(*v, concrete.clone());
                true
            }
        }
        // Concrete type variable or unif var could be anything
        (_, Type::Var(_)) | (_, Type::Unif(_)) => true,
        (Type::Con(a), Type::Con(b)) => type_con_qi_eq(a, b),
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            could_match_instance_type(f1, f2, subst) && could_match_instance_type(a1, a2, subst)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            could_match_instance_type(a1, a2, subst) && could_match_instance_type(b1, b2, subst)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            if f1.len() != f2.len() {
                return false;
            }
            for ((l1, ty1), (l2, ty2)) in f1.iter().zip(f2.iter()) {
                if l1 != l2 || !could_match_instance_type(ty1, ty2, subst) {
                    return false;
                }
            }
            match (t1, t2) {
                (None, None) => true,
                (Some(a), Some(b)) => could_match_instance_type(a, b, subst),
                _ => false,
            }
        }
        (Type::TypeString(a), Type::TypeString(b)) => a == b,
        (Type::TypeInt(a), Type::TypeInt(b)) => a == b,
        _ => inst_ty == concrete,
    }
}

/// Result of chain ambiguity analysis.
pub(crate) enum ChainResult {
    /// The chain definitely resolves to a matching instance.
    Resolved,
    /// The chain is ambiguous — an instance could match but doesn't definitely match.
    Ambiguous,
    /// No instance in the chain could even potentially match.
    NoMatch,
}

/// Check if an instance chain can be resolved for the given concrete args.
/// Processes instances in order and checks for "Apart" (can't match) vs "could match".
/// If an instance could match but doesn't definitely match, the chain is ambiguous.
pub(crate) fn check_chain_ambiguity(
    instances: &[(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)],
    concrete_args: &[Type],
) -> ChainResult {
    for (inst_types, _inst_constraints, _) in instances {
        if inst_types.len() != concrete_args.len() {
            continue;
        }

        // Check if this instance could potentially match (liberal check)
        let mut liberal_subst: HashMap<TypeVarName, Type> = HashMap::new();
        let could_match = inst_types
            .iter()
            .zip(concrete_args.iter())
            .all(|(inst_ty, arg)| could_match_instance_type(inst_ty, arg, &mut liberal_subst));

        if !could_match {
            // Instance is Apart — skip to next in chain
            continue;
        }

        // Instance could match. Check if it definitely matches (exact check).
        let mut exact_subst: HashMap<TypeVarName, Type> = HashMap::new();
        let definitely_matches = inst_types
            .iter()
            .zip(concrete_args.iter())
            .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut exact_subst));

        if definitely_matches {
            // Chain resolves at this instance
            return ChainResult::Resolved;
        }

        // Could match but doesn't definitely match — ambiguous
        return ChainResult::Ambiguous;
    }

    // No instance could even potentially match
    ChainResult::NoMatch
}

/// Graph-based solver for type-level integer comparison constraints.
/// Uses directed graph reachability to transitively reason about orderings.
///
/// Given constraints like `Compare a b LT, Compare b c LT`, builds a graph
/// with edges a→b, b→c and can derive that `Compare a c LT` (path a→c exists).
///
/// Based on the PureScript compiler's IntCompare solver.
pub(crate) fn solve_compare_graph(
    given_relations: &[(Type, Type, &str)], // (lhs, rhs, "LT"|"EQ"|"GT")
    extra_concrete_ints: &[Type],           // additional TypeInt values for fact generation
    lhs: &Type,
    rhs: &Type,
) -> Option<QualifiedIdent> {
    if lhs == rhs {
        return Some(unqualified_ident("Eq"));
    }

    // Build adjacency list: directed edges
    // EQ → bidirectional edges (cycle), LT → lhs→rhs, GT → rhs→lhs
    let mut nodes: Vec<Type> = Vec::new();
    let node_idx = |t: &Type, nodes: &mut Vec<Type>| -> usize {
        if let Some(pos) = nodes.iter().position(|n| n == t) {
            pos
        } else {
            nodes.push(t.clone());
            nodes.len() - 1
        }
    };

    // Collect all edges
    let mut edges: Vec<(usize, usize)> = Vec::new();

    for (l, r, ord) in given_relations {
        let li = node_idx(l, &mut nodes);
        let ri = node_idx(r, &mut nodes);
        match *ord {
            "EQ" => {
                edges.push((li, ri));
                edges.push((ri, li));
            }
            "LT" => {
                edges.push((li, ri));
            }
            "GT" => {
                edges.push((ri, li));
            }
            _ => {}
        }
    }

    // Also add ordering facts between concrete integers found in constraints.
    // Extract all concrete TypeLevelInt values that appear alongside non-concrete args.
    let mut concrete_ints: Vec<(i64, usize)> = Vec::new(); // (value, node_index)
    for (l, r, _) in given_relations {
        let l_is_int = matches!(l, Type::TypeInt(_));
        let r_is_int = matches!(r, Type::TypeInt(_));
        // Only add facts when not both concrete (the concrete solver handles that)
        if l_is_int && !r_is_int {
            if let Type::TypeInt(v) = l {
                let idx = node_idx(l, &mut nodes);
                concrete_ints.push((*v, idx));
            }
        }
        if r_is_int && !l_is_int {
            if let Type::TypeInt(v) = r {
                let idx = node_idx(r, &mut nodes);
                concrete_ints.push((*v, idx));
            }
        }
    }
    // Include extra concrete integers from wanted constraints
    for t in extra_concrete_ints {
        if let Type::TypeInt(v) = t {
            let idx = node_idx(t, &mut nodes);
            concrete_ints.push((*v, idx));
        }
    }
    // Check the query args too
    if let Type::TypeInt(v) = lhs {
        let idx = node_idx(lhs, &mut nodes);
        concrete_ints.push((*v, idx));
    }
    if let Type::TypeInt(v) = rhs {
        let idx = node_idx(rhs, &mut nodes);
        concrete_ints.push((*v, idx));
    }
    // Deduplicate
    concrete_ints.sort_by_key(|(v, _)| *v);
    concrete_ints.dedup_by_key(|(v, _)| *v);
    // Create LessThan edges between consecutive concrete integers
    for window in concrete_ints.windows(2) {
        if let [(v1, idx1), (v2, idx2)] = window {
            if v1 < v2 {
                edges.push((*idx1, *idx2));
            }
        }
    }

    // Ensure query nodes exist
    let lhs_idx = node_idx(lhs, &mut nodes);
    let rhs_idx = node_idx(rhs, &mut nodes);

    // Build adjacency list for BFS
    let n = nodes.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (from, to) in &edges {
        adj[*from].push(*to);
    }

    // BFS reachability check
    let reachable = |start: usize, end: usize| -> bool {
        if start == end {
            return true;
        }
        let mut visited = vec![false; n];
        let mut queue = std::collections::VecDeque::new();
        visited[start] = true;
        queue.push_back(start);
        while let Some(node) = queue.pop_front() {
            for &next in &adj[node] {
                if next == end {
                    return true;
                }
                if !visited[next] {
                    visited[next] = true;
                    queue.push_back(next);
                }
            }
        }
        false
    };

    let lhs_to_rhs = reachable(lhs_idx, rhs_idx);
    let rhs_to_lhs = reachable(rhs_idx, lhs_idx);

    match (lhs_to_rhs, rhs_to_lhs) {
        (true, true) => Some(prim_qi(intern("EQ"))),
        (true, false) => Some(prim_qi(intern("LT"))),
        (false, true) => Some(prim_qi(intern("GT"))),
        (false, false) => None, // Can't determine
    }
}

/// E.g., `Parallel ?f Aff` matched against `instance Parallel ParAff Aff`
/// → unify `?f` with `ParAff`.
pub(crate) fn try_unify_from_instance(
    state: &mut crate::typechecker::unify::UnifyState,
    class_name: &QualifiedIdent,
    concrete_args: &[Type],
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
    _instance_var_kinds: &HashMap<Symbol, HashMap<Symbol, Symbol>>,
) {
    if let Some(known) = lookup_instances(instances, class_name) {
        for (inst_types, _inst_constraints, _) in known {
            if inst_types.len() != concrete_args.len() {
                continue;
            }
            let mut expanding = HashSet::new();
            let expanded_args: Vec<Type> = concrete_args
                .iter()
                .map(|t| expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None))
                .collect();
            let expanded_inst: Vec<Type> = inst_types
                .iter()
                .map(|t| {
                    let mut exp = HashSet::new();
                    expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut exp, None)
                })
                .collect();
            // Check if this instance matches (same logic as match_instance_type)
            let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
            let matched = expanded_inst.iter().zip(expanded_args.iter())
                .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst));
            if matched {
                // Found the matching instance. For each concrete arg that's a Unif,
                // unify it with the corresponding fully-substituted instance type.
                for (inst_ty, arg) in expanded_inst.iter().zip(expanded_args.iter()) {
                    if let Type::Unif(_) = arg {
                        // Apply the instance's var substitution to get the concrete type
                        let concrete_inst_ty = apply_var_subst(&subst, inst_ty);
                        // Only unify if the instance type is concrete (no Var remaining)
                        if !contains_type_var(&concrete_inst_ty) {
                            let _ = state.unify(crate::span::Span { start: 0, end: 0 }, arg, &concrete_inst_ty);
                        }
                    }
                }
                return;
            }
        }
    }
}

pub(crate) fn resolve_dict_expr_from_registry(
    combined_registry: &HashMap<(Symbol, Symbol), (Symbol, Option<Vec<Symbol>>)>,
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    class_name: &QualifiedIdent,
    concrete_args: &[Type],
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
    instance_var_kinds: &HashMap<Symbol, HashMap<Symbol, Symbol>>,
) -> Option<DictExpr> {
    resolve_dict_expr_from_registry_inner(
        combined_registry, instances, type_aliases,
        class_name, concrete_args, type_con_arities, None, None, false, 0,
        instance_var_kinds,
    )
}

pub(crate) fn resolve_dict_expr_from_registry_inner(
    combined_registry: &HashMap<(Symbol, Symbol), (Symbol, Option<Vec<Symbol>>)>,
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    class_name: &QualifiedIdent,
    concrete_args: &[Type],
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
    given_constraints: Option<&[(QualifiedIdent, Vec<Type>)]>,
    mut given_used_positions: Option<&mut Vec<Option<Vec<Type>>>>,
    is_sub_constraint: bool,
    depth: u32,
    instance_var_kinds: &HashMap<Symbol, HashMap<Symbol, Symbol>>,
) -> Option<DictExpr> {
    if depth > 50 {
        return None; // Prevent infinite recursion in deeply nested instance chains
    }
    // Skip compiler-magic classes (Partial, Coercible, RowToList, etc.)
    let class_str = crate::interner::resolve(class_name.name)
        .unwrap_or_default()
        .to_string();

    // Handle IsSymbol constraints — generate inline dictionaries from type-level symbol literals.
    if class_str == "IsSymbol" { // TODO: this should include module as well as class name 
        if let Some(Type::TypeString(sym)) = concrete_args.first() {
            let label = crate::interner::resolve(*sym).unwrap_or_default().to_string();
            return Some(DictExpr::InlineIsSymbol(label));
        }
        return None;
    }

    // Handle Reflectable constraints — generate inline dictionaries from type-level literals.
    if class_str == "Reflectable" { // TODO: this should include module as well as class name 
        if let Some(first_arg) = concrete_args.first() {
            use crate::typechecker::registry::ReflectableValue;
            let reflected = match first_arg {
                Type::TypeString(sym) => {
                    let s = crate::interner::resolve(*sym).unwrap_or_default().to_string();
                    Some(ReflectableValue::String(s))
                }
                Type::TypeInt(n) => Some(ReflectableValue::Int(*n)),
                Type::Con(c) => {
                    let name = crate::interner::resolve(c.name).unwrap_or_default().to_string();
                    match name.as_str() {
                        "True" => Some(ReflectableValue::Boolean(true)),
                        "False" => Some(ReflectableValue::Boolean(false)),
                        "LT" | "EQ" | "GT" => Some(ReflectableValue::Ordering(name)),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(val) = reflected {
                return Some(DictExpr::InlineReflectable(val));
            }
        }
        return None;
    }

    match class_str.as_str() { // TODO: this should include module as well as class name 
        "Partial" | "Coercible" | "RowToList" | "Nub" | "Union" | "Cons" | "Lacks"
        | "Warn" | "Fail" | "CompareSymbol" | "Compare" | "Add" | "Mul"
        | "ToString" => return None,
        _ => {}
    }

    // Extract head type constructor from concrete args.
    // First try the first arg (standard single-param classes).
    // If that fails or doesn't match the registry, try all args — multi-parameter
    // type classes may have type variables in early positions (e.g., `IsStream el s`).
    let head_opt = {
        let first_head = concrete_args.first().and_then(|t| extract_head_from_type_tc(t));
        if first_head.is_some() && combined_registry.contains_key(&(class_name.name, first_head.unwrap())) {
            first_head
        } else if first_head.is_none() || !combined_registry.contains_key(&(class_name.name, first_head.unwrap())) {
            // Try other args for multi-param classes
            let mut found = None;
            for t in concrete_args.iter().skip(if first_head.is_some() { 1 } else { 0 }) {
                if let Some(h) = extract_head_from_type_tc(t) {
                    if combined_registry.contains_key(&(class_name.name, h)) {
                        found = Some(h);
                        break;
                    }
                }
            }
            found.or(first_head)
        } else {
            first_head
        }
    };

    // If head is a type alias, try expanding type aliases and re-extracting.
    // E.g., `type I t = t` means `Show (I String)` → head `I` → not in registry.
    // After expansion: `Show String` → head `String` → found in registry.
    let expanded_concrete_args: Option<Vec<Type>> = if head_opt.is_some() {
        let head = head_opt.unwrap();
        if combined_registry.get(&(class_name.name, head)).is_none() {
            // Head not in registry — might be a type alias. Try expanding.
            let expanded: Vec<Type> = concrete_args
                .iter()
                .map(|t| {
                    let mut expanding = HashSet::new();
                    expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None)
                })
                .collect();
            let new_head = expanded.iter().find_map(|t| {
                let h = extract_head_from_type_tc(t)?;
                if combined_registry.contains_key(&(class_name.name, h)) { Some(h) } else { None }
            }).or_else(|| expanded.first().and_then(|t| extract_head_from_type_tc(t)));
            if new_head != head_opt {
                Some(expanded)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    let (_effective_args, head_opt) = if let Some(ref expanded) = expanded_concrete_args {
        let head = expanded.iter().find_map(|t| {
            let h = extract_head_from_type_tc(t)?;
            if combined_registry.contains_key(&(class_name.name, h)) { Some(h) } else { None }
        }).or_else(|| expanded.first().and_then(|t| extract_head_from_type_tc(t)));
        (expanded.as_slice(), head)
    } else {
        (concrete_args, head_opt)
    };

    // If head extraction fails (type variable / unif var) AND we're in a sub-constraint
    // context, try given_constraints. This handles instance method constraints where
    // the class dict is passed as a parameter (ConstraintArg).
    if head_opt.is_none() && is_sub_constraint {
        {
            if let Some(given) = given_constraints {
                let has_var_args = concrete_args.iter().any(|t| contains_type_var_or_unif(t));
                if has_var_args {
                    if let Some(used_pos) = given_used_positions.as_deref_mut() {
                        // With used_positions: skip positions claimed by DIFFERENT args.
                        // Allow reuse if the same args match (same constraint in nested sub-trees).
                        for (pos, (gc_class, gc_args)) in given.iter().enumerate() {
                            if gc_class.name != class_name.name { continue; }
                            if gc_args.len() != concrete_args.len() { continue; }
                            if pos < used_pos.len() {
                                if let Some(prev_args) = &used_pos[pos] {
                                    // Already claimed — reuse only if same concrete args
                                    if prev_args == concrete_args { return Some(DictExpr::ConstraintArg(pos)); }
                                    continue;
                                }
                                used_pos[pos] = Some(concrete_args.to_vec());
                            }
                            return Some(DictExpr::ConstraintArg(pos));
                        }
                    } else {
                        // Without used_positions: just find the first match
                        for (pos, (gc_class, gc_args)) in given.iter().enumerate() {
                            if gc_class.name != class_name.name { continue; }
                            if gc_args.len() != concrete_args.len() { continue; }
                            return Some(DictExpr::ConstraintArg(pos));
                        }
                    }
                }
            }
        }
        return None;
    }
    let head = match head_opt {
        Some(h) => h,
        None => return None,
    };

    // Look up in combined registry
    let (inst_name, _inst_module) = combined_registry.get(&(class_name.name, head))?;

    // Check if the instance has constraints (parameterized instance)
    // For now, handle simple instances and instances with resolvable sub-dicts
    if let Some(known) = lookup_instances(instances, class_name) {
        let given_used_len = given_constraints.map(|g| g.len()).unwrap_or(0);
        let mut local_given_used_positions: Vec<Option<Vec<Type>>> = vec![None; given_used_len];
        let used_positions = given_used_positions.unwrap_or(&mut local_given_used_positions);
        for (_inst_idx_dbg, (inst_types, inst_constraints, matched_inst_name)) in known.iter().enumerate() {
            // Try matching
            let mut expanding = HashSet::new();
            let expanded_args: Vec<Type> = concrete_args
                .iter()
                .map(|t| expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None))
                .collect();
            let expanded_inst: Vec<Type> = inst_types
                .iter()
                .map(|t| {
                    let mut exp = HashSet::new();
                    expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut exp, None)
                })
                .collect();
            if expanded_inst.len() != expanded_args.len() {
                continue;
            }
            let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
            let matched = expanded_inst
                .iter()
                .zip(expanded_args.iter())
                .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst));
            if !matched {
                continue;
            }

            // Check kind annotations: if the instance has kind-annotated type vars,
            // verify the matched concrete types are compatible with those kinds.
            // e.g., if var `a :: Symbol` matched `Int`, reject (Int has kind Type, not Symbol).
            let effective_inst_name = matched_inst_name.unwrap_or(*inst_name);
            if let Some(kind_anns) = instance_var_kinds.get(&effective_inst_name) {
                let mut kind_mismatch = false;
                for (var, kind_sym) in kind_anns {
                    if let Some(bound_type) = subst.get(&TypeVarName::new(*var)) {
                        let kind_str = crate::interner::resolve(*kind_sym).unwrap_or_default();
                        if !type_matches_kind(bound_type, &kind_str) {
                            kind_mismatch = true;
                            break;
                        }
                    }
                }
                if kind_mismatch {
                    continue;
                }
            }

            if inst_constraints.is_empty() {
                // Simple instance: DictExpr::Var
                return Some(DictExpr::Var(effective_inst_name));
            }

            // Parameterized instance: resolve sub-dicts recursively
            let mut sub_dicts = Vec::new();
            let mut all_resolved = true;
            for (c_class, c_args) in inst_constraints {
                // Skip phantom/type-level constraints — they don't produce runtime
                // dictionaries (the codegen emits `()` calls for them automatically).
                let c_class_str = crate::interner::resolve(c_class.name)
                    .unwrap_or_default()
                    .to_string();
                if matches!(c_class_str.as_str(), // TODO: this should include module as well as class name 
                    "Partial" | "Coercible" | "Nub" | "Union" | "Lacks"
                    | "Warn" | "Fail" | "CompareSymbol" | "Compare" | "Add" | "Mul"
                    | "ToString" | "Reflectable" | "Reifiable"
                ) {
                    continue;
                }

                // Handle Row.Cons specially: compute row tail from row decomposition.
                // Row.Cons key focus rowTail row means row = { key: focus | rowTail }
                // We need to bind rowTail so downstream constraints can use it.
                if c_class_str == "Cons" && c_args.len() == 4 { // TODO: this should include module as well as class name
                    let key_ty = apply_var_subst(&subst, &c_args[0]);
                    let row_ty = apply_var_subst(&subst, &c_args[3]);
                    if let Type::TypeString(key_sym) = &key_ty {
                        if let Type::Record(fields, tail) = &row_ty {
                            let key_str = crate::interner::resolve(*key_sym).unwrap_or_default();
                            // Compute rowTail = row \ key
                            let tail_fields: Vec<_> = fields.iter()
                                .filter(|(name, _)| {
                                    !name.eq_str(&key_str)
                                })
                                .cloned()
                                .collect();
                            let row_tail = Type::Record(tail_fields, tail.clone());
                            // Bind rowTail (c_args[2])
                            if let Type::Var(tail_var) = &c_args[2] {
                                subst.insert(*tail_var, row_tail);
                            }
                            // Bind focus (c_args[1]) if it's a var
                            if let Type::Var(focus_var) = &c_args[1] {
                                if let Some((_, field_ty)) = fields.iter().find(|(name, _)| {
                                    name.eq_str(&key_str)
                                }) {
                                    subst.insert(*focus_var, field_ty.clone());
                                }
                            }
                        }
                    }
                    continue;
                }

                // Handle RowToList specially: compute the RowList type from the
                // concrete row and bind it in the substitution, so downstream
                // constraints (like EqRecord list row) can be resolved.
                if c_class_str == "RowToList" { // TODO: this should include module as well as class name 
                    // RowToList has args: [row, list]
                    if c_args.len() == 2 {
                        let row_ty = apply_var_subst(&subst, &c_args[0]);
                        if let Type::Record(fields, _) = &row_ty {
                            // Compute RowList from record fields (sorted alphabetically)
                            let mut sorted_fields = fields.clone();
                            sorted_fields.sort_by(|(a, _), (b, _)| {
                                a.to_string().cmp(&b.to_string())
                            });
                            let nil_sym = crate::interner::intern("Nil");
                            let cons_sym = crate::interner::intern("Cons");
                            let mut list_ty = Type::Con(qi(nil_sym));
                            for (label, field_ty) in sorted_fields.iter().rev() {
                                let label_str = label.to_string();
                                let label_sym = crate::interner::intern(&label_str);
                                list_ty = Type::App(
                                    Box::new(Type::App(
                                        Box::new(Type::App(
                                            Box::new(Type::Con(qi(cons_sym))),
                                            Box::new(Type::TypeString(label_sym)),
                                        )),
                                        Box::new(field_ty.clone()),
                                    )),
                                    Box::new(list_ty),
                                );
                            }
                            // Bind the list variable
                            if let Type::Var(list_var) = &c_args[1] {
                                subst.insert(*list_var, list_ty);
                            }
                        }
                    }
                    continue;
                }

                // Handle IsSymbol constraints specially — generate inline dictionaries
                // from the type-level symbol literal. IsSymbol instances are compiler-magic.
                if c_class_str == "IsSymbol" { // TODO: this should include module as well as class name 
                    let subst_args: Vec<Type> =
                        c_args.iter().map(|t| apply_var_subst(&subst, t)).collect();
                    if let Some(Type::TypeString(sym)) = subst_args.first() {
                        let label = crate::interner::resolve(*sym).unwrap_or_default().to_string();
                        sub_dicts.push(DictExpr::InlineIsSymbol(label));
                        continue;
                    }
                    // If we can't extract the symbol, fall through to normal resolution
                }

                // Handle Reflectable constraints specially — generate inline dictionaries
                // from type-level literals. Reflectable instances are compiler-magic.
                if c_class_str == "Reflectable" { // TODO: this should include module as well as class name 
                    let subst_args: Vec<Type> =
                        c_args.iter().map(|t| apply_var_subst(&subst, t)).collect();
                    if let Some(first_arg) = subst_args.first() {
                        use crate::typechecker::registry::ReflectableValue;
                        let reflected = match first_arg {
                            Type::TypeString(sym) => {
                                let s = crate::interner::resolve(*sym).unwrap_or_default().to_string();
                                Some(ReflectableValue::String(s))
                            }
                            Type::TypeInt(n) => Some(ReflectableValue::Int(*n)),
                            Type::Con(c) => {
                                let name = crate::interner::resolve(c.name).unwrap_or_default().to_string();
                                match name.as_str() {
                                    "True" => Some(ReflectableValue::Boolean(true)),
                                    "False" => Some(ReflectableValue::Boolean(false)),
                                    "LT" | "EQ" | "GT" => Some(ReflectableValue::Ordering(name)),
                                    _ => None,
                                }
                            }
                            _ => None,
                        };
                        if let Some(val) = reflected {
                            sub_dicts.push(DictExpr::InlineReflectable(val));
                            continue;
                        }
                    }
                }

                let subst_args: Vec<Type> =
                    c_args.iter().map(|t| apply_var_subst(&subst, t)).collect();

                // Handle TypeEquals specially: TypeEquals a a => refl.
                let c_class_str = crate::interner::resolve(c_class.name);
                if c_class_str.as_deref() == Some("TypeEquals") && subst_args.len() == 2 {
                    if types_equal_ignoring_row_tails(&subst_args[0], &subst_args[1]) {
                        let refl_sym = crate::interner::intern("refl");
                        if combined_registry.contains_key(&(c_class.name, refl_sym)) {
                            sub_dicts.push(DictExpr::Var(refl_sym));
                            continue;
                        }
                        if let Some(te_instances) = lookup_instances(instances, c_class) {
                            if let Some((_, _, Some(inst_name_sym))) = te_instances.iter().find(|(_, _, n)| n.is_some()) {
                                sub_dicts.push(DictExpr::Var(*inst_name_sym));
                                continue;
                            }
                        }
                        sub_dicts.push(DictExpr::Var(refl_sym));
                        continue;
                    }
                }

                // Try recursive resolution first (works when head type is concrete,
                // even if inner parts have type vars — e.g. Show (List a)).
                if let Some(sub_dict) = resolve_dict_expr_from_registry_inner(
                    combined_registry, instances, type_aliases,
                    c_class, &subst_args, type_con_arities, given_constraints,
                    Some(&mut *used_positions), true, depth + 1,
                    instance_var_kinds,
                ) {
                    sub_dicts.push(sub_dict);
                } else {
                    // Fall back to given_constraints matching for pure type-variable args
                    // (e.g., Show a where a is a constraint parameter).
                    let has_vars = subst_args.iter().any(|t| contains_type_var_or_unif(t));
                    if has_vars {
                        if let Some(given) = given_constraints {
                            let mut found_match = false;
                            for (pos, (gc_class, gc_args)) in given.iter().enumerate() {
                                if let Some(prev_args) = &used_positions[pos] {
                                    if prev_args != &subst_args { continue; }
                                    // Same args — reuse this position
                                    sub_dicts.push(DictExpr::ConstraintArg(pos));
                                    found_match = true;
                                    break;
                                }
                                if gc_class.name != c_class.name { continue; }
                                if gc_args.len() != subst_args.len() { continue; }
                                sub_dicts.push(DictExpr::ConstraintArg(pos));
                                used_positions[pos] = Some(subst_args.clone());
                                found_match = true;
                                break;
                            }
                            if !found_match {
                                all_resolved = false;
                                break;
                            }
                        } else {
                            all_resolved = false;
                            break;
                        }
                    } else {
                        all_resolved = false;
                        break;
                    }
                }
            }
            if all_resolved {
                if sub_dicts.is_empty() {
                    return Some(DictExpr::Var(effective_inst_name));
                } else {
                    return Some(DictExpr::App(effective_inst_name, sub_dicts));
                }
            }
        }
    }

    // Fallback: if we found a registry entry, use it as Var (best effort)
    Some(DictExpr::Var(*inst_name))
}

/// Compare two types structurally, treating open row tails (Unif vars) as equivalent to None.
pub(crate) fn types_equal_ignoring_row_tails(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Con(qa), Type::Con(qb)) => qa.name == qb.name,
        (Type::Var(va), Type::Var(vb)) => va == vb,
        (Type::Unif(ua), Type::Unif(ub)) => ua == ub,
        (Type::App(a1, a2), Type::App(b1, b2)) => {
            types_equal_ignoring_row_tails(a1, b1) && types_equal_ignoring_row_tails(a2, b2)
        }
        (Type::Fun(a1, a2), Type::Fun(b1, b2)) => {
            types_equal_ignoring_row_tails(a1, b1) && types_equal_ignoring_row_tails(a2, b2)
        }
        (Type::Record(fa, ta), Type::Record(fb, tb)) => {
            if fa.len() != fb.len() { return false; }
            let fields_match = fa.iter().zip(fb.iter()).all(|((na, ta), (nb, tb))| {
                na == nb && types_equal_ignoring_row_tails(ta, tb)
            });
            if !fields_match { return false; }
            match (ta, tb) {
                (None, None) => true,
                (Some(ta), Some(tb)) => types_equal_ignoring_row_tails(ta, tb),
                (Some(t), None) | (None, Some(t)) => matches!(t.as_ref(), Type::Unif(_)),
            }
        }
        (Type::TypeString(a), Type::TypeString(b)) => a == b,
        (Type::TypeInt(a), Type::TypeInt(b)) => a == b,
        (Type::Forall(va, ba), Type::Forall(vb, bb)) => {
            va == vb && types_equal_ignoring_row_tails(ba, bb)
        }
        _ => false,
    }
}

/// Check if a type contains any unification variables (Type::Unif).
pub(crate) fn has_unif_vars(ty: &Type) -> bool {
    match ty {
        Type::Unif(_) => true,
        Type::Var(_) | Type::Con(_) | Type::TypeString(_) | Type::TypeInt(_) => false,
        Type::App(a, b) | Type::Fun(a, b) => has_unif_vars(a) || has_unif_vars(b),
        Type::Forall(_, body) => has_unif_vars(body),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| has_unif_vars(t))
                || tail.as_ref().map_or(false, |t| has_unif_vars(t))
        }
    }
}
