use std::collections::{HashMap, HashSet};

use crate::ast::TypeExpr;
use crate::interner::Symbol;
use crate::names::{Qualified, ClassName, TypeName, TypeVarName};
use crate::typechecker::registry::DictExpr;
use crate::typechecker::types::Type;

use super::{
    apply_var_subst, contains_type_var, contains_type_var_or_unif, expand_type_aliases_inner,
    expand_type_aliases_limited_inner, extract_head_from_type_tc,
    lookup_instances, qi_type,
};


/// Result of instance resolution with depth tracking.
pub(crate) enum InstanceResult {
    Match,
    NoMatch,
    DepthExceeded,
    UnknownClass(Qualified<ClassName>),
}

/// Like `has_matching_instance_depth` but returns a tri-state result to distinguish
/// "no instance found" from "possibly infinite instance" (depth exceeded).
pub(crate) fn check_instance_depth(
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    class_name: &Qualified<ClassName>,
    concrete_args: &[Type],
    depth: u32,
    known_classes: Option<&HashSet<Qualified<ClassName>>>,
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
) -> InstanceResult {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    check_instance_depth_impl(instances, type_aliases, class_name, concrete_args, depth, known_classes, type_con_arities)
    })
}

pub(crate) fn check_instance_depth_impl(
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    class_name: &Qualified<ClassName>,
    concrete_args: &[Type],
    depth: u32,
    known_classes: Option<&HashSet<Qualified<ClassName>>>,
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
) -> InstanceResult {
    if depth > 200 {
        return InstanceResult::DepthExceeded;
    }

    // Check if the class is in scope (only for sub-constraints at depth > 0)
    // Also accept classes that have instances (covers Prim built-in classes like Nub)
    // Use lookup_instances for qualified fallback (e.g. SimpleJson.WriteForeign → WriteForeign).
    // NOTE: compiler-magic classes are handled by the built-in solver below — skip this check for them
    // so transitive sub-constraints (e.g. Reflectable from ToParameters) don't produce UnknownClass.
    if depth > 0 {
        if let Some(kc) = known_classes {
            let class_str = class_name.name.to_string();
            let is_magic = matches!(
                class_str.as_str(),
                "IsSymbol" | "Reflectable" | "Reifiable"
                | "Partial" | "Warn" | "Fail"
                | "Coercible"
                | "Lacks" | "Cons" | "Nub" | "Union" | "RowToList"
                | "CompareSymbol" | "Append" | "Compare"
                | "Add" | "Mul" | "ToString"
            );
            if !is_magic {
                let kc_known = kc.contains(class_name) || (class_name.module.is_some() && kc.iter().any(|k| k.name == class_name.name));
                if !kc_known && lookup_instances(instances, class_name).is_none() {
                    return InstanceResult::UnknownClass(*class_name);
                }
            }
        }
    }

    // Built-in solver instances for compiler-magic type classes.
    let class_str = class_name.name.to_string();
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
                        s.name.eq_str("String")
                    }
                    (Type::TypeInt(_), Type::Con(s)) => {
                        s.name.eq_str("Int")
                    }
                    (Type::Con(c), Type::Con(s)) => {
                        (c.name.eq_str("True") || c.name.eq_str("False")) && s.name.eq_str("Boolean")
                            || (c.name.eq_str("LT") || c.name.eq_str("EQ") || c.name.eq_str("GT"))
                                && s.name.eq_str("Ordering")
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

        // Try matching with expanded types, then unexpanded, then all-var fallback.
        let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
        let matched = expanded_inst_types
            .iter()
            .zip(expanded_args.iter())
            .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst))
            || {
                // Retry with unexpanded types (handles same-alias matching)
                let mut subst2: HashMap<TypeVarName, Type> = HashMap::new();
                let ok = inst_types.len() == concrete_args.len()
                    && inst_types.iter().zip(concrete_args.iter())
                        .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst2));
                if ok { subst = subst2; }
                ok
            }
            || {
                // Fallback: when expanded Record types fail structural comparison due
                // to cross-module row concatenation differences, try matching with a
                // lenient strategy: compare non-Record types normally, but for Record
                // vs Record, check if the concrete arg's UNEXPANDED Con name matches
                // the instance arg's UNEXPANDED Con name (same alias → same type).
                let mut subst3: HashMap<TypeVarName, Type> = HashMap::new();
                let ok = inst_types.len() == concrete_args.len()
                    && inst_types.iter().zip(concrete_args.iter()).zip(expanded_inst_types.iter().zip(expanded_args.iter()))
                        .all(|((inst_ty, ca), (exp_inst, exp_ca))| {
                            // If both expanded forms are Records AND both unexpanded forms are Cons
                            // with the same name → treat as match (same alias, different expansion)
                            if matches!(exp_inst, Type::Record(..)) && matches!(exp_ca, Type::Record(..)) {
                                if let (Type::Con(a), Type::Con(b)) = (inst_ty, ca) {
                                    if type_con_qi_eq(a, b) {
                                        return true;
                                    }
                                }
                            }
                            match_instance_type(inst_ty, ca, &mut subst3)
                        });
                if ok { subst = subst3; }
                ok
            };

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
            match check_instance_depth_impl(
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
                r @ InstanceResult::UnknownClass(_) => {
                    return r;
                }
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
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    class_name: &Qualified<ClassName>,
    concrete_args: &[Type],
    depth: u32,
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
) -> bool {
    if depth > 20 {
        // Avoid infinite recursion on circular constraint chains
        return false;
    }

    // Built-in solver instances for compiler-magic type classes.
    let class_str = class_name.name.to_string();
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
                        s.name.eq_str("String")
                    }
                    (Type::TypeInt(_), Type::Con(s)) => {
                        s.name.eq_str("Int")
                    }
                    (Type::Con(c), Type::Con(s)) => {
                        (c.name.eq_str("True") || c.name.eq_str("False")) && s.name.eq_str("Boolean")
                            || (c.name.eq_str("LT") || c.name.eq_str("EQ") || c.name.eq_str("GT"))
                                && s.name.eq_str("Ordering")
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
        "Fail" => {
            // Fail is a compile-time error mechanism — it can never be satisfied
            return false;
        }
        "RowToList" | "Nub" | "Union" | "Cons" | "Lacks" | "Coercible" | "Partial"
        | "Warn" | "CompareSymbol" | "Compare" | "Add" | "Mul"
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
                out.push(name.name.symbol());
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

pub(crate) fn type_has_local_con(ty: &Type, local_types: &HashSet<TypeName>) -> bool {
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
    class_name: &Qualified<ClassName>,
    class_fundeps: &HashMap<Qualified<ClassName>, (Vec<TypeVarName>, Vec<(Vec<usize>, Vec<usize>)>)>,
    local_type_names: &HashSet<TypeName>,
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
pub(crate) fn extract_kind_annotations(types: &[TypeExpr]) -> HashMap<TypeVarName, Symbol> {
    let mut result = HashMap::new();
    fn walk(ty: &TypeExpr, result: &mut HashMap<TypeVarName, Symbol>) {
        match ty {
            TypeExpr::Kinded { ty, kind, .. } => {
                // If the inner type is a variable, record its kind
                if let TypeExpr::Var { name, .. } = ty.as_ref() {
                    if let Some(kind_name) = extract_kind_name_ast(kind) {
                        result.insert(TypeVarName::new(name.value), kind_name);
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
        TypeExpr::Constructor { name, .. } => Some(name.name.symbol()),
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
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    no_expand: &HashSet<TypeName>,
) -> bool {
    if types_a.len() != types_b.len() {
        return false;
    }
    // Pre-seed the expanding set with locally-defined data/newtype names
    // to prevent alias expansion for those names (avoids false overlaps
    // e.g. newtype Thread matching Record via imported Thread alias).
    let seed: HashSet<Qualified<TypeName>> = no_expand.iter().map(|s| Qualified::unqualified(*s)).collect();
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
pub(crate) fn type_con_names_eq(a: TypeName, b: TypeName) -> bool {
    a == b || {
        (a.eq_str("->") || a.eq_str("Function")) && (b.eq_str("->") || b.eq_str("Function"))
    }
}

/// Module-aware type constructor comparison.
/// When both types have module qualifiers and they differ, the types are distinct
/// (e.g., `List.List` vs `LazyList.List` are different types even though both are named "List").
/// When either type has no module qualifier, falls back to name-only comparison.
pub(crate) fn type_con_qi_eq(a: &Qualified<TypeName>, b: &Qualified<TypeName>) -> bool {
    // When both have module qualifiers and they match, that's a strong positive.
    // When they differ, DON'T return false — the difference may be due to
    // import aliases vs canonical module names (e.g., "FO" vs "Foreign.Object"
    // both referring to Foreign.Object.Object). Always fall back to name comparison.
    type_con_names_eq(a.name, b.name)
}

/// Strict module-aware type constructor comparison for overlap checking.
/// Unlike `type_con_qi_eq`, when one type has a module qualifier and the other
/// doesn't, treats them as distinct (e.g., `List` vs `Lazy.List`).
pub(crate) fn type_con_qi_eq_strict(a: &Qualified<TypeName>, b: &Qualified<TypeName>) -> bool {
    match (a.module, b.module) {
        (Some(ma), Some(mb)) => {
            // Both qualified: if the module qualifiers differ, they're distinct types.
            // E.g., `List.List` vs `LazyList.List` — same name, different types.
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

/// Compare two types for equality with lenient module-qualifier comparison for type constructors,
/// also treating `Unif` on either side as a wildcard match.
/// Used when comparing a type var's existing binding against a new concrete type during
/// instance matching — codegen deferred constraints may have unsolved unif vars that the
/// typechecker would have unified to be compatible.
pub(crate) fn types_eq_lenient_with_unif(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Unif(_), _) | (_, Type::Unif(_)) => true,
        (Type::Con(ca), Type::Con(cb)) => type_con_qi_eq(ca, cb),
        (Type::App(f1, a1), Type::App(f2, a2)) => types_eq_lenient_with_unif(f1, f2) && types_eq_lenient_with_unif(a1, a2),
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => types_eq_lenient_with_unif(a1, a2) && types_eq_lenient_with_unif(b1, b2),
        (Type::Forall(v1, body1), Type::Forall(v2, body2)) => {
            v1.len() == v2.len() && types_eq_lenient_with_unif(body1, body2)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            // When field counts differ, one side may have an open row tail (with Unif var)
            // that accounts for the extra fields. Check that all fields from the shorter
            // record match the longer one, and that the open tail is on the shorter side.
            if f1.len() == f2.len() {
                f1.iter().zip(f2.iter()).all(|((l1, ty1), (l2, ty2))| l1 == l2 && types_eq_lenient_with_unif(ty1, ty2))
                    && match (t1, t2) {
                        (None, None) => true,
                        (Some(a), Some(b)) => types_eq_lenient_with_unif(a, b),
                        (Some(_), None) | (None, Some(_)) => true,
                    }
            } else {
                // Different field counts — check if the shorter side has a Unif row tail
                let (shorter, longer, shorter_tail) = if f1.len() < f2.len() {
                    (f1, f2, t1)
                } else {
                    (f2, f1, t2)
                };
                let has_unif_tail = shorter_tail.as_ref().map_or(false, |t| matches!(**t, Type::Unif(_)));
                has_unif_tail && shorter.iter().all(|(sl, sty)| {
                    longer.iter().any(|(ll, lty)| sl == ll && types_eq_lenient_with_unif(sty, lty))
                })
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
                // Use lenient comparison that treats Unif vars as wildcards. This is safe
                // because instance matching here is for codegen dict resolution, not type
                // soundness. The typechecker guarantees that unsolved unif vars will
                // eventually unify to compatible types. Without this, partially-solved
                // record types (e.g., { size :: ?r } vs { size :: Int }) cause instance
                // matching to fail, leading to partial dict resolution.
                // Also treat type variables in concrete position as wildcards.
                // This handles sub-constraint resolution where the parent instance's
                // constraint has free type variables (e.g., Sub b c from opRDRD).
                // These vars represent types determined by functional dependencies
                // that our resolver doesn't trace.
                let result = types_eq_lenient_with_unif(existing, concrete)
                    || matches!(concrete, Type::Var(_));
                result
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
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type(inst_ty, &desugared, subst)
        }
        (Type::Fun(a, b), Type::App(_, _)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type(&desugared, concrete, subst)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            match_instance_type(a1, a2, subst) && match_instance_type(b1, b2, subst)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            // Flatten both records: collect all fields from nested row tails
            // into flat field lists. This handles cross-module row concatenation
            // where the same type alias expands with different nesting structures.
            fn flatten_record_fields(fields: &[(crate::names::LabelName, Type)], tail: &Option<Box<Type>>) -> Vec<(crate::names::LabelName, Type)> {
                let mut all = fields.to_vec();
                if let Some(t) = tail {
                    if let Type::Record(inner_fields, inner_tail) = t.as_ref() {
                        all.extend(flatten_record_fields(inner_fields, inner_tail));
                    }
                }
                all
            }
            let flat1 = flatten_record_fields(f1, t1);
            let flat2 = flatten_record_fields(f2, t2);
            // Match by checking all f1 fields exist in flat f2
            let mut remaining2 = flat2.clone();
            for (l1, ty1) in &flat1 {
                if let Some(idx) = remaining2.iter().position(|(l, _)| l == l1) {
                    let (_, ty2) = remaining2.remove(idx);
                    if !match_instance_type(ty1, &ty2, subst) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            // Remaining f2 fields: if f1 has no tail, they must be empty
            match (t1, remaining2.is_empty()) {
                (_, true) => true,
                (Some(_), false) => true, // f1 has open tail — remaining f2 fields are fine
                (None, false) => false,
            }
        }
        // App(Con("Record"), row) vs Record(fields, tail): `Record row` matches any record
        (Type::App(f, inst_row), Type::Record(..)) => {
            if let Type::Con(sym) = f.as_ref() {
                if sym.name.eq_str("Record") {
                    return match_instance_type(inst_row, concrete, subst);
                }
            }
            inst_ty == concrete
        }
        (Type::Record(..), Type::App(f, concrete_row)) => {
            if let Type::Con(sym) = f.as_ref() {
                if sym.name.eq_str("Record") {
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
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type_strict(inst_ty, &desugared, subst)
        }
        (Type::Fun(a, b), Type::App(_, _)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), a.clone())),
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

/// Like `match_instance_type_strict` but uses lenient constructor comparison for
/// chain ambiguity "definitely matches" checking.
///
/// The strict version (`match_instance_type_strict`) uses `type_con_qi_eq_strict` which
/// treats `Some(module)` vs `None` as distinct (needed for overlap detection of `List`
/// vs `Lazy.List`). But for chain ambiguity, instance head types may carry the module
/// alias qualifier (e.g., `Yield.Yield v` stored as `Con(Some("Yield"), "Yield")`) while
/// the concrete type uses the bare import (`Yield a` = `Con(None, "Yield")`).
/// These should match because they refer to the same type.
///
/// The strict-vars property is preserved: bound instance variable must match exactly
/// (no treating `Type::Var` in concrete position as wildcard).
pub(crate) fn match_instance_type_for_chain(inst_ty: &Type, concrete: &Type, subst: &mut HashMap<TypeVarName, Type>) -> bool {
    match (inst_ty, concrete) {
        (Type::Var(v), _) => {
            if let Some(existing) = subst.get(v) {
                // Strict: must match exactly (no wildcard for concrete Type::Var)
                existing == concrete
            } else {
                subst.insert(*v, concrete.clone());
                true
            }
        }
        // Lenient constructor comparison: module aliases vs bare imports refer to the same type.
        (Type::Con(a), Type::Con(b)) => type_con_qi_eq(a, b),
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            match_instance_type_for_chain(f1, f2, subst) && match_instance_type_for_chain(a1, a2, subst)
        }
        (Type::App(_, _), Type::Fun(a, b)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type_for_chain(inst_ty, &desugared, subst)
        }
        (Type::Fun(a, b), Type::App(_, _)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), a.clone())),
                b.clone(),
            );
            match_instance_type_for_chain(&desugared, concrete, subst)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            match_instance_type_for_chain(a1, a2, subst) && match_instance_type_for_chain(b1, b2, subst)
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
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), fa.clone())),
                fb.clone(),
            );
            could_unify_types(app, &desugared)
        }
        (Type::Fun(fa, fb), app @ Type::App(_, _)) => {
            let function_sym = crate::interner::intern("Function");
            let desugared = Type::App(
                Box::new(Type::App(Box::new(Type::Con(qi_type(function_sym))), fa.clone())),
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
    instances: &[(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)],
    concrete_args: &[Type],
) -> ChainResult {
    for (inst_types, inst_constraints, _) in instances {
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

        // Instance could match. Check if it definitely matches (strict-vars check).
        // Must NOT use the lenient match_instance_type, because it treats Type::Var in
        // concrete position as a wildcard. That's wrong for chain ambiguity:
        // `Inject l (Either l r)` should NOT "definitely match" `Inject g (Either f g)`
        // just because f is a type var — the instance requires l=g AND l=f, which
        // fails when f≠g (distinct rigid vars).
        // Use match_instance_type_for_chain instead of match_instance_type_strict: the
        // former is strict about bound type variables but lenient about constructor module
        // qualifiers. This correctly handles `Yield.Yield v` (module-aliased in instance)
        // matching `Yield a` (bare import in concrete type) — same type, different qualification.
        let mut exact_subst: HashMap<TypeVarName, Type> = HashMap::new();
        let definitely_matches = inst_types
            .iter()
            .zip(concrete_args.iter())
            .all(|(inst_ty, arg)| match_instance_type_for_chain(inst_ty, arg, &mut exact_subst));

        if definitely_matches {
            // If the instance has a Fail constraint, it can never be satisfied —
            // treat as NoMatch (the chain fell through to a Fail guard).
            let has_fail = inst_constraints.iter().any(|(c, _)| {
                let s = c.name.to_string();
                s == "Fail"
            });
            if has_fail {
                return ChainResult::NoMatch;
            }
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
) -> Option<Qualified<TypeName>> {
    if lhs == rhs {
        return Some(crate::names::unqualified_type("EQ"));
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
        (true, true) => Some(crate::names::unqualified_type("EQ")),
        (true, false) => Some(crate::names::unqualified_type("LT")),
        (false, true) => Some(crate::names::unqualified_type("GT")),
        (false, false) => None, // Can't determine
    }
}

/// Check if an arg with unif vars is structurally compatible with a resolved instance type.
/// E.g., `App(Unif(?340), Con("Unit"))` is compatible with `App(Con("Aff"), Con("Unit"))`.
fn structural_compatible(arg: &Type, resolved: &Type) -> bool {
    match (arg, resolved) {
        (Type::App(a1, a2), Type::App(r1, r2)) => {
            structural_compatible(a1, r1) && structural_compatible(a2, r2)
        }
        (Type::Fun(a1, a2), Type::Fun(r1, r2)) => {
            structural_compatible(a1, r1) && structural_compatible(a2, r2)
        }
        (Type::Con(_), Type::Con(_)) => arg == resolved,
        (Type::Unif(_), _) => true, // Unif var can match anything
        // If structures differ (e.g., Fun vs App), not compatible
        _ => false,
    }
}

/// E.g., `Parallel ?f Aff` matched against `instance Parallel ParAff Aff`
/// → unify `?f` with `ParAff`.
pub(crate) fn try_unify_from_instance(
    state: &mut crate::typechecker::unify::UnifyState,
    class_name: &Qualified<ClassName>,
    concrete_args: &[Type],
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
    _instance_var_kinds: &HashMap<Symbol, HashMap<TypeVarName, Symbol>>,
) {
    let found = lookup_instances(instances, class_name);
    if let Some(known) = found {
        // Two-phase matching: first match concrete positions to build substitution,
        // then use the substitution to resolve unsolved positions.
        // This handles cases like Example (?340 Unit) Unit Aff where position 0
        // has a unif var but position 2 has the concrete type that determines it.
        let mut expanding = HashSet::new();
        let expanded_args: Vec<Type> = concrete_args
            .iter()
            .map(|t| expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None))
            .collect();

        // Identify which positions have unsolved unif vars
        let has_unif_at: Vec<bool> = expanded_args.iter()
            .map(|t| !state.free_unif_vars(t).is_empty())
            .collect();

        // Collect instances that match on concrete positions only
        let mut matches: Vec<(Vec<Type>, HashMap<TypeVarName, Type>)> = Vec::new();
        for (inst_types, _inst_constraints, _) in known {
            if inst_types.len() != concrete_args.len() {
                continue;
            }
            let expanded_inst: Vec<Type> = inst_types
                .iter()
                .map(|t| {
                    let mut exp = HashSet::new();
                    expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut exp, None)
                })
                .collect();

            // Phase 1: Match only concrete arg positions to build substitution
            let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
            let concrete_matched = expanded_inst.iter().zip(expanded_args.iter()).zip(has_unif_at.iter())
                .all(|((inst_ty, arg), has_unif)| {
                    if *has_unif {
                        true // Skip unsolved positions in phase 1
                    } else {
                        match_instance_type(inst_ty, arg, &mut subst)
                    }
                });
            if !concrete_matched {
                continue;
            }

            // Phase 2: Verify unsolved positions are structurally compatible
            // (the unsolved args should have structure matching the instance type after subst)
            let unsolved_compatible = expanded_inst.iter().zip(expanded_args.iter()).zip(has_unif_at.iter())
                .all(|((inst_ty, arg), has_unif)| {
                    if !*has_unif {
                        true // Already matched in phase 1
                    } else {
                        // Check structural compatibility: the instance type after subst
                        // should be compatible with the arg's structure
                        let resolved = apply_var_subst(&subst, inst_ty);
                        if contains_type_var(&resolved) {
                            // Instance type still has unresolved vars — can't verify, assume compatible
                            true
                        } else {
                            // Structural check: if arg is App(X, Y) and resolved is App(A, B),
                            // the structure should match even if X contains unif vars
                            structural_compatible(arg, &resolved)
                        }
                    }
                });
            if unsolved_compatible {
                matches.push((expanded_inst, subst));
                if matches.len() > 1 {
                    return; // Ambiguous
                }
            }
        }
        if matches.len() == 1 {
            let (expanded_inst, subst) = &matches[0];
            let dummy_span = crate::span::Span { start: 0, end: 0 };
            for (inst_ty, arg) in expanded_inst.iter().zip(expanded_args.iter()) {
                let has_unif = !state.free_unif_vars(arg).is_empty();
                if has_unif {
                    let concrete_inst_ty = apply_var_subst(subst, inst_ty);
                    if !contains_type_var(&concrete_inst_ty) {
                        let _ = state.unify(dummy_span, arg, &concrete_inst_ty);
                    }
                }
            }
        }
    }
}

pub(crate) fn resolve_dict_expr_from_registry(
    combined_registry: &HashMap<(Symbol, Symbol), Vec<(Symbol, Option<Vec<Symbol>>)>>,
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    class_name: &Qualified<ClassName>,
    concrete_args: &[Type],
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
    instance_var_kinds: &HashMap<Symbol, HashMap<TypeVarName, Symbol>>,
    inst_name_all_modules: &HashMap<(String, usize), Vec<Vec<Symbol>>>,
) -> Option<DictExpr> {
    resolve_dict_expr_from_registry_inner(
        combined_registry, instances, type_aliases,
        class_name, concrete_args, type_con_arities, None, None, false, 0,
        instance_var_kinds, inst_name_all_modules, None,
    )
}

/// DFS through the superclass hierarchy to find a chain of accessor names from
/// `current_class current_args` to `target_class target_args`.
/// Returns `Some(vec!["Accessor1", "Accessor2", ...])` if found, `None` otherwise.
pub(super) fn find_superclass_chain(
    class_superclasses: &HashMap<Qualified<ClassName>, (Vec<Symbol>, Vec<(Qualified<ClassName>, Vec<Type>)>)>,
    current_class: &Qualified<ClassName>,
    current_args: &[Type],
    target_class: &Qualified<ClassName>,
    target_args: &[Type],
    depth: usize,
) -> Option<Vec<String>> {
    if depth > 6 { return None; }
    let (tvs, sc_constraints) = class_superclasses.get(current_class)?;
    if tvs.len() != current_args.len() { return None; }
    let subst: HashMap<TypeVarName, Type> = tvs.iter().zip(current_args.iter())
        .map(|(tv_sym, ty)| (TypeVarName::new(*tv_sym), ty.clone()))
        .collect();
    for (sc_idx, (sc_class, sc_args)) in sc_constraints.iter().enumerate() {
        let concretized: Vec<Type> = sc_args.iter()
            .map(|t| apply_var_subst(&subst, t))
            .collect();
        let accessor = format!("{}{sc_idx}", sc_class.name.to_string());
        if sc_class.name == target_class.name && concretized == target_args {
            return Some(vec![accessor]);
        }
        if let Some(mut chain) = find_superclass_chain(
            class_superclasses, sc_class, &concretized,
            target_class, target_args, depth + 1,
        ) {
            chain.insert(0, accessor);
            return Some(chain);
        }
    }
    None
}

pub(crate) fn resolve_dict_expr_from_registry_inner(
    combined_registry: &HashMap<(Symbol, Symbol), Vec<(Symbol, Option<Vec<Symbol>>)>>,
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    class_name: &Qualified<ClassName>,
    concrete_args: &[Type],
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
    given_constraints: Option<&[(Qualified<ClassName>, Vec<Type>)]>,
    mut given_used_positions: Option<&mut Vec<Option<Vec<Type>>>>,
    is_sub_constraint: bool,
    depth: u32,
    instance_var_kinds: &HashMap<Symbol, HashMap<TypeVarName, Symbol>>,
    inst_name_all_modules: &HashMap<(String, usize), Vec<Vec<Symbol>>>,
    class_superclasses: Option<&HashMap<Qualified<ClassName>, (Vec<Symbol>, Vec<(Qualified<ClassName>, Vec<Type>)>)>>,
) -> Option<DictExpr> {
    if depth > 50 {
        return None; // Prevent infinite recursion in deeply nested instance chains
    }
    // Skip compiler-magic classes (Partial, Coercible, RowToList, etc.)
    let class_str = class_name.name.to_string();
    // DEBUG removed

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
                    let name = c.name.to_string();
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
    // If that fails or doesn't match the registry, try alias expansion on the first arg,
    // then try all args — multi-parameter type classes may have type variables in early
    // positions (e.g., `IsStream el s`).
    let head_opt = {
        let first_head = concrete_args.first().and_then(|t| extract_head_from_type_tc(t));
        if first_head.is_some() && combined_registry.contains_key(&(class_name.name.symbol(),first_head.unwrap())) {
            first_head
        } else if first_head.is_none() || !combined_registry.contains_key(&(class_name.name.symbol(),first_head.unwrap())) {
            // Before trying other args, try expanding the first arg's type alias.
            // E.g., Op (RD' String) (RD' Int) String: first head is RD' (alias for RD a a).
            // After expansion: head is RD, which IS in the registry. Without this,
            // multi-param fallback incorrectly picks String (third arg) → wrong instance.
            let expanded_first_head = if first_head.is_some() {
                if let Some(first_arg) = concrete_args.first() {
                    let mut expanding = HashSet::new();
                    let expanded = expand_type_aliases_limited_inner(first_arg, type_aliases, type_con_arities, 0, &mut expanding, None);
                    let h = extract_head_from_type_tc(&expanded);
                    if h.is_some() && h != first_head && combined_registry.contains_key(&(class_name.name.symbol(), h.unwrap())) {
                        h
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };
            if expanded_first_head.is_some() {
                expanded_first_head
            } else {
                // Try other args for multi-param classes
                let mut found = None;
                for t in concrete_args.iter().skip(if first_head.is_some() { 1 } else { 0 }) {
                    if let Some(h) = extract_head_from_type_tc(t) {
                        if combined_registry.contains_key(&(class_name.name.symbol(),h)) {
                            found = Some(h);
                            break;
                        }
                    }
                }
                found.or(first_head)
            }
        } else {
            first_head
        }
    };

    // If head is a type alias, try expanding type aliases and re-extracting.
    // E.g., `type I t = t` means `Show (I String)` → head `I` → not in registry.
    // After expansion: `Show String` → head `String` → found in registry.
    let expanded_concrete_args: Option<Vec<Type>> = if head_opt.is_some() {
        let head = head_opt.unwrap();
        if combined_registry.get(&(class_name.name.symbol(),head)).is_none() {
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
                if combined_registry.contains_key(&(class_name.name.symbol(),h)) { Some(h) } else { None }
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
            if combined_registry.contains_key(&(class_name.name.symbol(),h)) { Some(h) } else { None }
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
                    // First pass: try exact type argument match (e.g., Show n vs Show c vs Show a).
                    // This ensures the correct constraint position is returned when multiple constraints
                    // share the same class but differ in type variable arguments.
                    let exact_pos = given.iter().enumerate().find_map(|(pos, (gc_class, gc_args))| {
                        if gc_class.name != class_name.name { return None; }
                        if gc_args.len() != concrete_args.len() { return None; }
                        if gc_args == concrete_args { Some(pos) } else { None }
                    });
                    if let Some(pos) = exact_pos {
                        if let Some(used_pos) = given_used_positions.as_deref_mut() {
                            if pos < used_pos.len() {
                                used_pos[pos] = Some(concrete_args.to_vec());
                            }
                        }
                        return Some(DictExpr::ConstraintArg(pos));
                    }
                    // Fallback: positional matching (for cases where exact match fails).
                    if let Some(used_pos) = given_used_positions.as_deref_mut() {
                        for (pos, (gc_class, gc_args)) in given.iter().enumerate() {
                            if gc_class.name != class_name.name { continue; }
                            if gc_args.len() != concrete_args.len() { continue; }
                            if pos < used_pos.len() {
                                if let Some(prev_args) = &used_pos[pos] {
                                    if prev_args == concrete_args { return Some(DictExpr::ConstraintArg(pos)); }
                                    continue;
                                }
                                used_pos[pos] = Some(concrete_args.to_vec());
                            }
                            return Some(DictExpr::ConstraintArg(pos));
                        }
                    } else {
                        for (pos, (gc_class, gc_args)) in given.iter().enumerate() {
                            if gc_class.name != class_name.name { continue; }
                            if gc_args.len() != concrete_args.len() { continue; }
                            return Some(DictExpr::ConstraintArg(pos));
                        }
                    }
                    // Superclass chain traversal: if no direct constraint match was found,
                    // check if the needed class is a (transitive) superclass of any given constraint.
                    // E.g., given `MonadWriter String m`, can derive `Monad m` via
                    // MonadWriter → MonadTell → Monad (chain: ["MonadTell1", "Monad1"]).
                    if let Some(sc_map) = class_superclasses {
                        for (pos, (gc_class, gc_args)) in given.iter().enumerate() {
                            if gc_class.name == class_name.name { continue; } // already tried above
                            if let Some(chain) = find_superclass_chain(
                                sc_map, gc_class, gc_args, class_name, concrete_args, 0,
                            ) {
                                return Some(DictExpr::SuperClassAccess(pos, chain));
                            }
                        }
                    }
                }
            }
        }
        // Before giving up, try instance matching for zero-constraint instances.
        // When sub-constraint args are Unif/Var (no head type constructor), lenient
        // matching allows zero-constraint instances to resolve. This is safe because:
        // 1. The outer instance already matched the concrete types
        // 2. Zero-constraint instances don't need further sub-dict resolution
        // 3. Type soundness is enforced by the typechecker, not dict resolution
        if let Some(known) = lookup_instances(instances, class_name) {
            for (inst_types, inst_constraints, matched_inst_name) in known {
                if !inst_constraints.is_empty() { continue; } // only zero-constraint
                if inst_types.len() != concrete_args.len() { continue; }
                let mut subst_check: HashMap<TypeVarName, Type> = HashMap::new();
                // Use lenient matching that treats Var in concrete position as wildcard
                let matched = inst_types.iter().zip(concrete_args.iter())
                    .all(|(it, ca)| {
                        if matches!(ca, Type::Var(_)) { return true; }
                        match_instance_type(it, ca, &mut subst_check)
                    });
                if matched {
                    if let Some(name) = matched_inst_name {
                        return Some(DictExpr::Var(*name, None));
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

    // Look up in combined registry (multi-map: may have multiple entries for same (class, head)
    // when different modules define types with the same unqualified name, e.g., Data.Proxy.Proxy
    // vs Pipes.Internal.Proxy).
    let registry_entries = combined_registry.get(&(class_name.name.symbol(),head));
    // When multiple registry entries exist for the same (class, head) key, disambiguate
    // using the module qualifier from the concrete type. This handles cases like
    // Data.List.Types.List vs Data.List.Lazy.Types.List which both have head name "List".
    let (inst_name, inst_module) = match registry_entries {
        Some(entries) if entries.len() > 1 => {
            // Extract module qualifier from concrete type head
            let concrete_module: Option<String> = concrete_args.iter().find_map(|t| {
                fn extract_head_module(ty: &Type) -> Option<String> {
                    match ty {
                        Type::Con(qi) => qi.module.map(|mq| {
                            crate::interner::resolve(mq.symbol()).unwrap_or_default().to_string()
                        }),
                        Type::App(f, _) => extract_head_module(f),
                        _ => None,
                    }
                }
                extract_head_module(t)
            });
            if let Some(ref cm) = concrete_module {
                // Find the entry whose defining module matches the concrete type's module
                let matched = entries.iter().find(|(_, mod_parts)| {
                    if let Some(parts) = mod_parts {
                        let mod_str = parts.iter()
                            .filter_map(|s| crate::interner::resolve(*s))
                            .collect::<Vec<_>>()
                            .join(".");
                        mod_str == *cm
                    } else {
                        false
                    }
                });
                match matched {
                    Some(entry) => (&entry.0, entry.1.clone()),
                    None => (&entries[0].0, entries[0].1.clone()),
                }
            } else {
                (&entries[0].0, entries[0].1.clone())
            }
        }
        Some(entries) if !entries.is_empty() => {
            (&entries[0].0, entries[0].1.clone())
        }
        _ => {
            // Registry miss — fall through to full instance matching below.
            // This handles instances with universal type variable args (e.g.,
            // TypeEquals a a) that can't be indexed by head type constructor.
            // Use a dummy inst_name; the matched instance will override it.
            let dummy = &head; // won't be used if instance matching succeeds
            (dummy, None)
        }
    };

    // Check if the instance has constraints (parameterized instance)
    // For now, handle simple instances and instances with resolvable sub-dicts
    let mut last_matched_inst: Option<(Symbol, Option<Vec<Symbol>>)> = None;
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
            // For registry miss with unnamed instances (type-var-headed like
            // `instance ConstClass a where`), generate a name matching codegen's convention.
            let effective_inst_name = if let Some(name) = matched_inst_name {
                *name
            } else if registry_entries.is_some() {
                *inst_name
            } else {
                // Registry miss + unnamed instance: generate name from class + instance types
                let class_str = crate::interner::resolve(class_name.name_symbol()).unwrap_or_default().to_string();
                let mut gen_name = String::new();
                for (i, c) in class_str.chars().enumerate() {
                    if i == 0 {
                        gen_name.extend(c.to_lowercase());
                    } else {
                        gen_name.push(c);
                    }
                }
                for ity in inst_types {
                    gen_name.push_str(&super::type_utils::type_to_instance_name_part(ity));
                }
                crate::interner::intern(&gen_name)
            };
            // Determine the defining module for the matched instance.
            // When the instance name is unique across all modules, inst_module is correct.
            // But when multiple modules define instances with the same name (e.g., bindProxy
            // in both Control.Bind and Pipes.Internal), we need to disambiguate.
            // Use (inst_name, num_constraints) as key — this uniquely identifies instances
            // even when names collide, since the colliding instances typically have different
            // numbers of constraints.
            // IMPORTANT: If inst_module is None, the instance came from the current module's
            // locally-defined instances (inserted at front with None module). Never override
            // a local instance with inst_name_all_modules — local always wins.
            let effective_module = if inst_module.is_none() {
                None // Local instance — generate as local variable, not module accessor
            } else {
                let effective_name_str = crate::interner::resolve(effective_inst_name).unwrap_or_default().to_string();
                let num_constraints = inst_constraints.len();
                let key = (effective_name_str, num_constraints);
                if let Some(modules) = inst_name_all_modules.get(&key) {
                    if modules.len() == 1 {
                        Some(modules[0].clone())
                    } else {
                        // Multiple modules with same name and constraint count — fall back
                        inst_module.clone()
                    }
                } else {
                    inst_module.clone()
                }
            };
            if let Some(kind_anns) = instance_var_kinds.get(&effective_inst_name) {
                let mut kind_mismatch = false;
                for (var, kind_sym) in kind_anns {
                    if let Some(bound_type) = subst.get(var) {
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

            // Track the last matched instance for fallback (in case sub-dict resolution fails)
            last_matched_inst = Some((effective_inst_name, effective_module.clone()));

            if inst_constraints.is_empty() {
                // Simple instance: DictExpr::Var
                return Some(DictExpr::Var(effective_inst_name, effective_module.clone()));
            }

            // Parameterized instance: resolve sub-dicts recursively.
            // Pre-pass: process computational constraints (RowToList, Row.Cons) first to
            // populate `subst` before the main loop uses those bindings. This is necessary
            // when a computational constraint appears AFTER the constraint that uses its
            // result (e.g., `GEncodeJson row list` before `RowToList row list`).
            {
                for (c_class, c_args) in inst_constraints.iter() {
                    let c_str = c_class.name.to_string();
                    if c_str == "RowToList" && c_args.len() == 2 {
                        let row_ty = apply_var_subst(&subst, &c_args[0]);
                        if let Type::Record(fields, _) = &row_ty {
                            let mut sorted_fields = fields.clone();
                            sorted_fields.sort_by(|(a, _), (b, _)| {
                                a.to_string().cmp(&b.to_string())
                            });
                            let nil_sym = crate::interner::intern("Nil");
                            let cons_sym = crate::interner::intern("Cons");
                            let mut list_ty = Type::Con(qi_type(nil_sym));
                            for (label, field_ty) in sorted_fields.iter().rev() {
                                let label_str = label.to_string();
                                let label_sym = crate::interner::intern(&label_str);
                                list_ty = Type::App(
                                    Box::new(Type::App(
                                        Box::new(Type::App(
                                            Box::new(Type::Con(qi_type(cons_sym))),
                                            Box::new(Type::TypeString(label_sym)),
                                        )),
                                        Box::new(field_ty.clone()),
                                    )),
                                    Box::new(list_ty),
                                );
                            }
                            if let Type::Var(list_var) = &c_args[1] {
                                subst.insert(*list_var, list_ty);
                            }
                        }
                    } else if c_str == "Cons" && c_args.len() == 4 {
                        let key_ty = apply_var_subst(&subst, &c_args[0]);
                        let row_ty = apply_var_subst(&subst, &c_args[3]);
                        if let Type::TypeString(key_sym) = &key_ty {
                            if let Type::Record(fields, tail) = &row_ty {
                                let key_str = crate::interner::resolve(*key_sym).unwrap_or_default();
                                let tail_fields: Vec<_> = fields.iter()
                                    .filter(|(name, _)| !name.eq_str(&key_str))
                                    .cloned()
                                    .collect();
                                let row_tail = Type::Record(tail_fields, tail.clone());
                                if let Type::Var(tail_var) = &c_args[2] {
                                    subst.entry(*tail_var).or_insert(row_tail);
                                }
                                if let Type::Var(focus_var) = &c_args[1] {
                                    if let Some((_, field_ty)) = fields.iter().find(|(name, _)| name.eq_str(&key_str)) {
                                        subst.entry(*focus_var).or_insert(field_ty.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }
            let mut sub_dicts = Vec::new();
            let mut all_resolved = true;
            for (c_class, c_args) in inst_constraints {
                // Skip phantom/type-level constraints — they don't produce runtime
                // dictionaries (the codegen emits `()` calls for them automatically).
                let c_class_str = c_class.name.to_string();
                // Fail is a compile-time error mechanism — an instance with a Fail
                // constraint can never be satisfied, so reject this instance.
                if c_class_str == "Fail" {
                    all_resolved = false;
                    break;
                }
                if matches!(c_class_str.as_str(), // TODO: this should include module as well as class name
                    "Partial" | "Coercible" | "Nub" | "Union" | "Lacks"
                    | "Warn" | "CompareSymbol" | "Compare" | "Add" | "Mul"
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
                            let mut list_ty = Type::Con(qi_type(nil_sym));
                            for (label, field_ty) in sorted_fields.iter().rev() {
                                let label_str = label.to_string();
                                let label_sym = crate::interner::intern(&label_str);
                                list_ty = Type::App(
                                    Box::new(Type::App(
                                        Box::new(Type::App(
                                            Box::new(Type::Con(qi_type(cons_sym))),
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
                                let name = c.name.to_string();
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

                // Try recursive resolution first (works when head type is concrete,
                // even if inner parts have type vars — e.g. Show (List a)).
                if let Some(sub_dict) = resolve_dict_expr_from_registry_inner(
                    combined_registry, instances, type_aliases,
                    c_class, &subst_args, type_con_arities, given_constraints,
                    Some(&mut *used_positions), true, depth + 1,
                    instance_var_kinds, inst_name_all_modules, class_superclasses,
                ) {
                    sub_dicts.push(sub_dict);
                } else if subst_args.len() >= 2 && {
                    // Fallback: identity-instance resolution for classes like TypeEquals a a.
                    // Only tried when normal resolution fails (e.g., codegen deferred constraints
                    // have unsolved unif vars that prevent matching the identity instance).
                    let mut identity_resolved = false;
                    if let Some(identity_instances) = lookup_instances(instances, c_class) {
                        let identity_match = identity_instances.iter().find(|(itypes, _, _)| {
                            if itypes.len() != subst_args.len() { return false; }
                            if let Some(Type::Var(first_var)) = itypes.first() {
                                itypes.iter().skip(1).all(|t| matches!(t, Type::Var(v) if v == first_var))
                            } else {
                                false
                            }
                        });
                        if let Some((_itypes, _iconstraints, identity_name)) = identity_match {
                            let args_match = subst_args.windows(2).all(|w| {
                                types_equal_ignoring_row_tails(&w[0], &w[1])
                                    || types_eq_lenient_with_unif(&w[0], &w[1])
                            });
                            if args_match {
                                if let Some(inst_name_sym) = identity_name {
                                    sub_dicts.push(DictExpr::Var(*inst_name_sym, None));
                                    identity_resolved = true;
                                } else if c_class.name.eq_str("TypeEquals") {
                                    let refl_sym = crate::interner::intern("refl");
                                    sub_dicts.push(DictExpr::Var(refl_sym, None));
                                    identity_resolved = true;
                                }
                            }
                        }
                    }
                    identity_resolved
                } {
                    // Identity instance was resolved in the condition above
                } else {
                    // Fall back to given_constraints matching for pure type-variable args
                    // (e.g., Show a where a is a constraint parameter).
                    let has_vars = subst_args.iter().any(|t| contains_type_var_or_unif(t));
                    if has_vars {
                        if let Some(given) = given_constraints {
                            let mut found_match = false;
                            // First pass: try exact type argument match.
                            // This handles cases like (Show c, Show a, Show n) => Show (Tree n c a)
                            // where multiple constraints share the same class but different type vars.
                            // Without exact matching, we'd always return the first (Show c) for any var.
                            for (pos, (gc_class, gc_args)) in given.iter().enumerate() {
                                if gc_class.name != c_class.name { continue; }
                                if gc_args.len() != subst_args.len() { continue; }
                                if gc_args != &subst_args { continue; }
                                sub_dicts.push(DictExpr::ConstraintArg(pos));
                                used_positions[pos] = Some(subst_args.clone());
                                found_match = true;
                                break;
                            }
                            if !found_match {
                                // Second pass: fall back to positional matching (reuse or first-available).
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
                    return Some(DictExpr::Var(effective_inst_name, effective_module.clone()));
                } else {
                    return Some(DictExpr::App(effective_inst_name, sub_dicts, effective_module.clone()));
                }
            }
        }
    }

    // If the matched instance's sub-dict resolution failed due to Var args in sub-constraints,
    // try resolving the sub-dicts using lenient matching (Var-as-wildcard) for zero-constraint
    // sub-instances only. This handles cases like GSep → gsepProduct → GRouteDuplexCtr where
    // the outer GSep matching leaves some type vars unresolved in the sub-constraint args.
    if let Some((matched_name, matched_module)) = &last_matched_inst {
        if let Some(known) = lookup_instances(instances, class_name) {
            if let Some((_, inst_constraints, _)) = known.iter().find(|(_, _, name)| *name == Some(*matched_name)) {
                if !inst_constraints.is_empty() {
                    let mut expanded_subst: HashMap<TypeVarName, Type> = HashMap::new();
                    // Re-match to populate subst
                    if let Some((itypes, _, _)) = known.iter().find(|(_, _, name)| *name == Some(*matched_name)) {
                        let mut expanding = HashSet::new();
                        let expanded_args: Vec<Type> = concrete_args.iter()
                            .map(|t| expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut expanding, None))
                            .collect();
                        let expanded_inst: Vec<Type> = itypes.iter().map(|t| {
                            let mut exp = HashSet::new();
                            expand_type_aliases_limited_inner(t, type_aliases, type_con_arities, 0, &mut exp, None)
                        }).collect();
                        for (it, ca) in expanded_inst.iter().zip(expanded_args.iter()) {
                            match_instance_type(it, ca, &mut expanded_subst);
                        }
                    }
                    let mut sub_dicts = Vec::new();
                    let mut all_ok = true;
                    for (c_class, c_args) in inst_constraints {
                        let c_str = c_class.name.to_string();
                        if matches!(c_str.as_str(), "Partial" | "Coercible" | "Nub" | "Union" | "Lacks"
                            | "Warn" | "CompareSymbol" | "Compare" | "Add" | "Mul" | "ToString" | "Reflectable" | "Reifiable"
                        ) { continue; }
                        let subst_args: Vec<Type> = c_args.iter().map(|t| apply_var_subst(&expanded_subst, t)).collect();
                        // Try lenient matching (Var-as-wildcard) for zero-constraint instances
                        let mut found = false;
                        if let Some(sub_known) = lookup_instances(instances, c_class) {
                            for (sub_itypes, sub_iconstr, sub_iname) in sub_known {
                                if !sub_iconstr.is_empty() { continue; }
                                if sub_itypes.len() != subst_args.len() { continue; }
                                let mut sub_subst: HashMap<TypeVarName, Type> = HashMap::new();
                                let matched = sub_itypes.iter().zip(subst_args.iter())
                                    .all(|(it, ca)| {
                                        if matches!(ca, Type::Var(_)) { return true; }
                                        match_instance_type(it, ca, &mut sub_subst)
                                    });
                                if matched {
                                    if let Some(name) = sub_iname {
                                        sub_dicts.push(DictExpr::Var(*name, None));
                                        found = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if !found { all_ok = false; break; }
                    }
                    if all_ok && !sub_dicts.is_empty() {
                        return Some(DictExpr::App(*matched_name, sub_dicts, matched_module.clone()));
                    }
                }
            }
        }
    }

    // Fallback: use the matched instance if available (more accurate than registry entry).
    if let Some((matched_name, matched_module)) = last_matched_inst {
        Some(DictExpr::Var(matched_name, matched_module))
    } else if registry_entries.is_some() {
        Some(DictExpr::Var(*inst_name, inst_module))
    } else {
        None
    }
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
