use std::collections::{HashMap, HashSet};

use crate::ast::{Binder, Decl, TypeExpr};
use crate::cst::Spanned;
use crate::interner::{intern, Symbol};
use crate::names::{Qualified, TypeOpName, TypeName, ClassName, ConstructorName, TypeVarName, LabelName};
use crate::span::Span;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::{TyVarId, Type};

use crate::typechecker::convert::convert_type_expr;

use super::{
    expand_type_aliases_limited, has_synonym_head, qi_type, qi_class,
};

/// Check for duplicate type arguments in a list of type variables.
/// Returns an error if any name appears more than once.
pub(crate) fn check_duplicate_type_args(type_vars: &[Spanned<Symbol>], errors: &mut Vec<TypeError>) {
    let mut seen: HashMap<Symbol, Vec<Span>> = HashMap::new();
    for tv in type_vars {
        seen.entry(tv.value).or_default().push(tv.span);
    }
    for (name, spans) in seen {
        if spans.len() > 1 {
            errors.push(TypeError::DuplicateTypeArgument { spans, name: TypeVarName::new(name) });
        }
    }
}

/// Check for overlapping argument names in a list of binders.
/// Returns an error if any variable name appears more than once.
pub(crate) fn check_overlapping_arg_names(decl_span: Span, binders: &[Binder], errors: &mut Vec<TypeError>) {
    let mut seen: HashMap<Symbol, Vec<Span>> = HashMap::new();
    for binder in binders {
        collect_binder_vars(binder, &mut seen);
    }
    for (name, spans) in seen {
        if spans.len() > 1 {
            errors.push(TypeError::OverlappingArgNames {
                span: decl_span,
                name: crate::names::ValueName::new(name),
                spans,
            });
        }
    }
}

/// Collect type constructor references from a CST TypeExpr.
pub(crate) fn collect_type_refs(ty: &crate::ast::TypeExpr, refs: &mut HashSet<Symbol>) {
    match ty {
        crate::ast::TypeExpr::Constructor { name, .. } => {
            // Only track unqualified references as local alias dependencies.
            // Qualified refs (e.g. P.Number) point to external modules, not local aliases.
            if name.module.is_none() {
                refs.insert(name.name.symbol());
            }
        }
        crate::ast::TypeExpr::App {
            constructor, arg, ..
        } => {
            collect_type_refs(constructor, refs);
            collect_type_refs(arg, refs);
        }
        crate::ast::TypeExpr::Function { from, to, .. } => {
            collect_type_refs(from, refs);
            collect_type_refs(to, refs);
        }
        crate::ast::TypeExpr::Forall { vars, ty, .. } => {
            for (_v, _visible, kind) in vars {
                if let Some(kind_expr) = kind {
                    collect_type_refs(kind_expr, refs);
                }
            }
            collect_type_refs(ty, refs);
        }
        crate::ast::TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            for constraint in constraints {
                for arg in &constraint.args {
                    collect_type_refs(arg, refs);
                }
            }
            collect_type_refs(ty, refs);
        }
        crate::ast::TypeExpr::Kinded { ty, kind, .. } => {
            collect_type_refs(ty, refs);
            collect_type_refs(kind, refs);
        }
        crate::ast::TypeExpr::Record { fields, .. } => {
            for field in fields {
                collect_type_refs(&field.ty, refs);
            }
        }
        crate::ast::TypeExpr::Row { fields, tail, .. } => {
            for field in fields {
                collect_type_refs(&field.ty, refs);
            }
            if let Some(tail) = tail {
                collect_type_refs(tail, refs);
            }
        }
        _ => {} // Var, Wildcard, Hole, StringLiteral, IntLiteral
    }
}

/// Check that all type variables in a TypeExpr are bound.
/// Reports UndefinedTypeVariable for any free type variables not in `bound`.
pub(crate) fn collect_type_expr_vars(
    ty: &TypeExpr,
    bound: &HashSet<TypeVarName>,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        TypeExpr::Var { span, name } => {
            if !bound.contains(&TypeVarName::new(name.value)) {
                errors.push(TypeError::UndefinedTypeVariable {
                    span: *span,
                    name: TypeVarName::new(name.value),
                });
            }
        }
        TypeExpr::App {
            constructor, arg, ..
        } => {
            collect_type_expr_vars(constructor, bound, errors);
            collect_type_expr_vars(arg, bound, errors);
        }
        TypeExpr::Function { from, to, .. } => {
            collect_type_expr_vars(from, bound, errors);
            collect_type_expr_vars(to, bound, errors);
        }
        TypeExpr::Forall { vars, ty, .. } => {
            let mut inner_bound = bound.clone();
            for (v, _visible, kind) in vars {
                // Validate kind annotations against vars declared so far (not including v itself).
                // This allows `forall k (a :: Id k). ...` — k is in scope for a's kind.
                if let Some(kind_expr) = kind {
                    collect_type_expr_vars(kind_expr, &inner_bound, errors);
                }
                inner_bound.insert(TypeVarName::new(v.value));
            }
            collect_type_expr_vars(ty, &inner_bound, errors);
        }
        TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            for c in constraints {
                for arg in &c.args {
                    collect_type_expr_vars(arg, bound, errors);
                }
            }
            collect_type_expr_vars(ty, bound, errors);
        }
        TypeExpr::Record { fields, .. } => {
            for field in fields {
                collect_type_expr_vars(&field.ty, bound, errors);
            }
        }
        TypeExpr::Row { fields, tail, .. } => {
            for field in fields {
                collect_type_expr_vars(&field.ty, bound, errors);
            }
            if let Some(tail) = tail {
                collect_type_expr_vars(tail, bound, errors);
            }
        }
        TypeExpr::Kinded { ty, kind, .. } => {
            collect_type_expr_vars(ty, bound, errors);
            collect_type_expr_vars(kind, bound, errors);
        }
        _ => {} // Constructor, Wildcard, Hole, StringLiteral, IntLiteral
    }
}

/// Check if a CST TypeExpr contains `forall` or wildcards (invalid in constraint args).
/// Returns the span of the first invalid node found.
pub(crate) fn has_forall_or_wildcard(ty: &TypeExpr) -> Option<crate::span::Span> {
    match ty {
        TypeExpr::Forall { span, .. } => Some(*span),
        TypeExpr::Wildcard { span, .. } => Some(*span),
        TypeExpr::App {
            constructor, arg, ..
        } => has_forall_or_wildcard(constructor).or_else(|| has_forall_or_wildcard(arg)),
        TypeExpr::Function { from, to, .. } => {
            has_forall_or_wildcard(from).or_else(|| has_forall_or_wildcard(to))
        }
        _ => None,
    }
}

/// Check if a CST TypeExpr contains wildcards (invalid in instance heads).
pub(crate) fn has_invalid_instance_head_type_expr(ty: &TypeExpr) -> bool {
    match ty {
        TypeExpr::Wildcard { .. } | TypeExpr::Hole { .. } => true,
        TypeExpr::App {
            constructor, arg, ..
        } => {
            has_invalid_instance_head_type_expr(constructor)
                || has_invalid_instance_head_type_expr(arg)
        }
        _ => false,
    }
}

/// Walk a CST TypeExpr and validate that all constraint class names are known.
/// Emits UnknownClass for unqualified constraints referencing undefined classes.
pub(crate) fn check_constraint_class_names(
    ty: &TypeExpr,
    known_classes: &HashSet<Qualified<ClassName>>,
    class_param_counts: &HashMap<Qualified<ClassName>, usize>,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            for constraint in constraints {
                let constraint_class_typed = constraint.class;
                if constraint.class.module.is_none()
                    && !known_classes.contains(&constraint_class_typed)
                {
                    errors.push(TypeError::UnknownClass {
                        span: constraint.span,
                        name: constraint_class_typed,
                    });
                }
                // Check constraint arity: the number of type args must match
                // the class param count. E.g. `Foo a` when `class Foo a b` is an error.
                // Skip ambiguous classes (usize::MAX = multiple imports with different arities).
                if let Some(&expected) = class_param_counts.get(&constraint_class_typed) {
                    if expected != usize::MAX && constraint.args.len() != expected {
                        // PureScript reports constraint arity mismatches as KindsDoNotUnify
                        // because class Foo a b has kind Type -> Type -> Constraint,
                        // and Foo a would have kind Type -> Constraint (not Constraint).
                        let mut found_kind = Type::kind_constraint();
                        for _ in 0..expected.saturating_sub(constraint.args.len()) {
                            found_kind = Type::Fun(
                                Box::new(Type::kind_type()),
                                Box::new(found_kind),
                            );
                        }
                        errors.push(TypeError::KindsDoNotUnify {
                            span: constraint.span,
                            expected: Type::kind_constraint(),
                            found: found_kind,
                        });
                    }
                }
            }
            check_constraint_class_names(ty, known_classes, class_param_counts, errors);
        }
        TypeExpr::Forall { ty, .. } => {
            check_constraint_class_names(ty, known_classes, class_param_counts, errors);
        }
        TypeExpr::Function { from, to, .. } => {
            check_constraint_class_names(from, known_classes, class_param_counts, errors);
            check_constraint_class_names(to, known_classes, class_param_counts, errors);
        }
        _ => {}
    }
}

/// Check if a type used in an instance head is a type synonym that expands to
/// a non-nominal type (record, function). Synonyms expanding to data types are fine.
pub(crate) fn is_non_nominal_instance_head(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
) -> bool {
    if !has_synonym_head(ty, type_aliases) {
        return false;
    }
    let expanded = expand_type_aliases_limited(ty, type_aliases, 0);
    match &expanded {
        // Functions are always non-nominal
        Type::Fun(..) => true,
        // Open records (with a row tail) are non-nominal due to row polymorphism;
        // closed records (no tail, fully determined) are fine — they act nominally.
        Type::Record(_, Some(_)) => true,
        _ => false,
    }
}

/// Like `is_non_nominal_instance_head`, but only rejects open records —
/// function types are allowed in instance heads (e.g. `Fn1 a b = a -> b`).
/// Only triggers when the alias body is DIRECTLY a Record type (e.g. `type X r = {x :: Int | r}`),
/// not when it becomes a Record through further row-alias expansion (e.g. `type Links r = A + B + r`).
/// This avoids false positives for row-kind type aliases used as class parameters.
pub(crate) fn is_non_nominal_instance_head_record_only(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
) -> bool {
    if !has_synonym_head(ty, type_aliases) {
        return false;
    }
    // Extract the synonym name from the head
    fn get_head_name(ty: &Type) -> Option<Symbol> {
        match ty {
            Type::Con(name) => Some(name.name_symbol()),
            Type::App(f, _) => get_head_name(f),
            _ => None,
        }
    }
    let Some(name) = get_head_name(ty) else { return false };
    let Some((_params, body)) = type_aliases.get(&name) else { return false };
    // Only reject if the alias body is a truly open record (has Var/Unif tail).
    // Row composition aliases and closed records (body ending in Record(_, None)) are valid.
    has_open_row_tail(body)
}

/// Check if a type contains a record with an open row variable tail.
/// E.g., `{ | r }` where `r` is a type variable.
pub(crate) fn has_open_record_row(ty: &Type) -> bool {
    match ty {
        Type::Record(_, Some(tail)) => matches!(tail.as_ref(), Type::Var(_) | Type::Unif(_)),
        Type::App(f, a) => has_open_record_row(f) || has_open_record_row(a),
        Type::Fun(a, b) => has_open_record_row(a) || has_open_record_row(b),
        Type::Forall(_, body) => has_open_record_row(body),
        _ => false,
    }
}

/// Check if a type is non-nominal for derive instance heads.
/// For plain `derive instance`: records, functions, and synonyms expanding to them
/// are all invalid — derive requires a data/newtype constructor.
/// For `derive newtype instance` (is_newtype=true): only open records (with row
/// variables) are invalid. Closed records and functions are allowed as class
/// parameters (e.g. `derive newtype instance MonadState St (ForEach m a b)`
/// where `St` is a closed record alias).
/// Check if a record type has a truly open row tail (Var or Unif).
/// `Record(_, Some(Record(_, None)))` is closed despite nested `Some`.
/// This happens when row composition aliases like `{ | FixtureEnvRow () }` expand.
pub(crate) fn has_open_row_tail(ty: &Type) -> bool {
    match ty {
        Type::Record(_, None) => false,
        Type::Record(_, Some(tail)) => row_tail_is_open(tail),
        _ => false,
    }
}

pub(crate) fn row_tail_is_open(tail: &Type) -> bool {
    match tail {
        Type::Var(_) | Type::Unif(_) => true,
        Type::Record(_, None) => false,
        Type::Record(_, Some(inner)) => row_tail_is_open(inner),
        _ => true, // conservative: App/Con/etc treated as potentially open
    }
}

pub(crate) fn is_non_nominal_for_derive(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    data_constructors: &HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>>,
    is_newtype: bool,
) -> bool {
    if is_newtype {
        // derive newtype: only reject truly open records (with Var/Unif tail)
        if has_open_row_tail(ty) {
            return true;
        }
    } else {
        // plain derive: reject any record or function
        if matches!(ty, Type::Record(..) | Type::Fun(..)) {
            return true;
        }
    }
    // Expand type aliases and check expanded forms
    // But skip expansion if the name also exists as a data type (name collision
    // from module qualifier stripping — e.g. `Mutex` newtype vs imported alias).
    if has_synonym_head(ty, type_aliases) {
        let is_also_data_type = match ty {
            Type::Con(q) => data_constructors.contains_key(q),
            Type::App(f, _) => match f.as_ref() {
                Type::Con(q) => data_constructors.contains_key(q),
                _ => false,
            },
            _ => false,
        };
        if !is_also_data_type {
            let expanded = expand_type_aliases_limited(ty, type_aliases, 0);
            if is_newtype {
                if has_open_row_tail(&expanded) {
                    return true;
                }
            } else {
                if matches!(&expanded, Type::Record(..) | Type::Fun(..)) {
                    return true;
                }
            }
        }
    }
    if is_newtype {
        is_non_nominal_instance_head_record_only(ty, type_aliases)
    } else {
        is_non_nominal_instance_head(ty, type_aliases)
    }
}


pub(crate) fn collect_binder_vars(binder: &Binder, seen: &mut HashMap<Symbol, Vec<Span>>) {
    // eprintln!("Collecting binder vars in {:?}, seen so far: {:?}", binder, seen);
    match binder {
        Binder::Var { name, .. } => {
            seen.entry(name.value).or_default().push(name.span);
        }
        Binder::Constructor { args, .. } => {
            for arg in args {
                collect_binder_vars(arg, seen);
            }
        }
        Binder::As { name, binder, .. } => {
            seen.entry(name.value).or_default().push(name.span);
            collect_binder_vars(binder, seen);
        }
        Binder::Typed { binder, .. } => collect_binder_vars(binder, seen),
        Binder::Array { elements, .. } => {
            for elem in elements {
                collect_binder_vars(elem, seen);
            }
        }
        Binder::Record { fields, .. } => {
            for field in fields {
                if let Some(binder) = &field.binder {
                    collect_binder_vars(binder, seen);
                }
                // Pun { x } is not collected here — duplicate labels are caught by DuplicateLabel
            }
        }
        Binder::Wildcard { .. } | Binder::Literal { .. } => {}
    }
}

/// Extract the head type constructor name from a CST TypeExpr,
/// peeling through type applications and parentheses.
/// E.g. `Maybe Int` → Some("Maybe"), `(Foo a b)` → Some("Foo")
pub(crate) fn extract_head_constructor(ty: &crate::ast::TypeExpr) -> Option<Qualified<TypeName>> {
    match ty {
        crate::ast::TypeExpr::Constructor { name, .. } => Some(*name),
        crate::ast::TypeExpr::App { constructor, .. } => extract_head_constructor(constructor),
        _ => None,
    }
}

// ===== Binding group analysis =====
// Collects value references from CST expressions to build a dependency graph
// for top-level declarations. This enables correct processing order so that
// forward references and mutual recursion are handled properly.

/// Collect references to top-level value names from an expression.
pub(crate) fn collect_expr_refs(expr: &crate::ast::Expr, top: &HashSet<Symbol>, refs: &mut HashSet<Symbol>) {
    use crate::ast::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => {
            if top.contains(&name.name.symbol()) {
                refs.insert(name.name.symbol());
            }
        }
        Expr::App { func, arg, .. } => {
            collect_expr_refs(func, top, refs);
            collect_expr_refs(arg, top, refs);
        }
        Expr::VisibleTypeApp { func, .. } => collect_expr_refs(func, top, refs),
        Expr::Lambda { body, .. } => collect_expr_refs(body, top, refs),
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => {
            collect_expr_refs(cond, top, refs);
            collect_expr_refs(then_expr, top, refs);
            collect_expr_refs(else_expr, top, refs);
        }
        Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                collect_expr_refs(e, top, refs);
            }
            for alt in alts {
                collect_guarded_refs(&alt.result, top, refs);
            }
        }
        Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let crate::ast::LetBinding::Value { expr, .. } = b {
                    collect_expr_refs(expr, top, refs);
                }
            }
            collect_expr_refs(body, top, refs);
        }
        Expr::Do { statements, .. } | Expr::Ado { statements, .. } => {
            for stmt in statements {
                match stmt {
                    crate::ast::DoStatement::Bind { expr, .. } => {
                        collect_expr_refs(expr, top, refs)
                    }
                    crate::ast::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let crate::ast::LetBinding::Value { expr, .. } = b {
                                collect_expr_refs(expr, top, refs);
                            }
                        }
                    }
                    crate::ast::DoStatement::Discard { expr, .. } => {
                        collect_expr_refs(expr, top, refs)
                    }
                }
            }
            if let Expr::Ado { result, .. } = expr {
                collect_expr_refs(result, top, refs);
            }
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    collect_expr_refs(v, top, refs);
                }
            }
        }
        Expr::RecordAccess { expr, .. } => collect_expr_refs(expr, top, refs),
        Expr::RecordUpdate { expr, updates, .. } => {
            collect_expr_refs(expr, top, refs);
            for u in updates {
                collect_expr_refs(&u.value, top, refs);
            }
        }
        Expr::TypeAnnotation { expr, .. } => collect_expr_refs(expr, top, refs),
        Expr::Array { elements, .. } => {
            for e in elements {
                collect_expr_refs(e, top, refs);
            }
        }
        Expr::Negate { expr, .. } => collect_expr_refs(expr, top, refs),
        Expr::Literal { lit, .. } => {
            if let crate::ast::Literal::Array(elems) = lit {
                for e in elems {
                    collect_expr_refs(e, top, refs);
                }
            }
        }
        Expr::AsPattern { name, pattern, .. } => {
            collect_expr_refs(name, top, refs);
            collect_expr_refs(pattern, top, refs);
        }
        _ => {}
    }
}

/// Collect references from a guarded expression (unconditional or guarded).
pub(crate) fn collect_guarded_refs(
    guarded: &crate::ast::GuardedExpr,
    top: &HashSet<Symbol>,
    refs: &mut HashSet<Symbol>,
) {
    match guarded {
        crate::ast::GuardedExpr::Unconditional(e) => collect_expr_refs(e, top, refs),
        crate::ast::GuardedExpr::Guarded(guards) => {
            for g in guards {
                for p in &g.patterns {
                    match p {
                        crate::ast::GuardPattern::Boolean(e) => collect_expr_refs(e, top, refs),
                        crate::ast::GuardPattern::Pattern(_, e) => collect_expr_refs(e, top, refs),
                    }
                }
                collect_expr_refs(&g.expr, top, refs);
            }
        }
    }
}

/// Collect all top-level value references from a value declaration group.
pub(crate) fn collect_decl_refs(decls: &[&Decl], top: &HashSet<Symbol>) -> HashSet<Symbol> {
    let mut refs = HashSet::new();
    for decl in decls {
        if let Decl::Value {
            guarded,
            where_clause,
            ..
        } = decl
        {
            collect_guarded_refs(guarded, top, &mut refs);
            for wb in where_clause {
                if let crate::ast::LetBinding::Value { expr, .. } = wb {
                    collect_expr_refs(expr, top, &mut refs);
                }
            }
        }
    }
    refs
}

/// Compute strongly connected components using Tarjan's algorithm.
/// Returns SCCs in reverse topological order (leaves first).
pub(crate) fn tarjan_scc(nodes: &[Symbol], edges: &HashMap<Symbol, HashSet<Symbol>>) -> Vec<Vec<Symbol>> {
    let n = nodes.len();
    let idx_of: HashMap<Symbol, usize> = nodes.iter().enumerate().map(|(i, s)| (*s, i)).collect();

    let mut index_counter: usize = 0;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut index = vec![usize::MAX; n];
    let mut lowlink = vec![0usize; n];
    let mut sccs: Vec<Vec<Symbol>> = Vec::new();

    fn strongconnect(
        v: usize,
        nodes: &[Symbol],
        edges: &HashMap<Symbol, HashSet<Symbol>>,
        idx_of: &HashMap<Symbol, usize>,
        index_counter: &mut usize,
        stack: &mut Vec<usize>,
        on_stack: &mut Vec<bool>,
        index: &mut Vec<usize>,
        lowlink: &mut Vec<usize>,
        sccs: &mut Vec<Vec<Symbol>>,
    ) {
        index[v] = *index_counter;
        lowlink[v] = *index_counter;
        *index_counter += 1;
        stack.push(v);
        on_stack[v] = true;

        if let Some(deps) = edges.get(&nodes[v]) {
            for dep in deps {
                if let Some(&w) = idx_of.get(dep) {
                    if index[w] == usize::MAX {
                        strongconnect(
                            w,
                            nodes,
                            edges,
                            idx_of,
                            index_counter,
                            stack,
                            on_stack,
                            index,
                            lowlink,
                            sccs,
                        );
                        lowlink[v] = lowlink[v].min(lowlink[w]);
                    } else if on_stack[w] {
                        lowlink[v] = lowlink[v].min(index[w]);
                    }
                }
            }
        }

        if lowlink[v] == index[v] {
            let mut scc = Vec::new();
            while let Some(w) = stack.pop() {
                on_stack[w] = false;
                scc.push(nodes[w]);
                if w == v {
                    break;
                }
            }
            sccs.push(scc);
        }
    }

    for i in 0..n {
        if index[i] == usize::MAX {
            strongconnect(
                i,
                nodes,
                edges,
                &idx_of,
                &mut index_counter,
                &mut stack,
                &mut on_stack,
                &mut index,
                &mut lowlink,
                &mut sccs,
            );
        }
    }

    sccs
}


/// Collect all Type::Unif IDs in a type, assigning each a fresh named type variable.
pub(crate) fn collect_unif_var_ids(ty: &Type, map: &mut HashMap<TyVarId, TypeVarName>) {
    match ty {
        Type::Unif(id) => {
            map.entry(*id).or_insert_with(|| {
                TypeVarName::new(crate::interner::intern(&format!("$r{}", id.0)))
            });
        }
        Type::Fun(a, b) => {
            collect_unif_var_ids(a, map);
            collect_unif_var_ids(b, map);
        }
        Type::App(f, a) => {
            collect_unif_var_ids(f, map);
            collect_unif_var_ids(a, map);
        }
        Type::Forall(_, body) => collect_unif_var_ids(body, map),
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                collect_unif_var_ids(t, map);
            }
            if let Some(t) = tail {
                collect_unif_var_ids(t, map);
            }
        }
        _ => {}
    }
}

/// Replace all Type::Unif with Type::Var according to the given mapping.
pub(crate) fn replace_unif_with_vars(ty: &Type, map: &HashMap<TyVarId, TypeVarName>) -> Type {
    match ty {
        Type::Unif(id) => {
            if let Some(&name) = map.get(id) {
                Type::Var(name)
            } else {
                ty.clone()
            }
        }
        Type::Fun(a, b) => {
            Type::fun(replace_unif_with_vars(a, map), replace_unif_with_vars(b, map))
        }
        Type::App(f, a) => {
            Type::app(replace_unif_with_vars(f, map), replace_unif_with_vars(a, map))
        }
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(replace_unif_with_vars(body, map)))
        }
        Type::Record(fields, tail) => {
            let fields = fields.iter().map(|(l, t)| (*l, replace_unif_with_vars(t, map))).collect();
            let tail = tail.as_ref().map(|t| Box::new(replace_unif_with_vars(t, map)));
            Type::Record(fields, tail)
        }
        _ => ty.clone(),
    }
}

/// Check if a constructor field type is directly a partially applied type synonym.
/// Only checks the outermost type expression (counts args at the top-level App chain).
/// Nested partial applications (e.g. `F ((~>) Array)`) are left for the kind checker
/// to report as KindsDoNotUnify.
pub(crate) fn check_field_partially_applied_synonym(
    te: &crate::ast::TypeExpr,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_ops: &HashMap<Qualified<TypeOpName>, Qualified<TypeName>>,
) -> Option<TypeError> {
    use crate::ast::TypeExpr;
    // Count top-level App args and find the head
    let mut head = te;
    let mut arg_count = 0usize;
    while let TypeExpr::App { constructor, .. } = head {
        arg_count += 1;
        head = constructor.as_ref();
    }
    // Check if head is a type synonym (directly or via type operator)
    let alias_sym = match head {
        TypeExpr::Constructor { name, .. } => {
            if type_aliases.contains_key(&name.name.symbol()) {
                Some(name.name.symbol())
            } else {
                {
                    let op_key = name.map(|n| TypeOpName::new(n.symbol()));
                    type_ops.get(&op_key).and_then(|target| {
                        let sym = target.name.symbol();
                        if type_aliases.contains_key(&sym) {
                            Some(sym)
                        } else {
                            None
                        }
                    })
                }
            }
        }
        _ => None,
    };
    if let Some(sym) = alias_sym {
        if let Some((params, _)) = type_aliases.get(&sym) {
            if arg_count < params.len() {
                return Some(TypeError::PartiallyAppliedSynonym {
                    span: te.span(),
                    name: Qualified::<TypeName>::unqualified(TypeName::new(sym)),
                });
            }
        }
    }
    None
}


/// Generalize unresolved Unif vars in a kind type into forall bindings.
/// Used when exporting type kinds to avoid leaking KindState-local var IDs
/// while preserving polykinds (e.g., `Proxy :: ?k -> Type` → `forall k0. k0 -> Type`).
pub(crate) fn generalize_kind_for_export(kind: &Type) -> Type {
    use crate::typechecker::types::TyVarId;
    let mut unif_ids: Vec<TyVarId> = Vec::new();
    collect_kind_unif_ids(kind, &mut unif_ids);
    unif_ids.sort_by_key(|id| id.0);
    unif_ids.dedup();
    if unif_ids.is_empty() {
        return kind.clone();
    }
    let mut subst: HashMap<TyVarId, TypeVarName> = HashMap::new();
    let mut forall_vars = Vec::new();
    for (i, id) in unif_ids.iter().enumerate() {
        let sym = TypeVarName::new(crate::interner::intern(&format!("k{}", i)));
        subst.insert(*id, sym);
        forall_vars.push((sym, false));
    }
    let body = replace_unif_with_var(kind, &subst);
    Type::Forall(forall_vars, Box::new(body))
}

pub(crate) fn collect_kind_unif_ids(kind: &Type, out: &mut Vec<crate::typechecker::types::TyVarId>) {
    match kind {
        Type::Unif(id) => out.push(*id),
        Type::Fun(a, b) | Type::App(a, b) => {
            collect_kind_unif_ids(a, out);
            collect_kind_unif_ids(b, out);
        }
        Type::Forall(_, body) => collect_kind_unif_ids(body, out),
        _ => {}
    }
}

pub(crate) fn replace_unif_with_var(
    kind: &Type,
    subst: &HashMap<crate::typechecker::types::TyVarId, TypeVarName>,
) -> Type {
    match kind {
        Type::Unif(id) => {
            if let Some(&sym) = subst.get(id) {
                Type::Var(sym)
            } else {
                Type::kind_type() // fallback
            }
        }
        Type::Fun(a, b) => Type::fun(
            replace_unif_with_var(a, subst),
            replace_unif_with_var(b, subst),
        ),
        Type::App(a, b) => Type::app(
            replace_unif_with_var(a, subst),
            replace_unif_with_var(b, subst),
        ),
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(replace_unif_with_var(body, subst)))
        }
        _ => kind.clone(),
    }
}

/// Recursively check if a type contains any `Type::Var` (rigid type variables).
pub(crate) fn contains_type_var(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Fun(a, b) => contains_type_var(a) || contains_type_var(b),
        Type::App(f, a) => contains_type_var(f) || contains_type_var(a),
        Type::Forall(_, body) => contains_type_var(body),
        Type::Record(fields, rest) => {
            fields.iter().any(|(_, t)| contains_type_var(t))
                || rest.as_ref().is_some_and(|r| contains_type_var(r))
        }
        _ => false,
    }
}

/// Like `contains_type_var` but also considers unification variables (Type::Unif)
/// as "unknown" types. Used in instance constraint checking where unsolved unif vars
/// should be treated optimistically (the constraint may be satisfiable once resolved).
pub(crate) fn contains_type_var_or_unif(ty: &Type) -> bool {
    match ty {
        Type::Var(_) | Type::Unif(_) => true,
        Type::Fun(a, b) => contains_type_var_or_unif(a) || contains_type_var_or_unif(b),
        Type::App(f, a) => contains_type_var_or_unif(f) || contains_type_var_or_unif(a),
        Type::Forall(_, body) => contains_type_var_or_unif(body),
        Type::Record(fields, rest) => {
            fields.iter().any(|(_, t)| contains_type_var_or_unif(t))
                || rest.as_ref().is_some_and(|r| contains_type_var_or_unif(r))
        }
        _ => false,
    }
}

/// Check if a type contains any concrete type constructors (Type::Con).
/// Used to distinguish fully polymorphic constraints (all args are type vars/records
/// with type var tails) from constraints with concrete type constructors that can
/// potentially be resolved by instance matching.
pub(crate) fn type_has_concrete_con(ty: &Type) -> bool {
    match ty {
        Type::Con(_) => true,
        Type::App(f, a) => type_has_concrete_con(f) || type_has_concrete_con(a),
        Type::Fun(a, b) => type_has_concrete_con(a) || type_has_concrete_con(b),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_has_concrete_con(t))
                || tail.as_ref().map_or(false, |t| type_has_concrete_con(t))
        }
        Type::Forall(_, body) => type_has_concrete_con(body),
        Type::Var(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => false,
    }
}

/// Check if a type variable is in a valid position for deriving a functor-like class.
///
/// `want_covariant` indicates whether we want the variable in covariant (true) or
/// contravariant (false) position. `positive` tracks the current polarity as we
/// walk through the type.
///
/// Returns true if the variable is in a valid position for derivation.
pub(crate) fn check_derive_position(
    ty: &Type,
    var: Symbol,
    positive: bool,
    want_covariant: bool,
    allow_forall: bool,
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    tyvar_classes: &HashMap<TypeVarName, Vec<Symbol>>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    data_constructors: &HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>>,
    local_concrete_type_names: &HashSet<Symbol>,
    depth: usize,
) -> bool {
    if depth > 50 {
        return true;
    } // avoid infinite recursion
      // If the variable doesn't appear in this type, it's always fine
    if !type_var_occurs_in(TypeVarName::new(var), ty) {
        return true;
    }

    let functor_sym = crate::interner::intern("Functor");
    let foldable_sym = crate::interner::intern("Foldable");
    let traversable_sym = crate::interner::intern("Traversable");
    let contravariant_sym = crate::interner::intern("Contravariant");
    let bifunctor_sym = crate::interner::intern("Bifunctor");
    let profunctor_sym = crate::interner::intern("Profunctor");

    match ty {
        Type::Var(v) if v.matches_ident(var) => {
            if want_covariant {
                positive
            } else {
                !positive
            }
        }
        Type::Var(_) => true,

        Type::Fun(arg, ret) => {
            check_derive_position(
                arg,
                var,
                !positive,
                want_covariant,
                allow_forall,
                instances,
                tyvar_classes,
                ctor_details,
                data_constructors,
                local_concrete_type_names,
                depth + 1,
            ) && check_derive_position(
                ret,
                var,
                positive,
                want_covariant,
                allow_forall,
                instances,
                tyvar_classes,
                ctor_details,
                data_constructors,
                local_concrete_type_names,
                depth + 1,
            )
        }

        Type::Forall(vars, body) => {
            if vars.iter().any(|(v, _)| v.matches_ident(var)) {
                // Derived variable is shadowed by the forall — invalid
                false
            } else if !allow_forall {
                // Foldable/Traversable can't derive through forall types
                // (can't extract values from quantified types)
                false
            } else {
                check_derive_position(
                    body,
                    var,
                    positive,
                    want_covariant,
                    allow_forall,
                    instances,
                    tyvar_classes,
                    ctor_details,
                    data_constructors,
                    local_concrete_type_names,
                    depth + 1,
                )
            }
        }

        Type::App(_f, _a) => {
            let mut head = ty;
            let mut args = Vec::new();
            while let Type::App(ff, aa) = head {
                args.push(aa.as_ref());
                head = ff.as_ref();
            }
            args.reverse();

            if let Type::Con(head_con) = head {
                // Check for class instances first. If the type has a known
                // Functor/Contravariant/Bifunctor/Profunctor instance, prefer
                // instance-based checking over structural expansion. This avoids
                // expanding newtypes like Coyoneda whose internals use abstract
                // types (like Exists) that lack instances.
                let has_functor = has_class_instance_for(instances, qi_class(functor_sym), *head_con)
                    || has_class_instance_for(instances, qi_class(foldable_sym), *head_con)
                    || has_class_instance_for(instances, qi_class(traversable_sym), *head_con);
                let has_contravariant =
                    has_class_instance_for(instances, qi_class(contravariant_sym), *head_con);
                let has_bifunctor = has_class_instance_for(instances, qi_class(bifunctor_sym), *head_con);
                let has_profunctor = has_class_instance_for(instances, qi_class(profunctor_sym), *head_con);

                let has_any_instance = has_functor || has_contravariant || has_bifunctor || has_profunctor;

                // If no instances are found, try structural expansion for
                // single-constructor types (newtypes, single-ctor data types).
                if !has_any_instance {
                    if let Some(expanded_fields) =
                        try_expand_type_constructors(*head_con, &args, ctor_details, depth)
                    {
                        return expanded_fields.iter().all(|field_ty| {
                            check_derive_position(
                                field_ty,
                                var,
                                positive,
                                want_covariant,
                                allow_forall,
                                instances,
                                tyvar_classes,
                                ctor_details,
                                data_constructors,
                                local_concrete_type_names,
                                depth + 1,
                            )
                        });
                    }
                }

                for (i, arg) in args.iter().enumerate() {
                    if !type_var_occurs_in(TypeVarName::new(var), arg) {
                        continue;
                    }
                    let is_last = i == args.len() - 1;
                    let is_second_last = args.len() >= 2 && i == args.len() - 2;

                    if is_last {
                        if has_functor || has_bifunctor || has_profunctor {
                            if !check_derive_position(
                                arg,
                                var,
                                positive,
                                want_covariant,
                                allow_forall,
                                instances,
                                tyvar_classes,
                                ctor_details,
                                data_constructors,
                                local_concrete_type_names,
                                depth + 1,
                            ) {
                                return false;
                            }
                        } else if has_contravariant {
                            if !check_derive_position(
                                arg,
                                var,
                                !positive,
                                want_covariant,
                                allow_forall,
                                instances,
                                tyvar_classes,
                                ctor_details,
                                data_constructors,
                                local_concrete_type_names,
                                depth + 1,
                            ) {
                                return false;
                            }
                        } else if data_constructors
                            .get(head_con)
                            .map_or(false, |ctors| !ctors.is_empty())
                            || data_constructors.iter().any(|(k, v)| k.name.symbol() == head_con.name_symbol() && !v.is_empty())
                            || local_concrete_type_names.contains(&head_con.name_symbol())
                        {
                            // Known concrete data type without imported instances (or locally-defined
                            // type not yet processed in Pass 1 declaration order).
                            // PureScript's derive can structurally expand any concrete type
                            // regardless of import visibility. Assume covariant (product-like).
                            // Also check by unqualified name for cross-module types.
                            if !check_derive_position(
                                arg,
                                var,
                                positive,
                                want_covariant,
                                allow_forall,
                                instances,
                                tyvar_classes,
                                ctor_details,
                                data_constructors,
                                local_concrete_type_names,
                                depth + 1,
                            ) {
                                return false;
                            }
                        } else {
                            return false;
                        }
                    } else if is_second_last {
                        if has_bifunctor {
                            if !check_derive_position(
                                arg,
                                var,
                                positive,
                                want_covariant,
                                allow_forall,
                                instances,
                                tyvar_classes,
                                ctor_details,
                                data_constructors,
                                local_concrete_type_names,
                                depth + 1,
                            ) {
                                return false;
                            }
                        } else if has_profunctor {
                            if !check_derive_position(
                                arg,
                                var,
                                !positive,
                                want_covariant,
                                allow_forall,
                                instances,
                                tyvar_classes,
                                ctor_details,
                                data_constructors,
                                local_concrete_type_names,
                                depth + 1,
                            ) {
                                return false;
                            }
                        } else if data_constructors
                            .get(head_con)
                            .map_or(false, |ctors| !ctors.is_empty())
                            || local_concrete_type_names.contains(&head_con.name_symbol())
                        {
                            // Same product type assumption as above; also covers locally-defined
                            // types not yet processed in Pass 1 declaration order.
                            if !check_derive_position(
                                arg,
                                var,
                                positive,
                                want_covariant,
                                allow_forall,
                                instances,
                                tyvar_classes,
                                ctor_details,
                                data_constructors,
                                local_concrete_type_names,
                                depth + 1,
                            ) {
                                return false;
                            }
                        } else {
                            return false;
                        }
                    } else if data_constructors
                        .get(head_con)
                        .map_or(false, |ctors| !ctors.is_empty())
                        || local_concrete_type_names.contains(&head_con.name_symbol())
                    {
                        // Variable in earlier positions — assume covariant for known data types,
                        // or locally-defined types not yet processed in Pass 1 declaration order.
                        if !check_derive_position(
                            arg,
                            var,
                            positive,
                            want_covariant,
                            allow_forall,
                            instances,
                            tyvar_classes,
                            ctor_details,
                            data_constructors,
                            local_concrete_type_names,
                            depth + 1,
                        ) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
            } else if let Type::Var(head_var) = head {
                // Type variable head: use constraint info
                let (has_functor, has_contravariant, _has_bifunctor, _has_profunctor) =
                    if let Some(classes) = tyvar_classes.get(head_var) {
                        (
                            classes.contains(&functor_sym)
                                || classes.contains(&foldable_sym)
                                || classes.contains(&traversable_sym),
                            classes.contains(&contravariant_sym),
                            classes.contains(&bifunctor_sym),
                            classes.contains(&profunctor_sym),
                        )
                    } else {
                        // No constraints on this type variable — can't assume any class instances
                        (false, false, false, false)
                    };

                // If the type variable has no relevant class constraints at all,
                // we can't derive through it
                let has_any = has_functor || has_contravariant || _has_bifunctor || _has_profunctor;
                if !has_any {
                    return false;
                }

                for (i, arg) in args.iter().enumerate() {
                    if !type_var_occurs_in(TypeVarName::new(var), arg) {
                        continue;
                    }
                    let is_last = i == args.len() - 1;
                    let is_second_last = args.len() >= 2 && i == args.len() - 2;

                    if is_last || is_second_last {
                        // Use the constraint class to determine polarity
                        let flipped = if is_last {
                            has_contravariant && !has_functor
                        } else {
                            // second-to-last: Profunctor flips
                            _has_profunctor && !_has_bifunctor
                        };
                        let pos = if flipped { !positive } else { positive };
                        if !check_derive_position(
                            arg,
                            var,
                            pos,
                            want_covariant,
                            allow_forall,
                            instances,
                            tyvar_classes,
                            ctor_details,
                            data_constructors,
                            local_concrete_type_names,
                            depth + 1,
                        ) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
            } else {
                false
            }
        }

        Type::Record(fields, rest) => {
            fields.iter().all(|(_, ft)| {
                check_derive_position(
                    ft,
                    var,
                    positive,
                    want_covariant,
                    allow_forall,
                    instances,
                    tyvar_classes,
                    ctor_details,
                    data_constructors,
                    local_concrete_type_names,
                    depth + 1,
                )
            }) && rest.as_ref().map_or(true, |r| {
                check_derive_position(
                    r,
                    var,
                    positive,
                    want_covariant,
                    allow_forall,
                    instances,
                    tyvar_classes,
                    ctor_details,
                    data_constructors,
                    local_concrete_type_names,
                    depth + 1,
                )
            })
        }

        _ => true,
    }
}

/// Try to expand a concrete type constructor application into its constituent fields.
/// Returns `Some(expanded_field_types)` if the constructor is a known data/newtype type
/// with a single constructor (e.g. Tuple, Predicate, etc.).
/// Returns `None` for types with zero/multiple constructors (must fall back to instances)
/// or if the arity doesn't match.
pub(crate) fn try_expand_type_constructors(
    head_con: Qualified<TypeName>,
    args: &[&Type],
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    depth: usize,
) -> Option<Vec<Type>> {
    if depth > 20 {
        return None;
    } // avoid infinite expansion
      // Find a constructor whose parent type matches head_con
      // For types with exactly one constructor (newtypes, single-ctor data types),
      // we can expand structurally
    let mut matching_ctors = Vec::new();
    for (_ctor_name, (parent, type_vars, field_types)) in ctor_details {
        if *parent == head_con {
            matching_ctors.push((type_vars, field_types));
        }
    }

    // Only expand for single-constructor types (safe to destructure)
    if matching_ctors.len() != 1 {
        return None;
    }

    let (type_vars, field_types) = matching_ctors[0];

    // Check arity matches
    if args.len() != type_vars.len() {
        return None;
    }

    // Build substitution from type vars to actual args
    let subst: HashMap<TypeVarName, Type> = type_vars
        .iter()
        .copied()
        .zip(args.iter().map(|a| (*a).clone()))
        .collect();

    // Apply substitution to each field type
    let expanded: Vec<Type> = field_types
        .iter()
        .map(|ft| apply_var_subst(&subst, ft))
        .collect();

    Some(expanded)
}

/// Check if a type constructor has an instance of a given class.
/// Looks for instances where the head type of the first/only type argument
/// matches the given constructor.
pub(crate) fn has_class_instance_for(
    instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    class: Qualified<ClassName>,
    type_con: Qualified<TypeName>,
) -> bool {
    // Try both the exact class key and unqualified fallback
    let class_instances = instances.get(&class).or_else(|| {
        if class.module.is_some() {
            instances.get(&Qualified::unqualified(class.name))
        } else {
            None
        }
    });
    if let Some(class_instances) = class_instances {
        for (inst_types, _, _) in class_instances {
            // Instance like `Functor Array` has inst_types = [Con(Array)]
            // Instance like `Functor (Tuple a)` has inst_types = [App(Con(Tuple), Var(a))]
            if let Some(first) = inst_types.first() {
                if let Some(head) = get_type_constructor_head(first) {
                    // Match by exact Qualified<TypeName> or by unqualified name
                    if head == type_con || head.name == type_con.name {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Get the head type constructor from a type (unwrapping applications).
pub(crate) fn get_type_constructor_head(ty: &Type) -> Option<Qualified<TypeName>> {
    match ty {
        Type::Con(s) => Some(*s),
        Type::App(f, _) => get_type_constructor_head(f),
        _ => None,
    }
}

/// Check if a specific type variable appears in a type.
pub(crate) fn type_var_occurs_in(var: TypeVarName, ty: &Type) -> bool {
    match ty {
        Type::Var(v) => *v == var,
        Type::Fun(a, b) => type_var_occurs_in(var, a) || type_var_occurs_in(var, b),
        Type::App(f, a) => type_var_occurs_in(var, f) || type_var_occurs_in(var, a),
        Type::Forall(vars, body) => {
            // Don't recurse if var is shadowed
            if vars.iter().any(|(v, _)| *v == var) {
                false
            } else {
                type_var_occurs_in(var, body)
            }
        }
        Type::Record(fields, rest) => {
            fields.iter().any(|(_, t)| type_var_occurs_in(var, t))
                || rest.as_ref().is_some_and(|r| type_var_occurs_in(var, r))
        }
        _ => false,
    }
}




/// Apply a variable substitution (Type::Var → Type) to a type.
/// Fully capture-avoiding: when a forall-bound variable would capture a free
/// variable in a substitution value, the forall-bound variable is alpha-renamed.
pub(crate) fn apply_var_subst(subst: &HashMap<TypeVarName, Type>, ty: &Type) -> Type {
    apply_var_subst_inner(subst, ty, &mut 0u32)
}

pub(crate) fn apply_var_subst_inner(subst: &HashMap<TypeVarName, Type>, ty: &Type, counter: &mut u32) -> Type {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || apply_var_subst_inner_impl(subst, ty, counter))
}

pub(crate) fn apply_var_subst_inner_impl(subst: &HashMap<TypeVarName, Type>, ty: &Type, counter: &mut u32) -> Type {
    if subst.is_empty() {
        return ty.clone();
    }
    match ty {
        Type::Var(v) => subst.get(v).cloned().unwrap_or_else(|| ty.clone()),
        Type::Fun(a, b) => Type::fun(
            apply_var_subst_inner(subst, a, counter),
            apply_var_subst_inner(subst, b, counter),
        ),
        Type::App(f, a) => Type::app(
            apply_var_subst_inner(subst, f, counter),
            apply_var_subst_inner(subst, a, counter),
        ),
        Type::Forall(vars, body) => {
            // Capture-avoiding: remove forall-bound variables from the substitution keys
            let mut inner_subst = subst.clone();
            for (v, _) in vars {
                inner_subst.remove(v);
            }
            // Check if any forall-bound variable appears free in the remaining
            // substitution values. If so, alpha-rename it to avoid capture.
            let mut renames: HashMap<TypeVarName, TypeVarName> = HashMap::new();
            let mut new_vars = vars.clone();
            for (i, (v, _vis)) in vars.iter().enumerate() {
                let captured = inner_subst.values().any(|val| type_has_free_var(val, *v));
                if captured {
                    let fresh = TypeVarName::new(crate::interner::intern(&format!("$r{}", *counter)));
                    *counter += 1;
                    renames.insert(*v, fresh);
                    new_vars[i].0 = fresh;
                }
            }
            let body = if renames.is_empty() {
                apply_var_subst_inner(&inner_subst, body, counter)
            } else {
                // Rename the captured vars in the body first, then apply substitution
                let renamed_body = rename_type_vars(body, &renames);
                apply_var_subst_inner(&inner_subst, &renamed_body, counter)
            };
            Type::Forall(new_vars, Box::new(body))
        }
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| (*l, apply_var_subst_inner(subst, t, counter)))
                .collect();
            let tail = tail.as_ref().map(|t| Box::new(apply_var_subst_inner(subst, t, counter)));
            Type::Record(fields, tail)
        }
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
    }
}

/// Check if a type variable name appears free in a type.
pub(crate) fn type_has_free_var(ty: &Type, name: TypeVarName) -> bool {
    match ty {
        Type::Var(v) => *v == name,
        Type::Fun(a, b) => type_has_free_var(a, name) || type_has_free_var(b, name),
        Type::App(f, a) => type_has_free_var(f, name) || type_has_free_var(a, name),
        Type::Forall(vars, body) => {
            // name is bound by this forall — not free
            if vars.iter().any(|(v, _)| *v == name) {
                return false;
            }
            type_has_free_var(body, name)
        }
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_has_free_var(t, name))
                || tail.as_ref().map_or(false, |t| type_has_free_var(t, name))
        }
        _ => false,
    }
}

/// Rename type variables in a type (capture-avoiding for inner Foralls).
pub(crate) fn rename_type_vars(ty: &Type, renames: &HashMap<TypeVarName, TypeVarName>) -> Type {
    if renames.is_empty() {
        return ty.clone();
    }
    match ty {
        Type::Var(v) => {
            if let Some(&new) = renames.get(v) {
                Type::Var(new)
            } else {
                ty.clone()
            }
        }
        Type::Fun(a, b) => Type::fun(rename_type_vars(a, renames), rename_type_vars(b, renames)),
        Type::App(f, a) => Type::app(rename_type_vars(f, renames), rename_type_vars(a, renames)),
        Type::Forall(vars, body) => {
            // Don't rename vars that are rebound by this inner forall
            let mut inner_renames = renames.clone();
            for (v, _) in vars {
                inner_renames.remove(v);
            }
            Type::Forall(vars.clone(), Box::new(rename_type_vars(body, &inner_renames)))
        }
        Type::Record(fields, tail) => {
            let fields = fields.iter().map(|(l, t)| (*l, rename_type_vars(t, renames))).collect();
            let tail = tail.as_ref().map(|t| Box::new(rename_type_vars(t, renames)));
            Type::Record(fields, tail)
        }
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
    }
}

/// Check if a recursive function without a type annotation would generalize
/// constrained type variables. Returns a CannotGeneralizeRecursiveFunction error
/// if so, because the compiler can't introduce dictionary parameters without a signature.
pub(crate) fn check_cannot_generalize_recursive(
    state: &mut crate::typechecker::unify::UnifyState,
    deferred_constraints: &[(crate::span::Span, Qualified<ClassName>, Vec<Type>)],
    op_deferred_constraints: &[(crate::span::Span, Qualified<ClassName>, Vec<Type>)],
    name: Symbol,
    span: crate::span::Span,
    zonked_ty: &Type,
) -> Option<TypeError> {
    use std::collections::HashSet;

    // Find which unif vars would be generalized (free in type, not free in env)
    let free_in_ty: HashSet<crate::typechecker::types::TyVarId> =
        state.free_unif_vars(zonked_ty).into_iter().collect();
    if free_in_ty.is_empty() {
        return None; // Monomorphic — no generalization issue
    }

    // Check if any of those vars appear in deferred constraints (from infer_var)
    // or op deferred constraints (from infer_op_binary)
    for (_, _, constraint_args) in deferred_constraints
        .iter()
        .chain(op_deferred_constraints.iter())
    {
        for arg in constraint_args {
            let free_in_constraint: HashSet<crate::typechecker::types::TyVarId> =
                state.free_unif_vars(arg).into_iter().collect();
            if free_in_ty
                .intersection(&free_in_constraint)
                .next()
                .is_some()
            {
                return Some(TypeError::CannotGeneralizeRecursiveFunction {
                    span,
                    name: crate::names::ValueName::new(name),
                    type_: zonked_ty.clone(),
                });
            }
        }
    }

    None
}

/// Check if a non-annotated binding has ambiguous type variables: constraint type
/// args that are pure unsolved unif vars NOT free in the inferred type.
/// E.g., `test = show <<< spin` where the Show constraint's type variable
/// doesn't appear in the result type `a -> String`.
/// Only flags constraints where ALL args are pure unsolved unif vars to avoid
/// false positives from partially resolved constraints.
pub(crate) fn check_ambiguous_type_variables(
    state: &mut crate::typechecker::unify::UnifyState,
    deferred_constraints: &[(crate::span::Span, Qualified<ClassName>, Vec<Type>)],
    constraint_start: usize,
    span: crate::span::Span,
    zonked_ty: &Type,
    class_fundeps: &HashMap<Qualified<ClassName>, (Vec<TypeVarName>, Vec<(Vec<usize>, Vec<usize>)>)>,
) -> Option<TypeError> {
    use std::collections::HashSet;

    let free_in_ty: HashSet<crate::typechecker::types::TyVarId> =
        state.free_unif_vars(zonked_ty).into_iter().collect();

    // Only check polymorphic bindings (those with free type vars that will be
    // generalized). For monomorphic bindings, constraint vars not in the type
    // are expected — they're determined by the body's concrete types.
    if free_in_ty.is_empty() {
        return None;
    }

    // Collect all unif var IDs across all constraints and determine which are
    // "known" (free in type, generalized, or concrete).
    // A var is determined if it appears in a fundep output position where all
    // fundep input positions are known. This must be computed globally across
    // all constraints (not per-constraint) because a fundep in one constraint
    // can determine a var that appears in another constraint.
    let constraints: Vec<_> = deferred_constraints.iter().skip(constraint_start).collect();

    // Collect all classes that have fundeps — vars in these constraints may be
    // resolvable through instance improvement even if they look ambiguous now.
    // Build a set of unif var IDs that appear in ANY constraint of a fundep class.
    let mut fundep_reachable_vars: HashSet<crate::typechecker::types::TyVarId> = HashSet::new();
    // Prim Row/RowList classes that are compiler-solved (not tracked in class_fundeps
    // but effectively have fundeps since the solver determines outputs from inputs).
    let prim_solver_classes: HashSet<&str> = ["Nub", "Union", "Cons", "Lacks", "RowToList",
        "Add", "Compare", "Mul", "ToString", "Append", "Reflectable", "Reifiable"]
        .into_iter().collect();
    for (_, class_name, constraint_args) in &constraints {
        let cn = crate::interner::resolve(class_name.name_symbol()).unwrap_or_default();
        if class_fundeps.get(class_name).is_some() || prim_solver_classes.contains(cn.as_str()) {
            for arg in constraint_args.iter() {
                let zonked = state.zonk(arg.clone());
                // Collect ALL nested unif vars, not just bare ones.
                // E.g., MapRecord c b (j l) (j k) x d — the `j` inside App(j, l) must be found.
                for uv in state.free_unif_vars(&zonked) {
                    fundep_reachable_vars.insert(uv);
                }
            }
        }
    }

    // Map from unif var ID → set of (constraint_index, position)
    let mut var_locations: HashMap<crate::typechecker::types::TyVarId, Vec<(usize, usize)>> = HashMap::new();
    // Set of known/determined unif var IDs
    let mut known_vars: HashSet<crate::typechecker::types::TyVarId> = HashSet::new();
    // Track which constraints have any resolved (non-Unif) args
    let mut constraint_has_resolved: Vec<bool> = vec![false; constraints.len()];

    // Zonked args per constraint
    let mut all_zonked: Vec<Vec<(Type, Option<crate::typechecker::types::TyVarId>)>> = Vec::new();

    for (ci, (_, _, constraint_args)) in constraints.iter().enumerate() {
        let mut zonked_args = Vec::new();
        for (i, arg) in constraint_args.iter().enumerate() {
            let zonked = state.zonk(arg.clone());
            if let Type::Unif(id) = zonked {
                if state.generalized_vars.contains(&id) || free_in_ty.contains(&id) {
                    known_vars.insert(id);
                    zonked_args.push((Type::Unif(id), Some(id)));
                } else {
                    var_locations.entry(id).or_default().push((ci, i));
                    zonked_args.push((Type::Unif(id), Some(id)));
                }
            } else {
                constraint_has_resolved[ci] = true;
                zonked_args.push((zonked, None));
            }
        }
        all_zonked.push(zonked_args);
    }

    // Fixed-point: propagate fundep determinations
    let mut changed = true;
    while changed {
        changed = false;
        for (ci, (_, class_name, _)) in constraints.iter().enumerate() {
            if let Some((_, fundeps)) = class_fundeps.get(class_name) {
                for (inputs, outputs) in fundeps {
                    // Check if all input positions are known
                    let all_inputs_known = inputs.iter().all(|&idx| {
                        if idx >= all_zonked[ci].len() { return false; }
                        match &all_zonked[ci][idx] {
                            (_, None) => true, // concrete
                            (_, Some(id)) => known_vars.contains(id),
                        }
                    });
                    if all_inputs_known {
                        for &idx in outputs {
                            if idx >= all_zonked[ci].len() { continue; }
                            if let (_, Some(id)) = &all_zonked[ci][idx] {
                                if known_vars.insert(*id) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Now check: any constraint where ALL unsolved vars are still unknown is ambiguous
    for (ci, (_, _class_name, constraint_args)) in constraints.iter().enumerate() {
        let mut ambiguous_names: Vec<TypeVarName> = Vec::new();
        for (i, _) in constraint_args.iter().enumerate() {
            if i >= all_zonked[ci].len() { continue; }
            if let (_, Some(id)) = &all_zonked[ci][i] {
                // Skip vars reachable through fundep constraints — they may be
                // resolved through instance improvement during constraint solving.
                if !known_vars.contains(id) && !fundep_reachable_vars.contains(id) {
                    ambiguous_names.push(TypeVarName::new(crate::interner::intern(&format!("t{}", id.0))));
                }
            }
        }
        if !ambiguous_names.is_empty() && !constraint_has_resolved[ci] {
            return Some(TypeError::AmbiguousTypeVariables {
                span,
                names: ambiguous_names,
            });
        }
    }

    None
}

// ============================================================================
// Instance registry helpers
// ============================================================================

/// Extract head type constructor from first type arg of an instance.
/// E.g. for `Show Int`, inst_types=[Con("Int")] → head=Int.
/// For `Show (Array a)`, inst_types=[App(Con("Array"), Var("a"))] → head=Array.
/// Compute the Generic representation type for a data type.
/// This constructs the type-level representation using Sum, Constructor, Product, Argument, NoArguments
/// from Data.Generic.Rep.
pub(crate) fn compute_generic_rep_type(
    target_name: &Qualified<TypeName>,
    data_constructors: &HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>>,
    ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
) -> Option<Type> {
    let target_typed = *target_name;
    let ctors = data_constructors.get(&target_typed)
        .or_else(|| {
            data_constructors.iter()
                .find(|(k, _)| k.name.symbol() == target_name.name.symbol())
                .map(|(_, v)| v)
        })?;
    if ctors.is_empty() { return None; }

    let sum_sym = intern("Sum");
    let constructor_sym = intern("Constructor");
    let product_sym = intern("Product");
    let argument_sym = intern("Argument");
    let no_arguments_sym = intern("NoArguments");

    let mut ctor_reps: Vec<Type> = Vec::new();
    for ctor_qi in ctors {
        let ctor_name_str = crate::interner::resolve(ctor_qi.name_symbol()).unwrap_or_default().to_string();
        let ctor_name_type_sym = intern(&ctor_name_str);

        let fields = ctor_details.get(ctor_qi)
            .or_else(|| ctor_details.iter().find(|(k, _)| k.name.symbol() == ctor_qi.name_symbol()).map(|(_, v)| v))
            .map(|(_, _, fields)| fields.as_slice())
            .unwrap_or(&[]);

        let args_rep = if fields.is_empty() {
            Type::Con(qi_type(no_arguments_sym))
        } else {
            // Right-nested Product of Argument types
            let arg_types: Vec<Type> = fields.iter()
                .map(|t| Type::App(Box::new(Type::Con(qi_type(argument_sym))), Box::new(t.clone())))
                .collect();
            arg_types.into_iter().rev().reduce(|acc, arg| {
                Type::App(
                    Box::new(Type::App(Box::new(Type::Con(qi_type(product_sym))), Box::new(arg))),
                    Box::new(acc),
                )
            }).unwrap()
        };

        // Constructor "Name" args
        let ctor_rep = Type::App(
            Box::new(Type::App(
                Box::new(Type::Con(qi_type(constructor_sym))),
                Box::new(Type::TypeString(ctor_name_type_sym)),
            )),
            Box::new(args_rep),
        );
        ctor_reps.push(ctor_rep);
    }

    // Right-nested Sum of constructors
    Some(ctor_reps.into_iter().rev().reduce(|acc, ctor| {
        Type::App(
            Box::new(Type::App(Box::new(Type::Con(qi_type(sum_sym))), Box::new(ctor))),
            Box::new(acc),
        )
    }).unwrap())
}

/// Generate an instance name part from a Type (for anonymous instance registry entries).
/// Mirrors the logic in codegen's `type_expr_to_name` but works on `Type` instead of `TypeExpr`.
pub(crate) fn type_to_instance_name_part(ty: &Type) -> String {
    match ty {
        Type::Con(qi) => {
            let name = crate::interner::resolve(qi.name_symbol()).unwrap_or_default().to_string();
            // Strip module qualifier if present
            if let Some(dot_pos) = name.rfind('.') {
                name[dot_pos + 1..].to_string()
            } else {
                name
            }
        }
        Type::App(f, _) => type_to_instance_name_part(f),
        Type::Record(_, _) => "Record".to_string(),
        Type::Fun(_, _) => "Function".to_string(),
        Type::Var(v) => {
            format!("{}", v)
        }
        _ => String::new(),
    }
}

/// Extract head type constructors from ALL type args (for multi-param classes).
pub(crate) fn extract_all_head_type_cons(inst_types: &[Type]) -> Vec<Symbol> {
    inst_types.iter().filter_map(|t| extract_head_from_type_tc(t)).collect()
}

pub(crate) fn extract_head_from_type_tc(ty: &Type) -> Option<Symbol> {
    match ty {
        Type::Con(qi) => Some(qi.name_symbol()),
        Type::App(f, _) => extract_head_from_type_tc(f),
        Type::Record(_, _) => Some(intern("Record")),
        Type::Fun(_, _) => Some(intern("Function")),
        _ => None,
    }
}

// ============================================================================
// Role inference and Coercible solver

/// Find the return type of a function type, stripping outer Forall.
/// E.g. `Forall(a, Fun(Var(a), App(Con("Foo"), Var(a))))` → `App(Con("Foo"), Var(a))`
pub(crate) fn find_return_type(ty: &Type) -> &Type {
    match ty {
        Type::Forall(_, body) => find_return_type(body),
        Type::Fun(_, ret) => find_return_type(ret),
        other => other,
    }
}

/// Count function arrow depth, stripping Forall.
pub(crate) fn find_return_type_depth(ty: &Type) -> usize {
    match ty {
        Type::Forall(_, body) => find_return_type_depth(body),
        Type::Fun(_, ret) => 1 + find_return_type_depth(ret),
        _ => 0,
    }
}

/// Extract the head type constructor name from a Type.
/// E.g. `App(Con("Expr"), Con("Number"))` → Some("Expr")
/// E.g. `Con("Foo")` → Some("Foo")
pub(crate) fn extract_type_head_name(ty: &Type) -> Option<Symbol> {
    match ty {
        Type::Con(qi) => Some(qi.name_symbol()),
        Type::App(head, _) => extract_type_head_name(head),
        _ => None,
    }
}

/// Walks through Forall → Constrained patterns, converting constraint args to internal Types.
/// Skips Partial and Warn (which are handled separately).
pub(crate) fn extract_type_signature_constraints(
    ty: &crate::ast::TypeExpr,
    type_ops: &HashMap<Qualified<TypeOpName>, Qualified<TypeName>>,
) -> Vec<(Qualified<ClassName>, Vec<Type>)> {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Forall { ty, .. } => {
            extract_type_signature_constraints(ty, type_ops)
        }
        TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            let mut result = Vec::new();
            for c in constraints {
                // Skip auto-satisfied compiler-magic classes that never fail and
                // don't need solver verification at call sites. These are always
                // auto-satisfied regardless of import source.
                // Do NOT skip classes with solvers that can fail (Lacks, Coercible,
                // Compare, Add, Mul, ToString, IsSymbol, Fail, etc.).
                // Union MUST reach deferred_constraints so the solver can
                // resolve output row variables before generalization.
                let class_str = crate::interner::resolve(c.class.name.symbol()).unwrap_or_default();
                let is_auto_satisfied = matches!( // TODO: this should include module as well as class name
                    class_str.as_str(),
                    "Partial" | "Warn" | "Cons" | "RowToList" | "CompareSymbol"
                );
                if is_auto_satisfied {
                    continue;
                }
                let mut args = Vec::new();
                let mut ok = true;
                for arg in &c.args {
                    match convert_type_expr(arg, type_ops) {
                        Ok(converted) => args.push(converted),
                        Err(_) => {
                            ok = false;
                            break;
                        }
                    }
                }
                let class_typed = c.class;
                if ok {
                    result.push((class_typed, args));
                } else if c.class.name.eq_str("Fail") {
                    // Fail constraints should always be recorded even if args can't
                    // be converted (e.g. type-level Text/Quote from Prim.TypeError).
                    // The args aren't needed for error detection — any use of Fail
                    // means the constraint is deliberately unsatisfiable.
                    result.push((class_typed, Vec::new()));
                }
            }
            // Recurse into the inner type for chained constraints
            // (e.g. `Compare a b EQ => Compare b c GT => ...` parses as nested Constrained)
            result.extend(extract_type_signature_constraints(
                ty,
                type_ops,
            ));
            result
        }
        _ => Vec::new(),
    }
}

/// Extract inner-forall constraints from the return type of a function signature.
/// For `sequence :: forall t. Sequence t -> (forall m a. Monad m => t (m a) -> m (t a))`,
/// this extracts `[(Monad, [Var(m)])]` where `m` is the inner forall var.
/// The returned constraints use type variables from the INNER forall.
pub(crate) fn extract_return_type_constraints(
    ty: &crate::ast::TypeExpr,
    type_ops: &HashMap<Qualified<TypeOpName>, Qualified<TypeName>>,
) -> Vec<(Qualified<ClassName>, Vec<Type>)> {

    // Strip outer forall
    let ty = strip_outer_forall_and_constraints(ty);
    // Walk past function arrows to find the return type
    let ret = find_return_type_expr(ty);
    // Extract constraints from the return type's inner forall
    extract_inner_forall_constraints_from_type_expr(ret, type_ops)
}

/// Count the number of function arrows before the return type's inner forall.
/// For `Sequence t -> (forall m a. Monad m => ...)`, returns 1.
/// For `a -> b -> (forall m. Monad m => ...)`, returns 2.
pub(crate) fn count_return_type_arrow_depth(ty: &crate::ast::TypeExpr) -> usize {
    
    let ty = strip_outer_forall_and_constraints(ty);
    count_arrows(ty)
}

pub(crate) fn count_arrows(ty: &crate::ast::TypeExpr) -> usize {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Function { to, .. } => 1 + count_arrows(to),
        _ => 0,
    }
}

/// Strip outer Forall and Constrained wrappers.
pub(crate) fn strip_outer_forall_and_constraints(ty: &crate::ast::TypeExpr) -> &crate::ast::TypeExpr {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Forall { ty, .. } => strip_outer_forall_and_constraints(ty),
        TypeExpr::Constrained { ty, .. } => strip_outer_forall_and_constraints(ty),
        other => other,
    }
}

/// Walk past function arrows (rightward) to find the return type.
pub(crate) fn find_return_type_expr(ty: &crate::ast::TypeExpr) -> &crate::ast::TypeExpr {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Function { to, .. } => find_return_type_expr(to),
        other => other,
    }
}

/// Extract constraints from a type that is `Forall { Constrained { ... } }` or just `Constrained`.
pub(crate) fn extract_inner_forall_constraints_from_type_expr(
    ty: &crate::ast::TypeExpr,
    type_ops: &HashMap<Qualified<TypeOpName>, Qualified<TypeName>>,
) -> Vec<(Qualified<ClassName>, Vec<Type>)> {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Forall { ty, .. } => extract_inner_forall_constraints_from_type_expr(ty, type_ops),
        TypeExpr::Constrained { constraints, .. } => {
            let mut result = Vec::new();
            for c in constraints {
                let class_str = crate::interner::resolve(c.class.name.symbol()).unwrap_or_default();
                let is_auto_satisfied = matches!( // TODO: this should include module as well as class name
                    class_str.as_str(),
                    "Partial" | "Warn" | "Union" | "Cons" | "RowToList" | "CompareSymbol"
                );
                if is_auto_satisfied {
                    continue;
                }
                let mut args = Vec::new();
                let mut ok = true;
                for arg in &c.args {
                    match convert_type_expr(arg, type_ops) {
                        Ok(converted) => args.push(converted),
                        Err(_) => { ok = false; break; }
                    }
                }
                if ok {
                    result.push((c.class, args));
                }
            }
            result
        }
        _ => Vec::new(),
    }
}

/// Check if a TypeExpr has a Partial constraint.
pub(crate) fn has_partial_constraint(ty: &crate::ast::TypeExpr) -> bool {
    match ty {
        crate::ast::TypeExpr::Constrained { constraints, .. } => constraints
            .iter()
            .any(|c| c.class.name.eq_str("Partial")),
        crate::ast::TypeExpr::Forall { ty, .. } => has_partial_constraint(ty),
        _ => false,
    }
}

/// Used to detect functions that discharge the Partial constraint (like unsafePartial).
pub(crate) fn has_partial_in_function_param(ty: &crate::ast::TypeExpr) -> bool {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Forall { ty, .. } => has_partial_in_function_param(ty),
        TypeExpr::Constrained { ty, .. } => has_partial_in_function_param(ty),
        TypeExpr::Function { from, .. } => has_partial_constraint(from),
        _ => false,
    }
}

/// Check if a type expression contains a wildcard `_` anywhere.
pub(crate) fn find_wildcard_span(ty: &crate::ast::TypeExpr) -> Option<crate::span::Span> {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Wildcard { span } => Some(*span),
        TypeExpr::App {
            constructor, arg, ..
        } => find_wildcard_span(constructor).or_else(|| find_wildcard_span(arg)),
        TypeExpr::Function { from, to, .. } => {
            find_wildcard_span(from).or_else(|| find_wildcard_span(to))
        }
        TypeExpr::Forall { ty, .. } => find_wildcard_span(ty),
        TypeExpr::Constrained { ty, .. } => find_wildcard_span(ty),
        TypeExpr::Kinded { ty, kind, .. } => {
            find_wildcard_span(ty).or_else(|| find_wildcard_span(kind))
        }
        TypeExpr::Record { fields, .. } => fields.iter().find_map(|f| find_wildcard_span(&f.ty)),
        TypeExpr::Row { fields, tail, .. } => fields
            .iter()
            .find_map(|f| find_wildcard_span(&f.ty))
            .or_else(|| tail.as_ref().and_then(|t| find_wildcard_span(t))),
        _ => None,
    }
}

/// Check if an expression is directly a variable reference to any name in the set.
/// Used for conservative cycle detection: `x = y` where y is in the set IS a direct
/// reference, but `x = f y` or `x = f <$> y` is NOT. The idea is to only flag the
/// simplest cycles like `x = x` or `x = y; y = x`, while allowing `x = f <$> z`
/// even if z is in the same SCC (since f creates a thunk/intermediate value).
pub(crate) fn is_direct_var_ref(expr: &crate::ast::Expr, names: &HashSet<Symbol>) -> bool {
    use crate::ast::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => names.contains(&name.name.symbol()),
        Expr::TypeAnnotation { expr, .. } => is_direct_var_ref(expr, names),
        _ => false,
    }
}

/// Extract the "application head" of an expression — the leftmost function in an application chain.
/// Returns the unqualified variable name if the head is a simple Var, None otherwise.
/// Used for instance method cycle detection: only the head of the application matters,
/// not arguments (which may dispatch to different typeclass instances).
pub(crate) fn expr_app_head_name(expr: &crate::ast::Expr) -> Option<Symbol> {
    use crate::ast::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => Some(name.name.symbol()),
        Expr::App { func, .. } => expr_app_head_name(func),
        Expr::TypeAnnotation { expr, .. } => expr_app_head_name(expr),
        _ => None,
    }
}

/// Try to compute the nub of a row type (remove duplicate labels, keeping the first occurrence).
/// Returns `Some(nubbed_row)` if the row can be flattened and nubbed, `None` if the row
/// has unsolved parts (type variables, unif vars) that prevent nubbing.
pub(crate) fn try_nub_row(ty: &Type) -> Option<Type> {
    // Flatten the row: collect all fields from nested Record types
    let (fields, tail) = flatten_row(ty);

    // Can only nub if the row is fully concrete (no open tail with non-record types)
    match &tail {
        Some(t) => {
            // If the tail is a type variable or unif var, we can't nub
            match t.as_ref() {
                Type::Var(_) | Type::Unif(_) => return None,
                _ => return None,
            }
        }
        None => {} // Closed row — can nub
    }

    // Check that we have at least one duplicate (otherwise nub is identity — no need to solve)
    let mut label_set = std::collections::HashSet::new();
    let has_duplicates = fields.iter().any(|(label, _)| !label_set.insert(*label));
    if !has_duplicates {
        return None; // No duplicates — nub is identity, nothing to check
    }

    // Compute the nub: keep first occurrence of each label
    let mut seen = std::collections::HashSet::new();
    let nubbed_fields: Vec<(LabelName, Type)> = fields
        .into_iter()
        .filter(|(label, _)| seen.insert(*label))
        .collect();

    Some(Type::Record(nubbed_fields, None))
}

/// Try to compute the union of two row types (merge fields from left and right).
/// Returns `Some(merged_row)` if both rows can be flattened, `None` if they have unsolved parts.
pub(crate) fn try_union_rows(left: &Type, right: &Type) -> Option<Type> {
    let (left_fields, left_tail) = flatten_row(left);
    let (right_fields, right_tail) = flatten_row(right);

    // Both rows must be closed (no open tails)
    match (&left_tail, &right_tail) {
        (None, None) => {}
        _ => return None,
    }

    // If either has unsolved vars in field types, bail
    // (We allow it if the fields themselves are concrete)

    // Merge: left fields first, then right fields
    let mut merged = left_fields;
    merged.extend(right_fields);

    Some(Type::Record(merged, None))
}

/// Flatten a row type by collecting all fields from nested Record types.
/// Returns (all_fields, optional_non_record_tail).
pub(crate) fn flatten_row(ty: &Type) -> (Vec<(LabelName, Type)>, Option<Box<Type>>) {
    match ty {
        Type::Record(fields, tail) => {
            let mut all_fields: Vec<(LabelName, Type)> = fields.clone();
            let final_tail = if let Some(t) = tail {
                let (more_fields, inner_tail) = flatten_row(t);
                all_fields.extend(more_fields);
                inner_tail
            } else {
                None
            };
            (all_fields, final_tail)
        }
        _ => (vec![], Some(Box::new(ty.clone()))),
    }
}

/// Check kind consistency of a class parameter type with its application arguments.
///
/// When a class method is used (e.g., `imap identity foo`), the class parameter `f`
/// gets resolved to a concrete type (e.g., `Indexed Array`) and is applied to
/// arguments (e.g., `D1`, `D2`, `Int`). The class kind signature constrains the
/// parameter's kind (e.g., `ix -> ix -> Type -> Type`). This function checks that
/// the concrete application arguments have compatible kinds.
///
/// Returns `Err(KindMismatch)` if the kinds are inconsistent.
pub(crate) fn check_class_param_kind_consistency(
    span: crate::span::Span,
    class_name: Qualified<ClassName>,
    constraint_type: &Type,
    app_args: &[Type],
    saved_type_kinds: &HashMap<Qualified<ClassName>, Type>,
    saved_class_kinds: &HashMap<Qualified<ClassName>, Type>,
) -> Result<(), TypeError> {
    use crate::typechecker::kind::{self, KindState};
    use crate::typechecker::unify::UnifyState;

    // Only check if there are application arguments to validate
    if app_args.is_empty() {
        return Ok(());
    }

    // Look up the class kind — prefer class_kinds (avoids collision with same-named data types)
    let class_kind_raw = match saved_class_kinds.get(&class_name)
        .or_else(|| saved_type_kinds.get(&class_name)) {
        Some(k) => k.clone(),
        None => {
            return Ok(());
        }
    };

    // Check if the class kind has shared type variables (e.g., ix -> ix -> ...).
    // Shared Var nodes indicate kind equality constraints from the class signature.
    if !kind_has_shared_type_vars(&class_kind_raw) {
        return Ok(());
    }

    // Create a fresh KindState for this check
    let mut ks = KindState {
        state: UnifyState::new(),
        type_kinds: HashMap::new(),
        class_kinds: HashMap::new(),
        binding_group: std::collections::HashSet::new(),
        deferred_quantification_checks: Vec::new(),
        class_param_kind_types: Vec::new(),
        qualifier_to_canonical: HashMap::new(),
    };

    // Remap saved type kinds to fresh variables in the new state
    let mut old_to_new: HashMap<crate::typechecker::types::TyVarId, Type> = HashMap::new();
    for (name, kind_val) in saved_type_kinds {
        let remapped = kind::remap_unif_vars(kind_val, &mut old_to_new, &mut ks);
        ks.register_type(name.name.symbol(), remapped);
    }
    for (name, kind_val) in saved_class_kinds {
        let remapped = kind::remap_unif_vars(kind_val, &mut old_to_new, &mut ks);
        ks.class_kinds.insert(name.name.symbol(), remapped);
    }

    // Look up the class kind and instantiate it (replacing Forall vars with fresh unif vars).
    // This ensures both occurrences of `ix` in `forall ix. (ix -> ix -> ...) -> Constraint`
    // map to the SAME unif var, creating the kind equality constraint.
    let class_kind = match ks.lookup_class_kind_fresh(class_name.name_symbol()) {
        Some(k) => kind::instantiate_kind(&mut ks, &k),
        None => return Ok(()),
    };


    // Extract the class parameter kind (strip the result Constraint).
    // E.g., (ix -> ix -> Type -> Type) -> Constraint  →  ix -> ix -> Type -> Type
    let param_kind = match class_kind {
        Type::Fun(param, _) => *param,
        _ => return Ok(()),
    };

    // Infer the kind of the constraint type (e.g., Indexed Array)
    let constraint_kind = match kind::infer_runtime_kind_pub(constraint_type, &mut ks, span) {
        Ok(k) => k,
        Err(_) => return Ok(()), // Kind inference failed — don't cascade errors
    };

    // Unify the constraint type's kind with the class parameter kind.
    // This establishes kind constraints (e.g., ?k2 = ?k3 = ?ix).
    if ks.unify_kinds(span, &param_kind, &constraint_kind).is_err() {
        return Err(TypeError::KindsDoNotUnify {
            span,
            expected: param_kind,
            found: constraint_kind,
        });
    }

    // Now check each application argument's kind against the constrained param kind.
    // Walk the param kind as a chain of function arrows.
    // NOTE: infer_runtime_kind looks up kinds by unqualified name, which can be wrong
    // when different imported types share the same name (e.g., Concur.Core.Props.Props
    // :: Type -> Type -> Type vs React.DOM.Props.Props :: Type). We detect such cases by
    // checking if the inferred arg kind has strictly more function arrows than the
    // expected kind position — this indicates a wrong kind lookup for a higher-kinded
    // type when a simpler type was expected.
    let mut remaining_kind = ks.state.zonk(param_kind.clone());
    for arg in app_args {
        let arg_kind = match kind::infer_runtime_kind_pub(arg, &mut ks, span) {
            Ok(k) => k,
            Err(_) => return Ok(()),
        };
        let result_kind = ks.fresh_kind_var();
        let expected = Type::fun(arg_kind.clone(), result_kind.clone());
        if ks.unify_kinds(span, &expected, &remaining_kind).is_err() {
            // Check if the failure might be due to wrong kind lookup: if the inferred
            // arg_kind is a function type but the expected position is a simple type,
            // this suggests a name collision gave us the wrong (higher-kinded) type.
            let zonked_arg = ks.state.zonk(arg_kind);
            let is_likely_lookup_error = matches!(zonked_arg, Type::Fun(..));
            if is_likely_lookup_error {
                return Ok(());
            }
            return Err(TypeError::KindsDoNotUnify {
                span,
                expected: remaining_kind,
                found: expected,
            });
        }
        remaining_kind = ks.state.zonk(result_kind);
    }

    Ok(())
}

/// Check if a kind type has shared type variables (same Var name in multiple positions).
/// This indicates the kind introduces equality constraints (e.g., `forall ix. ix -> ix -> Type -> Type`).
/// Works on raw kinds from saved_type_kinds which use Type::Var (not Type::Unif).
pub(crate) fn kind_has_shared_type_vars(ty: &Type) -> bool {
    let mut seen = std::collections::HashSet::new();
    kind_collect_type_vars_shared(ty, &mut seen)
}

pub(crate) fn kind_collect_type_vars_shared(ty: &Type, seen: &mut std::collections::HashSet<TypeVarName>) -> bool {
    match ty {
        Type::Var(name) => !seen.insert(*name), // Returns true if already seen (duplicate)
        Type::Unif(id) => {
            // Also check Unif vars (for remapped kinds)
            let fake_sym = crate::interner::intern(&format!("__unif_{}", id.0));
            !seen.insert(TypeVarName::new(fake_sym))
        }
        Type::Fun(a, b) | Type::App(a, b) => {
            kind_collect_type_vars_shared(a, seen) || kind_collect_type_vars_shared(b, seen)
        }
        Type::Forall(_, body) => kind_collect_type_vars_shared(body, seen),
        _ => false,
    }
}

/// Check if a type expression has any type class constraint (at the top level, under forall/parens).
pub(crate) fn has_any_constraint(ty: &crate::ast::TypeExpr) -> Option<crate::span::Span> {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Constrained { span, .. } => Some(*span),
        TypeExpr::Forall { ty, .. } => has_any_constraint(ty),
        _ => None,
    }
}

pub(crate) fn is_compare(class_name: &Qualified<ClassName>) -> bool {
    class_name.name.eq_str("Compare")
}

