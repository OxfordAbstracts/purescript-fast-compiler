use std::collections::{HashMap, HashSet};

use crate::span::Span;
use crate::ast::{
    Binder, Decl, Module, TypeExpr,
};
use crate::cst::{
    unqualified_ident, qualified_ident, Associativity, DataMembers,
    Export, Import, ImportList, KindSigSource, ModuleName, QualifiedIdent, Spanned,
};
use crate::interner::intern;
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::{
    check_exhaustiveness, extract_type_con, is_refutable, is_unconditional_for_exhaustiveness,
    unwrap_binder, InferCtx,
};
use crate::typechecker::registry::{DictExpr, ModuleExports, ModuleRegistry};
use crate::typechecker::types::{Role, Scheme, TyVarId, Type};

/// Wrap a bare Symbol as an unqualified QualifiedIdent. Only for local identifier, not for imports
#[inline]
fn qi(sym: Symbol) -> QualifiedIdent {
    QualifiedIdent {
        module: None,
        name: sym,
    }
}

#[inline]
fn imported_qi(module: &str, name: Symbol) -> QualifiedIdent {
    QualifiedIdent {
        module: Some(intern(module)),
        name,
    }
}

fn prim_qi(name: Symbol) -> QualifiedIdent {
    imported_qi("Prim", name)
}

/// Check for duplicate type arguments in a list of type variables.
/// Returns an error if any name appears more than once.
fn check_duplicate_type_args(type_vars: &[Spanned<Symbol>], errors: &mut Vec<TypeError>) {
    let mut seen: HashMap<Symbol, Vec<Span>> = HashMap::new();
    for tv in type_vars {
        seen.entry(tv.value).or_default().push(tv.span);
    }
    for (name, spans) in seen {
        if spans.len() > 1 {
            errors.push(TypeError::DuplicateTypeArgument { spans, name });
        }
    }
}

/// Check for overlapping argument names in a list of binders.
/// Returns an error if any variable name appears more than once.
fn check_overlapping_arg_names(decl_span: Span, binders: &[Binder], errors: &mut Vec<TypeError>) {
    let mut seen: HashMap<Symbol, Vec<Span>> = HashMap::new();
    for binder in binders {
        collect_binder_vars(binder, &mut seen);
    }
    for (name, spans) in seen {
        if spans.len() > 1 {
            errors.push(TypeError::OverlappingArgNames {
                span: decl_span,
                name,
                spans,
            });
        }
    }
}

/// Collect type constructor references from a CST TypeExpr.
fn collect_type_refs(ty: &crate::ast::TypeExpr, refs: &mut HashSet<Symbol>) {
    match ty {
        crate::ast::TypeExpr::Constructor { name, .. } => {
            // Only track unqualified references as local alias dependencies.
            // Qualified refs (e.g. P.Number) point to external modules, not local aliases.
            if name.module.is_none() {
                refs.insert(name.name);
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
    bound: &HashSet<Symbol>,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        TypeExpr::Var { span, name } => {
            if !bound.contains(&name.value) {
                errors.push(TypeError::UndefinedTypeVariable {
                    span: *span,
                    name: name.value,
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
                inner_bound.insert(v.value);
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
fn has_forall_or_wildcard(ty: &TypeExpr) -> Option<crate::span::Span> {
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
fn has_invalid_instance_head_type_expr(ty: &TypeExpr) -> bool {
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
fn check_constraint_class_names(
    ty: &TypeExpr,
    known_classes: &HashSet<QualifiedIdent>,
    class_param_counts: &HashMap<QualifiedIdent, usize>,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            for constraint in constraints {
                if constraint.class.module.is_none()
                    && !known_classes.contains(&constraint.class)
                {
                    errors.push(TypeError::UnknownClass {
                        span: constraint.span,
                        name: constraint.class,
                    });
                }
                // Check constraint arity: the number of type args must match
                // the class param count. E.g. `Foo a` when `class Foo a b` is an error.
                // Skip ambiguous classes (usize::MAX = multiple imports with different arities).
                if let Some(&expected) = class_param_counts.get(&constraint.class) {
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
fn is_non_nominal_instance_head(
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
fn is_non_nominal_instance_head_record_only(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
) -> bool {
    if !has_synonym_head(ty, type_aliases) {
        return false;
    }
    // Extract the synonym name from the head
    fn get_head_name(ty: &Type) -> Option<Symbol> {
        match ty {
            Type::Con(name) => Some(name.name),
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
fn has_open_record_row(ty: &Type) -> bool {
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
fn has_open_row_tail(ty: &Type) -> bool {
    match ty {
        Type::Record(_, None) => false,
        Type::Record(_, Some(tail)) => row_tail_is_open(tail),
        _ => false,
    }
}

fn row_tail_is_open(tail: &Type) -> bool {
    match tail {
        Type::Var(_) | Type::Unif(_) => true,
        Type::Record(_, None) => false,
        Type::Record(_, Some(inner)) => row_tail_is_open(inner),
        _ => true, // conservative: App/Con/etc treated as potentially open
    }
}

fn is_non_nominal_for_derive(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    data_constructors: &HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
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
            Type::Con(qi) => data_constructors.contains_key(qi),
            Type::App(f, _) => match f.as_ref() {
                Type::Con(qi) => data_constructors.contains_key(qi),
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

/// Check if the outermost constructor of a type is a known type synonym.
fn has_synonym_head(ty: &Type, type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>) -> bool {
    match ty {
        Type::Con(name) => type_aliases.contains_key(&name.name),
        Type::App(f, _) => has_synonym_head(f, type_aliases),
        _ => false,
    }
}

/// Collect all type constructor names (Con) referenced in a type.
/// Used to determine which type_con_arities entries are needed for
/// alias expansion disambiguation.
fn collect_type_con_names_from_type(ty: &Type, names: &mut HashSet<Symbol>) {
    match ty {
        Type::Con(qi) => { names.insert(qi.name); }
        Type::App(f, a) => { collect_type_con_names_from_type(f, names); collect_type_con_names_from_type(a, names); }
        Type::Fun(a, b) => { collect_type_con_names_from_type(a, names); collect_type_con_names_from_type(b, names); }
        Type::Forall(_, body) => { collect_type_con_names_from_type(body, names); }
        Type::Record(fields, tail) => {
            for (_, t) in fields { collect_type_con_names_from_type(t, names); }
            if let Some(t) = tail { collect_type_con_names_from_type(t, names); }
        }
        _ => {}
    }
}

/// Expand type aliases with a depth limit to prevent stack overflow.
/// Uses exact arity matching (args == params) for safety.
pub fn expand_type_aliases_limited(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    depth: u32,
) -> Type {
    let mut expanding = HashSet::new();
    expand_type_aliases_limited_inner(ty, type_aliases, None, depth, &mut expanding, None)
}

/// Expand type aliases with over-saturation support and data-type disambiguation.
/// Look up type constructor arity, falling back to unqualified or name-only match.
/// Needed because alias bodies contain unqualified type references, but
/// type_con_arities stores entries under qualified import keys.
fn lookup_type_con_arity(
    arities: &HashMap<QualifiedIdent, usize>,
    name: &QualifiedIdent,
) -> Option<usize> {
    // Always return the MAXIMUM arity found across all entries with matching .name.
    // This handles the case where an alias body (from another module) contains an
    // unqualified Con that refers to a type with arity N, but the consuming module
    // also has a local definition with the same name but lower arity
    // (e.g. `Data.Options.Options` arity 1 vs local `data Options` arity 0).
    // Using the max prevents spurious KindArityMismatch errors when the alias
    // body's Con is checked in a context with a lower-arity local definition.
    //
    // For qualified names (e.g. `Opt.Options`), first try exact match, then fall
    // back to unqualified; since there's an exact key we don't need the max trick.
    if name.module.is_some() {
        arities.get(name).copied()
            .or_else(|| arities.get(&QualifiedIdent { module: None, name: name.name }).copied())
    } else {
        // Unqualified: return max arity across all entries with matching .name
        // (both qualified and unqualified entries in the map).
        arities.iter()
            .filter(|(k, _)| k.name == name.name)
            .map(|(_, &v)| v)
            .max()
    }
}

/// Uses `>=` matching: when args > params, extra args are applied to the expanded result.
/// The `type_con_arities` map prevents incorrect expansion when a name is both an alias
/// and a data type (due to module qualifier stripping): if arg count exceeds alias params
/// but fits the data type arity, the alias expansion is skipped.
fn expand_type_aliases_limited_with_arities(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_con_arities: &HashMap<QualifiedIdent, usize>,
    depth: u32,
) -> Type {
    let mut expanding = HashSet::new();
    expand_type_aliases_limited_inner(
        ty,
        type_aliases,
        Some(type_con_arities),
        depth,
        &mut expanding,
        None,
    )
}


fn type_contains_con_name(ty: &Type, name: &QualifiedIdent) -> bool {
    match ty {
        Type::Con(n) => n.name == name.name,
        Type::App(f, a) => type_contains_con_name(f, name) || type_contains_con_name(a, name),
        Type::Fun(a, b) => type_contains_con_name(a, name) || type_contains_con_name(b, name),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_contains_con_name(t, name))
                || tail.as_ref().map_or(false, |t| type_contains_con_name(t, name))
        }
        Type::Forall(_, body) => type_contains_con_name(body, name),
        _ => false,
    }
}

/// Check if a type contains Con(name) applied to exactly `expected_args` arguments.
/// Arity-aware version for self-referential alias detection at export time.
fn contains_self_referential_usage_in_type(ty: &Type, name: Symbol, expected_args: usize) -> bool {
    match ty {
        Type::Con(n) => n.name == name && expected_args == 0,
        Type::App(_, _) => {
            let mut head = ty;
            let mut args: Vec<&Type> = Vec::new();
            while let Type::App(f, a) = head {
                args.push(a.as_ref());
                head = f.as_ref();
            }
            if let Type::Con(n) = head {
                if n.name == name && args.len() == expected_args {
                    return true;
                }
            }
            contains_self_referential_usage_in_type(head, name, expected_args)
                || args.iter().any(|a| contains_self_referential_usage_in_type(a, name, expected_args))
        }
        Type::Fun(from, to) => {
            contains_self_referential_usage_in_type(from, name, expected_args)
                || contains_self_referential_usage_in_type(to, name, expected_args)
        }
        Type::Forall(_, body) => contains_self_referential_usage_in_type(body, name, expected_args),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| contains_self_referential_usage_in_type(t, name, expected_args))
                || tail.as_ref().map_or(false, |t| contains_self_referential_usage_in_type(t, name, expected_args))
        }
        _ => false,
    }
}

/// Check if a type alias body is a simple re-export: `type X a b = M.X a b`
/// where M is a qualified import alias and X matches the alias name.
fn is_alias_reexport(body: &Type, alias_name: Symbol, params: &[Symbol]) -> bool {
    let mut head = body;
    let mut app_args = Vec::new();
    while let Type::App(f, a) = head {
        app_args.push(a.as_ref());
        head = f.as_ref();
    }
    if let Type::Con(qi_name) = head {
        if qi_name.module.is_some() && qi_name.name == alias_name && app_args.len() == params.len() {
            // For zero-param aliases, body is just Con(M.X)
            if params.is_empty() {
                return true;
            }
            // For parameterized aliases, each arg must be a matching Var
            return app_args.iter().rev().zip(params.iter()).all(|(arg, param)| {
                matches!(arg, Type::Var(v) if *v == *param)
            });
        }
    }
    false
}

/// Inner expansion function.
/// When `type_con_arities` is `Some`, over-saturated aliases (args > params) are expanded
/// with extra args applied to the result, but expansion is skipped when the name also
/// exists as a data type with a matching arity (alias/data-type name collision).
/// When `None`, only exact arity matches (args == params) are expanded.
///
/// `con_zero_blockers`: optional set of alias names to block in the zero-arg Con path.
/// Used during export expansion to prevent wrong expansion of alias names that collide
/// with data types from different modules (e.g. `type GqlError = { ... }` alias vs
/// `data GqlError = ...`). Only blocks standalone `Con(X)` expansion, NOT `App(Con(X), ...)`
/// expansion, so over-saturated usage (like `POST url input output`) still works.
fn expand_type_aliases_limited_inner(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
    depth: u32,
    expanding: &mut HashSet<QualifiedIdent>,
    con_zero_blockers: Option<&HashSet<Symbol>>,
) -> Type {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    expand_type_aliases_limited_inner_impl(ty, type_aliases, type_con_arities, depth, expanding, con_zero_blockers)
    })
}

fn expand_type_aliases_limited_inner_impl(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_con_arities: Option<&HashMap<QualifiedIdent, usize>>,
    depth: u32,
    expanding: &mut HashSet<QualifiedIdent>,
    con_zero_blockers: Option<&HashSet<Symbol>>,
) -> Type {
    if depth > 200 || type_aliases.is_empty() {
        return ty.clone();
    }

    // For App types, collect the full spine first to determine the total arg count.
    // This prevents inner App nodes from being independently expanded as aliases
    // when they're part of a larger application (e.g., App(App(App(App(App(Con("Codec"),
    // ED), a), b), c), d) where Codec has a 1-param alias but is used here as a
    // 5-param data type).
    if let Type::App(_, _) = ty {
        let mut raw_args: Vec<&Type> = Vec::new();
        let mut head = ty;
        while let Type::App(f, a) = head {
            raw_args.push(a.as_ref());
            head = f.as_ref();
        }
        raw_args.reverse();

        if let Type::Con(name) = head {
            if !expanding.contains(name) {
                // When the type constructor has a module qualifier (e.g. Codec.Codec),
                // prefer the qualified form for alias lookup. If only the unqualified
                // name matches an alias but the qualified form doesn't exist, this might
                // be a data type that happens to share a name with an alias from a
                // different module (e.g. Data.Codec.Codec data type vs Data.Codec.JSON.Codec alias).
                let alias_entry = if let Some(module) = name.module {
                    let mod_str = crate::interner::resolve(module).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let qualified = crate::interner::intern(&format!("{}.{}", mod_str, name_str));
                    type_aliases.get(&qualified)
                } else {
                    type_aliases.get(&name.name)
                };
                if let Some((params, body)) = alias_entry {
                    let should_expand = if params.is_empty() {
                        // Zero-arg alias applied to args: expand head, re-apply args
                        true
                    } else if raw_args.len() == params.len() {
                        // Exactly saturated: always expand
                        true
                    } else if raw_args.len() > params.len() && type_con_arities.is_some() {
                        // Over-saturated: only expand when we have arities for disambiguation.
                        // Skip if name is also a data type and arg count fits the data type arity.
                        let arities = type_con_arities.unwrap();
                        !lookup_type_con_arity(arities, name)
                            .map_or(false, |arity| raw_args.len() <= arity)
                    } else {
                        false
                    };
                    if should_expand {
                        let expanded_args: Vec<Type> = raw_args
                            .iter()
                            .map(|a| {
                                expand_type_aliases_limited_inner(
                                    a,
                                    type_aliases,
                                    type_con_arities,
                                    depth + 1,
                                    expanding,
                                    con_zero_blockers,
                                )
                            })
                            .collect();
                        let n_sat = params.len();
                        if n_sat == 0 {
                            // Zero-arg alias: expand body, apply all args
                            expanding.insert(*name);
                            let expanded_head = expand_type_aliases_limited_inner(
                                body,
                                type_aliases,
                                type_con_arities,
                                depth + 1,
                                expanding,
                                con_zero_blockers,
                            );
                            expanding.remove(name);
                            let mut result = expanded_head;
                            for arg in expanded_args {
                                result = Type::app(result, arg);
                            }
                            return result;
                        }
                        // Saturated or over-saturated: substitute first n_sat args, apply extras
                        let (sat_args, extra_args) = expanded_args.split_at(n_sat);
                        let subst: HashMap<Symbol, Type> = params
                            .iter()
                            .copied()
                            .zip(sat_args.iter().cloned())
                            .collect();
                        let mut result = apply_var_subst(&subst, body);
                        for extra in extra_args {
                            result = Type::app(result, extra.clone());
                        }
                        // Only add to expanding set if the substituted result might
                        // reference this alias (self-referential). For aliases like
                        // RowApply (body = f a), after substitution the result won't
                        // contain RowApply, so blocking it prevents legitimate nested
                        // uses (e.g. OptionsRow body using RowApply again).
                        let is_self_ref = type_contains_con_name(&result, name);
                        if is_self_ref {
                            expanding.insert(*name);
                        }
                        let expanded = expand_type_aliases_limited_inner(
                            &result,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        );
                        if is_self_ref {
                            expanding.remove(name);
                        }
                        return expanded;
                    }
                }
            }
        }

        // Not an expandable alias — expand each arg independently.
        // For the head: if it's a bare Con, don't try to expand it (it's not saturated).
        // Otherwise (e.g., nested App, Fun, etc.), recurse into it.
        let expanded_args: Vec<Type> = raw_args
            .iter()
            .map(|a| {
                expand_type_aliases_limited_inner(
                    a,
                    type_aliases,
                    type_con_arities,
                    depth + 1,
                    expanding,
                    con_zero_blockers,
                )
            })
            .collect();
        let expanded_head = match head {
            Type::Con(_) => head.clone(),
            _ => expand_type_aliases_limited_inner(
                head,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            ),
        };
        let mut result = expanded_head;
        for arg in expanded_args {
            result = Type::app(result, arg);
        }
        return result;
    }

    match ty {
        Type::Fun(a, b) => Type::fun(
            expand_type_aliases_limited_inner(
                a,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            ),
            expand_type_aliases_limited_inner(
                b,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            ),
        ),
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| {
                    (
                        *l,
                        expand_type_aliases_limited_inner(
                            t,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        ),
                    )
                })
                .collect();
            let tail = tail.as_ref().map(|t| {
                Box::new(expand_type_aliases_limited_inner(
                    t,
                    type_aliases,
                    type_con_arities,
                    depth + 1,
                    expanding,
                    con_zero_blockers,
                ))
            });
            Type::Record(fields, tail)
        }
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(expand_type_aliases_limited_inner(
                body,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            )),
        ),
        Type::Con(name) => {
            // Zero-arg alias expansion
            // Use qualified lookup when a module qualifier is present (matching the App path),
            // so that e.g. Border.Evaluated and Style.Evaluated resolve to different aliases
            // instead of colliding on the unqualified "Evaluated" key.
            let (lookup_key, expand_key) = if let Some(module) = name.module {
                let mod_str = crate::interner::resolve(module).unwrap_or_default();
                let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                let qualified = crate::interner::intern(&format!("{}.{}", mod_str, name_str));
                (qualified, qualified_ident(&mod_str, &name_str))
            } else {
                (name.name, *name)
            };
            if !expanding.contains(&expand_key) {
                if let Some((params, body)) = type_aliases.get(&lookup_key) {
                    if params.is_empty() {
                        // Check zero-arg blockers: skip expansion if this alias name
                        // was marked as colliding with a data type at the call site.
                        if let Some(blockers) = con_zero_blockers {
                            if blockers.contains(&name.name) {
                                return ty.clone();
                            }
                        }
                        expanding.insert(expand_key);
                        let result = expand_type_aliases_limited_inner(
                            body,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        );
                        expanding.remove(&expand_key);
                        return result;
                    }
                }
                // Do NOT fall back to unqualified lookup when qualified not found.
                // Qualified aliases are always stored under their qualified keys during
                // import (e.g. Border.Evaluated, Tick.Easing). Falling back to unqualified
                // would incorrectly expand data type references (e.g. HATS.Easing) using
                // an alias from a different module with the same unqualified name.
                // Eta-reduce partially applied aliases (unqualified)
                if let Some((params, body)) = type_aliases.get(&lookup_key) {
                    if let Some(reduced) = eta_reduce_alias(params, body) {
                        expanding.insert(expand_key);
                        let result = expand_type_aliases_limited_inner(
                            &reduced,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        );
                        expanding.remove(&expand_key);
                        return result;
                    }
                }
            }
            ty.clone()
        }
        _ => ty.clone(),
    }
}

/// Check a type for partially applied type synonyms and over-applied type constructors,
/// using known type constructor arities.
fn check_type_for_partial_synonyms_with_arities(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_con_arities: &HashMap<QualifiedIdent, usize>,
    record_type_aliases: &HashSet<QualifiedIdent>,
    span: Span,
    errors: &mut Vec<TypeError>,
) {
    // Pre-expansion check: detect record-kind type aliases in row tails
    // before they get expanded away by expand_type_aliases_limited.
    check_record_alias_row_tails(ty, record_type_aliases, type_con_arities, span, errors);
    let expanded = expand_type_aliases_limited_with_arities(ty, type_aliases, type_con_arities, 0);
    check_partially_applied_synonyms_inner(
        &expanded,
        type_aliases,
        type_con_arities,
        record_type_aliases,
        span,
        errors,
        false,
    );
}

/// Pre-expansion check: walk a type and detect record-kind type aliases used
/// as row tails (e.g. `{ | Foo }` where `type Foo = { x :: Number }`).
/// This must happen before alias expansion because expansion replaces
/// `Type::Con("Foo")` with `Type::Record(...)` which is indistinguishable from valid rows.
fn check_record_alias_row_tails(
    ty: &Type,
    record_type_aliases: &HashSet<QualifiedIdent>,
    type_con_arities: &HashMap<QualifiedIdent, usize>,
    span: Span,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                check_record_alias_row_tails(
                    t,
                    record_type_aliases,
                    type_con_arities,
                    span,
                    errors,
                );
            }
            if let Some(t) = tail {
                if let Type::Con(name) = t.as_ref() {
                    if record_type_aliases.contains(name) {
                        errors.push(TypeError::KindsDoNotUnify {
                            span,
                            expected: Type::kind_row_of(Type::kind_type()),
                            found: Type::kind_type(),
                        });
                        return;
                    }
                }
                check_record_alias_row_tails(
                    t,
                    record_type_aliases,
                    type_con_arities,
                    span,
                    errors,
                );
            }
        }
        Type::Fun(a, b) => {
            check_record_alias_row_tails(a, record_type_aliases, type_con_arities, span, errors);
            check_record_alias_row_tails(b, record_type_aliases, type_con_arities, span, errors);
        }
        Type::App(f, a) => {
            check_record_alias_row_tails(f, record_type_aliases, type_con_arities, span, errors);
            check_record_alias_row_tails(a, record_type_aliases, type_con_arities, span, errors);
        }
        Type::Forall(_, body) => {
            check_record_alias_row_tails(body, record_type_aliases, type_con_arities, span, errors);
        }
        _ => {}
    }
}

/// Walk a (post-expansion) type looking for partially applied synonyms
/// and over-applied type constructors.
fn check_partially_applied_synonyms_inner(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_con_arities: &HashMap<QualifiedIdent, usize>,
    record_type_aliases: &HashSet<QualifiedIdent>,
    span: Span,
    errors: &mut Vec<TypeError>,
    is_arg: bool,
) {
    match ty {
        Type::App(_, _) => {
            // Collect the head and all arguments of this application chain
            let mut head = ty;
            let mut args: Vec<&Type> = Vec::new();
            while let Type::App(f, a) = head {
                args.push(a.as_ref());
                head = f.as_ref();
            }
            // Check if head is a partially or over-applied synonym
            if let Type::Con(name) = head {
                // When the name has a module qualifier, use the qualified alias key.
                // This prevents confusing a data type (e.g. Codec.Codec) with
                // an unrelated alias of the same unqualified name (e.g. CJ.Codec alias).
                let alias_entry = if let Some(module) = name.module {
                    let mod_str = crate::interner::resolve(module).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let qualified = crate::interner::intern(&format!("{}.{}", mod_str, name_str));
                    type_aliases.get(&qualified)
                } else {
                    type_aliases.get(&name.name)
                };
                if let Some((params, _)) = alias_entry {
                    if args.len() < params.len() {
                        // Before flagging as partially applied, check if the name also refers
                        // to a data type with a compatible arity. If so, the user is referencing
                        // the data type, not the alias (name collision between modules).
                        let is_data_type = lookup_type_con_arity(type_con_arities, name)
                            .map_or(false, |arity| args.len() <= arity);
                        if !is_data_type {
                            errors.push(TypeError::PartiallyAppliedSynonym { span, name: *name });
                            return;
                        }
                    } else if args.len() > params.len() {
                        // Over-saturation: the alias might expand to a type that takes more args.
                        // E.g., `type POST = Route "POST"` where Route is a 2-param data type.
                        // `POST "/path"` expands to `Route "POST" "/path"` which is valid.
                        // Only report KAM if we know this name is a data type with insufficient
                        // arity; otherwise assume the alias expansion will accommodate the args.
                        let arity_ok = lookup_type_con_arity(type_con_arities, name)
                            .map_or(true, |arity| args.len() <= arity);
                        if !arity_ok {
                            errors.push(TypeError::KindArityMismatch {
                                span,
                                name: *name,
                                expected: params.len(),
                                found: args.len(),
                            });
                            return;
                        }
                    }
                }
                // NOTE: Do NOT check over-applied non-alias type constructors here.
                // Foreign data types may have result kinds that are type aliases expanding
                // to function types (e.g., `UseEffect :: Type -> HookType` where
                // `type HookType = HookType' -> HookType'`), allowing more applications
                // than the declared arity suggests. The kind checker handles these cases.
            } else {
                check_partially_applied_synonyms_inner(
                    head,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    false,
                );
            }
            // Recurse into each argument — pass is_arg=true so bare synonyms
            // used as higher-kinded arguments (e.g. `Id` in `ReactAttributesF Id r`)
            // are not flagged as partially applied.
            for arg in args {
                check_partially_applied_synonyms_inner(
                    arg,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    true,
                );
            }
        }
        Type::Con(name) => {
            // When this Con appears as an argument to a type application, it may be
            // a higher-kinded type argument (e.g. `type Id a = a` passed as `f` in
            // `ReactAttributesF f r`). Don't flag these as partially applied.
            if is_arg {
                return;
            }
            // Use qualified lookup when the name has a module qualifier,
            // to avoid false positives (e.g. DOM.Node matching a different Node alias).
            let alias_entry = if let Some(module) = name.module {
                let mod_str = crate::interner::resolve(module).unwrap_or_default();
                let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                let qualified = crate::interner::intern(&format!("{}.{}", mod_str, name_str));
                type_aliases.get(&qualified)
            } else {
                type_aliases.get(&name.name)
            };
            if let Some((params, _)) = alias_entry {
                if !params.is_empty() {
                    // Check if the name also refers to a data type (any arity).
                    // Data types can be used bare (partially applied) for higher-kinded
                    // usage, so if the name resolves to a data type, skip the PAS check.
                    let is_data_type = lookup_type_con_arity(type_con_arities, name).is_some();
                    if !is_data_type {
                        errors.push(TypeError::PartiallyAppliedSynonym { span, name: *name });
                    }
                }
            }
        }
        Type::Fun(a, b) => {
            check_partially_applied_synonyms_inner(
                a,
                type_aliases,
                type_con_arities,
                record_type_aliases,
                span,
                errors,
                false,
            );
            check_partially_applied_synonyms_inner(
                b,
                type_aliases,
                type_con_arities,
                record_type_aliases,
                span,
                errors,
                false,
            );
        }
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                check_partially_applied_synonyms_inner(
                    t,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    false,
                );
            }
            if let Some(t) = tail {
                // Check if the row tail has kind Type instead of Row Type.
                // A row tail must have kind `Row Type`. Two cases are invalid:
                // 1. A data type with arity 0 (kind Type), e.g. `{ | Int }`
                // 2. A record-kind type alias (kind Type), e.g. `type Foo = { x :: Number }; { | Foo }`
                if let Type::Con(name) = t.as_ref() {
                    // Case 1: data type with arity 0 (kind Type, not Row)
                    if let Some(&arity) = type_con_arities.get(name) {
                        if arity == 0 {
                            errors.push(TypeError::KindsDoNotUnify {
                                span,
                                expected: Type::kind_row_of(Type::kind_type()),
                                found: Type::kind_type(),
                            });
                            return;
                        }
                    }
                    // Case 2: type alias declared with record syntax (kind Type)
                    if record_type_aliases.contains(name) {
                        errors.push(TypeError::KindsDoNotUnify {
                            span,
                            expected: Type::kind_row_of(Type::kind_type()),
                            found: Type::kind_type(),
                        });
                        return;
                    }
                }
                check_partially_applied_synonyms_inner(
                    t,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    false,
                );
            }
        }
        Type::Forall(_, body) => {
            check_partially_applied_synonyms_inner(
                body,
                type_aliases,
                type_con_arities,
                record_type_aliases,
                span,
                errors,
                false,
            );
        }
        _ => {}
    }
}

/// Detect cycles in type synonym definitions.
fn check_type_synonym_cycles(
    type_aliases: &HashMap<Symbol, (Span, &crate::ast::TypeExpr)>,
    errors: &mut Vec<TypeError>,
) {
    let alias_names: HashSet<Symbol> = type_aliases.keys().map(|k| *k).collect();

    // Build a Symbol-keyed span lookup for error reporting
    let alias_spans: HashMap<Symbol, Span> =
        type_aliases.iter().map(|(k, (s, _))| (*k, *s)).collect();

    // Build adjacency: alias → set of other aliases it references
    let mut deps: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for (name, (_, ty)) in type_aliases {
        let mut refs = HashSet::new();
        collect_type_refs(ty, &mut refs);
        // Only keep references to other aliases
        refs.retain(|r| alias_names.contains(r));
        deps.insert(*name, refs);
    }

    // DFS cycle detection
    let mut visited: HashSet<Symbol> = HashSet::new();
    let mut on_stack: HashSet<Symbol> = HashSet::new();

    for name in type_aliases.keys() {
        if !visited.contains(&name) {
            let mut path = Vec::new();
            if let Some(cycle) =
                dfs_find_cycle(*name, &deps, &mut visited, &mut on_stack, &mut path)
            {
                let span = alias_spans[&name];
                let cycle_spans: Vec<Span> = cycle
                    .iter()
                    .filter_map(|n| alias_spans.get(n).copied())
                    .collect();
                errors.push(TypeError::CycleInTypeSynonym {
                    name: name.clone(),
                    span,
                    names_in_cycle: cycle.clone(),
                    spans: cycle_spans,
                });
            }
        }
    }
}

fn dfs_find_cycle(
    node: Symbol,
    deps: &HashMap<Symbol, HashSet<Symbol>>,
    visited: &mut HashSet<Symbol>,
    on_stack: &mut HashSet<Symbol>,
    path: &mut Vec<Symbol>,
) -> Option<Vec<Symbol>> {
    visited.insert(node);
    on_stack.insert(node);
    path.push(node);

    if let Some(neighbors) = deps.get(&node) {
        for &neighbor in neighbors {
            if !visited.contains(&neighbor) {
                if let Some(cycle) = dfs_find_cycle(neighbor, deps, visited, on_stack, path) {
                    return Some(cycle);
                }
            } else if on_stack.contains(&neighbor) {
                // Found a cycle — extract the cycle from path
                let cycle_start = path.iter().position(|&n| n == neighbor).unwrap();
                return Some(path[cycle_start..].to_vec());
            }
        }
    }

    path.pop();
    on_stack.remove(&node);
    None
}

/// Detect cycles in type class superclass declarations.
/// E.g. `class Foo a <= Bar a` and `class Bar a <= Foo a` form a cycle.
fn check_type_class_cycles(
    class_defs: &HashMap<Symbol, (Span, Vec<Symbol>)>,
    errors: &mut Vec<TypeError>,
) {
    let class_names: HashSet<Symbol> = class_defs.keys().copied().collect();

    // Build adjacency: class → set of superclasses that are also defined locally
    let mut deps: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for (&name, (_, superclasses)) in class_defs {
        let refs: HashSet<Symbol> = superclasses
            .iter()
            .copied()
            .filter(|s| class_names.contains(s))
            .collect();
        deps.insert(name, refs);
    }

    // DFS cycle detection
    let mut visited: HashSet<Symbol> = HashSet::new();
    let mut on_stack: HashSet<Symbol> = HashSet::new();

    for &name in class_defs.keys() {
        if !visited.contains(&name) {
            let mut path = Vec::new();
            if let Some(cycle) = dfs_find_cycle(name, &deps, &mut visited, &mut on_stack, &mut path)
            {
                let (span, _) = class_defs[&name];
                let cycle_spans: Vec<Span> = cycle
                    .iter()
                    .filter_map(|n| class_defs.get(n).map(|(s, _)| *s))
                    .collect();
                errors.push(TypeError::CycleInTypeClassDeclaration {
                    name,
                    span,
                    names_in_cycle: cycle.clone(),
                    spans: cycle_spans,
                });
            }
        }
    }
}

fn collect_binder_vars(binder: &Binder, seen: &mut HashMap<Symbol, Vec<Span>>) {
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

/// Result of typechecking a module: partial type map + accumulated errors + exports.
pub struct CheckResult {
    pub types: HashMap<Symbol, Type>,
    pub errors: Vec<TypeError>,
    pub exports: ModuleExports,
    /// Span→Type map for local variable bindings, for hover support.
    pub span_types: HashMap<crate::span::Span, Type>,
    /// Record update field info: span of RecordUpdate → all field names in the record type.
    /// Used by codegen to generate object literal copies instead of for-in loops.
    pub record_update_fields: HashMap<crate::span::Span, Vec<Symbol>>,
}

// Build the exports for the built-in Prim module.
// Prim provides core types (Int, Number, String, Char, Boolean, Array, Function, Record)
// and is implicitly imported unqualified in every module.
static PRIM_EXPORTS: std::sync::LazyLock<ModuleExports> =
    std::sync::LazyLock::new(prim_exports_inner);

pub fn prim_exports() -> &'static ModuleExports {
    &PRIM_EXPORTS
}

fn prim_exports_inner() -> ModuleExports {
    let mut exports = ModuleExports::default();

    // Register Prim types as known types (empty constructor lists since they're opaque).
    // This makes them findable by the import system (import_item looks up data_constructors).
    // Exports use unqualified keys (like all module exports); import processing
    // adds qualification as needed.
    // Core value types
    for name in &[
        "Int", "Number", "String", "Char", "Boolean", "Array", "Function", "Record", "->",
    ] {
        exports.data_constructors.insert(unqualified_ident(name), Vec::new());
    }

    // Kind types: Type, Constraint, Symbol, Row
    for name in &["Type", "Constraint", "Symbol", "Row"] {
        exports.data_constructors.insert(unqualified_ident(name), Vec::new());
    }

    // Type constructor arities for Prim types
    exports.type_con_arities.insert(unqualified_ident("Int"), 0);
    exports.type_con_arities.insert(unqualified_ident("Number"), 0);
    exports.type_con_arities.insert(unqualified_ident("String"), 0);
    exports.type_con_arities.insert(unqualified_ident("Char"), 0);
    exports.type_con_arities.insert(unqualified_ident("Boolean"), 0);
    exports.type_con_arities.insert(unqualified_ident("Array"), 1);
    exports.type_con_arities.insert(unqualified_ident("Record"), 1);
    exports.type_con_arities.insert(unqualified_ident("Function"), 2);
    exports.type_con_arities.insert(unqualified_ident("Type"), 0);
    exports.type_con_arities.insert(unqualified_ident("Constraint"), 0);
    exports.type_con_arities.insert(unqualified_ident("Symbol"), 0);
    exports.type_con_arities.insert(unqualified_ident("Row"), 1);

    // class Partial
    exports.instances.insert(unqualified_ident("Partial"), Vec::new());
    exports.class_param_counts.insert(unqualified_ident("Partial"), 0);

    // class IsSymbol (sym :: Symbol) — compiler-solved class for type-level symbols
    exports.instances.insert(unqualified_ident("IsSymbol"), Vec::new());
    exports.class_param_counts.insert(unqualified_ident("IsSymbol"), 1);

    exports
}

/// Check if a CST ModuleName matches "Prim".
pub(super) fn is_prim_module(module_name: &crate::cst::ModuleName) -> bool {
    module_name.parts.len() == 1
        && crate::interner::symbol_eq(module_name.parts[0], "Prim")
}

/// Check if a CST ModuleName is a Prim submodule (e.g. Prim.Coerce, Prim.Row).
pub(super) fn is_prim_submodule(module_name: &crate::cst::ModuleName) -> bool {
    module_name.parts.len() >= 2
        && crate::interner::symbol_eq(module_name.parts[0], "Prim")
}

/// Build exports for Prim submodules (Prim.Coerce, Prim.Row, Prim.RowList, etc.).
/// These are built-in modules with compiler-magic classes and types.
pub fn prim_submodule_exports(module_name: &crate::cst::ModuleName) -> ModuleExports {
    let mut exports = ModuleExports::default();

    let sub = if module_name.parts.len() >= 2 {
        crate::interner::resolve(module_name.parts[1]).unwrap_or_default()
    } else {
        return exports;
    };

    // Exports use unqualified keys (like all module exports); import processing
    // adds qualification as needed.
    match sub.as_str() {
        "Boolean" => {
            // Type-level booleans: True, False
            exports.data_constructors.insert(unqualified_ident("True"), Vec::new());
            exports
                .data_constructors
                .insert(unqualified_ident("False"), Vec::new());
        }
        "Coerce" => {
            // class Coercible (no user-visible methods)
            exports.instances.insert(unqualified_ident("Coercible"), Vec::new());
            exports.class_param_counts.insert(unqualified_ident("Coercible"), 2);
            // Coercible :: forall k. k -> k -> Constraint
            use crate::typechecker::types::Type as CoerceType;
            let k_var = intern("k");
            let k = CoerceType::Var(k_var);
            let cc = CoerceType::kind_constraint();
            exports.class_type_kinds.insert(intern("Coercible"),
                CoerceType::Forall(vec![(k_var, false)], Box::new(
                    CoerceType::fun(k.clone(), CoerceType::fun(k, cc))
                )));
        }
        "Int" => {
            // Compiler-solved type classes for type-level Ints
            // class Add (3), class Compare (3), class Mul (3), class ToString (2)
            for class in &["Add", "Compare", "Mul"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
                exports.class_param_counts.insert(unqualified_ident(class), 3);
            }
            exports.instances.insert(unqualified_ident("ToString"), Vec::new());
            exports.class_param_counts.insert(unqualified_ident("ToString"), 2);
        }
        "Ordering" => {
            // type Ordering with constructors LT, EQ, GT
            exports.data_constructors.insert(
                unqualified_ident("Ordering"),
                vec![unqualified_ident("LT"), unqualified_ident("EQ"), unqualified_ident("GT")],
            );
            exports.data_constructors.insert(unqualified_ident("LT"), Vec::new());
            exports.data_constructors.insert(unqualified_ident("EQ"), Vec::new());
            exports.data_constructors.insert(unqualified_ident("GT"), Vec::new());
        }
        "Row" => {
            // classes: Lacks, Cons, Nub, Union
            for class in &["Lacks", "Cons", "Nub", "Union"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
            }
            exports.class_param_counts.insert(unqualified_ident("Lacks"), 2);
            exports.class_param_counts.insert(unqualified_ident("Cons"), 4);
            exports.class_param_counts.insert(unqualified_ident("Nub"), 2);
            exports.class_param_counts.insert(unqualified_ident("Union"), 3);

            // Export class kinds so they can be registered in class_kinds on import,
            // preventing collisions with data types of the same name.
            use crate::typechecker::types::Type;
            let _k_type = Type::kind_type();
            let k_constraint = Type::kind_constraint();
            let k_symbol = Type::kind_symbol();
            let k_var = intern("k");
            let k_row_k = Type::kind_row_of(Type::Var(k_var));

            // Union :: forall k. Row k -> Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Union"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), k_constraint.clone())))
                )));
            // Nub :: forall k. Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Nub"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), k_constraint.clone()))
                )));
            // Lacks :: forall k. Symbol -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Lacks"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_symbol, Type::fun(k_row_k.clone(), k_constraint.clone()))
                )));
            // Cons :: forall k. Symbol -> k -> Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Cons"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(Type::kind_symbol(), Type::fun(Type::Var(k_var),
                        Type::fun(k_row_k.clone(), Type::fun(k_row_k, k_constraint))))
                )));
        }
        "RowList" => {
            // type RowList with constructors Cons, Nil; class RowToList
            exports
                .data_constructors
                .insert(unqualified_ident("RowList"), vec![unqualified_ident("Cons"), unqualified_ident("Nil")]);
            exports.data_constructors.insert(unqualified_ident("Cons"), Vec::new());
            exports.data_constructors.insert(unqualified_ident("Nil"), Vec::new());
            exports.instances.insert(unqualified_ident("RowToList"), Vec::new());
            exports.class_param_counts.insert(unqualified_ident("RowToList"), 2);
        }
        "Symbol" => {
            // classes: Append, Compare, Cons
            for class in &["Append", "Compare", "Cons"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
            }
            exports.class_param_counts.insert(unqualified_ident("Append"), 3);
            exports.class_param_counts.insert(unqualified_ident("Compare"), 3);
            exports.class_param_counts.insert(unqualified_ident("Cons"), 3);
        }
        "TypeError" => {
            // classes: Fail, Warn; type constructors: Text, Beside, Above, Quote, QuoteLabel
            for class in &["Fail", "Warn"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
            }
            exports.class_param_counts.insert(unqualified_ident("Fail"), 1);
            exports.class_param_counts.insert(unqualified_ident("Warn"), 1);
            for ty in &["Doc", "Text", "Beside", "Above", "Quote", "QuoteLabel"] {
                exports.data_constructors.insert(unqualified_ident(ty), Vec::new());
            }
        }
        _ => {
            // Unknown Prim submodule — return empty exports
        }
    }

    exports
}

/// Strip a Forall wrapper from a type, keeping the body with rigid Type::Var intact.
/// Unlike `instantiate_forall_type` which replaces vars with fresh unification variables,
/// this preserves the type variables as rigid, for checking function bodies against
/// their declared signatures (skolemization).
fn strip_forall(ty: Type) -> Type {
    match ty {
        Type::Forall(_, body) => *body,
        other => other,
    }
}

/// Instantiate ALL type variables (Forall-bound and free Type::Var) with fresh unif vars,
/// and normalize `App(App(Function, a), b)` to `Fun(a, b)`.
/// Used for instance method expected types where both method-level forall vars and
/// instance-head type vars need to be flexible.
fn instantiate_all_vars(ctx: &mut InferCtx, ty: Type) -> Type {
    let function_sym = crate::interner::intern("Function");

    fn collect_vars(ty: &Type, vars: &mut HashSet<Symbol>) {
        match ty {
            Type::Var(v) => {
                vars.insert(*v);
            }
            Type::Fun(a, b) => {
                collect_vars(a, vars);
                collect_vars(b, vars);
            }
            Type::App(f, a) => {
                collect_vars(f, vars);
                collect_vars(a, vars);
            }
            Type::Forall(bound, body) => {
                let mut inner_vars = HashSet::new();
                collect_vars(body, &mut inner_vars);
                for v in &inner_vars {
                    if !bound.iter().any(|(b, _)| b == v) {
                        vars.insert(*v);
                    }
                }
            }
            Type::Record(fields, tail) => {
                for (_, t) in fields {
                    collect_vars(t, vars);
                }
                if let Some(t) = tail {
                    collect_vars(t, vars);
                }
            }
            _ => {}
        }
    }

    /// Normalize `App(App(Function, a), b)` → `Fun(a, b)` recursively.
    fn normalize_function(ty: Type, function_sym: Symbol) -> Type {
        match ty {
            Type::App(f, b) => {
                let f = normalize_function(*f, function_sym);
                let b = normalize_function(*b, function_sym);
                // Check for App(App(Function, a), b)
                if let Type::App(ff, a) = &f {
                    if let Type::Con(name) = ff.as_ref() {
                        if name.name == function_sym {
                            return Type::fun(a.as_ref().clone(), b);
                        }
                    }
                }
                Type::app(f, b)
            }
            Type::Fun(a, b) => Type::fun(
                normalize_function(*a, function_sym),
                normalize_function(*b, function_sym),
            ),
            Type::Forall(vars, body) => {
                Type::Forall(vars, Box::new(normalize_function(*body, function_sym)))
            }
            Type::Record(fields, tail) => {
                let fields = fields
                    .into_iter()
                    .map(|(l, t)| (l, normalize_function(t, function_sym)))
                    .collect();
                let tail = tail.map(|t| Box::new(normalize_function(*t, function_sym)));
                Type::Record(fields, tail)
            }
            other => other,
        }
    }

    // Instantiate forall first
    let ty = match ty {
        Type::Forall(vars, body) => {
            let subst: HashMap<Symbol, Type> = vars
                .iter()
                .map(|&(v, _)| (v, Type::Unif(ctx.state.fresh_var())))
                .collect();
            apply_var_subst(&subst, &body)
        }
        other => other,
    };

    // Normalize Function type constructor to Fun
    let ty = normalize_function(ty, function_sym);

    // Replace remaining free Type::Var with fresh unif vars
    let mut free_vars = HashSet::new();
    collect_vars(&ty, &mut free_vars);
    if free_vars.is_empty() {
        ty
    } else {
        let subst: HashMap<Symbol, Type> = free_vars
            .into_iter()
            .map(|v| (v, Type::Unif(ctx.state.fresh_var())))
            .collect();
        apply_var_subst(&subst, &ty)
    }
}

/// Extract the head type constructor name from a CST TypeExpr,
/// peeling through type applications and parentheses.
/// E.g. `Maybe Int` → Some("Maybe"), `(Foo a b)` → Some("Foo")
fn extract_head_constructor(ty: &crate::ast::TypeExpr) -> Option<QualifiedIdent> {
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
fn collect_expr_refs(expr: &crate::ast::Expr, top: &HashSet<Symbol>, refs: &mut HashSet<Symbol>) {
    use crate::ast::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => {
            if top.contains(&name.name) {
                refs.insert(name.name);
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
fn collect_guarded_refs(
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
fn collect_decl_refs(decls: &[&Decl], top: &HashSet<Symbol>) -> HashSet<Symbol> {
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
pub fn tarjan_scc(nodes: &[Symbol], edges: &HashMap<Symbol, HashSet<Symbol>>) -> Vec<Vec<Symbol>> {
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

/// Typecheck an entire module, returning a map of top-level names to their types
/// and a list of any errors encountered. Checking continues past errors so that
/// partial results are available for tooling (e.g. IDE hover types).
pub fn check_module(module: &Module, registry: &ModuleRegistry) -> CheckResult {
    check_module_impl(module, registry, false)
}

pub fn check_module_for_ide(module: &Module, registry: &ModuleRegistry) -> CheckResult {
    check_module_impl(module, registry, true)
}

fn check_module_impl(module: &Module, registry: &ModuleRegistry, collect_span_types: bool) -> CheckResult {
    let mut ctx = InferCtx::new();
    ctx.module_mode = true;
    ctx.collect_span_types = collect_span_types;
    let mut env = Env::new();
    let mut signatures: HashMap<Symbol, (crate::span::Span, Type)> = HashMap::new();
    let mut result_types: HashMap<Symbol, Type> = HashMap::new();
    let mut errors: Vec<TypeError> = Vec::new();
    // Classes that appear in explicit type signature constraints (not inferred).
    // Used to distinguish legitimate "given" constraints from inferred body constraints
    // for chain ambiguity checking in Pass 3.
    let mut explicit_sig_classes: HashSet<Symbol> = HashSet::new();

    // Track class info for instance checking
    // Each instance stores (type_args, constraints) where constraints are (class_name, constraint_type_args)
    let mut instances: HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>> =
        HashMap::new();

    // Track locally-defined instance heads for overlap checking
    // Stores (converted types, had_kind_annotations, CST types) for each instance
    let mut local_instance_heads: HashMap<
        Symbol,
        Vec<(Vec<Type>, bool, Vec<crate::ast::TypeExpr>)>,
    > = HashMap::new();

    // Track classes that have instance chains (else keyword).
    // Used during deferred constraint checking to detect ambiguous chain resolution.
    let mut chained_classes: HashSet<QualifiedIdent> = HashSet::new();

    // Track locally-defined names for export computation
    let mut local_values: HashMap<Symbol, Scheme> = HashMap::new();

    // Track names with Partial constraint (intentionally non-exhaustive)
    let mut partial_names: HashSet<Symbol> = HashSet::new();

    // Track class declaration spans for duplicate detection
    let mut seen_classes: HashMap<Symbol, Vec<Span>> = HashMap::new();

    // Track named instance spans for duplicate detection
    let mut seen_instance_names: HashMap<Symbol, Vec<Span>> = HashMap::new();

    // newtype_names is now on ctx.newtype_names (shared via ModuleExports for Coercible)

    // Track type alias definitions for cycle detection
    let mut type_alias_defs: HashMap<Symbol, (Span, &crate::ast::TypeExpr)> = HashMap::new();

    // Track class definitions for superclass cycle detection: name → (span, superclass class names)
    let mut class_defs: HashMap<Symbol, (Span, Vec<Symbol>)> = HashMap::new();

    // Track superclass constraints per class for instance validation:
    // class name → (class type var names, superclass constraints as (class_name, type_args))
    let mut class_superclasses: HashMap<QualifiedIdent, (Vec<Symbol>, Vec<(QualifiedIdent, Vec<Type>)>)> = HashMap::new();

    // Track class type parameter counts for instance arity validation.
    let mut class_param_counts: HashMap<QualifiedIdent, usize> = HashMap::new();

    // Track kind signatures for orphan detection: name → span
    let mut kind_sigs: HashMap<Symbol, (Span, KindSigSource)> = HashMap::new();
    // Track names that have real definitions, categorized by declaration kind
    let mut has_real_definition: HashSet<Symbol> = HashSet::new();
    // More specific tracking: which kind of definition exists (for source-aware orphan check)
    let mut has_data_def: HashSet<Symbol> = HashSet::new();
    let mut has_type_alias_def: HashSet<Symbol> = HashSet::new();
    let mut has_newtype_def: HashSet<Symbol> = HashSet::new();
    let mut has_class_def: HashSet<Symbol> = HashSet::new();

    // Pre-scan: Collect locally-defined type and class names for orphan instance detection.
    // An instance is orphan if neither the class nor any type in the instance head is locally defined.
    let local_type_names: HashSet<Symbol> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Data { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::TypeAlias { name, .. }
            | Decl::ForeignData { name, .. } => Some(name.value),
            _ => None,
        })
        .collect();
    // Data/newtype names only (excludes type aliases) — used for orphan instance checks
    // where type aliases should be treated as transparent (expanded to their underlying type).
    let local_data_type_names: HashSet<Symbol> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Data { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::ForeignData { name, .. } => Some(name.value),
            _ => None,
        })
        .collect();
    // Concrete locally-defined data/newtype names only — excludes foreign data types.
    // Used in derive position checking to allow locally-defined types that haven't
    // been processed yet in Pass 1 declaration order to be treated as covariant.
    // Foreign data types are excluded because they're abstract and have unknown variance.
    let local_concrete_type_names: HashSet<Symbol> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Data { name, .. } | Decl::Newtype { name, .. } => Some(name.value),
            _ => None,
        })
        .collect();
    let local_class_names: HashSet<Symbol> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Class {
                name, is_kind_sig, ..
            } if !*is_kind_sig => Some(name.value),
            _ => None,
        })
        .collect();

    // Track locally-registered instances for superclass validation: (span, class_name, inst_types)
    let mut registered_instances: Vec<(Span, Symbol, Vec<Type>)> = Vec::new();
    /// Instance registry: (class_name, head_type_con) → instance_name.
    /// Populated during instance processing for codegen dictionary resolution.
    let mut instance_registry_entries: HashMap<(Symbol, Symbol), Symbol> = HashMap::new();
    let mut instance_module_entries: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    // Kind annotations for instance type variables (for polykinded dispatch).
    let mut instance_var_kinds_entries: HashMap<Symbol, HashMap<Symbol, Symbol>> = HashMap::new();

    // Deferred instance method bodies: checked after Pass 1.5 so foreign imports and fixity are available.
    // Tuple: (method_name, span, binders, guarded, where_clause, expected_type, scoped_vars, given_classes, instance_id, instance_constraints)
    let mut deferred_instance_methods: Vec<(
        Symbol,
        Span,
        &[Binder],
        &crate::ast::GuardedExpr,
        &[crate::ast::LetBinding],
        Option<Type>,
        HashSet<Symbol>,
        HashSet<QualifiedIdent>,
        usize, // instance_id: groups methods from the same instance
        Vec<(QualifiedIdent, Vec<Type>)>, // instance constraints (class_name, type_args)
    )> = Vec::new();
    let mut next_instance_id: usize = 0;
    // Instance method groups: each entry is the list of method names for one instance.
    // Used for CycleInDeclaration detection among sibling methods.
    let mut instance_method_groups: Vec<Vec<Symbol>> = Vec::new();

    // Import Prim unqualified. Prim is implicitly available in all modules,
    // BUT if the module has an explicit `import Prim (...)` or `import Prim hiding (...)`,
    // skip the automatic full import and let process_imports handle the selective import.
    let has_explicit_prim_import = module
        .imports
        .iter()
        .any(|imp| is_prim_module(&imp.module) && imp.imports.is_some() && imp.qualified.is_none());
    if !has_explicit_prim_import {
        let prim = prim_exports();
        import_all(None, prim, &mut env, &mut ctx, None, &HashSet::new(), &HashSet::new(), &HashSet::new());
        // Also register Prim type_con_arities with "Prim." qualifier so explicit
        // Prim.Array, Prim.Int etc. references work in source code.
        let prim_sym = intern("Prim");
        for name in prim.type_con_arities.keys() {
            ctx.type_con_arities.insert(QualifiedIdent { module: Some(prim_sym), name: name.name }, *prim.type_con_arities.get(name).unwrap());
        }
        // Import Prim instances (instances now handled centrally, not in import_all)
        for (class_name, insts) in &prim.instances {
            instances
                .entry(*class_name)
                .or_default()
                .extend(insts.iter().cloned());
        }
        // Also register Prim's class_param_counts so Partial etc. are known classes
        for (class_name, count) in &prim.class_param_counts {
            class_param_counts.entry(*class_name).or_insert(*count);
            ctx.prim_class_names.insert(class_name.name);
        }
    }

    // Process imports: bring imported names into scope
    let explicitly_imported_types = process_imports(
        module,
        registry,
        &mut env,
        &mut ctx,
        &mut instances,
        &mut errors,
    );

    // Build canonical → import-alias mapping for the unifier.
    // This allows try_expand_alias to resolve canonical qualified types
    // (e.g. Components.AskForReview.Model) back to import-alias keys
    // (e.g. AskForReview.Model) for alias lookup.
    for import_decl in &module.imports {
        if let Some(ref alias) = import_decl.qualified {
            let canonical = module_name_to_symbol(&import_decl.module);
            let alias_sym = module_name_to_symbol(alias);
            ctx.state.canonical_to_qualifier.insert(canonical, alias_sym);
            // Also register qualifier → qualifier (self-mapping) so try_expand_alias
            // recognizes the import alias as a known module when defined_types
            // canonicalization uses the qualifier (e.g. Con("Card.Action")).
            ctx.state.canonical_to_qualifier.entry(alias_sym)
                .or_insert(alias_sym);
        }
    }

    // Pre-populate class param counts from imported class methods and class definitions.
    for (_method, (class_name, tvs)) in &ctx.class_methods {
        class_param_counts
            .entry(*class_name)
            .or_insert(tvs.len());
    }
    // Also populate from explicitly exported class_param_counts (catches classes without methods)
    for import_decl in &module.imports {
        let prim_sub;
        let module_exports = if is_prim_module(&import_decl.module) {
            Some(prim_exports())
        } else if is_prim_submodule(&import_decl.module) {
            prim_sub = prim_submodule_exports(&import_decl.module);
            Some(&prim_sub)
        } else {
            registry.lookup(&import_decl.module.parts)
        };
        let is_prim_source = is_prim_module(&import_decl.module) || is_prim_submodule(&import_decl.module);
        if let Some(exports) = module_exports {
            for (class_name, count) in &exports.class_param_counts {
                match class_param_counts.entry(*class_name) {
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert(*count);
                    }
                    std::collections::hash_map::Entry::Occupied(e) => {
                        // If same name has different arity from another module,
                        // mark as ambiguous by using usize::MAX (won't match any real arity)
                        if *e.get() != *count {
                            *e.into_mut() = usize::MAX;
                        }
                    }
                }
                if is_prim_source {
                    ctx.prim_class_names.insert(class_name.name);
                } else {
                    // Also track compiler-solved classes re-exported from non-Prim modules.
                    // These class names match the magic solver in check_instance_depth and
                    // must be recognized regardless of import source.
                    let class_str = crate::interner::resolve(class_name.name).unwrap_or_default();
                    let is_compiler_solved = matches!(
                        class_str.as_str(),
                        "IsSymbol" | "Reflectable" | "Reifiable"
                        | "Partial" | "Warn" | "Fail"
                        | "Coercible"
                        | "Lacks" | "Cons" | "Nub" | "Union" | "RowToList"
                        | "CompareSymbol" | "Append" | "Compare"
                        | "Add" | "Mul" | "ToString"
                    );
                    if is_compiler_solved {
                        ctx.prim_class_names.insert(class_name.name);
                    }
                }
            }
            for (class_name, fd) in &exports.class_fundeps {
                ctx.class_fundeps
                    .entry(qi(*class_name))
                    .or_insert_with(|| fd.clone());
            }
            // Import superclass constraints for transitively expanding "given" constraints
            for (class_name, sc_info) in &exports.class_superclasses {
                class_superclasses.entry(*class_name).or_insert_with(|| sc_info.clone());
            }
        }
    }

    // Pre-scan: Register all locally declared type names for type_con_arities
    // before any type expressions are converted. This mirrors PureScript's
    // non-order-dependent module scoping for types.
    for decl in &module.decls {
        match decl {
            Decl::Data {
                name,
                type_vars,
                kind_sig,
                ..
            } => {
                // Only set arity for real data declarations, not standalone kind signatures
                // (e.g. `type Id :: forall k. k -> k` is parsed as Data with type_vars=[])
                if *kind_sig == crate::cst::KindSigSource::None {
                    ctx.type_con_arities.insert(qi(name.value), type_vars.len());
                }
            }
            Decl::Newtype {
                name, type_vars, ..
            } => {
                ctx.type_con_arities.insert(qi(name.value), type_vars.len());
            }
            Decl::ForeignData { name, kind, .. } => {
                // Compute arity from kind annotation by counting arrows.
                // e.g. `foreign import data Stream :: Row Effect -> Type` has arity 1.
                fn count_kind_arrows(te: &TypeExpr) -> usize {
                    match te {
                        TypeExpr::Function { to, .. } => 1 + count_kind_arrows(to),
                        TypeExpr::Forall { ty, .. } => count_kind_arrows(ty),
                        _ => 0,
                    }
                }
                ctx.type_con_arities.insert(qi(name.value), count_kind_arrows(kind));
            }
            Decl::TypeAlias { name, .. } => {
                // Local type aliases shadow imported types, just like data/newtype declarations.
                // A ScopeConflict is only raised if the ambiguous name is actually referenced
                // (not merely declared or exported). Record the conflict for deferred checking.
                if explicitly_imported_types.contains(&name.value) {
                    ctx.type_scope_conflicts.insert(name.value);
                }
            }
            _ => {}
        }
    }

    // Pre-scan: Detect declaration conflicts (type vs type, type vs class, ctor vs ctor, etc.)
    {
        // Track which names are declared as types, constructors, or classes
        // Each entry stores (kind_label, span) for the first occurrence
        let mut declared_types: HashMap<Symbol, (&str, Span)> = HashMap::new();
        let mut declared_ctors: HashMap<Symbol, (&str, Span)> = HashMap::new();
        let mut declared_classes: HashMap<Symbol, (&str, Span)> = HashMap::new();

        for decl in &module.decls {
            match decl {
                Decl::Data {
                    span,
                    name,
                    constructors,
                    kind_sig,
                    is_role_decl,
                    ..
                } => {
                    // Kind signatures and role declarations don't count as type declarations
                    if *kind_sig == KindSigSource::None && !*is_role_decl {
                        // Check type name conflicts
                        if let Some((existing_kind, _)) = declared_types.get(&name.value) {
                            errors.push(TypeError::DeclConflict {
                                span: *span,
                                name: name.value,
                                new_kind: "type",
                                existing_kind,
                            });
                        } else if let Some((existing_kind, _)) = declared_classes.get(&name.value) {
                            errors.push(TypeError::DeclConflict {
                                span: *span,
                                name: name.value,
                                new_kind: "type",
                                existing_kind,
                            });
                        } else {
                            declared_types.insert(name.value, ("type", *span));
                        }

                        // Check data constructors
                        for ctor in constructors {
                            if let Some((existing_kind, _)) = declared_ctors.get(&ctor.name.value) {
                                errors.push(TypeError::DeclConflict {
                                    span: ctor.span,
                                    name: ctor.name.value,
                                    new_kind: "data constructor",
                                    existing_kind,
                                });
                            } else if let Some((existing_kind, _)) =
                                declared_classes.get(&ctor.name.value)
                            {
                                errors.push(TypeError::DeclConflict {
                                    span: ctor.span,
                                    name: ctor.name.value,
                                    new_kind: "data constructor",
                                    existing_kind,
                                });
                            } else {
                                declared_ctors
                                    .insert(ctor.name.value, ("data constructor", ctor.span));
                            }
                        }
                    }
                }
                Decl::Newtype {
                    span,
                    name,
                    constructor,
                    ..
                } => {
                    // Check type name
                    if let Some((existing_kind, _)) = declared_types.get(&name.value) {
                        errors.push(TypeError::DeclConflict {
                            span: *span,
                            name: name.value,
                            new_kind: "type",
                            existing_kind,
                        });
                    } else if let Some((existing_kind, _)) = declared_classes.get(&name.value) {
                        errors.push(TypeError::DeclConflict {
                            span: *span,
                            name: name.value,
                            new_kind: "type",
                            existing_kind,
                        });
                    } else {
                        declared_types.insert(name.value, ("type", *span));
                    }

                    // Check constructor
                    if let Some((existing_kind, _)) = declared_ctors.get(&constructor.value) {
                        errors.push(TypeError::DeclConflict {
                            span: *span,
                            name: constructor.value,
                            new_kind: "data constructor",
                            existing_kind,
                        });
                    } else if let Some((existing_kind, _)) =
                        declared_classes.get(&constructor.value)
                    {
                        errors.push(TypeError::DeclConflict {
                            span: *span,
                            name: constructor.value,
                            new_kind: "data constructor",
                            existing_kind,
                        });
                    } else {
                        declared_ctors.insert(constructor.value, ("data constructor", *span));
                    }
                }
                Decl::TypeAlias { span, name, .. } | Decl::ForeignData { span, name, .. } => {
                    if let Some((existing_kind, _)) = declared_types.get(&name.value) {
                        errors.push(TypeError::DeclConflict {
                            span: *span,
                            name: name.value,
                            new_kind: "type",
                            existing_kind,
                        });
                    } else if let Some((existing_kind, _)) = declared_classes.get(&name.value) {
                        errors.push(TypeError::DeclConflict {
                            span: *span,
                            name: name.value,
                            new_kind: "type",
                            existing_kind,
                        });
                    } else {
                        declared_types.insert(name.value, ("type", *span));
                    }
                }
                Decl::Class {
                    span,
                    name,
                    is_kind_sig,
                    ..
                } => {
                    if !*is_kind_sig {
                        if let Some((existing_kind, _)) = declared_classes.get(&name.value) {
                            // DuplicateTypeClass is handled separately — skip here
                            let _ = existing_kind;
                        } else if let Some((existing_kind, _)) = declared_types.get(&name.value) {
                            errors.push(TypeError::DeclConflict {
                                span: *span,
                                name: name.value,
                                new_kind: "type class",
                                existing_kind,
                            });
                        } else if let Some((existing_kind, _)) = declared_ctors.get(&name.value) {
                            errors.push(TypeError::DeclConflict {
                                span: *span,
                                name: name.value,
                                new_kind: "type class",
                                existing_kind,
                            });
                        } else {
                            declared_classes.insert(name.value, ("type class", *span));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    let _module_start = std::time::Instant::now();
    // Pass 0: Collect fixity declarations and check for duplicates.
    let mut seen_value_ops: HashMap<Symbol, Vec<crate::span::Span>> = HashMap::new();
    let mut seen_type_ops: HashMap<Symbol, Vec<crate::span::Span>> = HashMap::new();
    let mut type_fixities: HashMap<Symbol, (Associativity, u8)> = HashMap::new();
    for decl in &module.decls {
        if let Decl::Fixity {
            span,
            associativity,
            precedence,
            target,
            operator,
            is_type,
            ..
        } = decl
        {
            if *is_type {
                seen_type_ops.entry(operator.value).or_default().push(*span);
                ctx.type_operators.insert(qi(operator.value), *target);
                type_fixities.insert(operator.value, (*associativity, *precedence));
            } else {
                seen_value_ops
                    .entry(operator.value)
                    .or_default()
                    .push(*span);
                ctx.value_fixities
                    .insert(operator.value, (*associativity, *precedence));
            }
        }
    }
    for (name, spans) in &seen_value_ops {
        if spans.len() > 1 {
            errors.push(TypeError::MultipleValueOpFixities {
                spans: spans.clone(),
                name: *name,
            });
        }
    }
    for (name, spans) in &seen_type_ops {
        if spans.len() > 1 {
            errors.push(TypeError::MultipleTypeOpFixities {
                spans: spans.clone(),
                name: *name,
            });
        }
    }

    // Clone so we don't hold an immutable borrow on ctx across mutable uses.
    let type_ops = ctx.type_operators.clone();
    // Symbol-keyed version for kind:: functions which still use Symbol maps

    // Build set of known class names for constraint validation (from all sources).
    // Note: we do NOT include instances.keys() here because instances propagate
    // transitively (they're globally visible in PureScript), but the class NAME
    // should only be in scope if it's actually imported. E.g. Prim.Row.Cons
    // instances leak through the registry, but using `Cons` in a constraint
    // requires `import Prim.Row (class Cons)`.
    let mut known_classes: HashSet<QualifiedIdent> = class_param_counts.keys().copied().collect();
    for (_, (class_name, _)) in &ctx.class_methods {
        known_classes.insert(*class_name);
    }
    for name in &local_class_names {
        known_classes.insert(qi(*name));
    }

    // ===== Kind Pass: Infer and check kinds for all type declarations =====
    let saved_type_kinds: HashMap<QualifiedIdent, Type>;
    let saved_class_kinds: HashMap<QualifiedIdent, Type>;
    {
        use crate::typechecker::kind::{self, KindState};

        let mut ks = KindState::new();

        // Build mapping from import qualifier aliases to canonical (full) module names.
        // This is used to canonicalize kind constructor qualifiers so that the same type
        // imported via different aliases (e.g. `import M as K` and `import M as Subject`)
        // produces identical kind representations.
        for import_decl in &module.imports {
            if let Some(q) = &import_decl.qualified {
                let alias = module_name_to_symbol(q);
                let canonical = module_name_to_symbol(&import_decl.module);
                ks.qualifier_to_canonical.insert(alias, canonical);
            }
        }
        // Sync to the kind UnifyState so module qualifier resolution works during kind unification.
        ks.state.qualifier_to_canonical = ks.qualifier_to_canonical.clone();

        // Register imported type kinds for cross-module kind checking.
        // Both qualified and unqualified imports are registered so that the kind
        // checker can determine kinds from imported type constructors (e.g.,
        // SlotStorage's kind annotation constraining `slot :: (Type -> Type) -> Type -> Type`).
        // Qualified imports are additionally registered under their qualified name
        // for disambiguation (e.g., LibA.DemoKind ≠ LibB.DemoKind).
        for import_decl in &module.imports {
            let qualifier = import_decl.qualified.as_ref().map(|q| module_name_to_symbol(q));

            let prim_sub;
            let module_exports = if is_prim_module(&import_decl.module) {
                continue; // Prim types are already registered as builtins
            } else if is_prim_submodule(&import_decl.module) {
                prim_sub = prim_submodule_exports(&import_decl.module);
                &prim_sub
            } else {
                match registry.lookup(&import_decl.module.parts) {
                    Some(exports) => exports,
                    None => continue,
                }
            };

            let exported_type_names: HashSet<Symbol> =
                module_exports.type_kinds.keys().copied().collect();

            // Compute which type names are actually imported (respecting explicit lists).
            // For `import M (Foo, Bar)`, only register kinds for Foo and Bar.
            // For `import M` or `import M hiding (...)`, register all (or filtered).
            let allowed_type_names: Option<HashSet<Symbol>> = match &import_decl.imports {
                Some(crate::cst::ImportList::Explicit(items)) => {
                    let names: HashSet<Symbol> = items.iter().filter_map(|item| match item {
                        crate::cst::Import::Type(name, _) => Some(name.value),
                        crate::cst::Import::Class(name) => Some(name.value),
                        _ => None,
                    }).collect();
                    Some(names)
                }
                Some(crate::cst::ImportList::Hiding(items)) => {
                    let hidden: HashSet<Symbol> = items.iter().filter_map(|item| match item {
                        crate::cst::Import::Type(name, _) => Some(name.value),
                        crate::cst::Import::Class(name) => Some(name.value),
                        _ => None,
                    }).collect();
                    let names: HashSet<Symbol> = exported_type_names.iter()
                        .filter(|n| !hidden.contains(n))
                        .copied()
                        .collect();
                    Some(names)
                }
                None => None, // import everything
            };

            for (&type_name, kind) in &module_exports.type_kinds {
                // Skip types not in the explicit import list
                if let Some(ref allowed) = allowed_type_names {
                    if !allowed.contains(&type_name) {
                        continue;
                    }
                }

                if let Some(q) = qualifier {
                    // Qualify Con references in the kind to use the import qualifier
                    let qualified_kind = qualify_kind_refs(kind, q, &exported_type_names);
                    let qualified_name = qualified_symbol(q, type_name);
                    ks.register_type(qualified_name, qualified_kind);
                } else {
                    // Register under the bare name only for unqualified imports.
                    ks.register_type(type_name, kind.clone());
                }
            }
            // Import class kinds separately so they don't get overwritten by
            // data types with the same name (e.g., class Error vs data Error).
            for (&type_name, kind) in &module_exports.class_type_kinds {
                if let Some(ref allowed) = allowed_type_names {
                    if !allowed.contains(&type_name) {
                        continue;
                    }
                }
                if let Some(q) = qualifier {
                    let qualified_kind = qualify_kind_refs(kind, q, &exported_type_names);
                    let qualified_name = qualified_symbol(q, type_name);
                    ks.class_kinds.insert(qualified_name, qualified_kind);
                } else {
                    ks.class_kinds.insert(type_name, kind.clone());
                }
            }
            // Also register type alias kinds under qualified names so that
            // qualified references (e.g. CJ.Codec) find the alias's kind
            // rather than falling back to a data type with the same unqualified name
            // but different arity (e.g. Data.Codec's 5-param `data Codec`).
            // Register type alias kinds so the kind checker knows their arities.
            // For qualified imports, register under the qualified name;
            // for unqualified imports, register under the bare name.
            for (alias_name, (params, _body)) in &module_exports.type_aliases {
                // Skip aliases not in the explicit import list
                if let Some(ref allowed) = allowed_type_names {
                    if !allowed.contains(&alias_name.name) {
                        continue;
                    }
                }
                let reg_name = if let Some(q) = qualifier {
                    qualified_symbol(q, alias_name.name)
                } else {
                    alias_name.name
                };
                // Don't overwrite if already registered from type_kinds
                if ks.type_kinds.get(&reg_name).is_none() {
                    // Build kind: ?k1 -> ?k2 -> ... -> ?kN -> ?k_result
                    let mut kind = ks.fresh_kind_var();
                    for _ in 0..params.len() {
                        kind = Type::fun(ks.fresh_kind_var(), kind);
                    }
                    ks.register_type(reg_name, kind);
                }
            }
        }

        // Register foreign data types with their kind expressions
        for decl in &module.decls {
            if let Decl::ForeignData { name, kind, .. } = decl {
                // Check for unsupported constructs in kind (e.g., constraints)
                if let Err(e) = kind::check_kind_expr_supported(kind) {
                    errors.push(e);
                    continue;
                }
                // Check for visible dependent quantification (e.g., forall (k :: Type) (t :: k). ...)
                if let Some(e) = kind::check_visible_dependent_quantification(kind) {
                    errors.push(e);
                }
                let k = ks.convert_kind_expr_canonical(kind);
                ks.register_type(name.value, k);
            }
        }

        // Register type aliases in the kind-level UnifyState so that type synonyms
        // used in kind annotations (e.g., `data P (a :: Id Type)`) are expanded during
        // kind unification. Also register already-known type aliases from imports.
        for (&alias_name, (params, body)) in &ctx.state.type_aliases {
            ks.state
                .type_aliases
                .insert(alias_name, (params.clone(), body.clone()));
        }
        for decl in &module.decls {
            if let Decl::TypeAlias {
                name,
                type_vars,
                ty,
                ..
            } = decl
            {
                let var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                if let Ok(body) = convert_type_expr(ty, &type_ops) {
                    ks.state.type_aliases.insert(name.value, (var_syms, body));
                }
            }
        }

        // Collect standalone kind signatures: name → kind Type
        let mut standalone_kinds: HashMap<Symbol, Type> = HashMap::new();
        for decl in &module.decls {
            if let Decl::Data {
                name,
                kind_sig,
                kind_type: Some(kind_ty),
                ..
            } = decl
            {
                if *kind_sig != KindSigSource::None {
                    // Check for quantification failures in the standalone kind sig
                    if let Some(e) =
                        kind::check_standalone_kind_quantification(&mut ks, kind_ty, &type_ops)
                    {
                        errors.push(e);
                    }
                    let k = ks.convert_kind_expr_canonical(kind_ty);
                    standalone_kinds.insert(name.value, k.clone());
                    // Pre-register so other declarations can reference this type's kind
                    ks.register_type(name.value, k);
                }
            }
            if let Decl::Class {
                is_kind_sig: true,
                name,
                kind_type: Some(kind_ty),
                ..
            } = decl
            {
                // Check for quantification failures in the standalone kind sig
                if let Some(e) =
                    kind::check_standalone_kind_quantification(&mut ks, kind_ty, &type_ops)
                {
                    errors.push(e);
                }
                let k = ks.convert_kind_expr_canonical(kind_ty);
                standalone_kinds.insert(name.value, k.clone());
                ks.register_class_kind(name.value, k);
            }
        }

        // Two-pass approach for mutually recursive types:
        // Pass A: Pre-assign fresh kind variables for all local types
        let mut pre_assigned: HashMap<Symbol, Type> = HashMap::new();
        for decl in &module.decls {
            match decl {
                Decl::Data {
                    name,
                    kind_sig,
                    is_role_decl,
                    ..
                } if *kind_sig == KindSigSource::None && !*is_role_decl => {
                    if !standalone_kinds.contains_key(&name.value) {
                        let fresh = ks.fresh_kind_var();
                        pre_assigned.insert(name.value, fresh.clone());
                        ks.register_type(name.value, fresh);
                    }
                }
                Decl::Newtype { name, .. } => {
                    if !standalone_kinds.contains_key(&name.value) {
                        let fresh = ks.fresh_kind_var();
                        pre_assigned.insert(name.value, fresh.clone());
                        ks.register_type(name.value, fresh);
                    }
                }
                Decl::TypeAlias { name, .. } => {
                    if !standalone_kinds.contains_key(&name.value) {
                        let fresh = ks.fresh_kind_var();
                        pre_assigned.insert(name.value, fresh.clone());
                        ks.register_type(name.value, fresh);
                    }
                }
                Decl::Class {
                    name, is_kind_sig, ..
                } if !*is_kind_sig => {
                    if !standalone_kinds.contains_key(&name.value) {
                        let fresh = ks.fresh_kind_var();
                        pre_assigned.insert(name.value, fresh.clone());
                        ks.register_class_kind(name.value, fresh);
                    }
                }
                _ => {}
            }
        }

        // Pass B: Infer actual kinds for each declaration and unify with pre-assigned vars.
        // Uses SCC analysis to identify binding groups — types in the same SCC share
        // kind variables (monomorphic inference) while independent types are freshened.
        let sccs = kind::compute_type_sccs(&module.decls);
        let scc_members: HashMap<Symbol, HashSet<Symbol>> = {
            let mut map = HashMap::new();
            for scc in &sccs {
                let set: HashSet<Symbol> = scc.iter().copied().collect();
                for &name in scc {
                    map.insert(name, set.clone());
                }
            }
            map
        };

        // Build SCC-ordered declaration list: declarations that participate in kind
        // inference are processed in SCC topological order (dependencies first) to ensure
        // kinds are resolved before use. Other declarations keep their source order.
        let scc_order: HashMap<Symbol, usize> = {
            let mut m = HashMap::new();
            for (i, scc) in sccs.iter().enumerate() {
                for &name in scc {
                    m.insert(name, i);
                }
            }
            m
        };
        let mut decl_indices: Vec<usize> = (0..module.decls.len()).collect();
        decl_indices.sort_by_key(|&i| {
            let decl = &module.decls[i];
            let name = match decl {
                Decl::Data { name, kind_sig, is_role_decl, .. }
                    if *kind_sig == KindSigSource::None && !*is_role_decl => Some(name.value),
                Decl::Newtype { name, .. } => Some(name.value),
                Decl::TypeAlias { name, .. } => Some(name.value),
                Decl::Class { name, is_kind_sig, .. } if !*is_kind_sig => Some(name.value),
                _ => None,
            };
            // SCC-participating decls get their SCC index; others go to the end
            name.and_then(|n| scc_order.get(&n).copied()).unwrap_or(usize::MAX)
        });

        for &decl_idx in &decl_indices {
            let decl = &module.decls[decl_idx];
            // Set binding group for the current declaration's SCC
            let decl_name = match decl {
                Decl::Data {
                    name,
                    kind_sig,
                    is_role_decl,
                    ..
                } if *kind_sig == KindSigSource::None && !*is_role_decl => Some(name.value),
                Decl::Newtype { name, .. } => Some(name.value),
                Decl::TypeAlias { name, .. } => Some(name.value),
                Decl::Class {
                    name, is_kind_sig, ..
                } if !*is_kind_sig => Some(name.value),
                _ => None,
            };
            if let Some(dn) = decl_name {
                if let Some(group) = scc_members.get(&dn) {
                    ks.binding_group = group.clone();
                }
            }

            match decl {
                Decl::Data {
                    span,
                    name,
                    type_vars,
                    constructors,
                    kind_sig,
                    is_role_decl,
                    kind_type: _,
                    type_var_kind_anns,
                } => {
                    if *kind_sig != KindSigSource::None || *is_role_decl {
                        continue;
                    }
                    // Check type var kind annotations for partially applied synonyms
                    let mut has_pas = false;
                    for ann in type_var_kind_anns.iter().flatten() {
                        if let Err(e) = kind::check_type_expr_partial_synonym(
                            ann,
                            &ks.state.type_aliases,
                            &type_ops,
                        ) {
                            errors.push(e);
                            has_pas = true;
                        }
                    }
                    if has_pas {
                        continue;
                    }
                    // Check constructor field types for directly partially applied synonyms
                    // (e.g. `data X = Y S` where `type S a = D a`).
                    for ctor in constructors.iter() {
                        for field in &ctor.fields {
                            if let Some(e) = check_field_partially_applied_synonym(
                                field,
                                &ks.state.type_aliases,
                                &type_ops,
                            ) {
                                errors.push(e);
                                has_pas = true;
                            }
                        }
                    }
                    if has_pas {
                        continue;
                    }

                    match kind::infer_data_kind(
                        &mut ks,
                        name.value,
                        type_vars,
                        type_var_kind_anns,
                        constructors,
                        *span,
                        &type_ops,
                    ) {
                        Ok(inferred) => {
                            // Unify with pre-assigned or standalone kind
                            if let Some(standalone) = standalone_kinds.get(&name.value) {
                                let inst = kind::instantiate_kind(&mut ks, standalone);
                                if let Err(e) = ks.unify_kinds(*span, &inst, &inferred) {
                                    errors.push(e);
                                }
                                // Also check with skolemized kinds for data types
                                let field_refs: Vec<&crate::ast::TypeExpr> =
                                    constructors.iter().flat_map(|c| c.fields.iter()).collect();
                                if let Some(e) = kind::check_body_against_standalone_kind(
                                    &mut ks,
                                    standalone,
                                    type_vars,
                                    &field_refs,
                                    name.value,
                                    *span,
                                    &type_ops,
                                ) {
                                    errors.push(e);
                                }
                            } else if let Some(pre) = pre_assigned.get(&name.value) {
                                if let Err(e) = ks.unify_kinds(*span, pre, &inferred) {
                                    errors.push(e);
                                }
                            }
                        }
                        Err(e) => errors.push(e),
                    }
                }
                Decl::Newtype {
                    span,
                    name,
                    type_vars,
                    ty,
                    type_var_kind_anns,
                    ..
                } => {
                    // Check type var kind annotations for partially applied synonyms
                    let mut has_pas = false;
                    for ann in type_var_kind_anns.iter().flatten() {
                        if let Err(e) = kind::check_type_expr_partial_synonym(
                            ann,
                            &ks.state.type_aliases,
                            &type_ops,
                        ) {
                            errors.push(e);
                            has_pas = true;
                        }
                    }
                    if has_pas {
                        continue;
                    }
                    // Check if the newtype field is directly a partially applied synonym
                    // (e.g. `newtype N = N S` where `type S a = D a` — S is missing its argument).
                    // Must run BEFORE kind inference to produce the specific
                    // PartiallyAppliedSynonym error instead of the generic KindsDoNotUnify.
                    // Only check the outermost type — nested partial apps (like `F ((~>) Array)`)
                    // should be reported as KindsDoNotUnify by the kind checker.
                    if let Some(e) = check_field_partially_applied_synonym(
                        ty,
                        &ks.state.type_aliases,
                        &type_ops,
                    ) {
                        errors.push(e);
                        continue;
                    }
                    match kind::infer_newtype_kind(
                        &mut ks,
                        name.value,
                        type_vars,
                        type_var_kind_anns,
                        ty,
                        *span,
                        &type_ops,
                    ) {
                        Ok(inferred) => {
                            if let Some(standalone) = standalone_kinds.get(&name.value) {
                                let inst = kind::instantiate_kind(&mut ks, standalone);
                                if let Err(e) = ks.unify_kinds(*span, &inst, &inferred) {
                                    errors.push(e);
                                }
                                // Also check with skolemized kinds to detect over-constraining
                                if let Some(e) = kind::check_body_against_standalone_kind(
                                    &mut ks,
                                    standalone,
                                    type_vars,
                                    &[ty],
                                    name.value,
                                    *span,
                                    &type_ops,
                                ) {
                                    errors.push(e);
                                }
                            } else if let Some(pre) = pre_assigned.get(&name.value) {
                                if let Err(e) = ks.unify_kinds(*span, pre, &inferred) {
                                    errors.push(e);
                                }
                            }
                        }
                        Err(e) => errors.push(e),
                    }
                }
                Decl::TypeAlias {
                    span,
                    name,
                    type_vars,
                    ty,
                    type_var_kind_anns,
                } => {
                    // Check type var kind annotations for partially applied synonyms
                    let mut has_pas = false;
                    for ann in type_var_kind_anns.iter().flatten() {
                        if let Err(e) = kind::check_type_expr_partial_synonym(
                            ann,
                            &ks.state.type_aliases,
                            &type_ops,
                        ) {
                            errors.push(e);
                            has_pas = true;
                        }
                    }
                    if has_pas {
                        continue;
                    }
                    match kind::infer_type_alias_kind(
                        &mut ks,
                        name.value,
                        type_vars,
                        type_var_kind_anns,
                        ty,
                        *span,
                        &type_ops,
                    ) {
                        Ok(inferred) => {
                            if let Some(standalone) = standalone_kinds.get(&name.value) {
                                // Unify with standalone kind signature
                                let inst = kind::instantiate_kind(&mut ks, standalone);
                                if let Err(e) = ks.unify_kinds(*span, &inst, &inferred) {
                                    errors.push(e);
                                }
                            } else if let Some(pre) = pre_assigned.get(&name.value) {
                                // Silently ignore kind unification failures for aliases
                                let _ = ks.unify_kinds(*span, pre, &inferred);
                                // Register the inferred kind so importing modules
                                // can use it for kind checking.
                                let zonked_kind = ks.zonk_kind(inferred);
                                ks.register_type(name.value, zonked_kind);
                            } else {
                                let zonked_kind = ks.zonk_kind(inferred);
                                ks.register_type(name.value, zonked_kind);
                            }
                        }
                        Err(e) => errors.push(e),
                    }
                    // Clear any deferred quantification checks that accumulated
                    // from foralls inside the alias body (e.g. `type Foo r = ∀ s. ...`).
                    // These don't need quantification checking — alias bodies are
                    // transparent and their forall kind vars are constrained by usage.
                    // Without this, they leak into the next data/newtype's check.
                    ks.deferred_quantification_checks.clear();
                }
                Decl::Class {
                    span,
                    name,
                    type_vars,
                    members,
                    is_kind_sig,
                    type_var_kind_anns,
                    ..
                } => {
                    if *is_kind_sig {
                        continue;
                    }
                    // Check type var kind annotations for partially applied synonyms
                    let mut has_pas = false;
                    for ann in type_var_kind_anns.iter().flatten() {
                        if let Err(e) = kind::check_type_expr_partial_synonym(
                            ann,
                            &ks.state.type_aliases,
                            &type_ops,
                        ) {
                            errors.push(e);
                            has_pas = true;
                        }
                    }
                    if has_pas {
                        continue;
                    }
                    match kind::infer_class_kind(
                        &mut ks, name.value, type_vars, members, *span, &type_ops,
                    ) {
                        Ok(inferred) => {
                            if let Some(pre) = pre_assigned.get(&name.value) {
                                if let Err(e) = ks.unify_kinds(*span, pre, &inferred) {
                                    errors.push(e);
                                }
                            }
                        }
                        Err(e) => errors.push(e),
                    }
                }
                _ => {}
            }

            ks.binding_group.clear();
        }

        // Pass C: Kind-check usage sites — type signatures and instance heads.
        // We use the main `ks` directly (no temp state clone). This is safe because
        // lookup_type_fresh freshens all unsolved vars into new IDs, so Pass C's
        // kind unification can never solve the original vars from Passes A/B.
        // Save deferred quantification checks from Passes A/B since Pass C will
        // add its own (from forall vars in type annotations) which are not relevant.
        let saved_deferred = std::mem::take(&mut ks.deferred_quantification_checks);
        let saved_class_param_kinds = ks.class_param_kind_types.clone();
        {
            let empty_var_kinds: HashMap<Symbol, Type> = HashMap::new();
            let k_type = Type::kind_type();
            for decl in &module.decls {
                match decl {
                    Decl::TypeSignature { ty, .. } => {
                        if let Err(e) = kind::check_kind_annotations_for_partial_synonym(
                            ty,
                            &ks.state.type_aliases,
                            &type_ops,
                        ) {
                            errors.push(e);
                        } else {
                            match kind::infer_kind(&mut ks, ty, &empty_var_kinds, &type_ops, None) {
                                Ok(kind) => {
                                    let zonked = ks.zonk_kind(kind);
                                    if zonked != k_type && !matches!(zonked, Type::Unif(_)) {
                                        errors.push(TypeError::ExpectedType {
                                            span: ty.span(),
                                            found: zonked,
                                        });
                                    }
                                }
                                Err(e) => errors.push(e),
                            }
                        }
                    }
                    Decl::Instance {
                        span,
                        class_name,
                        types,
                        ..
                    }
                    | Decl::Derive {
                        span,
                        class_name,
                        types,
                        ..
                    } => {
                        // For qualified class names (e.g., Route.Route from
                        // `import OaRouteClass as Route`), try the composite key
                        // first since class kinds are registered under qualified keys.
                        let class_kind_raw = if let Some(m) = class_name.module {
                            let qualified = crate::interner::intern_qualified(m, class_name.name);
                            ks.lookup_class_kind_fresh(qualified)
                                .or_else(|| ks.lookup_class_kind_fresh(class_name.name))
                        } else {
                            ks.lookup_class_kind_fresh(class_name.name)
                        };
                        let class_kind = match class_kind_raw {
                            Some(k) => kind::instantiate_kind(&mut ks, &k),
                            None => continue,
                        };
                        let mut remaining_kind = class_kind;
                        let mut had_error = false;
                        for ty_expr in types.iter() {
                            let arg_kind = match kind::infer_kind(&mut ks, ty_expr, &empty_var_kinds, &type_ops, None) {
                                Ok(k) => k,
                                Err(e) => { errors.push(e); had_error = true; break; }
                            };
                            let result_kind = ks.fresh_kind_var();
                            let expected = Type::fun(arg_kind, result_kind.clone());
                            if let Err(e) = ks.unify_kinds(*span, &expected, &remaining_kind) {
                                errors.push(e); had_error = true; break;
                            }
                            remaining_kind = result_kind;
                        }
                        let _ = had_error;
                    }
                    Decl::Value {
                        binders,
                        guarded,
                        where_clause,
                        ..
                    } => {
                        let mut type_exprs = Vec::new();
                        for b in binders.iter() {
                            kind::collect_type_exprs_from_binder(b, &mut type_exprs);
                        }
                        kind::collect_type_exprs_from_guarded(guarded, &mut type_exprs);
                        for lb in where_clause.iter() {
                            kind::collect_type_exprs_from_let_binding(lb, &mut type_exprs);
                        }
                        for te in type_exprs {
                            match kind::infer_kind(&mut ks, te, &empty_var_kinds, &type_ops, None) {
                                Ok(kind) => {
                                    let zonked = ks.zonk_kind(kind);
                                    if zonked != k_type && !matches!(zonked, Type::Unif(_)) {
                                        errors.push(TypeError::ExpectedType {
                                            span: te.span(),
                                            found: zonked,
                                        });
                                    }
                                }
                                Err(e) => errors.push(e),
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        // Restore deferred quantification checks from Passes A/B, discarding
        // any checks accumulated during Pass C (those are for usage-site foralls
        // which don't need quantification checking).
        ks.deferred_quantification_checks = saved_deferred;
        ks.class_param_kind_types = saved_class_param_kinds;

        // Run deferred quantification checks now that ALL kind vars are maximally
        // constrained. This catches forall vars with ambiguous kinds (e.g.
        // `data P = P (forall a. Proxy a)` where a's kind is undetermined).
        // Running at the end avoids false positives from forall vars that reference
        // types whose kinds aren't yet fully inferred during per-declaration checking.
        if let Some(err) = ks.check_deferred_quantification() {
            errors.push(err);
        }

        // Save kind information for post-inference kind checking.
        // Zonk kinds using the kind pass state to resolve solved vars.
        saved_type_kinds = ks
            .type_kinds
            .iter()
            .map(|(&name, kind)| (qi(name), ks.state.zonk(kind.clone())))
            .collect();
        saved_class_kinds = ks
            .class_kinds
            .iter()
            .map(|(&name, kind)| (qi(name), ks.state.zonk(kind.clone())))
            .collect();
    }

    let module_name = module.name.value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".");
    let timed_module = std::env::var("TIME_MODULE").unwrap_or_default();
    // macro for only when when module name is the module name from env var
    macro_rules! timed_pass {
        ($pass_num:expr, $pass_desc:expr, $span:expr) => {
            if timed_module == module_name {
                eprintln!("[TIMING] {} pass {} ({}) at {} {:?}", module_name, $pass_num, $pass_desc, $span, _module_start.elapsed());
            }
        };
    }

    timed_pass!(0, "start", "");
    // Pre-scan: collect newtype names so derive statements that appear before
    // their corresponding newtype declaration (common in PureScript) work correctly.
    for decl in &module.decls {
        if let Decl::Newtype { name, .. } = decl {
            ctx.newtype_names.insert(qi(name.value));
        }
    }
    // Pre-register local type aliases so that PAS checks during data constructor
    // processing see the correct alias arity. Without this, when a data declaration
    // appears before a type alias in source order (e.g. `data Action = ... Input ...`
    // before `type Input = { ... }`), the PAS check finds an imported parametric alias
    // instead of the local 0-param one, producing a false PartiallyAppliedSynonym error.
    for decl in &module.decls {
        if let Decl::TypeAlias { name, type_vars, ty, .. } = decl {
            if let Ok(body_ty) = convert_type_expr(ty, &type_ops) {
                let params: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                // For re-exported aliases like `type X = M.X`, resolve the body
                // using the already-imported expanded alias instead of storing the
                // unexpandable qualified reference.
                let resolved_body = if is_alias_reexport(&body_ty, name.value, &params) {
                    if let Some((existing_params, existing_body)) = ctx.state.type_aliases.get(&name.value) {
                        if existing_params.len() == params.len() && !matches!(existing_body, Type::Con(_)) {
                            existing_body.clone()
                        } else {
                            body_ty
                        }
                    } else {
                        body_ty
                    }
                } else {
                    body_ty
                };
                ctx.state.type_aliases.insert(name.value, (params, resolved_body));
                if matches!(ty, TypeExpr::Record { .. }) {
                    ctx.record_type_aliases.insert(qi(name.value));
                }
            }
        }
    }

    // Pass 1: Collect type signatures and data constructors
    for decl in &module.decls {
        let decl_name =  match decl.name() { 
            Some(n) =>  crate::interner::resolve(n).unwrap_or_default(),
            None => "<unknown>".to_string(),
        };
        timed_pass!(1, format!("start decl {}", decl_name), decl.span());
        match decl {
            Decl::TypeSignature { span, name, ty } => {
                if signatures.contains_key(&name.value) {
                    errors.push(TypeError::DuplicateTypeSignature {
                        span: *span,
                        name: name.value,
                    });
                    continue;
                }
                // Check for Partial constraint (intentionally non-exhaustive functions)
                if has_partial_constraint(ty) {
                    partial_names.insert(name.value);
                }
                // Check for Partial in function parameter (discharges Partial constraint)
                if has_partial_in_function_param(ty) {
                    ctx.partial_dischargers.insert(qi(name.value));
                }
                // Check for undefined type variables (all vars must be bound by forall)
                collect_type_expr_vars(ty, &HashSet::new(), &mut errors);
                // Validate constraint class names in the type signature
                check_constraint_class_names(ty, &known_classes, &class_param_counts, &mut errors);
                // Check for type-level scope conflicts (ambiguous type names)
                if let Some((conflict_span, conflict_name)) = crate::typechecker::convert::find_type_scope_conflict(ty, &ctx.type_scope_conflicts) {
                    errors.push(TypeError::ScopeConflict {
                        span: conflict_span,
                        name: conflict_name,
                    });
                }
                match convert_type_expr(ty, &type_ops) {
                    Ok(converted) => {
                        // Check for partially applied synonyms in type signature
                        check_type_for_partial_synonyms_with_arities(
                            &converted,
                            &ctx.state.type_aliases,
                            &ctx.type_con_arities,
                            &ctx.record_type_aliases,
                            *span,
                            &mut errors,
                        );
                        // Replace wildcard `_` with fresh unification variables so
                        // signatures like `main :: Effect _` work correctly.
                        let converted = ctx.instantiate_wildcards(&converted);
                        signatures.insert(name.value, (*span, converted));
                        // Extract constraints from the type signature for propagation
                        // to call sites (e.g., Lacks "x" r => ...)
                        let sig_constraints =
                            extract_type_signature_constraints(ty, &type_ops);
                        if !sig_constraints.is_empty() {
                            // Check for Fail constraints — these are deliberately unsatisfiable
                            // and should always produce NoInstanceFound at the definition site.
                            for (class_name, type_args) in &sig_constraints {
                                let cn =
                                    crate::interner::resolve(class_name.name).unwrap_or_default();
                                if cn == "Fail" {
                                    errors.push(TypeError::NoInstanceFound {
                                        span: *span,
                                        class_name: *class_name,
                                        type_args: type_args.clone(),
                                    });
                                }
                            }
                            for (class_name, _) in &sig_constraints {
                                explicit_sig_classes.insert(class_name.name);
                            }
                            ctx.signature_constraints
                                .insert(qi(name.value), sig_constraints);
                        }
                        // Extract return-type inner-forall constraints
                        let rt_constraints = extract_return_type_constraints(ty, &type_ops);
                        if !rt_constraints.is_empty() {
                            let depth = count_return_type_arrow_depth(ty);
                            ctx.return_type_constraints
                                .insert(qi(name.value), rt_constraints);
                            ctx.return_type_arrow_depth
                                .insert(qi(name.value), depth);
                        }
                    }
                    Err(e) => errors.push(e),
                }
            }
            Decl::Data {
                span,
                name,
                type_vars,
                constructors,
                kind_sig,
                is_role_decl,
                ..
            } => {
                // Role declarations are handled separately
                if *is_role_decl {
                    continue;
                }
                // Track kind signatures vs real definitions for orphan detection
                if *kind_sig != KindSigSource::None {
                    kind_sigs.entry(name.value).or_insert((*span, *kind_sig));
                } else {
                    has_real_definition.insert(name.value);
                    has_data_def.insert(name.value);
                }

                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                let type_var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();

                // Build the result type: TypeName tv1 tv2 ...
                let mut result_type = Type::Con(qi(name.value));
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(tv));
                }

                // Register constructors for exhaustiveness checking.
                // Skip if this is a kind/role annotation (empty constructors) and
                // the type already has constructors registered (e.g. from a Newtype).
                let ctor_names: Vec<QualifiedIdent> =
                    constructors.iter().map(|c| qi(c.name.value)).collect();
                if !ctor_names.is_empty() || !ctx.data_constructors.contains_key(&qi(name.value)) {
                    ctx.data_constructors.insert(qi(name.value), ctor_names);
                }

                for ctor in constructors {
                    // Reject type wildcards in data constructor fields
                    for f in &ctor.fields {
                        if let Some(wc_span) = find_wildcard_span(f) {
                            errors.push(TypeError::SyntaxError { span: wc_span });
                        }
                    }

                    // Build constructor type: field1 -> field2 -> ... -> result_type
                    let field_results: Vec<Result<Type, TypeError>> = ctor
                        .fields
                        .iter()
                        .map(|f| convert_type_expr(f, &type_ops))
                        .collect();

                    // If any field type fails, record the error and skip this constructor
                    let mut field_types = Vec::new();
                    let mut failed = false;
                    for r in field_results {
                        match r {
                            Ok(ty) => field_types.push(ty),
                            Err(e) => {
                                errors.push(e);
                                failed = true;
                                break;
                            }
                        }
                    }
                    if failed {
                        continue;
                    }

                    // Check for partially applied synonyms in field types
                    for field_ty in &field_types {
                        check_type_for_partial_synonyms_with_arities(
                            field_ty,
                            &ctx.state.type_aliases,
                            &ctx.type_con_arities,
                            &ctx.record_type_aliases,
                            *span,
                            &mut errors,
                        );
                    }

                    // Save field types for nested exhaustiveness checking
                    ctx.ctor_details.insert(
                        qi(ctor.name.value),
                        (qi(name.value), type_var_syms.clone(), field_types.clone()),
                    );

                    let mut ctor_ty = result_type.clone();
                    for field_ty in field_types.into_iter().rev() {
                        ctor_ty = Type::fun(field_ty, ctor_ty);
                    }

                    // Wrap in Forall if there are type variables
                    // Data constructor type vars are always visible for VTA
                    if !type_var_syms.is_empty() {
                        ctor_ty = Type::Forall(
                            type_var_syms.iter().map(|&v| (v, true)).collect(),
                            Box::new(ctor_ty),
                        );
                    }

                    let scheme = Scheme::mono(ctor_ty);
                    env.insert_scheme(ctor.name.value, scheme.clone());
                    local_values.insert(ctor.name.value, scheme);
                }
            }
            Decl::Newtype {
                span,
                name,
                type_vars,
                constructor,
                ty,
                ..
            } => {
                has_real_definition.insert(name.value);
                has_newtype_def.insert(name.value);
                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Track as a newtype for derive validation and Coercible solving
                ctx.newtype_names.insert(qi(name.value));

                // Register constructor for exhaustiveness checking
                ctx.data_constructors
                    .insert(qi(name.value), vec![qi(constructor.value)]);

                let type_var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();

                let mut result_type = Type::Con(qi(name.value));
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(tv));
                }

                match convert_type_expr(ty, &type_ops) {
                    Ok(field_ty) => {
                        // Check for partially applied synonyms in field type
                        check_type_for_partial_synonyms_with_arities(
                            &field_ty,
                            &ctx.state.type_aliases,
                            &ctx.type_con_arities,
                            &ctx.record_type_aliases,
                            *span,
                            &mut errors,
                        );

                        // Save field type for nested exhaustiveness checking
                        ctx.ctor_details.insert(
                            qi(constructor.value),
                            (
                                qi(name.value),
                                type_var_syms.clone(),
                                vec![field_ty.clone()],
                            ),
                        );

                        let mut ctor_ty = Type::fun(field_ty, result_type);

                        // Newtype constructor type vars are always visible for VTA
                        if !type_var_syms.is_empty() {
                            ctor_ty = Type::Forall(
                                type_var_syms.iter().map(|&v| (v, true)).collect(),
                                Box::new(ctor_ty),
                            );
                        }

                        let scheme = Scheme::mono(ctor_ty);
                        env.insert_scheme(constructor.value, scheme.clone());
                        local_values.insert(constructor.value, scheme);
                    }
                    Err(e) => {
                        errors.push(e);
                    }
                }
            }
            Decl::Foreign { name, ty, .. } => {
                // Check for prime characters in foreign import names
                let resolved_name = crate::interner::resolve(name.value).unwrap_or_default();
                if resolved_name.contains('\'') {
                    errors.push(TypeError::DeprecatedFFIPrime {
                        span: name.span,
                        name: name.value,
                    });
                }
                // Check for undefined type variables
                collect_type_expr_vars(ty, &HashSet::new(), &mut errors);
                // Reject constraints in foreign import types
                if let Some(c_span) = has_any_constraint(ty) {
                    errors.push(TypeError::SyntaxError { span: c_span });
                }
                match convert_type_expr(ty, &type_ops) {
                    Ok(converted) => {
                        let scheme = Scheme::mono(converted);
                        env.insert_scheme(name.value, scheme.clone());
                        local_values.insert(name.value, scheme);
                    }
                    Err(e) => errors.push(e),
                }
            }
            Decl::Class {
                span,
                name,
                type_vars,
                members,
                constraints,
                fundeps,
                is_kind_sig,
                ..
            } => {
                // Track kind signatures vs real definitions for orphan detection
                if *is_kind_sig {
                    kind_sigs
                        .entry(name.value)
                        .or_insert((*span, KindSigSource::Class));
                } else {
                    has_real_definition.insert(name.value);
                    has_class_def.insert(name.value);
                }

                // Track class for duplicate detection (skip kind signatures)
                if !is_kind_sig {
                    seen_classes.entry(name.value).or_default().push(*span);

                    // Collect superclass names for cycle detection
                    // Skip qualified superclass refs — P.Show refers to an
                    // imported class, not the locally-defined one.
                    let superclass_names: Vec<Symbol> = constraints
                        .iter()
                        .filter(|c| c.class.module.is_none())
                        .map(|c| c.class.name)
                        .collect();
                    class_defs.insert(name.value, (*span, superclass_names));

                    // Validate superclass constraint arguments: reject forall and wildcards
                    for constraint in constraints {
                        for arg in &constraint.args {
                            if let Some(bad_span) = has_forall_or_wildcard(arg) {
                                errors
                                    .push(TypeError::SyntaxError { span: bad_span });
                            }
                        }
                    }

                    // Track superclass constraints with converted type args for instance validation
                    let tvs: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                    let mut sc_constraints: Vec<(QualifiedIdent, Vec<Type>)> = Vec::new();
                    for constraint in constraints {
                        let mut sc_args = Vec::new();
                        let mut ok = true;
                        for arg in &constraint.args {
                            match convert_type_expr(arg, &type_ops) {
                                Ok(ty) => sc_args.push(ty),
                                Err(_) => {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        if ok {
                            sc_constraints.push((constraint.class, sc_args));
                        }
                    }
                    class_superclasses.insert(qi(name.value), (tvs.clone(), sc_constraints));

                    // Store functional dependencies as index pairs for orphan checking
                    if !fundeps.is_empty() {
                        let fd_indices: Vec<(Vec<usize>, Vec<usize>)> = fundeps
                            .iter()
                            .filter_map(|fd| {
                                let lhs: Vec<usize> = fd
                                    .lhs
                                    .iter()
                                    .filter_map(|v| tvs.iter().position(|tv| tv == v))
                                    .collect();
                                let rhs: Vec<usize> = fd
                                    .rhs
                                    .iter()
                                    .filter_map(|v| tvs.iter().position(|tv| tv == v))
                                    .collect();
                                if lhs.len() == fd.lhs.len() && rhs.len() == fd.rhs.len() {
                                    Some((lhs, rhs))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        ctx.class_fundeps
                            .insert(qi(name.value), (tvs.clone(), fd_indices));
                    }

                    // Track class type parameter count for arity checking
                    class_param_counts.insert(qi(name.value), type_vars.len());
                    known_classes.insert(qi(name.value));
                    // A locally-defined class shadows any Prim magic class with the same name
                    ctx.prim_class_names.remove(&name.value);
                }

                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Check superclass constraints only reference bound type vars
                // and that superclass classes exist
                if !is_kind_sig {
                    let bound_vars: HashSet<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                    for constraint in constraints {
                        for arg in &constraint.args {
                            collect_type_expr_vars(arg, &bound_vars, &mut errors);
                        }
                        // Check that superclass is a known class
                        if constraint.class.module.is_none() {
                            let sc_known = class_param_counts.contains_key(&constraint.class)
                                || instances.contains_key(&constraint.class)
                                || local_class_names.contains(&constraint.class.name);
                            if !sc_known {
                                errors.push(TypeError::UnknownClass {
                                    span: *span,
                                    name: constraint.class,
                                });
                            }
                        }
                    }
                }

                // Register class methods in the environment with their declared types
                let type_var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                for member in members {
                    // Track methods with extra typeclass constraints (e.g. Applicative m =>).
                    // These get implicit dictionary parameters, making them functions even
                    // with 0 explicit binders (prevents false CycleInDeclaration).
                    // Extract method-level constraint class names for current_given_expanded
                    {
                        let mut constraint_classes = Vec::new();
                        let mut constraint_details: Vec<(QualifiedIdent, Vec<Type>)> = Vec::new();
                        fn extract_constraint_classes(ty: &crate::ast::TypeExpr, out: &mut Vec<Symbol>) {
                            match ty {
                                crate::ast::TypeExpr::Constrained { constraints, ty, .. } => {
                                    for c in constraints {
                                        out.push(c.class.name);
                                    }
                                    extract_constraint_classes(ty, out);
                                }
                                crate::ast::TypeExpr::Forall { ty, .. } => {
                                    extract_constraint_classes(ty, out);
                                }
                                _ => {}
                            }
                        }
                        fn extract_constraint_details(
                            ty: &crate::ast::TypeExpr,
                            type_ops: &HashMap<QualifiedIdent, QualifiedIdent>,
                            out: &mut Vec<(QualifiedIdent, Vec<Type>)>,
                        ) {
                            match ty {
                                crate::ast::TypeExpr::Constrained { constraints, ty, .. } => {
                                    for c in constraints {
                                        let mut args = Vec::new();
                                        let mut ok = true;
                                        for arg in &c.args {
                                            match convert_type_expr(arg, type_ops) {
                                                Ok(t) => args.push(t),
                                                Err(_) => { ok = false; break; }
                                            }
                                        }
                                        if ok {
                                            out.push((c.class, args));
                                        }
                                    }
                                    extract_constraint_details(ty, type_ops, out);
                                }
                                crate::ast::TypeExpr::Forall { ty, .. } => {
                                    extract_constraint_details(ty, type_ops, out);
                                }
                                _ => {}
                            }
                        }
                        extract_constraint_classes(&member.ty, &mut constraint_classes);
                        extract_constraint_details(&member.ty, &type_ops, &mut constraint_details);
                        if !constraint_classes.is_empty() {
                            ctx.constrained_class_methods.insert(member.name.value);
                            ctx.method_own_constraints.insert(member.name.value, constraint_classes);
                        }
                        if !constraint_details.is_empty() {
                            ctx.method_own_constraint_details.insert(member.name.value, constraint_details);
                        }
                    }
                    match convert_type_expr(&member.ty, &type_ops) {
                        Ok(member_ty) => {
                            // Class header type vars are always visible for VTA
                            let scheme_ty = if !type_var_syms.is_empty() {
                                Type::Forall(
                                    type_var_syms.iter().map(|&v| (v, true)).collect(),
                                    Box::new(member_ty),
                                )
                            } else {
                                member_ty
                            };
                            let scheme = Scheme::mono(scheme_ty);
                            env.insert_scheme(member.name.value, scheme.clone());
                            local_values.insert(member.name.value, scheme.clone());
                            // Save the canonical scheme so instance method expected-type
                            // lookup can use it without being affected by later value
                            // imports that shadow the same name in the env.
                            ctx.class_method_schemes.insert(member.name.value, scheme.clone());
                            // Track that this method belongs to this class
                            ctx.class_methods.insert(
                                qi(member.name.value),
                                (qi(name.value), type_var_syms.clone()),
                            );
                        }
                        Err(e) => errors.push(e),
                    }
                }
                // Record class method declaration order for codegen
                let method_order: Vec<Symbol> = members.iter().map(|m| m.name.value).collect();
                ctx.class_method_order.insert(name.value, method_order);
            }
            Decl::Instance {
                span,
                name: inst_name,
                class_name,
                types,
                constraints,
                members,
                chain: is_chain,
                ..
            } => {
                // Track named instances for duplicate detection
                if let Some(iname) = inst_name {
                    seen_instance_names
                        .entry(iname.value)
                        .or_default()
                        .push(*span);
                }

                // Reject user-written Coercible instances (compiler-solved only)
                {
                    if crate::interner::symbol_eq(class_name.name, "Coercible")
                        && ctx.prim_class_names.contains(&class_name.name)
                    {
                        errors.push(TypeError::InvalidCoercibleInstanceDeclaration { span: *span });
                        continue;
                    }
                }

                // Register this instance's types and constraints
                let mut inst_types = Vec::new();
                let mut inst_ok = true;
                for ty_expr in types {
                    match convert_type_expr(ty_expr, &type_ops) {
                        Ok(ty) => inst_types.push(ty),
                        Err(e) => {
                            errors.push(e);
                            inst_ok = false;
                            break;
                        }
                    }
                }
                // Check instance arity matches class parameter count
                if inst_ok {
                    if let Some(&expected_count) = class_param_counts.get(class_name) {
                        if expected_count != usize::MAX && inst_types.len() != expected_count {
                            errors.push(TypeError::ClassInstanceArityMismatch {
                                span: *span,
                                class_name: *class_name,
                                expected: expected_count,
                                found: inst_types.len(),
                            });
                            inst_ok = false;
                        }
                    }
                }

                // Validate instance head types
                if inst_ok {
                    // Check CST-level: no wildcards or type synonyms in instance heads
                    for ty_expr in types {
                        if has_invalid_instance_head_type_expr(ty_expr) {
                            errors.push(TypeError::InvalidInstanceHead { span: *span });
                            inst_ok = false;
                            break;
                        }
                    }
                }
                // Check for type synonyms expanding to open records in instance heads.
                // E.g. `type X r = {x :: Int | r}; instance Show (X r)` is invalid.
                // Only check the LAST type (the main instance head), not class parameters —
                // row types are valid as class parameters (e.g. `instance SSTLinks RowAlias (SomeType m)`).
                if inst_ok {
                    if let Some(last_ty) = inst_types.last() {
                        if is_non_nominal_instance_head_record_only(last_ty, &ctx.state.type_aliases) {
                            errors.push(TypeError::InvalidInstanceHead { span: *span });
                            inst_ok = false;
                        }
                    }
                }
                // Check for partially applied synonyms in instance types
                if inst_ok {
                    for inst_ty in &inst_types {
                        check_type_for_partial_synonyms_with_arities(
                            inst_ty,
                            &ctx.state.type_aliases,
                            &ctx.type_con_arities,
                            &ctx.record_type_aliases,
                            *span,
                            &mut errors,
                        );
                    }
                }
                // Validate constraint arguments: reject forall and wildcards
                if inst_ok {
                    for constraint in constraints {
                        for arg in &constraint.args {
                            if let Some(bad_span) = has_forall_or_wildcard(arg) {
                                errors
                                    .push(TypeError::SyntaxError { span: bad_span });
                                inst_ok = false;
                                break;
                            }
                        }
                        if !inst_ok {
                            break;
                        }
                    }
                }
                // Convert constraints (e.g., `A a =>` part)
                let mut inst_constraints: Vec<(QualifiedIdent, Vec<Type>)> = Vec::new();
                if inst_ok {
                    for constraint in constraints {
                        let mut c_args = Vec::new();
                        let mut c_ok = true;
                        for arg in &constraint.args {
                            match convert_type_expr(arg, &type_ops) {
                                Ok(ty) => c_args.push(ty),
                                Err(e) => {
                                    errors.push(e);
                                    c_ok = false;
                                    inst_ok = false;
                                    break;
                                }
                            }
                        }
                        if c_ok {
                            inst_constraints.push((constraint.class, c_args));
                        }
                    }
                }
                // Collect free type vars from constraint args (used for scoped vars below)
                let constraint_scoped_vars: Vec<Symbol> = {
                    let mut vars = Vec::new();
                    fn collect_vars_from_type(ty: &Type, vars: &mut Vec<Symbol>) {
                        match ty {
                            Type::Var(v) => {
                                if !vars.contains(v) {
                                    vars.push(*v);
                                }
                            }
                            Type::Fun(a, b) | Type::App(a, b) => {
                                collect_vars_from_type(a, vars);
                                collect_vars_from_type(b, vars);
                            }
                            Type::Forall(_, body) => collect_vars_from_type(body, vars),
                            Type::Record(fields, tail) => {
                                for (_, t) in fields {
                                    collect_vars_from_type(t, vars);
                                }
                                if let Some(t) = tail {
                                    collect_vars_from_type(t, vars);
                                }
                            }
                            _ => {}
                        }
                    }
                    for (_, c_args) in &inst_constraints {
                        for ty in c_args {
                            collect_vars_from_type(ty, &mut vars);
                        }
                    }
                    vars
                };
                // Check if the class is known (either via param counts or instances)
                let class_known = class_param_counts.contains_key(&class_name)
                    || instances.contains_key(&class_name)
                    || local_class_names.contains(&class_name.name);

                // If the class doesn't exist at all, report it
                if inst_ok && !class_known && class_name.module.is_none() {
                    errors.push(TypeError::UnknownClass {
                        span: *span,
                        name: *class_name,
                    });
                }

                // Check for orphan instances: the instance must be in a module that
                // defines either the class or at least one type in the instance head.
                // With functional dependencies, every covering set must have at least
                // one locally-defined type.
                if inst_ok && !*is_chain && class_known {
                    let class_is_local = local_class_names.contains(&class_name.name);
                    if !class_is_local {
                        let is_orphan = check_orphan_with_fundeps(
                            &inst_types,
                            &class_name,
                            &ctx.class_fundeps,
                            &local_type_names,
                        );
                        if is_orphan {
                            errors.push(TypeError::OrphanInstance {
                                span: *span,
                                class_name: *class_name,
                            });
                        }
                    }
                }

                // Check for row types in non-determined instance head positions.
                // Row/record types can only appear at positions that are fully determined
                // by other positions via functional dependencies.
                if inst_ok {
                    let has_row: Vec<bool> = inst_types
                        .iter()
                        .map(|ty| type_contains_record(ty))
                        .collect();
                    if has_row.iter().any(|&x| x) {
                        let covering_sets =
                            if let Some((_, fds)) = ctx.class_fundeps.get(class_name) {
                                compute_covering_sets(inst_types.len(), fds)
                            } else {
                                // No fundeps: the only covering set is all positions
                                vec![(0..inst_types.len()).collect()]
                            };
                        for (idx, &is_row) in has_row.iter().enumerate() {
                            if is_row {
                                // Row type is invalid if this position is in ANY covering set
                                let in_covering = covering_sets.iter().any(|cs| cs.contains(&idx));
                                if in_covering {
                                    errors.push(TypeError::InvalidInstanceHead { span: *span });
                                    break;
                                }
                            }
                        }
                    }
                }

                // Build substitution from class type vars → instance types for method type checking.
                // Must be computed before inst_types is moved into instances.
                let inst_subst: HashMap<Symbol, Type> = if inst_ok {
                    let class_tvs: Option<&Vec<Symbol>> = ctx
                        .class_methods
                        .values()
                        .find(|(cn, _)| *cn == *class_name)
                        .map(|(_, tvs)| tvs);
                    if let Some(tvs) = class_tvs {
                        tvs.iter()
                            .zip(inst_types.iter())
                            .map(|(tv, ty)| (*tv, ty.clone()))
                            .collect()
                    } else {
                        HashMap::new()
                    }
                } else {
                    HashMap::new()
                };

                if inst_ok {
                    // Check for overlapping instances at definition time
                    // Skip if this instance is part of an instance chain (else keyword)
                    // or if the class is qualified (from a different module's namespace)
                    let has_kind_ann = types.iter().any(|t| type_expr_has_kinded(t));
                    if !is_chain && class_name.module.is_none() {
                        let mut found_overlap = false;
                        // Check against other local instances
                        if let Some(existing) = local_instance_heads.get(&class_name.name) {
                            for (existing_types, existing_has_kind, existing_cst) in existing {
                                // When kind annotations are present, compare CST types
                                // (which preserve kind info) to avoid false positives
                                // from instances that differ only in kind annotations
                                if has_kind_ann || *existing_has_kind {
                                    if type_exprs_alpha_eq_list(types, existing_cst) {
                                        errors.push(TypeError::OverlappingInstances {
                                            span: *span,
                                            class_name: *class_name,
                                            type_args: inst_types.clone(),
                                        });
                                        found_overlap = true;
                                        break;
                                    }
                                } else if instance_heads_overlap(
                                    &inst_types,
                                    existing_types,
                                    &ctx.state.type_aliases,
                                    &local_data_type_names,
                                ) {
                                    errors.push(TypeError::OverlappingInstances {
                                        span: *span,
                                        class_name: *class_name,
                                        type_args: inst_types.clone(),
                                    });
                                    found_overlap = true;
                                    break;
                                }
                            }
                        }
                        // Also check against imported instances (cross-module overlap).
                        // Only when: (1) class is NOT locally defined (avoids false positives
                        // from local classes shadowing imported ones with same name),
                        // (2) all type args are concrete (no type variables, avoids false
                        // positives from instances that appear in imported set via re-exports),
                        // (3) no kind annotations (imported instances don't store CST types).
                        if !found_overlap
                            && !has_kind_ann
                            && !local_class_names.contains(&class_name.name)
                            && inst_types.iter().all(|t| !type_has_vars(t))
                        {
                            if let Some(imported) = lookup_instances(&instances, &class_name) {
                                for (existing_types, _, _) in imported {
                                    // Skip if the imported instance uses a type constructor with the
                                    // same name as a locally-defined type — they're actually different
                                    // types from different modules that happen to share a short name.
                                    let imported_shadows_local = existing_types.iter().any(|t| {
                                        fn has_local_con(
                                            ty: &Type,
                                            locals: &HashSet<Symbol>,
                                        ) -> bool {
                                            match ty {
                                                Type::Con(n) => {
                                                    n.module == None && locals.contains(&n.name)
                                                }
                                                Type::App(f, a) => {
                                                    has_local_con(f, locals)
                                                        || has_local_con(a, locals)
                                                }
                                                _ => false,
                                            }
                                        }
                                        has_local_con(t, &local_type_names)
                                    });
                                    if imported_shadows_local {
                                        continue;
                                    }
                                    if instance_heads_overlap(
                                        &inst_types,
                                        existing_types,
                                        &ctx.state.type_aliases,
                                        &local_data_type_names,
                                    ) {
                                        errors.push(TypeError::OverlappingInstances {
                                            span: *span,
                                            class_name: *class_name,
                                            type_args: inst_types.clone(),
                                        });
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    local_instance_heads
                        .entry(class_name.name)
                        .or_default()
                        .push((inst_types.clone(), has_kind_ann, types.clone()));
                    registered_instances.push((*span, class_name.name, inst_types.clone()));
                    // Store instances with unqualified class name key.
                    // Class names may have import alias qualifiers (e.g. Filterable.Filterable)
                    // but internal maps should use unqualified keys.
                    let unqual_class = qi(class_name.name);
                    // Populate instance_registry for codegen dict resolution.
                    // Register under all extractable head type constructors for
                    // multi-parameter type classes (e.g., MonadState s (State s)).
                    if let Some(iname) = inst_name {
                        for head in extract_all_head_type_cons(&inst_types) {
                            instance_registry_entries
                                .entry((class_name.name, head))
                                .or_insert(iname.value);
                        }
                        // Track defining module for each instance
                        let module_parts: Vec<Symbol> = module.name.value.parts.clone();
                        instance_module_entries.insert(iname.value, module_parts);
                    } else {
                        // Anonymous instances: generate a name for codegen dict resolution.
                        // Mirrors the name generation in codegen (gen_instance_decl).
                        let all_heads = extract_all_head_type_cons(&inst_types);
                        if !all_heads.is_empty() {
                            let class_str = crate::interner::resolve(class_name.name).unwrap_or_default().to_string();
                            let mut gen_name = String::new();
                            for (i, c) in class_str.chars().enumerate() {
                                if i == 0 {
                                    gen_name.extend(c.to_lowercase());
                                } else {
                                    gen_name.push(c);
                                }
                            }
                            for ty in &inst_types {
                                gen_name.push_str(&type_to_instance_name_part(ty));
                            }
                            let gen_sym = crate::interner::intern(&gen_name);
                            for h in &all_heads {
                                instance_registry_entries
                                    .entry((class_name.name, *h))
                                    .or_insert(gen_sym);
                            }
                            let module_parts: Vec<Symbol> = module.name.value.parts.clone();
                            instance_module_entries.insert(gen_sym, module_parts);
                        }
                    }
                    let inst_name_sym = inst_name.as_ref().map(|n| n.value);
                    // Extract and store kind annotations for polykinded dispatch
                    if has_kind_ann {
                        if let Some(iname_sym) = inst_name_sym {
                            let kind_anns = extract_kind_annotations(types);
                            if !kind_anns.is_empty() {
                                instance_var_kinds_entries.insert(iname_sym, kind_anns);
                            }
                        }
                    }
                    instances
                        .entry(unqual_class)
                        .or_default()
                        .push((inst_types, inst_constraints, inst_name_sym));
                    if *is_chain {
                        chained_classes.insert(unqual_class);
                        ctx.chained_classes.insert(unqual_class);
                    }
                }

                // Check for missing/extraneous class members in this instance
                {
                    // Collect method names expected for this class
                    let expected_methods: Vec<Symbol> = ctx
                        .class_methods
                        .iter()
                        .filter(|(_, (cn, _))| *cn == *class_name)
                        .map(|(method, _)| method.name)
                        .collect();

                    // Collect method names provided in this instance
                    let mut provided_methods: HashSet<Symbol> = HashSet::new();
                    let mut provided_method_spans: HashMap<Symbol, Vec<Span>> = HashMap::new();
                    for member_decl in members.iter() {
                        if let Decl::Value {
                            name: mname,
                            span: mspan,
                            ..
                        } = member_decl
                        {
                            provided_methods.insert(mname.value);
                            provided_method_spans
                                .entry(mname.value)
                                .or_default()
                                .push(*mspan);
                        }
                    }

                    // Check for duplicate method definitions within this instance.
                    // Instance methods with the same name that are not adjacent are
                    // treated as duplicate declarations (like fixture 881).
                    for (method_name, method_spans) in &provided_method_spans {
                        if method_spans.len() > 1 {
                            // Check adjacency: see if all equations for this method are
                            // grouped together (no other method names in between)
                            let mut is_adjacent = true;
                            let mut found_first = false;
                            let mut gap = false;
                            for member_decl in members.iter() {
                                if let Decl::Value { name: mname, .. } = member_decl {
                                    if mname.value == *method_name {
                                        if gap {
                                            is_adjacent = false;
                                            break;
                                        }
                                        found_first = true;
                                    } else if found_first {
                                        gap = true;
                                    }
                                }
                            }
                            if !is_adjacent {
                                errors.push(TypeError::DuplicateValueDeclaration {
                                    spans: method_spans.clone(),
                                    name: *method_name,
                                });
                            }
                        }
                    }

                    // Check for extraneous/missing members only if the instance defines at least
                    // one method. Empty instances (no `where` clause) are allowed (e.g., with Fail constraint).
                    if !expected_methods.is_empty() && !provided_methods.is_empty() {
                        for method_name in &provided_methods {
                            if !expected_methods.contains(method_name) {
                                // Only report as extraneous if this method is not a known
                                // class method at all. When two classes define the same method
                                // name (e.g. NumExpr.add and DataDSL.add), the class_methods
                                // map may be overwritten, causing expected_methods to miss the
                                // method. In that case, skip the error.
                                let is_known_class_method = ctx.class_methods.contains_key(&qi(*method_name));
                                if !is_known_class_method {
                                    errors.push(TypeError::ExtraneousClassMember {
                                        span: *span,
                                        class_name: *class_name,
                                        member_name: *method_name,
                                    });
                                }
                            }
                        }

                        // Check for missing members (expected but not provided)
                        let missing: Vec<(Symbol, Type)> = expected_methods
                            .iter()
                            .filter(|m| !provided_methods.contains(m))
                            .filter_map(|m| env.lookup(*m).map(|scheme| (*m, scheme.ty.clone())))
                            .collect();
                        if !missing.is_empty() {
                            errors.push(TypeError::MissingClassMember {
                                span: *span,
                                class_name: *class_name,
                                members: missing,
                            });
                        }
                    }
                }

                // Validate instance type signatures and detect orphans
                let expected_methods: HashSet<Symbol> = ctx
                    .class_methods
                    .iter()
                    .filter(|(_, (cn, _))| *cn == *class_name)
                    .map(|(method, _)| method.name)
                    .collect();

                for member_decl in members.iter() {
                    if let Decl::TypeSignature {
                        name: sig_name,
                        span: sig_span,
                        ..
                    } = member_decl
                    {
                        if !expected_methods.contains(&sig_name.value) {
                            // Orphan type declaration inside instance — not a class method
                            errors.push(TypeError::OrphanTypeSignature {
                                span: *sig_span,
                                name: sig_name.value,
                            });
                        } else if inst_ok && !inst_subst.is_empty() {
                            // Check that instance method signature matches the class-derived type.
                            // Use class_method_schemes (not env.lookup) so that an explicit value
                            // import like `import Data.Array (foldl)` doesn't shadow the class
                            // method's canonical type here.
                            let canon = ctx.class_method_schemes.get(&sig_name.value)
                                .map(|s| s.ty.clone())
                                .or_else(|| env.lookup(sig_name.value).map(|s| s.ty.clone()));
                            if let Some(class_ty) = canon {
                                // Strip outer forall (class type vars) and substitute
                                let inner = match &class_ty {
                                    Type::Forall(_, body) => (**body).clone(),
                                    other => other.clone(),
                                };
                                let expected_ty = apply_var_subst(&inst_subst, &inner);
                                // Convert the instance signature type
                                if let Decl::TypeSignature { ty, .. } = member_decl {
                                    if let Ok(mut sig_ty) =
                                        convert_type_expr(ty, &type_ops)
                                    {
                                        // Replace wildcard `_` type vars with fresh unif vars.
                                        // PureScript allows `_` in instance method type annotations
                                        // meaning "infer this part" (e.g. `foo :: _ (NT m Aff)`).
                                        let wildcard_sym = crate::interner::intern("_");
                                        fn replace_wildcards(ty: &Type, wildcard: Symbol, ctx: &mut InferCtx) -> Type {
                                            match ty {
                                                Type::Var(v) if *v == wildcard => Type::Unif(ctx.state.fresh_var()),
                                                Type::Fun(a, b) => Type::fun(
                                                    replace_wildcards(a, wildcard, ctx),
                                                    replace_wildcards(b, wildcard, ctx),
                                                ),
                                                Type::App(f, a) => Type::app(
                                                    replace_wildcards(f, wildcard, ctx),
                                                    replace_wildcards(a, wildcard, ctx),
                                                ),
                                                Type::Forall(vars, body) => Type::Forall(
                                                    vars.clone(),
                                                    Box::new(replace_wildcards(body, wildcard, ctx)),
                                                ),
                                                Type::Record(fields, tail) => Type::Record(
                                                    fields.iter().map(|(l, t)| (*l, replace_wildcards(t, wildcard, ctx))).collect(),
                                                    tail.as_ref().map(|t| Box::new(replace_wildcards(t, wildcard, ctx))),
                                                ),
                                                other => other.clone(),
                                            }
                                        }
                                        sig_ty = replace_wildcards(&sig_ty, wildcard_sym, &mut ctx);
                                        // Unify the declared instance sig with the class-derived type
                                        if let Err(e) =
                                            ctx.state.unify(*sig_span, &sig_ty, &expected_ty)
                                        {
                                            errors.push(e);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // Collect free type variables from instance head and constraints for scoped type variables.
                // E.g., for `instance foo :: GetVar l { | varL } => GetVar (Spread l) { | var }`,
                // both `l`, `var`, and `varL` are in scope within method bodies.
                let mut inst_scoped_vars: HashSet<Symbol> = HashSet::new();
                fn collect_free_vars_inst(ty: &Type, vars: &mut HashSet<Symbol>) {
                    match ty {
                        Type::Var(v) => {
                            vars.insert(*v);
                        }
                        Type::Fun(a, b) | Type::App(a, b) => {
                            collect_free_vars_inst(a, vars);
                            collect_free_vars_inst(b, vars);
                        }
                        Type::Forall(_, body) => collect_free_vars_inst(body, vars),
                        Type::Record(fields, tail) => {
                            for (_, t) in fields {
                                collect_free_vars_inst(t, vars);
                            }
                            if let Some(t) = tail {
                                collect_free_vars_inst(t, vars);
                            }
                        }
                        _ => {}
                    }
                }
                for ty in inst_subst.values() {
                    collect_free_vars_inst(ty, &mut inst_scoped_vars);
                }
                inst_scoped_vars.extend(constraint_scoped_vars.iter().copied());

                // Collect instance method type signatures for scoped type variables.
                // When a method has an explicit annotation like `compare1 :: forall a. ...`,
                // the forall-bound vars should be in scope in where-clause annotations.
                let mut method_sig_vars: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
                for member_decl in members {
                    if let Decl::TypeSignature { name, ty, .. } = member_decl {
                        let mut vars = HashSet::new();
                        fn collect_forall_vars_from_type_expr(ty: &TypeExpr, vars: &mut HashSet<Symbol>) {
                            match ty {
                                TypeExpr::Forall { vars: forall_vars, ty, .. } => {
                                    for (v, _, _) in forall_vars {
                                        vars.insert(v.value);
                                    }
                                    collect_forall_vars_from_type_expr(ty, vars);
                                }
                                TypeExpr::Constrained { ty, .. } => {
                                    collect_forall_vars_from_type_expr(ty, vars);
                                }
                                _ => {}
                            }
                        }
                        collect_forall_vars_from_type_expr(ty, &mut vars);
                        if !vars.is_empty() {
                            method_sig_vars.insert(name.value, vars);
                        }
                    }
                }

                // Collect instance method bodies for deferred checking (after foreign imports
                // and fixity declarations are processed, so all values are in scope)
                // Build instance constraints for codegen constraint parameter tracking
                let inst_constraints_for_codegen: Vec<(QualifiedIdent, Vec<Type>)> = constraints.iter().filter_map(|c| {
                    let mut args = Vec::new();
                    for arg in &c.args {
                        match convert_type_expr(arg, &type_ops) {
                            Ok(ty) => args.push(ty),
                            Err(_) => return None,
                        }
                    }
                    Some((c.class, args))
                }).collect();
                let mut method_names: Vec<Symbol> = Vec::new();
                for member_decl in members {
                    if let Decl::Value {
                        name,
                        span,
                        binders,
                        guarded,
                        where_clause,
                        ..
                    } = member_decl
                    {
                        // Compute the expected type for instance methods from class definition.
                        // Use class_method_schemes (not env.lookup) so that an explicit value
                        // import like `import Data.Array (foldl)` doesn't shadow the class
                        // method's canonical type used for instance checking.
                        let expected_ty = if inst_ok && !inst_subst.is_empty()
                        {
                            let canon = ctx.class_method_schemes.get(&name.value)
                                .map(|s| s.ty.clone())
                                .or_else(|| env.lookup(name.value).map(|s| s.ty.clone()));
                            if let Some(class_ty) = canon {
                                // Strip outer forall (class type vars)
                                let inner = match &class_ty {
                                    Type::Forall(_, body) => (**body).clone(),
                                    other => other.clone(),
                                };
                                // Apply class type var substitution
                                let substituted = apply_var_subst(&inst_subst, &inner);
                                // Instantiate method-level forall and remaining free type vars
                                // with fresh unif vars.
                                let instantiated = instantiate_all_vars(&mut ctx, substituted);
                                Some(instantiated)
                            } else {
                                None
                            }
                        } else {
                            None
                        };

                        // Include forall-bound vars from the method's explicit type annotation
                        let mut method_scoped = inst_scoped_vars.clone();
                        if let Some(sig_vars) = method_sig_vars.get(&name.value) {
                            method_scoped.extend(sig_vars);
                        }

                        let inst_given_classes: HashSet<QualifiedIdent> =
                            constraints.iter().map(|c| c.class).collect();
                        method_names.push(name.value);
                        deferred_instance_methods.push((
                            name.value,
                            *span,
                            binders as &[_],
                            guarded,
                            where_clause as &[_],
                            expected_ty,
                            method_scoped,
                            inst_given_classes,
                            next_instance_id,
                            inst_constraints_for_codegen.clone(),
                        ));
                    }
                }
                next_instance_id += 1;
                if method_names.len() > 1 {
                    instance_method_groups.push(method_names);
                }
            }
            Decl::Fixity { is_type, .. } => {
                if !*is_type {
                    // Value-level fixity: deferred to after Pass 2 so the target
                    // function's type is available in env.
                }
            }
            Decl::TypeAlias {
                span,
                name,
                type_vars,
                ty,
                ..
            } => {
                has_real_definition.insert(name.value);
                has_type_alias_def.insert(name.value);
                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Reject type wildcards in type alias bodies
                if let Some(wc_span) = find_wildcard_span(ty) {
                    errors.push(TypeError::SyntaxError { span: wc_span });
                }

                // Convert and register type alias for expansion during unification.
                match convert_type_expr(ty, &type_ops) {
                    Ok(body_ty) => {
                        // Check for partially applied synonyms in the body
                        check_type_for_partial_synonyms_with_arities(
                            &body_ty,
                            &ctx.state.type_aliases,
                            &ctx.type_con_arities,
                            &ctx.record_type_aliases,
                            *span,
                            &mut errors,
                        );
                        let params: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                        // Check that free type variables in the body are all declared parameters
                        let param_set: HashSet<Symbol> = params.iter().copied().collect();
                        let wildcard_sym = crate::interner::intern("_");
                        for fv in free_named_type_vars(&body_ty) {
                            if fv != wildcard_sym && !param_set.contains(&fv) {
                                errors.push(TypeError::UndefinedTypeVariable {
                                    span: *span,
                                    name: fv,
                                });
                            }
                        }
                        // For re-exported aliases, resolve the body using the
                        // already-imported expanded alias.
                        let resolved_body = if is_alias_reexport(&body_ty, name.value, &params) {
                            if let Some((existing_params, existing_body)) = ctx.state.type_aliases.get(&name.value) {
                                if existing_params.len() == params.len() && !matches!(existing_body, Type::Con(_)) {
                                    existing_body.clone()
                                } else {
                                    body_ty
                                }
                            } else {
                                body_ty
                            }
                        } else {
                            body_ty
                        };
                        ctx.state.type_aliases.insert(name.value, (params, resolved_body));
                        // Track if this is a record-kind alias (body is { } syntax, kind Type)
                        if matches!(ty, TypeExpr::Record { .. }) {
                            ctx.record_type_aliases.insert(qi(name.value));
                        }
                    }
                    Err(e) => {
                        if type_vars.is_empty() {
                            errors.push(e);
                        }
                        // Aliases with type vars may reference those vars as "unknown types";
                        // skip the error since the vars are just parameters
                    }
                }
                // Collect for cycle detection
                type_alias_defs.insert(name.value, (*span, ty));
            }
            Decl::ForeignData { name, .. } => {
                has_real_definition.insert(name.value);
                has_data_def.insert(name.value);
                // Register foreign data types in data_constructors so they can be imported
                // as types (e.g. `import Data.Unit (Unit)`). They have no constructors.
                ctx.data_constructors.insert(qi(name.value), Vec::new());
            }
            Decl::Derive {
                span,
                newtype,
                name: derive_inst_name,
                class_name,
                types,
                constraints,
                ..
            } => {
                // Check if the class exists
                let derive_class_known = class_param_counts.contains_key(class_name)
                    || instances.contains_key(class_name)
                    || local_class_names.contains(&class_name.name);
                if !derive_class_known && class_name.module.is_none() {
                    errors.push(TypeError::UnknownClass {
                        span: *span,
                        name: *class_name,
                    });
                }

                // Check for invalid instance heads: bare record/row/function types
                // at the top level of type arguments (wildcards are ok in derive, e.g. Newtype T _).
                // For `derive newtype instance`, records and functions are allowed as class
                // parameters (e.g. `derive newtype instance MonadAsk {} TestM`).
                // For plain `derive instance`, records and functions are invalid.
                for ty_expr in types {
                    let is_invalid = if *newtype {
                        // derive newtype: only reject bare row types
                        matches!(ty_expr, TypeExpr::Row { .. })
                    } else {
                        // derive: reject records, rows, and functions
                        matches!(
                            ty_expr,
                            TypeExpr::Record { .. } | TypeExpr::Row { .. } | TypeExpr::Function { .. }
                        )
                    };
                    if is_invalid {
                        errors.push(TypeError::InvalidInstanceHead { span: *span });
                        break;
                    }
                }

                // Extract the target type name from the type arguments.
                // Try the last arg first (for multi-param classes like FunctorWithIndex Int NonEmptyArray,
                // the newtype is the last arg), then fall back to any arg with a constructor head
                // (e.g. `derive instance Newtype (Pair Int Int) _` where last arg is wildcard).
                let target_type_name = types
                    .last()
                    .and_then(|t| extract_head_constructor(t))
                    .or_else(|| types.iter().rev().find_map(|t| extract_head_constructor(t)));

                // ExpectedWildcard: derive instance Newtype X String
                // where the second arg should be a wildcard (_), not a concrete type.
                let newtype_ident = crate::interner::intern("Newtype");
                if class_name.name == newtype_ident && types.len() >= 2 {
                    if !matches!(types.last(), Some(TypeExpr::Wildcard { .. })) {
                        errors.push(TypeError::ExpectedWildcard {
                            span: *span,
                            name: class_name.clone(),
                        });
                    }
                }

                if let Some(target_name) = target_type_name {
                    let is_newtype = ctx.newtype_names.contains(&target_name)
                        || ctx.newtype_names.iter().any(|n| n.name == target_name.name);

                    // InvalidNewtypeInstance: derive instance Newtype X _
                    // where X is not actually a newtype
                    if class_name.name == newtype_ident && !is_newtype
                    {
                        errors.push(TypeError::InvalidNewtypeInstance {
                            span: *span,
                            name: target_name,
                        });
                    }

                    // InvalidNewtypeDerivation: derive newtype instance SomeClass X
                    // where X is not actually a newtype
                    if *newtype && !is_newtype {
                        errors.push(TypeError::InvalidNewtypeDerivation {
                            span: *span,
                            name: target_name,
                        });
                    }

                    // InvalidNewtypeInstance: derive newtype instance Functor X
                    // where X's inner type is a bare type variable (e.g. `newtype X a = X a`).
                    // Only when the target is unapplied (bare constructor), because when
                    // applied (e.g. `N S`), the type var is substituted with concrete type.
                    if *newtype && is_newtype {
                        let target_is_bare = types.iter().any(|t| {
                            matches!(t, TypeExpr::Constructor { name, .. } if *name == target_name)
                        });
                        if target_is_bare {
                            if let Some(ctors) = ctx.data_constructors.get(&target_name) {
                                if let Some(ctor_name) = ctors.first() {
                                    if let Some((_, _, field_types)) =
                                        ctx.ctor_details.get(ctor_name)
                                    {
                                        if let Some(inner_ty) = field_types.first() {
                                            if matches!(inner_ty, Type::Var(_)) {
                                                errors.push(TypeError::InvalidNewtypeInstance {
                                                    span: *span,
                                                    name: target_name.clone(),
                                                });
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if *newtype {
                    // derive newtype instance with no type arguments (e.g. derive newtype instance Nullary)
                    // — there's no target type to be a newtype
                    errors.push(TypeError::InvalidNewtypeInstance {
                        span: *span,
                        name: class_name.clone(),
                    });
                }

                // Register derived instance types and constraints for instance resolution
                let mut inst_types = Vec::new();
                let mut inst_ok = true;
                for ty_expr in types {
                    match convert_type_expr(ty_expr, &type_ops) {
                        Ok(ty) => inst_types.push(ty),
                        Err(_) => {
                            inst_ok = false;
                            break;
                        }
                    }
                }
                // Check derived instance arity matches class parameter count
                if inst_ok {
                    if let Some(&expected_count) = class_param_counts.get(&class_name) {
                        if expected_count != usize::MAX && inst_types.len() != expected_count {
                            errors.push(TypeError::ClassInstanceArityMismatch {
                                span: *span,
                                class_name: *class_name,
                                expected: expected_count,
                                found: inst_types.len(),
                            });
                            inst_ok = false;
                        }
                    }
                }
                // Check for partially applied synonyms in derived instance types
                if inst_ok {
                    for inst_ty in &inst_types {
                        check_type_for_partial_synonyms_with_arities(
                            inst_ty,
                            &ctx.state.type_aliases,
                            &ctx.type_con_arities,
                            &ctx.record_type_aliases,
                            *span,
                            &mut errors,
                        );
                    }
                }
                // Check for non-nominal types in derived instance heads (records, functions,
                // or type synonyms expanding to them). Derive requires a data/newtype.
                // For derive newtype, records and functions are allowed as class parameters.
                if inst_ok {
                    for inst_ty in &inst_types {
                        if is_non_nominal_for_derive(inst_ty, &ctx.state.type_aliases, &ctx.data_constructors, *newtype) {
                            errors.push(TypeError::InvalidInstanceHead { span: *span });
                            inst_ok = false;
                            break;
                        }
                    }
                }
                // Orphan check for derived instances.
                // First check unexpanded types — if any type constructor in the instance head
                // is locally defined (data/newtype), it's not orphan. This prevents false
                // positives when imported type aliases share the same unqualified name as
                // a locally-defined data type (e.g. `Mutex` newtype vs imported `Mutex` alias).
                // Only fall through to expanded checking if unexpanded check doesn't find a local type.
                if inst_ok && class_name.module.is_none() {
                    let class_is_local = local_class_names.contains(&class_name.name);
                    if !class_is_local {
                        // Check unexpanded types first, using only data/newtype names
                        // (not type aliases, which are transparent for orphan checking).
                        let is_orphan_unexpanded = check_orphan_with_fundeps(
                            &inst_types,
                            &class_name,
                            &ctx.class_fundeps,
                            &local_data_type_names,
                        );
                        // Only expand and re-check if unexpanded check says orphan
                        let is_orphan = if is_orphan_unexpanded {
                            let expanded: Vec<Type> = inst_types
                                .iter()
                                .map(|t| expand_type_aliases(t, &ctx.state.type_aliases))
                                .collect();
                            check_orphan_with_fundeps(
                                &expanded,
                                &class_name,
                                &ctx.class_fundeps,
                                &local_type_names,
                            )
                        } else {
                            false
                        };
                        if is_orphan {
                            errors.push(TypeError::OrphanInstance {
                                span: *span,
                                class_name: *class_name,
                            });
                        }
                    }
                }
                // Check non-newtype derive for types with open record rows.
                // For Eq, Ord, etc., deriving requires instances on all record fields.
                // If a constructor field is a record with an open row variable (e.g. { | r }),
                // the required instances can't be guaranteed. (PureScript issue #2616)
                if inst_ok && !*newtype {
                    let eq_sym = crate::interner::intern("Eq");
                    let ord_sym = crate::interner::intern("Ord");
                    if class_name.name == eq_sym || class_name.name == ord_sym {
                        if let Some(target_name) = target_type_name {
                            // Extract type args applied to the target type in the instance head
                            let derive_args = if let Some(last_inst_ty) = inst_types.last() {
                                let mut head = last_inst_ty;
                                let mut args = Vec::new();
                                while let Type::App(f, a) = head {
                                    args.push(a.as_ref().clone());
                                    head = f.as_ref();
                                }
                                args.reverse();
                                args
                            } else {
                                Vec::new()
                            };
                            if let Some(ctors) = ctx.data_constructors.get(&target_name) {
                                'open_row_check: for ctor in ctors {
                                    if let Some((_, type_vars, field_types)) =
                                        ctx.ctor_details.get(ctor)
                                    {
                                        // Build substitution from data-decl type vars to instance args
                                        let subst: HashMap<Symbol, Type> = type_vars
                                            .iter()
                                            .zip(derive_args.iter())
                                            .map(|(v, t)| (*v, t.clone()))
                                            .collect();
                                        for field_ty in field_types {
                                            let concrete = apply_var_subst(&subst, field_ty);
                                            if has_open_record_row(&concrete) {
                                                errors.push(TypeError::NoInstanceFound {
                                                    span: *span,
                                                    class_name: class_name.clone(),
                                                    type_args: inst_types.clone(),
                                                });
                                                inst_ok = false;
                                                break 'open_row_check;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // Check derive constructor argument validity for variance-sensitive classes
                // (Functor, Foldable, Traversable, Contravariant, Bifunctor, Profunctor, etc.)
                if inst_ok && !*newtype {
                    if let Some(target_name) = target_type_name {
                        let functor_sym = crate::interner::intern("Functor");
                        let foldable_sym = crate::interner::intern("Foldable");
                        let traversable_sym = crate::interner::intern("Traversable");
                        let contravariant_sym = crate::interner::intern("Contravariant");
                        let bifunctor_sym = crate::interner::intern("Bifunctor");
                        let profunctor_sym = crate::interner::intern("Profunctor");

                        // Build list of (type_var_index_from_end, want_covariant) checks
                        // based on which class is being derived
                        let mut var_checks: Vec<(usize, bool)> = Vec::new();

                        if class_name.name == functor_sym
                            || class_name.name == foldable_sym
                            || class_name.name == traversable_sym
                        {
                            // Single covariant: last var must be covariant
                            var_checks.push((0, true));
                        } else if class_name.name == contravariant_sym {
                            // Single contravariant: last var must be contravariant
                            var_checks.push((0, false));
                        } else if class_name.name == bifunctor_sym {
                            // Both last two vars must be covariant
                            var_checks.push((0, true));
                            var_checks.push((1, true));
                        } else if class_name.name == profunctor_sym {
                            // Last var covariant, second-to-last contravariant
                            var_checks.push((0, true));
                            var_checks.push((1, false));
                        }

                        if !var_checks.is_empty() {
                            // Foldable/Traversable can't derive through forall types
                            // (can't extract values from quantified types), but
                            // Functor/Contravariant/Bifunctor/Profunctor can (wrap in lambda)
                            let allow_forall = class_name.name != foldable_sym
                                && class_name.name != traversable_sym;

                            // Build type variable → class constraint map from derive constraints
                            let mut tyvar_classes: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
                            for constraint in constraints {
                                // Extract type vars from constraint args (e.g. `Functor f` → f → [Functor])
                                for arg in &constraint.args {
                                    if let crate::ast::TypeExpr::Var { name, .. } = arg {
                                        tyvar_classes
                                            .entry(name.value)
                                            .or_default()
                                            .push(constraint.class.name);
                                    }
                                }
                            }

                            // Build substitution from data declaration type vars
                            // to instance type arguments, so that constraint lookups
                            // use the instance's variable names.
                            // E.g. for `data T key a = ...` with `derive instance Functor k => Functor (T k)`,
                            // we substitute `key → k` in field types.
                            let derive_subst = if let Some(last_inst_ty) = inst_types.last() {
                                let mut inst_head = last_inst_ty;
                                let mut inst_args = Vec::new();
                                while let Type::App(f, a) = inst_head {
                                    inst_args.push(a.as_ref().clone());
                                    inst_head = f.as_ref();
                                }
                                inst_args.reverse();
                                inst_args
                            } else {
                                Vec::new()
                            };

                            if let Some(ctors) = ctx.data_constructors.get(&target_name) {
                                'ctor_check: for ctor in ctors {
                                    if let Some((_, type_vars, field_types)) =
                                        ctx.ctor_details.get(ctor)
                                    {
                                        // Build field substitution: map data-decl vars to instance args
                                        let num_derived = var_checks
                                            .iter()
                                            .map(|(off, _)| off + 1)
                                            .max()
                                            .unwrap_or(1);
                                        let num_non_derived =
                                            type_vars.len().saturating_sub(num_derived);
                                        let mut field_subst: HashMap<Symbol, Type> = HashMap::new();
                                        for i in
                                            0..std::cmp::min(num_non_derived, derive_subst.len())
                                        {
                                            field_subst
                                                .insert(type_vars[i], derive_subst[i].clone());
                                        }

                                        for &(offset, want_covariant) in &var_checks {
                                            if offset >= type_vars.len() {
                                                continue;
                                            }
                                            let var = type_vars[type_vars.len() - 1 - offset];
                                            for field_ty in field_types {
                                                let expanded_ty = expand_type_aliases(
                                                    field_ty,
                                                    &ctx.state.type_aliases,
                                                );
                                                let subst_ty = if field_subst.is_empty() {
                                                    expanded_ty
                                                } else {
                                                    apply_var_subst(&field_subst, &expanded_ty)
                                                };
                                                if type_var_occurs_in(var, &subst_ty) {
                                                    let pos_result = check_derive_position(
                                                        &subst_ty,
                                                        var,
                                                        true, // start in positive position
                                                        want_covariant,
                                                        allow_forall,
                                                        &instances,
                                                        &tyvar_classes,
                                                        &ctx.ctor_details,
                                                        &ctx.data_constructors,
                                                        &local_concrete_type_names,
                                                        0,
                                                    );
                                                    if !pos_result {
                                                        errors.push(TypeError::CannotDeriveInvalidConstructorArg {
                                                            span: *span,
                                                        });
                                                        inst_ok = false;
                                                        break 'ctor_check;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                let mut inst_constraints: Vec<(QualifiedIdent, Vec<Type>)> = Vec::new();
                if inst_ok {
                    for constraint in constraints {
                        let mut c_args = Vec::new();
                        let mut c_ok = true;
                        for arg in &constraint.args {
                            match convert_type_expr(arg, &type_ops) {
                                Ok(ty) => c_args.push(ty),
                                Err(_) => {
                                    c_ok = false;
                                    inst_ok = false;
                                    break;
                                }
                            }
                        }
                        if c_ok {
                            inst_constraints.push((constraint.class, c_args));
                        }
                    }
                }
                // For `derive instance Generic T _`, compute the rep type from constructors
                // and replace the wildcard with the concrete representation type.
                if inst_ok {
                    let generic_sym = crate::interner::intern("Generic");
                    if class_name.name == generic_sym {
                        if let Some(target_name) = target_type_name {
                            let wildcard_sym = crate::interner::intern("_");
                            if inst_types.iter().any(|t| matches!(t, Type::Var(v) if *v == wildcard_sym)) {
                                if let Some(rep_type) = compute_generic_rep_type(
                                    &target_name,
                                    &ctx.data_constructors,
                                    &ctx.ctor_details,
                                ) {
                                    for ty in inst_types.iter_mut() {
                                        if matches!(ty, Type::Var(v) if *v == wildcard_sym) {
                                            *ty = rep_type.clone();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if inst_ok {
                    registered_instances.push((*span, class_name.name, inst_types.clone()));
                    // Populate instance_registry for codegen dict resolution (same as Decl::Instance)
                    if let Some(iname) = derive_inst_name {
                        for head in extract_all_head_type_cons(&inst_types) {
                            instance_registry_entries
                                .entry((class_name.name, head))
                                .or_insert(iname.value);
                        }
                        let module_parts: Vec<Symbol> = module.name.value.parts.clone();
                        instance_module_entries.insert(iname.value, module_parts);
                    } else {
                        // Anonymous derive instances: generate a name for codegen dict resolution.
                        // Mirrors the logic for anonymous Decl::Instance (above).
                        let all_heads = extract_all_head_type_cons(&inst_types);
                        if !all_heads.is_empty() {
                            let class_str = crate::interner::resolve(class_name.name).unwrap_or_default().to_string();
                            let mut gen_name = String::new();
                            for (i, c) in class_str.chars().enumerate() {
                                if i == 0 {
                                    gen_name.extend(c.to_lowercase());
                                } else {
                                    gen_name.push(c);
                                }
                            }
                            for ty in &inst_types {
                                gen_name.push_str(&type_to_instance_name_part(ty));
                            }
                            let gen_sym = crate::interner::intern(&gen_name);
                            for h in &all_heads {
                                instance_registry_entries
                                    .entry((class_name.name, *h))
                                    .or_insert(gen_sym);
                            }
                            let module_parts: Vec<Symbol> = module.name.value.parts.clone();
                            instance_module_entries.insert(gen_sym, module_parts);
                        }
                    }
                    let inst_name_sym = derive_inst_name.as_ref().map(|n| n.value);
                    instances
                        .entry(qi(class_name.name))
                        .or_default()
                        .push((inst_types, inst_constraints, inst_name_sym));
                }
            }
            Decl::Value { .. } => {
                // Handled in Pass 2
            }
        }
        timed_pass!(1, format!("end decl {}", decl_name), decl.span());
    }

    // Check for orphan kind declarations (kind sig without matching definition)
    // A kind sig is orphaned if there's no matching definition of the RIGHT kind:
    // - `data Foo :: Kind` needs a `data Foo = ...` or `foreign import data Foo :: ...`
    // - `type Foo :: Kind` needs a `type Foo = ...`
    // - `newtype Foo :: Kind` needs a `newtype Foo = ...`
    // - `class Foo :: Kind` needs a `class Foo where ...`
    for (name, (span, source)) in &kind_sigs {
        let has_matching = match source {
            KindSigSource::Data => has_data_def.contains(name),
            KindSigSource::Type => has_type_alias_def.contains(name),
            KindSigSource::Newtype => has_newtype_def.contains(name),
            KindSigSource::Class => has_class_def.contains(name),
            KindSigSource::None => true, // shouldn't happen
        };
        if !has_matching {
            errors.push(TypeError::OrphanKindDeclaration {
                span: *span,
                name: *name,
            });
        }
    }

    // Count the number of top-level function arrows in a kind signature.
    // e.g. `Type -> Type -> Type` has arity 2, `Type` has arity 0.
    fn count_kind_arity(kind: &TypeExpr) -> usize {
        match kind {
            TypeExpr::Function { to, .. } => 1 + count_kind_arity(to),
            TypeExpr::Forall { ty, .. } => count_kind_arity(ty),
            _ => 0,
        }
    }

    // Check role declarations: must immediately follow their data/foreign data definition,
    // cannot be duplicated, and must match arity.
    {
        // (name, kind: "data"/"foreign"/"synonym"/"class", arity)
        let mut prev_decl: Option<(Symbol, &str, usize)> = None;
        let mut prev_was_role_for: Option<Symbol> = None;
        for decl in &module.decls {
            match decl {
                Decl::Data {
                    name,
                    type_vars,
                    is_role_decl: true,
                    kind_sig,
                    ..
                } => {
                    if *kind_sig != KindSigSource::None {
                        prev_decl = None;
                        prev_was_role_for = None;
                        continue;
                    }
                    let role_name = name.value;
                    let role_span = name.span;
                    let role_count = type_vars.len();
                    // Check for duplicate role declaration
                    if let Some(prev_role_name) = prev_was_role_for {
                        if prev_role_name == role_name {
                            errors.push(TypeError::DuplicateRoleDeclaration {
                                span: role_span,
                                name: role_name,
                            });
                            prev_was_role_for = Some(role_name);
                            continue;
                        }
                    }
                    // Check that the immediately preceding decl is a matching data/foreign data
                    match prev_decl {
                        Some((prev_name, kind, arity)) if prev_name == role_name => {
                            if kind != "data" && kind != "foreign" {
                                errors.push(TypeError::UnsupportedRoleDeclaration {
                                    span: role_span,
                                    name: role_name,
                                });
                            } else if role_count != arity {
                                errors.push(TypeError::RoleDeclarationArityMismatch {
                                    span: role_span,
                                    name: role_name,
                                    expected: arity,
                                    found: role_count,
                                });
                            } else {
                                // Valid role declaration — store the roles
                                let roles: Vec<Role> = type_vars
                                    .iter()
                                    .map(|tv| {
                                        match crate::interner::resolve(tv.value)
                                            .unwrap_or_default()
                                            .as_str()
                                        {
                                            "nominal" => Role::Nominal,
                                            "representational" => Role::Representational,
                                            "phantom" | _ => Role::Phantom,
                                        }
                                    })
                                    .collect();
                                ctx.type_roles.insert(role_name, roles);
                            }
                        }
                        _ => {
                            errors.push(TypeError::OrphanRoleDeclaration {
                                span: role_span,
                                name: role_name,
                            });
                        }
                    };
                    prev_was_role_for = Some(role_name);
                    prev_decl = None;
                }
                Decl::Data {
                    name,
                    type_vars,
                    is_role_decl: false,
                    kind_sig,
                    ..
                } => {
                    if *kind_sig == KindSigSource::None {
                        prev_decl = Some((name.value, "data", type_vars.len()));
                    } else {
                        prev_decl = None;
                    }
                    prev_was_role_for = None;
                }
                Decl::Newtype {
                    name, type_vars, ..
                } => {
                    prev_decl = Some((name.value, "data", type_vars.len()));
                    prev_was_role_for = None;
                }
                Decl::ForeignData { name, kind, .. } => {
                    let arity = count_kind_arity(kind);
                    prev_decl = Some((name.value, "foreign", arity));
                    prev_was_role_for = None;
                }
                Decl::TypeAlias {
                    name, type_vars, ..
                } => {
                    prev_decl = Some((name.value, "synonym", type_vars.len()));
                    prev_was_role_for = None;
                }
                Decl::Class {
                    name, type_vars, ..
                } => {
                    prev_decl = Some((name.value, "class", type_vars.len()));
                    prev_was_role_for = None;
                }
                _ => {
                    prev_decl = None;
                    prev_was_role_for = None;
                }
            }
        }
    }

    // Infer roles for types without explicit role declarations, and validate declared roles.
    {
        // Collect constructor field info for role inference:
        // For each data type / newtype, map type_name → (type_var_names, [field_types_per_ctor])
        let mut type_ctor_fields: HashMap<Symbol, (Vec<Symbol>, Vec<Vec<Type>>)> = HashMap::new();
        // Also collect CST field types to scan for constrained vars (constraints are
        // stripped during convert_type_expr, but affect role inference — any type var
        // in a constraint position must be nominal).
        let mut type_cst_fields: HashMap<Symbol, Vec<&crate::ast::TypeExpr>> = HashMap::new();
        for decl in &module.decls {
            match decl {
                Decl::Data {
                    name,
                    type_vars,
                    constructors,
                    kind_sig,
                    is_role_decl,
                    ..
                } => {
                    if *is_role_decl || *kind_sig != KindSigSource::None {
                        continue;
                    }
                    let tvs: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                    let mut cst_fields = Vec::new();
                    let ctor_fields: Vec<Vec<Type>> = constructors
                        .iter()
                        .map(|c| {
                            c.fields
                                .iter()
                                .filter_map(|f| {
                                    cst_fields.push(f);
                                    convert_type_expr(f, &type_ops).ok()
                                })
                                .collect()
                        })
                        .collect();
                    type_cst_fields.insert(name.value, cst_fields);
                    type_ctor_fields.insert(name.value, (tvs, ctor_fields));
                }
                Decl::Newtype {
                    name,
                    type_vars,
                    ty,
                    ..
                } => {
                    let tvs: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                    if let Ok(field_ty) = convert_type_expr(ty, &type_ops) {
                        type_cst_fields.insert(name.value, vec![ty]);
                        type_ctor_fields.insert(name.value, (tvs, vec![vec![field_ty]]));
                    }
                }
                Decl::ForeignData { name, kind, .. } => {
                    // Foreign types without role declarations default to Nominal
                    // (matches PureScript behavior: foreign types are opaque, so all
                    // type params are assumed Nominal for safety)
                    let arity = count_kind_arity(kind);
                    if arity > 0 && !ctx.type_roles.contains_key(&name.value) {
                        ctx.type_roles
                            .insert(name.value, vec![Role::Nominal; arity]);
                    }
                }
                _ => {}
            }
        }

        // Track which types have explicitly declared roles (from `type role` declarations)
        let declared_role_types: HashSet<Symbol> = ctx.type_roles.keys().copied().collect();

        // Pre-initialize all non-declared types with Phantom roles.
        // This is essential for mutually recursive types: without it, looking up
        // a not-yet-computed type defaults to Representational, which propagates
        // incorrectly. Starting from Phantom and iterating upward gives the correct
        // least-restrictive fixed point.
        for (type_name, (type_vars, _)) in &type_ctor_fields {
            if !declared_role_types.contains(type_name) {
                ctx.type_roles
                    .insert(*type_name, vec![Role::Phantom; type_vars.len()]);
            }
        }

        // Iterate to a fixed point for mutually recursive types (limited iterations)
        for _ in 0..10 {
            let mut changed = false;
            for (type_name, (type_vars, ctor_fields)) in &type_ctor_fields {
                if declared_role_types.contains(type_name) {
                    // Already has declared roles; skip inference (will validate below)
                    continue;
                }
                let mut inferred = infer_roles_from_fields(type_vars, ctor_fields, &ctx.type_roles);
                // Also mark type vars in constraint positions as nominal
                if let Some(cst_fields) = type_cst_fields.get(type_name) {
                    for field_te in cst_fields {
                        mark_constrained_vars_nominal_cst(
                            field_te,
                            type_vars,
                            &mut inferred,
                            &HashSet::new(),
                        );
                    }
                }
                let existing = ctx.type_roles.get(type_name);
                if existing.map_or(true, |e| e != &inferred) {
                    ctx.type_roles.insert(*type_name, inferred);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        // Validate declared roles: declared role must be >= inferred role.
        // A declared role less restrictive than what the type actually needs is a RoleMismatch.
        for (type_name, (type_vars, ctor_fields)) in &type_ctor_fields {
            let declared = match ctx.type_roles.get(type_name) {
                Some(d) => d.clone(),
                None => continue,
            };
            // Re-infer with current known roles to get what the type actually needs
            let mut inferred = infer_roles_from_fields(type_vars, ctor_fields, &ctx.type_roles);
            if let Some(cst_fields) = type_cst_fields.get(type_name) {
                for field_te in cst_fields {
                    mark_constrained_vars_nominal_cst(
                        field_te,
                        type_vars,
                        &mut inferred,
                        &HashSet::new(),
                    );
                }
            }
            for (decl_role, inferred_role) in declared.iter().zip(inferred.iter()) {
                if *decl_role < *inferred_role {
                    // Find the span for this type's role declaration
                    for d in &module.decls {
                        if let Decl::Data {
                            name,
                            is_role_decl: true,
                            kind_sig,
                            ..
                        } = d
                        {
                            if *kind_sig == KindSigSource::None && name.value == *type_name {
                                errors.push(TypeError::RoleMismatch {
                                    span: name.span,
                                    name: *type_name,
                                });
                                break;
                            }
                        }
                    }
                    break; // Only one error per type
                }
            }
        }
    }

    // Check for cycles in type synonyms
    check_type_synonym_cycles(&type_alias_defs, &mut errors);

    // Check for cycles in kind declarations (data kind sigs and foreign data kinds)
    {
        let mut kind_decls: HashMap<Symbol, (Span, &crate::ast::TypeExpr)> = HashMap::new();
        for decl in &module.decls {
            match decl {
                Decl::Data {
                    name,
                    kind_sig,
                    kind_type: Some(kind_ty),
                    ..
                } if *kind_sig != KindSigSource::None => {
                    kind_decls.insert(name.value, (name.span, kind_ty));
                }
                Decl::ForeignData { name, kind, .. } => {
                    kind_decls.insert(name.value, (name.span, kind));
                }
                _ => {}
            }
        }
        if !kind_decls.is_empty() {
            let kind_names: HashSet<Symbol> = kind_decls.keys().copied().collect();
            let mut deps: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
            for (&name, (_, ty)) in &kind_decls {
                let mut refs = HashSet::new();
                collect_type_refs(ty, &mut refs);
                deps.insert(name, refs.intersection(&kind_names).copied().collect());
            }
            let mut visited = HashSet::new();
            let mut on_stack = HashSet::new();
            for &name in kind_decls.keys() {
                if !visited.contains(&name) {
                    let mut path = Vec::new();
                    if let Some(cycle) =
                        dfs_find_cycle(name, &deps, &mut visited, &mut on_stack, &mut path)
                    {
                        let (span, _) = kind_decls[&name];
                        let cycle_spans: Vec<Span> = cycle
                            .iter()
                            .filter_map(|n| kind_decls.get(n).map(|(s, _)| *s))
                            .collect();
                        errors.push(TypeError::CycleInKindDeclaration {
                            name,
                            span,
                            names_in_cycle: cycle.clone(),
                            spans: cycle_spans,
                        });
                    }
                }
            }
        }
    }

    // Check for cycles in type class superclass declarations
    check_type_class_cycles(&class_defs, &mut errors);

    // Check for duplicate class declarations
    for (name, spans) in &seen_classes {
        if spans.len() > 1 {
            errors.push(TypeError::DuplicateTypeClass {
                spans: spans.clone(),
                name: *name,
            });
        }
    }

    // Check for duplicate named instance declarations
    for (name, spans) in &seen_instance_names {
        if spans.len() > 1 {
            errors.push(TypeError::DuplicateInstance {
                spans: spans.clone(),
                name: *name,
            });
        }
    }

    // Copy type_con_arities to UnifyState for alias/data-type disambiguation in try_expand_alias.
    ctx.state.type_con_arities = ctx.type_con_arities.clone();
    // Pre-compute which aliases are transitively self-referential (e.g., Codec → Codec' → Codec).
    // This prevents infinite re-expansion loops during unification.
    ctx.state.compute_self_referential_aliases();
    // Pass 1.5: Process value-level fixity declarations whose targets are already
    // in local_values or env (class methods, data constructors, imported values).
    // This must happen before Pass 2 so operators like `==`, `<`, `+`, `/\` are available.
    for decl in &module.decls {
        if let Decl::Fixity {
            target,
            operator,
            is_type: false,
            ..
        } = decl
        {
            if let Some(scheme) = local_values.get(&target.name).cloned() {
                env.insert_scheme(operator.value, scheme.clone());
                local_values.insert(operator.value, scheme);
            } else if let Some(scheme) = env.lookup(target.name).cloned() {
                // Only use env fallback if scheme has no unresolved unif vars
                // (imported schemes are fully resolved; local failures have raw unif vars)
                if ctx.state.free_unif_vars(&scheme.ty).is_empty() {
                    env.insert_scheme(operator.value, scheme.clone());
                    local_values.insert(operator.value, scheme);
                }
            } else if let Some(m) = target.module {
                // Try qualified name (e.g. `infixl 9 S.compose as <.` where
                // compose is imported as `import Control.Semigroupoid as S`)
                let qualified = qualified_symbol(m, target.name);
                if let Some(scheme) = env.lookup(qualified).cloned() {
                    if ctx.state.free_unif_vars(&scheme.ty).is_empty() {
                        env.insert_scheme(operator.value, scheme.clone());
                        local_values.insert(operator.value, scheme);
                    }
                }
            }
            // If the target is a data constructor, register the operator→constructor mapping
            // so exhaustiveness checking recognizes operator patterns (e.g. `:` for `Cons`).
            if ctx.ctor_details.contains_key(&target) {
                ctx.ctor_details
                    .insert(qi(operator.value), ctx.ctor_details[&target].clone());
            }
        }
    }

    // Pass 1.6: Typecheck deferred instance method bodies
    // Pre-insert all values with type signatures so they're available during
    // instance method checking (e.g. stateL used in Functor (StateL s) instance)
    for decl in &module.decls {
        if let Decl::Value { name, .. } = decl {
            if let Some((_, sig_ty)) = signatures.get(&name.value) {
                env.insert_scheme(name.value, Scheme::mono(ctx.state.zonk(sig_ty.clone())));
            } else if !env.lookup(name.value).is_some() {
                // Pre-insert fresh unification variables for unsignatured values
                // so instance methods can reference them (e.g. runState)
                let fresh = Type::Unif(ctx.state.fresh_var());
                env.insert_mono(name.value, fresh);
            }
        }
    }

    // Pre-insert fixity operator aliases for values with type signatures
    // so operators like `<`, `>=` are available during instance method checking
    for decl in &module.decls {
        if let Decl::Fixity {
            target,
            operator,
            is_type: false,
            ..
        } = decl
        {
            if let Some((_, sig_ty)) = signatures.get(&target.name) {
                env.insert_scheme(operator.value, Scheme::mono(sig_ty.clone()));
            }
        }
    }

    // Populate function_op_aliases: operators that alias functions (not constructors).
    // Done here because ctor_details is now fully populated from Pass 1.
    // Local fixity declarations override imported ones, so we process all local
    // fixities and either add (function target) or remove (constructor target).
    for decl in &module.decls {
        if let Decl::Fixity {
            target,
            operator,
            is_type: false,
            ..
        } = decl
        {
            if ctx.ctor_details.contains_key(&target)
                || ctx.ctor_details.contains_key(&qi(target.name))
            {
                // Constructor target: remove any inherited function alias flag
                ctx.function_op_aliases.remove(&qi(operator.value));
            } else {
                ctx.function_op_aliases.insert(qi(operator.value));
            }
            // Track operator → class method target for deferred constraint tracking.
            // Local fixity overrides imported mapping, so remove if new target isn't a class method.
            if ctx.class_methods.contains_key(&target) {
                ctx.operator_class_targets
                    .insert(qi(operator.value), *target);
            } else {
                ctx.operator_class_targets.remove(&qi(operator.value));
                // Local fixity redefines the operator to a non-class-method target.
                // Remove any imported constraints so the typechecker doesn't try to
                // resolve constraints (e.g. Semigroupoid) for the new target.
                ctx.signature_constraints.remove(&qi(operator.value));
                ctx.codegen_signature_constraints.remove(&qi(operator.value));
                // Re-register constraints from the local target function (if it has any).
                // E.g., `infixl 4 applySecond as *>` where applySecond has `Apply f =>`.
                let target_qi = qi(target.name);
                let op_qi = qi(operator.value);
                if let Some(sig_c) = ctx.signature_constraints.get(&target_qi).cloned() {
                    ctx.signature_constraints.insert(op_qi.clone(), sig_c);
                }
                if let Some(codegen_c) = ctx.codegen_signature_constraints.get(&target_qi).cloned() {
                    ctx.codegen_signature_constraints.insert(op_qi, codegen_c);
                }
            }
        }
    }

    // Cycle detection for instance methods: detect 0-binder unconstrained methods
    // whose application head is a sibling method (CycleInDeclaration).
    //
    // We only check the application HEAD (leftmost function), not arguments:
    // - `g = f` → head is `f` (sibling) → cycle
    // - `size = fold (const ...) 0.0` → head is `fold` (sibling) → cycle
    // - `bottom = Date bottom bottom bottom` → head is `Date` (constructor) → ok
    // - `pos = pos <<< lower` → Op expression, no app head → ok
    //
    // We also exclude names that exist as top-level values in the module
    // or were imported as standalone (non-class-method) values,
    // since the RHS refers to the top-level/imported function, not the sibling method
    // (e.g. `chooseInt = chooseInt` delegates to a top-level function,
    //  and `eventIsArchived = eventIsArchived` delegates to an imported function).
    let top_level_values: HashSet<Symbol> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Value { name, .. } | Decl::TypeSignature { name, .. } => Some(name.value),
            Decl::Foreign { name, .. } => Some(name.value),
            _ => None,
        })
        .collect();
    // Collect non-class-method values imported from other modules.
    // These take precedence over sibling instance method names on the RHS,
    // so `eventIsArchived = eventIsArchived` (imported value) is NOT a cycle.
    let imported_non_class_values: HashSet<Symbol> = {
        let mut set = HashSet::new();
        for import_decl in &module.imports {
            // Skip qualified imports — they don't introduce unqualified names
            if import_decl.qualified.is_some() {
                continue;
            }
            let prim_sub;
            let module_exports = if is_prim_module(&import_decl.module) {
                continue; // Prim doesn't have relevant values for this check
            } else if is_prim_submodule(&import_decl.module) {
                prim_sub = prim_submodule_exports(&import_decl.module);
                &prim_sub
            } else {
                match registry.lookup(&import_decl.module.parts) {
                    Some(exports) => exports,
                    None => continue,
                }
            };
            match &import_decl.imports {
                None => {
                    // Open import: all non-class-method values are imported
                    for name in module_exports.values.keys() {
                        if !module_exports.class_methods.contains_key(name) {
                            set.insert(name.name);
                        }
                    }
                }
                Some(ImportList::Explicit(items)) => {
                    for item in items {
                        if let Import::Value(sym) = item {
                            // Explicitly imported value — check it's not a class method
                            // in the source module (e.g. `import Prelude (f)` where f
                            // is a class method should not count).
                            let qi_sym = qi(sym.value);
                            if !module_exports.class_methods.contains_key(&qi_sym) {
                                set.insert(sym.value);
                            }
                        }
                    }
                }
                Some(ImportList::Hiding(_)) => {
                    // Hiding import: all non-class-method, non-hidden values
                    for name in module_exports.values.keys() {
                        if !module_exports.class_methods.contains_key(name) {
                            set.insert(name.name);
                        }
                    }
                }
            }
        }
        set
    };
    let mut cycle_methods: HashSet<Symbol> = HashSet::new();
    for group in &instance_method_groups {
        let sibling_set: HashSet<Symbol> = group.iter().copied().collect();
        for (name, span, binders, guarded, _where, _expected, _scoped, _given, _inst_id, _inst_constraints) in
            &deferred_instance_methods
        {
            if !sibling_set.contains(name) || !binders.is_empty() {
                continue;
            }
            // Skip methods whose class type has extra constraints (e.g. Applicative m =>).
            // These get implicit dictionary parameters, making them functions even with
            // 0 explicit binders, so sibling references are deferred under a lambda.
            if ctx.constrained_class_methods.contains(name) {
                continue;
            }
            // Check if the application head is a sibling method name.
            // Exclude names that are top-level values in the module OR imported
            // as standalone (non-class-method) values — in both cases the RHS refers
            // to the existing function, not the sibling instance method.
            let head_is_sibling = |expr: &crate::ast::Expr| -> bool {
                if let Some(head) = expr_app_head_name(expr) {
                    sibling_set.contains(&head)
                        && !top_level_values.contains(&head)
                        && !imported_non_class_values.contains(&head)
                } else {
                    false
                }
            };
            let is_cycle = match guarded {
                crate::ast::GuardedExpr::Unconditional(expr) => head_is_sibling(expr),
                crate::ast::GuardedExpr::Guarded(guards) => {
                    guards.iter().any(|g| head_is_sibling(&g.expr))
                }
            };
            if is_cycle {
                errors.push(TypeError::CycleInDeclaration {
                    name: *name,
                    span: *span,
                    others_in_cycle: vec![],
                });
                cycle_methods.insert(*name);
            }
        }
    }

    // Now that foreign imports, fixity declarations, and value signatures have been
    // processed, all values are available in env for instance method checking.

    // Pre-compute which instance methods have at least one equation with no inherently
    // partial binders (e.g. a catch-all). For multi-equation methods like:
    //   uniqueId (Key []) = ...   -- has [] array binder (inherently partial)
    //   uniqueId e = ...          -- catch-all (not partial)
    // we should NOT emit a Partial error because the method as a whole is exhaustive.
    // Keyed by (instance_id, method_name) to avoid cross-instance interference.
    let mut inst_methods_with_total_eq: HashSet<(usize, Symbol)> = HashSet::new();
    for (name, _span, binders, _guarded, _where, _expected, _scoped, _given, inst_id, _inst_constraints2) in
        &deferred_instance_methods
    {
        if !binders.iter().any(|b| contains_inherently_partial_binder(b)) {
            inst_methods_with_total_eq.insert((*inst_id, *name));
        }
    }

    let mut prev_constraint_method: Option<(usize, Symbol)> = None;
    for (name, span, binders, guarded, where_clause, expected_ty, inst_scoped, inst_given, inst_id, inst_constraints_for_method) in
        &deferred_instance_methods
    {
        let prev_scoped = ctx.scoped_type_vars.clone();
        let prev_given = ctx.given_class_names.clone();
        ctx.scoped_type_vars.extend(inst_scoped);
        ctx.given_class_names.extend(inst_given);
        // Set current_binding_name for this instance method so deferred constraints
        // are associated with the right binding for constraint parameter resolution.
        ctx.current_binding_name = Some(*name);
        ctx.current_binding_span = Some(*span);
        ctx.current_instance_id = Some(*inst_id);
        // Store instance + method constraints for this method (for ConstraintArg resolution)
        {
            let mut all_constraints = inst_constraints_for_method.clone();
            // Append method-level constraints (from the class method type signature)
            if let Some(method_constraints) = ctx.method_own_constraint_details.get(name) {
                all_constraints.extend(method_constraints.iter().cloned());
            }
            if !all_constraints.is_empty() {
                ctx.instance_method_constraints.insert(*span, all_constraints);
            }
        }
        // Populate given_constraint_positions for multi-same-class constraints.
        // Only clear counters when processing a new method (not between equations
        // of the same multi-equation method, which share constraint mapping).
        let current_method = (*inst_id, *name);
        if prev_constraint_method.as_ref() != Some(&current_method) {
            ctx.given_constraint_counters.clear();
        }
        prev_constraint_method = Some(current_method);
        ctx.given_constraint_positions.clear();
        for (pos, (c, c_args)) in inst_constraints_for_method.iter().enumerate() {
            ctx.given_constraint_positions.push((c.name, c_args.clone(), pos));
        }
        // Set per-function given classes for instance method body
        ctx.current_given_expanded.clear();
        for gcn in &ctx.given_class_names {
            ctx.current_given_expanded.insert(gcn.name);
            let mut stack = vec![gcn.name];
            while let Some(cls) = stack.pop() {
                if let Some((_, sc_constraints)) = class_superclasses.get(&qi(cls)) {
                    for (sc_class, _) in sc_constraints {
                        if ctx.current_given_expanded.insert(sc_class.name) {
                            stack.push(sc_class.name);
                        }
                    }
                }
            }
        }
        // Also include method-level constraints from the class definition (e.g. IxBind f =>)
        if let Some(constraint_classes) = ctx.method_own_constraints.get(name) {
            for &cls_name in constraint_classes {
                ctx.current_given_expanded.insert(cls_name);
                let mut stack = vec![cls_name];
                while let Some(cls) = stack.pop() {
                    if let Some((_, sc_constraints)) = class_superclasses.get(&qi(cls)) {
                        for (sc_class, _) in sc_constraints {
                            if ctx.current_given_expanded.insert(sc_class.name) {
                                stack.push(sc_class.name);
                            }
                        }
                    }
                }
            }
        }
        let pre_deferred_len = ctx.codegen_deferred_constraints.len();
        if let Err(e) = check_value_decl(
            &mut ctx,
            &env,
            *name,
            *span,
            binders,
            guarded,
            where_clause,
            expected_ty.as_ref(),
        ) {
            errors.push(e);
        }
        // After method body inference, resolve ConstraintArg positions for
        // multi-same-class constraints by matching zonked type args.
        if !inst_constraints_for_method.is_empty() {
            let new_entries = &ctx.codegen_deferred_constraints[pre_deferred_len..];
            // Find class names that appear multiple times in instance constraints
            let mut class_counts: HashMap<Symbol, usize> = HashMap::new();
            for (c, _) in inst_constraints_for_method {
                *class_counts.entry(c.name).or_insert(0) += 1;
            }
            for (idx_offset, (constraint_span, class_name, type_args, _)) in new_entries.iter().enumerate() {
                let count = class_counts.get(&class_name.name).copied().unwrap_or(0);
                if count <= 1 { continue; }
                if ctx.resolved_dicts.get(constraint_span).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name)) { continue; }
                // Zonk the constraint's type args (now resolved after inference)
                let zonked_args: Vec<Type> = type_args.iter()
                    .map(|t| ctx.state.zonk(t.clone()))
                    .collect();
                // Find which constraint position matches by comparing with instance
                // constraint type args (also zonked)
                let mut matched = None;
                for (pos, (c, c_args)) in inst_constraints_for_method.iter().enumerate() {
                    if c.name != class_name.name { continue; }
                    if c_args.len() != zonked_args.len() { continue; }
                    let mut all_match = true;
                    for (entry_arg, constraint_arg) in zonked_args.iter().zip(c_args.iter()) {
                        let zonked_c = ctx.state.zonk(constraint_arg.clone());
                        if *entry_arg != zonked_c {
                            all_match = false;
                            break;
                        }
                    }
                    if all_match {
                        matched = Some(pos);
                        break;
                    }
                }
                if let Some(position) = matched {
                    ctx.resolved_dicts
                        .entry(*constraint_span)
                        .or_insert_with(Vec::new)
                        .push((class_name.name, DictExpr::ConstraintArg(position)));
                }
            }
        }
        ctx.scoped_type_vars = prev_scoped;
        ctx.given_class_names = prev_given;
        // Clear non-exhaustive state from instance method processing
        // to prevent leaking into subsequent declarations.
        ctx.has_partial_lambda = false;
        ctx.non_exhaustive_errors.clear();
        errors.extend(ctx.drain_pending_holes());

        // Check for non-exhaustive patterns in instance methods.
        // Array and literal binders are always refutable (can never be exhaustive
        // because you can't enumerate all array lengths or literal values).
        // These require a Partial constraint which instances don't provide.
        // Skip if another equation for the same method (in the same instance)
        // has no partial binders (catch-all).
        if !inst_methods_with_total_eq.contains(&(*inst_id, *name))
            && binders
                .iter()
                .any(|b| contains_inherently_partial_binder(b))
        {
            let partial_sym = unqualified_ident("Partial");
            errors.push(TypeError::NoInstanceFound {
                span: *span,
                class_name: partial_sym,
                type_args: vec![],
            });
        }
    }

    timed_pass!(1, "done", "");
    // Pass 2: Group value declarations by name and check them
    let mut value_groups: Vec<(Symbol, Vec<&Decl>)> = Vec::new();
    let mut seen_values: HashMap<Symbol, usize> = HashMap::new();

    for decl in &module.decls {
        if let Decl::Value { name, .. } = decl {
            if let Some(&idx) = seen_values.get(&name.value) {
                value_groups[idx].1.push(decl);
            } else {
                let idx = value_groups.len();
                seen_values.insert(name.value, idx);
                value_groups.push((name.value, vec![decl]));
            }
        }
    }

    // Check for orphan signatures
    for (sig_name, (span, _)) in &signatures {
        if !seen_values.contains_key(sig_name) {
            errors.push(TypeError::OrphanTypeSignature {
                span: *span,
                name: *sig_name,
            });
        }
    }

    // Pre-insert all values with type signatures so forward references work
    // (e.g. `crash = crashWith "..."` where crashWith is defined later)
    for (name, _) in &value_groups {
        if let Some((_, sig_ty)) = signatures.get(name) {
            env.insert_scheme(*name, Scheme::mono(sig_ty.clone()));
        }
    }

    // Pre-insert fixity operator aliases for values with type signatures
    // so operators like `<`, `>=` are available during Pass 2
    for decl in &module.decls {
        if let Decl::Fixity {
            target,
            operator,
            is_type: false,
            ..
        } = decl
        {
            if let Some((_, sig_ty)) = signatures.get(&target.name) {
                env.insert_scheme(operator.value, Scheme::mono(sig_ty.clone()));
            }
        }
    }

    // Binding group analysis: compute dependency graph and SCCs so that
    // value declarations are checked in the correct order.
    let top_names: HashSet<Symbol> = value_groups.iter().map(|(n, _)| *n).collect();
    let mut dep_edges: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for (name, decls) in &value_groups {
        let refs = collect_decl_refs(decls, &top_names);
        dep_edges.insert(*name, refs);
    }
    // Compute SCCs via Tarjan (returns leaves-first = correct processing order)
    let node_order: Vec<Symbol> = value_groups.iter().map(|(n, _)| *n).collect();
    let sccs = tarjan_scc(&node_order, &dep_edges);
    // Build lookup: name → index in value_groups
    let group_idx: HashMap<Symbol, usize> = value_groups
        .iter()
        .enumerate()
        .map(|(i, (n, _))| (*n, i))
        .collect();
    // Process each SCC in dependency order
    for scc in &sccs {
        let is_mutual = scc.len() > 1;
        let is_cyclic = if is_mutual {
            true
        } else {
            let name = scc[0];
            dep_edges
                .get(&name)
                .map_or(false, |refs| refs.contains(&name))
        };

        // Cycle detection: check for non-function (0-arity) value bindings in cyclic SCCs.
        // `x = x` or `x = y; y = x` with no arguments is a CycleInDeclaration.
        // Functions like `f x = f x` are fine — they're just infinite recursion.
        // `findMax = case _ of ...` and `mkFn4 \k v -> ...` are also OK because
        // the recursive reference only appears under a lambda.
        {
            let is_cyclic = if is_mutual {
                true
            } else {
                // Single-member SCC: cyclic only if self-referencing
                let name = scc[0];
                dep_edges
                    .get(&name)
                    .map_or(false, |refs| refs.contains(&name))
            };

            if is_cyclic {
                // For each member with 0 explicit binders, check if the body
                // contains a strict (not under lambda) reference to any SCC member.
                let scc_set: HashSet<Symbol> = scc.iter().copied().collect();
                let mut non_func_members: Vec<(Symbol, crate::span::Span)> = Vec::new();
                for &name in scc {
                    if let Some(&idx) = group_idx.get(&name) {
                        let (_, decls) = &value_groups[idx];
                        // Bindings with type signatures are OK — the signature
                        // provides the type even for self-referential values.
                        if signatures.contains_key(&name) {
                            continue;
                        }
                        let has_binders = decls.iter().any(|d| {
                            if let Decl::Value { binders, .. } = d {
                                !binders.is_empty()
                            } else {
                                false
                            }
                        });
                        if has_binders {
                            continue; // Function with explicit arguments — OK
                        }
                        // Check if the body is directly a reference to an SCC member
                        let has_strict_cycle = decls.iter().any(|d| {
                            if let Decl::Value { guarded, .. } = d {
                                if let crate::ast::GuardedExpr::Unconditional(expr) = guarded {
                                    is_direct_var_ref(expr, &scc_set)
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        });
                        if has_strict_cycle {
                            let span = if let Decl::Value { span, .. } = decls[0] {
                                *span
                            } else {
                                crate::span::Span { start: 0, end: 0 }
                            };
                            non_func_members.push((name, span));
                        }
                    }
                }

                if !non_func_members.is_empty() {
                    // Report cycle for the first non-function member
                    let (name, span) = non_func_members[0];
                    let others: Vec<(Symbol, crate::span::Span)> =
                        non_func_members[1..].to_vec();
                    errors.push(TypeError::CycleInDeclaration {
                        name,
                        span,
                        others_in_cycle: others,
                    });
                    // Skip processing this SCC
                    continue;
                }
            }
        }
        // For mutual recursion: pre-insert all unsignatured values so
        // forward references within the SCC resolve correctly.
        let mut scc_pre_vars: HashMap<Symbol, Type> = HashMap::new();
        if is_mutual {
            for &name in scc {
                if !signatures.contains_key(&name) {
                    let var = Type::Unif(ctx.state.fresh_var());
                    env.insert_mono(name, var.clone());
                    scc_pre_vars.insert(name, var);
                }
            }
        }

        // Deferred generalization for mutual recursion: collect results first
        struct CheckedValue {
            name: Symbol,
            ty: Type,
            #[allow(dead_code)]
            self_ty: Type,
            sig: Option<Type>,
        }
        let mut checked_values: Vec<CheckedValue> = Vec::new();

        for &scc_name in scc {
            let idx = group_idx[&scc_name];
            let (name, decls) = &value_groups[idx];
            let qualified = qi(*name);
            let sig = signatures.get(name).map(|(_, ty)| ty);

            // Expand type aliases in sig to expose hidden Foralls and their constraints.
            // E.g. `three :: Expr Number` where `type Expr a = forall e. E e => e a`
            // expands to `forall e. E e => e Number`, so the body is checked against
            // the inner type with rigid Var(e), producing deferrable constraints.
            let expanded_sig_storage;
            let sig = if let Some(sig_ty) = sig {
                if !matches!(sig_ty, Type::Forall(..)) {
                    let expanded = expand_type_aliases_limited(sig_ty, &ctx.state.type_aliases, 0);
                    if matches!(&expanded, Type::Forall(..)) {
                        expanded_sig_storage = expanded;
                        Some(&expanded_sig_storage)
                    } else {
                        sig
                    }
                } else {
                    sig
                }
            } else {
                sig
            };

            // Track current binding name for resolved_dicts
            ctx.current_binding_name = Some(*name);

            // Check for duplicate value declarations: multiple equations with 0 binders
            if decls.len() > 1 {
                let zero_arity_spans: Vec<crate::span::Span> = decls
                    .iter()
                    .filter_map(|d| {
                        if let Decl::Value { span, binders, .. } = d {
                            if binders.is_empty() {
                                Some(*span)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect();
                if zero_arity_spans.len() > 1 {
                    errors.push(TypeError::DuplicateValueDeclaration {
                        spans: zero_arity_spans,
                        name: *name,
                    });
                    continue;
                }
            }

            // Check for overlapping argument names in each equation
            for decl in decls {
                if let Decl::Value {
                    span,
                    binders,
                    ..
                } = decl
                {
                    if !binders.is_empty() {
                        check_overlapping_arg_names(*span, binders, &mut errors);
                    }
                }
            }

            // Pre-insert for self-recursion. Reuse SCC pre-var if available.
            // When a type signature with forall is present, use a proper polymorphic
            // scheme so recursive calls from where-clause helpers (which may use a
            // monomorphic specialization) don't constrain the outer type variable.
            let self_ty = if let Some(pre_var) = scc_pre_vars.get(name) {
                pre_var.clone()
            } else if let Some(sig_ty) = sig.as_ref() {
                // Check if the signature is polymorphic. First check directly, then
                // expand type aliases for cases like `create :: CreateT` where
                // `type CreateT = forall a. Effect (EventIO a)`.
                let forall_info = if let Type::Forall(vars, body) = *sig_ty {
                    Some((vars.clone(), (**body).clone()))
                } else {
                    let expanded = expand_type_aliases_limited(sig_ty, &ctx.state.type_aliases, 0);
                    if let Type::Forall(vars, body) = &expanded {
                        Some((vars.clone(), (**body).clone()))
                    } else {
                        None
                    }
                };
                if let Some((vars, body)) = forall_info {
                    let scheme = Scheme {
                        forall_vars: vars.iter().map(|&(v, _)| v).collect(),
                        ty: body,
                    };
                    let var = Type::Unif(ctx.state.fresh_var());
                    env.insert_scheme(*name, scheme);
                    var
                } else {
                    let var = Type::Unif(ctx.state.fresh_var());
                    env.insert_mono(*name, var.clone());
                    var
                }
            } else {
                let var = Type::Unif(ctx.state.fresh_var());
                env.insert_mono(*name, var.clone());
                var
            };

            // Set per-function given classes: the calling function's own signature
            // constraints (with transitive superclass expansion) so that deferred
            // constraints for transitively-given classes are filtered at push time.
            ctx.current_given_expanded.clear();
            if let Some(fn_constraints) = ctx.signature_constraints.get(&qualified).cloned() {
                for (cn, _) in &fn_constraints {
                    ctx.current_given_expanded.insert(cn.name);
                    let mut stack = vec![cn.name];
                    while let Some(cls) = stack.pop() {
                        if let Some((_, sc_constraints)) = class_superclasses.get(&qi(cls)) {
                            for (sc_class, _) in sc_constraints {
                                if ctx.current_given_expanded.insert(sc_class.name) {
                                    stack.push(sc_class.name);
                                }
                            }
                        }
                    }
                }
            }
            // Also include given_class_names (from enclosing instance declarations)
            for gcn in &ctx.given_class_names {
                ctx.current_given_expanded.insert(gcn.name);
                let mut stack = vec![gcn.name];
                while let Some(cls) = stack.pop() {
                    if let Some((_, sc_constraints)) = class_superclasses.get(&qi(cls)) {
                        for (sc_class, _) in sc_constraints {
                            if ctx.current_given_expanded.insert(sc_class.name) {
                                stack.push(sc_class.name);
                            }
                        }
                    }
                }
            }

            // Save constraint count before inference for AmbiguousTypeVariables detection
            let constraint_start = ctx.deferred_constraints.len();

            // Store function-level constraints for codegen dict resolution
            // (similar to instance_method_constraints but for standalone functions).
            // These are used by sub-constraint resolution (is_sub_constraint=true)
            // to resolve type-variable-headed constraints via ConstraintArg.
            {
                let decl_span = if let Decl::Value { span, .. } = decls[0] {
                    Some(*span)
                } else {
                    None
                };
                if let Some(sp) = decl_span {
                    ctx.current_binding_span = Some(sp);
                    if let Some(fn_constraints) = ctx.signature_constraints.get(&qualified).cloned() {
                        if !fn_constraints.is_empty() {
                            ctx.instance_method_constraints.insert(sp, fn_constraints);
                        }
                    }
                }
            }

            if decls.len() == 1 {
                // Single equation
                if let Decl::Value {
                    span,
                    binders,
                    guarded,
                    where_clause,
                    ..
                } = decls[0]
                {
                    match check_value_decl(
                        &mut ctx,
                        &env,
                        *name,
                        *span,
                        binders,
                        guarded,
                        where_clause,
                        sig,
                    ) {
                        Ok(ty) => {
                            if let Err(e) = ctx.state.unify(*span, &self_ty, &ty) {
                                errors.push(e);
                            }
                            // Compare constraint solver: check new Compare constraints
                            // against the function's own signature constraints using
                            // graph-based transitive reasoning.
                            if let Some(sig_constraints) =
                                ctx.signature_constraints.get(&qualified).cloned()
                            {
                                // Build relations from the function's own signature constraints
                                let mut relations: Vec<(Type, Type, &str)> = Vec::new();
                                for (class_name_c, args) in &sig_constraints {
                                    if is_compare(&class_name_c) && args.len() == 3 {
                                        if let Type::Con(ordering) = &args[2] {
                                            let ord_str =
                                                crate::interner::resolve(ordering.name)
                                                    .unwrap_or_default();
                                            let ord_static: &str = match ord_str.as_str() {
                                                "LT" => "LT",
                                                "EQ" => "EQ",
                                                "GT" => "GT",
                                                _ => continue,
                                            };
                                            // Expand type aliases so e.g. Common.NegOne becomes TypeInt(-1)
                                            let lhs = expand_type_aliases_limited(&args[0], &ctx.state.type_aliases, 10);
                                            let rhs = expand_type_aliases_limited(&args[1], &ctx.state.type_aliases, 10);
                                            relations.push((
                                                lhs,
                                                rhs,
                                                ord_static,
                                            ));
                                        }
                                    }
                                }

                                if !relations.is_empty() {
                                    // Collect all concrete integers from both given and wanted
                                    // Compare constraints (for mkFacts-style ordering).
                                    let mut extra_ints: Vec<Type> = Vec::new();
                                    for (_, args) in &sig_constraints {
                                        for arg in args {
                                            if matches!(arg, Type::TypeInt(_)) {
                                                extra_ints.push(arg.clone());
                                            }
                                        }
                                    }
                                    for i in constraint_start..ctx.deferred_constraints.len() {
                                        let (_, c_class_i, _) = ctx.deferred_constraints[i];
                                        if !is_compare(&c_class_i) {
                                            continue;
                                        }
                                        for arg in &ctx.deferred_constraints[i].2 {
                                            let z = ctx.state.zonk(arg.clone());
                                            if matches!(z, Type::TypeInt(_)) {
                                                extra_ints.push(z);
                                            }
                                        }
                                    }
                                    for i in constraint_start..ctx.deferred_constraints.len() {
                                        let (c_span, c_class, _) = ctx.deferred_constraints[i];
                                        if !is_compare(&c_class) {
                                            continue;
                                        }
                                        let zonked: Vec<Type> = ctx.deferred_constraints[i]
                                            .2
                                            .iter()
                                            .map(|t| ctx.state.zonk(t.clone()))
                                            .collect();
                                        if zonked.len() != 3 {
                                            continue;
                                        }
                                        // Only use given relations from the signature (NOT wanted
                                        // constraints, which would be circular reasoning).
                                        // Pass extra concrete ints for mkFacts-style ordering.
                                        if let Some(solved) = solve_compare_graph(
                                            &relations,
                                            &extra_ints,
                                            &zonked[0],
                                            &zonked[1],
                                        ) {
                                            let result = Type::Con(solved);
                                            if let Err(e) =
                                                ctx.state.unify(c_span, &zonked[2], &result)
                                            {
                                                errors.push(e);
                                            }
                                        } else {
                                            // Graph solver couldn't determine the relationship.
                                            // The given Compare constraints don't entail this wanted constraint.
                                            errors.push(TypeError::NoInstanceFound {
                                                span: c_span,
                                                class_name: c_class,
                                                type_args: zonked,
                                            });
                                        }
                                    }
                                }
                            }

                            // Lacks constraint solver: check that body-generated
                            // Lacks constraints with type variables are entailed by
                            // the function's signature constraints.
                            {
                                let lacks_sym = unqualified_ident("Lacks");
                                // Collect given Lacks constraints from signature
                                let sig_lacks: Vec<(Type, Type)> = if let Some(sig_constraints) =
                                    ctx.signature_constraints.get(&qualified)
                                {
                                    sig_constraints
                                        .iter()
                                        .filter(|(cn, args)| *cn == lacks_sym && args.len() == 2)
                                        .map(|(_, args)| (args[0].clone(), args[1].clone()))
                                        .collect()
                                } else {
                                    Vec::new()
                                };
                                for i in constraint_start..ctx.deferred_constraints.len() {
                                    let (c_span, c_class, _) = ctx.deferred_constraints[i];
                                    if c_class != lacks_sym {
                                        continue;
                                    }
                                    let zonked: Vec<Type> = ctx.deferred_constraints[i]
                                        .2
                                        .iter()
                                        .map(|t| ctx.state.zonk(t.clone()))
                                        .collect();
                                    if zonked.len() != 2 {
                                        continue;
                                    }
                                    let has_type_vars = zonked.iter().any(|t| contains_type_var(t));
                                    if !has_type_vars {
                                        continue;
                                    }
                                    // Decompose: Lacks label (fields | tail) → Lacks label tail
                                    let (label, row_tail) = match &zonked[1] {
                                        Type::Record(fields, Some(tail)) => {
                                            // Check label is not in known fields
                                            if let Type::TypeString(label_sym) = &zonked[0] {
                                                let label_str =
                                                    crate::interner::resolve(*label_sym)
                                                        .unwrap_or_default();
                                                let has_label = fields.iter().any(|(f, _)| {
                                                    crate::interner::resolve(*f).unwrap_or_default()
                                                        == label_str.as_str()
                                                });
                                                if has_label {
                                                    // Label IS in the row — Lacks fails
                                                    errors.push(TypeError::NoInstanceFound {
                                                        span: c_span,
                                                        class_name: c_class,
                                                        type_args: zonked,
                                                    });
                                                    continue;
                                                }
                                            }
                                            (zonked[0].clone(), *tail.clone())
                                        }
                                        other => (zonked[0].clone(), other.clone()),
                                    };
                                    // After decomposition, check if the reduced Lacks is given
                                    // by the function's signature constraints.
                                    let is_given = sig_lacks
                                        .iter()
                                        .any(|(sl, sr)| *sl == label && *sr == row_tail);
                                    if !is_given {
                                        // Check if the tail is a bare type variable (from forall).
                                        // If so, and there's no matching given Lacks constraint,
                                        // this is unsatisfiable.
                                        if matches!(row_tail, Type::Var(_)) {
                                            errors.push(TypeError::NoInstanceFound {
                                                span: c_span,
                                                class_name: c_class,
                                                type_args: zonked,
                                            });
                                        }
                                    }
                                }
                            }
                            // Coercible constraint solver: check Coercible constraints
                            // with type variables using role-based decomposition and
                            // the function's own given Coercible constraints.
                            // Track solved indices so they don't leak into signature_constraints.
                            let mut solved_coercible_indices: HashSet<usize> = HashSet::new();
                            {
                                let coercible_ident: QualifiedIdent =
                                    unqualified_ident("Coercible");
                                let newtype_ident = unqualified_ident("Newtype");
                                let type_equals_ident = unqualified_ident("TypeEquals");
                                let coercible_givens: Vec<(Type, Type)> = ctx
                                    .signature_constraints
                                    .get(&qualified.clone())
                                    .map(|constraints| {
                                        constraints
                                            .iter()
                                            .filter(|(cn, args)| {
                                                // Coercible a b directly, or TypeEquals a b
                                                // (since Coercible is a superclass of TypeEquals)
                                                (*cn == coercible_ident || *cn == type_equals_ident)
                                                    && args.len() == 2
                                            })
                                            .map(|(_, args)| (args[0].clone(), args[1].clone()))
                                            .collect()
                                    })
                                    .unwrap_or_default();
                                // Only trust Newtype constraints blindly (superclass relation).
                                // Coercible givens are handled through proper interaction.
                                let has_newtype_givens = ctx
                                    .signature_constraints
                                    .get(&qualified.clone())
                                    .map(|constraints| {
                                        constraints.iter().any(|(cn, _)| *cn == newtype_ident)
                                    })
                                    .unwrap_or(false);
                                for i in constraint_start..ctx.deferred_constraints.len() {
                                    let (c_span, c_class, _) = ctx.deferred_constraints[i];
                                    if c_class != coercible_ident {
                                        continue;
                                    }
                                    let zonked: Vec<Type> = ctx.deferred_constraints[i]
                                        .2
                                        .iter()
                                        .map(|t| {
                                            let z = ctx.state.zonk(t.clone());
                                            // Strip Forall wrappers that leak in when check_against's
                                            // fallthrough arm unifies a unif var with a Forall expected type.
                                            // The body's Var(a) matches the annotation's Var(a).
                                            strip_forall(z)
                                        })
                                        .collect();
                                    if zonked.len() != 2 {
                                        continue;
                                    }
                                    // Only handle constraints with type variables here
                                    // (concrete constraints are handled in Pass 3)
                                    let has_type_vars = zonked.iter().any(|t| contains_type_var(t));
                                    if !has_type_vars {
                                        continue;
                                    }
                                    // Skip if constraint contains unsolved unif vars — they may
                                    // be resolved later, so we can't definitively fail here.
                                    let has_unif_vars = zonked
                                        .iter()
                                        .any(|t| !ctx.state.free_unif_vars(t).is_empty());
                                    if has_unif_vars {
                                        continue;
                                    }
                                    match try_solve_coercible_with_interactions(
                                        &zonked[0],
                                        &zonked[1],
                                        &coercible_givens,
                                        &ctx.type_roles,
                                        &ctx.newtype_names,
                                        &ctx.state.type_aliases,
                                        &ctx.ctor_details,
                                    ) {
                                        CoercibleResult::Solved => {
                                            solved_coercible_indices.insert(i);
                                        }
                                        result => {
                                            // If the function has Newtype constraints, trust that
                                            // the superclass provides the needed Coercible.
                                            if has_newtype_givens {
                                                continue;
                                            }
                                            match result {
                                                CoercibleResult::Solved => unreachable!(),
                                                CoercibleResult::NotCoercible => {
                                                    errors.push(TypeError::NoInstanceFound {
                                                        span: c_span,
                                                        class_name: c_class,
                                                        type_args: zonked,
                                                    });
                                                }
                                                CoercibleResult::TypesDoNotUnify => {
                                                    errors.push(TypeError::UnificationError {
                                                        span: c_span,
                                                        expected: zonked[0].clone(),
                                                        found: zonked[1].clone(),
                                                    });
                                                }
                                                CoercibleResult::DepthExceeded => {
                                                    errors.push(TypeError::PossiblyInfiniteCoercibleInstance {
                                                        span: c_span,
                                                        class_name: c_class,
                                                        type_args: zonked,
                                                    });
                                                }
                                                CoercibleResult::KindMismatch => {
                                                    errors.push(TypeError::KindsDoNotUnify {
                                                        span: c_span,
                                                        expected: zonked[0].clone(),
                                                        found: zonked[1].clone(),
                                                    });
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            if is_mutual {
                                // Defer generalization for mutual recursion
                                checked_values.push(CheckedValue {
                                    name: *name,
                                    ty,
                                    self_ty,
                                    sig: sig.cloned(),
                                });
                            } else {
                                // Track whether the explicit signature hides constraints
                                // in type aliases (e.g. `three :: Expr Number` where
                                // `type Expr a = forall e. E e => e a`). Only alias-hidden
                                // constraints need body extraction; for regular explicit
                                // signatures, body constraints should NOT propagate.
                                let mut has_alias_hidden_forall = false;
                                let scheme = if let Some(sig_ty) = sig {
                                    // If sig_ty is NOT already a Forall, it might hide one inside
                                    // a type alias. Expand aliases to expose the hidden Forall
                                    // so the scheme has proper forall_vars.
                                    if !matches!(sig_ty, Type::Forall(..)) {
                                        let expanded = expand_type_aliases_limited(sig_ty, &ctx.state.type_aliases, 0);
                                        if let Type::Forall(vars, body) = expanded {
                                            has_alias_hidden_forall = true;
                                            Scheme {
                                                forall_vars: vars.iter().map(|&(v, _)| v).collect(),
                                                ty: *body,
                                            }
                                        } else {
                                            Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                                        }
                                    } else {
                                        Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                                    }
                                } else {
                                    let zonked = ctx.state.zonk(ty.clone());
                                    // Check CannotGeneralizeRecursiveFunction: recursive function
                                    // without type annotation that would generalize constrained vars
                                    if is_cyclic {
                                        if let Some(err) = check_cannot_generalize_recursive(
                                            &mut ctx.state,
                                            &ctx.deferred_constraints,
                                            &ctx.op_deferred_constraints,
                                            *name,
                                            *span,
                                            &zonked,
                                        ) {
                                            errors.push(err);
                                        }
                                    }
                                    // Check for ambiguous type variables: constraint vars not in the type
                                    if let Some(err) = check_ambiguous_type_variables(
                                        &mut ctx.state,
                                        &ctx.deferred_constraints,
                                        constraint_start,
                                        *span,
                                        &zonked,
                                        &ctx.class_fundeps,
                                    ) {
                                        errors.push(err);
                                    }
                                    // Eagerly solve solver constraints (Union, Nub, Lacks, etc.)
                                    // before generalization. Without this, unif vars constrained
                                    // by Union get over-generalized, disconnecting them from the
                                    // concrete types that the solver would determine.
                                    for _iter in 0..3 {
                                        let mut solved_any = false;
                                        for ci in constraint_start..ctx.deferred_constraints.len() {
                                            let (c_span, c_class, _) = ctx.deferred_constraints[ci];
                                            let c_str = crate::interner::resolve(c_class.name).unwrap_or_default();
                                            let z_args: Vec<Type> = ctx.deferred_constraints[ci].2.iter()
                                                .map(|t| {
                                                    let z = ctx.state.zonk(t.clone());
                                                    expand_type_aliases_limited(&z, &ctx.state.type_aliases, 0)
                                                }).collect();
                                            match c_str.as_str() {
                                                "Union" if z_args.len() == 3 => {
                                                    if let Some(merged) = try_union_rows(&z_args[0], &z_args[1]) {
                                                        if let Err(e) = ctx.state.unify(c_span, &z_args[2], &merged) {
                                                            errors.push(e);
                                                        } else {
                                                            solved_any = true;
                                                        }
                                                    }
                                                }
                                                "Nub" if z_args.len() == 2 => {
                                                    if let Some(nubbed) = try_nub_row(&z_args[0]) {
                                                        if let Err(e) = ctx.state.unify(c_span, &z_args[1], &nubbed) {
                                                            errors.push(e);
                                                        } else {
                                                            solved_any = true;
                                                        }
                                                    }
                                                }
                                                "Append" if z_args.len() == 3 => {
                                                    if let (Type::TypeString(a), Type::TypeString(b)) = (&z_args[0], &z_args[1]) {
                                                        let a_str = crate::interner::resolve(*a).unwrap_or_default();
                                                        let b_str = crate::interner::resolve(*b).unwrap_or_default();
                                                        let result = Type::TypeString(crate::interner::intern(&format!("{}{}", a_str, b_str)));
                                                        if let Err(e) = ctx.state.unify(c_span, &z_args[2], &result) {
                                                            errors.push(e);
                                                        } else {
                                                            solved_any = true;
                                                        }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        if !solved_any { break; }
                                    }
                                    let zonked = ctx.state.zonk(ty.clone());
                                    env.generalize_excluding(&mut ctx.state, zonked, *name)
                                };
                                let zonked = ctx.state.zonk(ty.clone());
                                env.insert_scheme(*name, scheme.clone());
                                local_values.insert(*name, scheme.clone());

                                // Extract constraints from deferred_constraints to populate
                                // signature_constraints (needed for codegen dict wrapping).
                                // This handles both unsignatured values and values whose type
                                // signature contains constraints inside type aliases (e.g.
                                // `three :: Expr Number` where `type Expr a = forall e. E e => e a`).
                                //
                                // Skip extraction when the function has an explicit type
                                // signature WITHOUT alias-hidden constraints. Body-internal
                                // constraints (e.g., Union from calling `make` inside
                                // `makeStateless`) should not propagate to callers — the
                                // explicit signature defines the public contract.
                                let skip_body_constraint_extraction =
                                    sig.is_some() && !has_alias_hidden_forall;
                                if !skip_body_constraint_extraction && !ctx.signature_constraints.contains_key(&qualified) {
                                    // Build a mapping from generalized unif vars to the scheme's Forall vars.
                                    // This lets us store constraints in terms of the scheme's type vars,
                                    // so they can be properly substituted when the scheme is instantiated.
                                    let unif_to_var: HashMap<crate::typechecker::types::TyVarId, Symbol> = {
                                        let mut map = HashMap::new();
                                        if !scheme.forall_vars.is_empty() {
                                            let pre_gen_vars = ctx.state.free_unif_vars(&zonked);
                                            for (i, &var_id) in pre_gen_vars.iter().enumerate() {
                                                if i < scheme.forall_vars.len() {
                                                    map.insert(var_id, scheme.forall_vars[i]);
                                                }
                                            }
                                        }
                                        map
                                    };

                                    // Collect the unif vars in the function's type — these are
                                    // the vars that will be generalized. Only constraints whose
                                    // unif vars overlap with the type's vars are polymorphic.
                                    let type_unif_vars = ctx.state.free_unif_vars(&zonked);
                                    let type_unif_set: std::collections::HashSet<crate::typechecker::types::TyVarId> =
                                        type_unif_vars.into_iter().collect();
                                    // Build set of scheme forall vars - these are the type variables
                                    // that belong to this function's polymorphic signature.
                                    // Type::Var args in constraints that are NOT in this set come from
                                    // inner foralls (e.g., data constructor fields) and should NOT
                                    // propagate as function-level constraints.
                                    let scheme_var_set: std::collections::HashSet<Symbol> =
                                        scheme.forall_vars.iter().copied().collect();
                                    let mut inferred_constraints: Vec<(QualifiedIdent, Vec<Type>)> = Vec::new();
                                    let mut seen_classes: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
                                    // Skip Coercible constraints — they are resolved at the
                                    // definition site and should never propagate to callers.
                                    let coercible_ident_for_filter = unqualified_ident("Coercible");
                                    for i in constraint_start..ctx.deferred_constraints.len() {
                                        if solved_coercible_indices.contains(&i) {
                                            continue;
                                        }
                                        let (_, class_name, _) = ctx.deferred_constraints[i];
                                        if class_name == coercible_ident_for_filter {
                                            continue;
                                        }
                                        let zonked_args: Vec<Type> = ctx.deferred_constraints[i]
                                            .2
                                            .iter()
                                            .map(|t| {
                                                let z = ctx.state.zonk(t.clone());
                                                replace_unif_with_vars(&z, &unif_to_var)
                                            })
                                            .collect();
                                        // After replacing known unif vars with named type vars,
                                        // skip constraints that still contain raw Type::Unif nodes.
                                        // These are stale TyVarIds from the function body (e.g., from
                                        // calling other constrained functions like `make`) that would
                                        // leak to consumer modules and cause incorrect unification.
                                        let has_stale_unif = zonked_args.iter().any(|a| has_unif_vars(a));
                                        if has_stale_unif {
                                            continue;
                                        }
                                        let mut constraint_has_overlap = false;
                                        for arg in &zonked_args {
                                            match arg {
                                                Type::Var(v) => {
                                                    // Only count as overlapping if the type variable
                                                    // is one of the scheme's own forall vars.
                                                    // Inner-forall vars from data constructor fields
                                                    // should not propagate as function-level constraints.
                                                    if scheme_var_set.contains(v) {
                                                        constraint_has_overlap = true;
                                                        break;
                                                    }
                                                }
                                                _ => {
                                                    if contains_type_var(arg) {
                                                        constraint_has_overlap = true;
                                                        break;
                                                    }
                                                    for uv in ctx.state.free_unif_vars(arg) {
                                                        if type_unif_set.contains(&uv) {
                                                            constraint_has_overlap = true;
                                                            break;
                                                        }
                                                    }
                                                }
                                            }
                                            if constraint_has_overlap { break; }
                                        }
                                        if constraint_has_overlap && seen_classes.insert(class_name.name) {
                                            inferred_constraints.push((class_name, zonked_args));
                                        }
                                    }
                                    if !inferred_constraints.is_empty() {
                                        // Also update instance_method_constraints for codegen
                                        // ConstraintArg resolution (alias-hidden constraints).
                                        let decl_span_for_imc = if let Decl::Value { span, .. } = decls[0] { Some(*span) } else { None };
                                        if let Some(sp) = decl_span_for_imc {
                                            if !ctx.instance_method_constraints.contains_key(&sp) {
                                                ctx.instance_method_constraints.insert(sp, inferred_constraints.clone());
                                            }
                                        }
                                        ctx.signature_constraints.insert(qualified.clone(), inferred_constraints);
                                    }
                                }

                                // Check for non-exhaustive pattern guards (single equation).
                                // The flag is set during infer_guarded when a pattern guard
                                // doesn't cover all constructors. We also need the overall
                                // function/case to lack an unconditional fallback.
                                if !partial_names.contains(name)
                                    && ctx.has_non_exhaustive_pattern_guards
                                {
                                    if !is_unconditional_for_exhaustiveness(guarded) {
                                        errors.push(TypeError::NoInstanceFound {
                                            span: *span,
                                            class_name: unqualified_ident("Partial"),
                                            type_args: vec![],
                                        });
                                    }
                                }
                                ctx.has_non_exhaustive_pattern_guards = false;

                                // Check for partial lambdas (refutable binders in lambda expressions).
                                // Unlike guard patterns, partial lambdas always require Partial
                                // regardless of the enclosing function's guard structure.
                                if !partial_names.contains(name) && ctx.has_partial_lambda {
                                    // Prefer specific NonExhaustivePattern errors from case expressions
                                    if !ctx.non_exhaustive_errors.is_empty() {
                                        errors.extend(ctx.non_exhaustive_errors.drain(..));
                                    } else {
                                        errors.push(TypeError::NoInstanceFound {
                                            span: *span,
                                            class_name: unqualified_ident("Partial"),
                                            type_args: vec![],
                                        });
                                    }
                                }
                                ctx.has_partial_lambda = false;
                                ctx.non_exhaustive_errors.clear();

                                // Drain any typed holes recorded during inference
                                errors.extend(ctx.drain_pending_holes());

                                result_types.insert(*name, zonked);
                            }
                        }
                        Err(e) => {
                            errors.push(e);
                            errors.extend(ctx.drain_pending_holes());
                            if let Some(sig_ty) = sig {
                                let scheme = Scheme::mono(ctx.state.zonk(sig_ty.clone()));
                                env.insert_scheme(*name, scheme.clone());
                                local_values.insert(*name, scheme);
                            }
                        }
                    }
                }
            } else {
                // Multiple equations — check arity consistency
                let first_arity = if let Decl::Value { binders, .. } = decls[0] {
                    binders.len()
                } else {
                    0
                };

                let mut arity_ok = true;
                for decl in &decls[1..] {
                    if let Decl::Value { span, binders, .. } = decl {
                        if binders.len() != first_arity {
                            errors.push(TypeError::ArityMismatch {
                                span: *span,
                                name: *name,
                                expected: first_arity,
                                found: binders.len(),
                            });
                            arity_ok = false;
                        }
                    }
                }

                if !arity_ok {
                    continue;
                }
                // Set scoped type vars from multi-equation function's signature
                let prev_scoped_multi = ctx.scoped_type_vars.clone();
                if let Some(sig_ty) = sig {
                    fn collect_sig_vars(ty: &Type, vars: &mut HashSet<Symbol>) {
                        match ty {
                            Type::Var(v) => {
                                vars.insert(*v);
                            }
                            Type::Forall(bv, body) => {
                                for &(v, _) in bv {
                                    vars.insert(v);
                                }
                                collect_sig_vars(body, vars);
                            }
                            Type::Fun(a, b) | Type::App(a, b) => {
                                collect_sig_vars(a, vars);
                                collect_sig_vars(b, vars);
                            }
                            Type::Record(fields, tail) => {
                                for (_, t) in fields {
                                    collect_sig_vars(t, vars);
                                }
                                if let Some(t) = tail {
                                    collect_sig_vars(t, vars);
                                }
                            }
                            _ => {}
                        }
                    }
                    collect_sig_vars(sig_ty, &mut ctx.scoped_type_vars);
                }

                let func_ty = match sig {
                    Some(sig_ty) => match ctx.instantiate_forall_type(sig_ty.clone()) {
                        Ok(ty) => ty,
                        Err(e) => {
                            errors.push(e);
                            ctx.scoped_type_vars = prev_scoped_multi;
                            continue;
                        }
                    },
                    None => Type::Unif(ctx.state.fresh_var()),
                };
                let mut group_failed = false;
                // Track partial lambda/exhaustiveness across all equations.
                // Save and restore between equations to prevent leakage, but
                // accumulate: if ANY equation sets the flag, keep it.
                let mut any_partial_lambda = false;
                let mut all_non_exhaustive_errors: Vec<TypeError> = Vec::new();
                for decl in decls {
                    if let Decl::Value {
                        span,
                        binders,
                        guarded,
                        where_clause,
                        ..
                    } = decl
                    {
                        // Clear flags before each equation so they don't leak
                        ctx.has_partial_lambda = false;
                        ctx.non_exhaustive_errors.clear();
                        // Pass func_ty as expected so binders get correct types
                        // from the signature (including rank-2 types like forall r).
                        let expected_sig = if sig.is_some() { Some(&func_ty) } else { None };
                        match check_value_decl(
                            &mut ctx,
                            &env,
                            *name,
                            *span,
                            binders,
                            guarded,
                            where_clause,
                            expected_sig,
                        ) {
                            Ok(eq_ty) => {
                                if let Err(e) = ctx.state.unify(*span, &func_ty, &eq_ty) {
                                    errors.push(e);
                                    group_failed = true;
                                }
                            }
                            Err(e) => {
                                errors.push(e);
                                group_failed = true;
                            }
                        }
                        // Accumulate flags from this equation
                        if ctx.has_partial_lambda {
                            any_partial_lambda = true;
                        }
                        all_non_exhaustive_errors.extend(ctx.non_exhaustive_errors.drain(..));
                    }
                }
                // Restore accumulated flags for the post-equation checks
                ctx.has_partial_lambda = any_partial_lambda;
                ctx.non_exhaustive_errors = all_non_exhaustive_errors;

                if !group_failed {
                    let first_span = if let Decl::Value { span, .. } = decls[0] {
                        *span
                    } else {
                        crate::span::Span::new(0, 0)
                    };
                    if let Err(e) = ctx.state.unify(first_span, &self_ty, &func_ty) {
                        errors.push(e);
                    }

                    // Inline Coercible solver for multi-equation declarations.
                    // Track solved indices so they don't leak into signature_constraints.
                    let mut solved_coercible_indices: HashSet<usize> = HashSet::new();
                    {
                        let coercible_ident = unqualified_ident("Coercible");
                        let newtype_ident = unqualified_ident("Newtype"); // probably not quite correct
                        let coercible_givens: Vec<(Type, Type)> = ctx
                            .signature_constraints
                            .get(&qi(*name))
                            .map(|constraints| {
                                constraints
                                    .iter()
                                    .filter(|(cn, args)| *cn == coercible_ident && args.len() == 2)
                                    .map(|(_, args)| (args[0].clone(), args[1].clone()))
                                    .collect()
                            })
                            .unwrap_or_default();
                        let has_newtype_givens = ctx
                            .signature_constraints
                            .get(&qualified)
                            .map(|constraints| {
                                constraints.iter().any(|(cn, _)| *cn == newtype_ident)
                            })
                            .unwrap_or(false);
                        for i in constraint_start..ctx.deferred_constraints.len() {
                            let (c_span, c_class, _) = ctx.deferred_constraints[i];
                            if c_class != coercible_ident {
                                continue;
                            }
                            let zonked: Vec<Type> = ctx.deferred_constraints[i]
                                .2
                                .iter()
                                .map(|t| {
                                    let z = ctx.state.zonk(t.clone());
                                    strip_forall(z)
                                })
                                .collect();
                            if zonked.len() != 2 {
                                continue;
                            }
                            let has_type_vars = zonked.iter().any(|t| contains_type_var(t));
                            if !has_type_vars {
                                continue;
                            }
                            let all_unif =
                                matches!((&zonked[0], &zonked[1]), (Type::Unif(_), Type::Unif(_)));
                            if all_unif {
                                continue;
                            }
                            match try_solve_coercible_with_interactions(
                                &zonked[0],
                                &zonked[1],
                                &coercible_givens,
                                &ctx.type_roles,
                                &ctx.newtype_names,
                                &ctx.state.type_aliases,
                                &ctx.ctor_details,
                            ) {
                                CoercibleResult::Solved => {
                                    solved_coercible_indices.insert(i);
                                }
                                result => {
                                    if has_newtype_givens {
                                        continue;
                                    }
                                    match result {
                                        CoercibleResult::Solved => unreachable!(),
                                        CoercibleResult::NotCoercible => {
                                            errors.push(TypeError::NoInstanceFound {
                                                span: c_span,
                                                class_name: c_class,
                                                type_args: zonked,
                                            });
                                        }
                                        CoercibleResult::TypesDoNotUnify => {
                                            errors.push(TypeError::UnificationError {
                                                span: c_span,
                                                expected: zonked[0].clone(),
                                                found: zonked[1].clone(),
                                            });
                                        }
                                        CoercibleResult::DepthExceeded => {
                                            errors.push(
                                                TypeError::PossiblyInfiniteCoercibleInstance {
                                                    span: c_span,
                                                    class_name: c_class,
                                                    type_args: zonked,
                                                },
                                            );
                                        }
                                        CoercibleResult::KindMismatch => {
                                            errors.push(TypeError::KindsDoNotUnify {
                                                span: c_span,
                                                expected: zonked[0].clone(),
                                                found: zonked[1].clone(),
                                            });
                                        }
                                    }
                                }
                            }
                        }
                    }

                    if is_mutual {
                        checked_values.push(CheckedValue {
                            name: *name,
                            ty: func_ty.clone(),
                            self_ty,
                            sig: sig.cloned(),
                        });
                    } else {
                        let zonked = ctx.state.zonk(func_ty);
                        let has_sig_without_alias_forall = sig.is_some();
                        let scheme = if let Some(sig_ty) = sig {
                            Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                        } else {
                            // Check CannotGeneralizeRecursiveFunction
                            if is_cyclic {
                                if let Some(err) = check_cannot_generalize_recursive(
                                    &mut ctx.state,
                                    &ctx.deferred_constraints,
                                    &ctx.op_deferred_constraints,
                                    *name,
                                    first_span,
                                    &zonked,
                                ) {
                                    errors.push(err);
                                }
                            }
                            // Check for ambiguous type variables
                            if let Some(err) = check_ambiguous_type_variables(
                                &mut ctx.state,
                                &ctx.deferred_constraints,
                                constraint_start,
                                first_span,
                                &zonked,
                                &ctx.class_fundeps,
                            ) {
                                errors.push(err);
                            }
                            env.generalize_excluding(&mut ctx.state, zonked.clone(), *name)
                        };
                        env.insert_scheme(*name, scheme.clone());
                        local_values.insert(*name, scheme.clone());

                        // Extract constraints from deferred_constraints to populate
                        // signature_constraints (needed for codegen dict wrapping).
                        // Skip when function has explicit signature (body constraints
                        // should not propagate — see single-equation block for details).
                        if !has_sig_without_alias_forall && !ctx.signature_constraints.contains_key(&qualified) {
                            let unif_to_var: HashMap<crate::typechecker::types::TyVarId, Symbol> = {
                                let mut map = HashMap::new();
                                if !scheme.forall_vars.is_empty() {
                                    let pre_gen_vars = ctx.state.free_unif_vars(&zonked);
                                    for (i, &var_id) in pre_gen_vars.iter().enumerate() {
                                        if i < scheme.forall_vars.len() {
                                            map.insert(var_id, scheme.forall_vars[i]);
                                        }
                                    }
                                }
                                map
                            };

                            let type_unif_vars = ctx.state.free_unif_vars(&zonked);
                            let type_unif_set: std::collections::HashSet<crate::typechecker::types::TyVarId> =
                                type_unif_vars.into_iter().collect();
                            // Build set of scheme forall vars for inner-forall filtering
                            let scheme_var_set: std::collections::HashSet<Symbol> =
                                scheme.forall_vars.iter().copied().collect();
                            let mut inferred_constraints: Vec<(QualifiedIdent, Vec<Type>)> = Vec::new();
                            let mut seen_classes: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
                            // Scan deferred_constraints (skip Coercible — resolved at definition site)
                            let coercible_ident_for_filter = unqualified_ident("Coercible");
                            for i in constraint_start..ctx.deferred_constraints.len() {
                                if solved_coercible_indices.contains(&i) {
                                    continue;
                                }
                                let (_, class_name, _) = ctx.deferred_constraints[i];
                                if class_name == coercible_ident_for_filter {
                                    continue;
                                }
                                let zonked_args: Vec<Type> = ctx.deferred_constraints[i]
                                    .2
                                    .iter()
                                    .map(|t| {
                                        let z = ctx.state.zonk(t.clone());
                                        replace_unif_with_vars(&z, &unif_to_var)
                                    })
                                    .collect();
                                // Skip constraints with stale unif vars (see first occurrence for details)
                                let has_stale_unif = zonked_args.iter().any(|a| has_unif_vars(a));
                                if has_stale_unif {
                                    continue;
                                }
                                let mut constraint_has_overlap = false;
                                for arg in &zonked_args {
                                    match arg {
                                        Type::Var(v) => {
                                            // Only count as overlapping if the type variable
                                            // is one of the scheme's own forall vars.
                                            if scheme_var_set.contains(v) {
                                                constraint_has_overlap = true;
                                                break;
                                            }
                                        }
                                        _ => {
                                            if contains_type_var(arg) {
                                                constraint_has_overlap = true;
                                                break;
                                            }
                                            for uv in ctx.state.free_unif_vars(arg) {
                                                if type_unif_set.contains(&uv) {
                                                    constraint_has_overlap = true;
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    if constraint_has_overlap { break; }
                                }
                                if constraint_has_overlap && seen_classes.insert(class_name.name) {
                                    inferred_constraints.push((class_name, zonked_args));
                                }
                            }
                            if !inferred_constraints.is_empty() {
                                ctx.signature_constraints.insert(qualified.clone(), inferred_constraints);
                            }
                        }

                        if first_arity > 0 && !partial_names.contains(name) {
                            check_multi_eq_exhaustiveness(
                                &ctx,
                                first_span,
                                &zonked,
                                first_arity,
                                decls,
                                &mut errors,
                            );
                        }
                        // Check for non-exhaustive pattern guards (multi-equation).
                        // The flag is set during infer_guarded when pattern guards
                        // don't cover all constructors. We also need the overall
                        // function to lack an unconditional fallback equation.
                        if !partial_names.contains(name) && ctx.has_non_exhaustive_pattern_guards {
                            let has_fallback = decls.iter().any(|d| {
                                if let Decl::Value { guarded, .. } = d {
                                    is_unconditional_for_exhaustiveness(guarded)
                                } else {
                                    false
                                }
                            });
                            if !has_fallback {
                                errors.push(TypeError::NoInstanceFound {
                                    span: first_span,
                                    class_name: unqualified_ident("Partial"),
                                    type_args: vec![],
                                });
                            }
                        }
                        ctx.has_non_exhaustive_pattern_guards = false;

                        // Check for partial lambdas (multi-equation).
                        // Skip for multi-equation functions (first_arity > 0) because
                        // individual equation binders are expected to be partial — the
                        // overall exhaustiveness is checked by check_multi_eq_exhaustiveness.
                        if first_arity == 0 && !partial_names.contains(name) && ctx.has_partial_lambda {
                            if !ctx.non_exhaustive_errors.is_empty() {
                                errors.extend(ctx.non_exhaustive_errors.drain(..));
                            } else {
                                errors.push(TypeError::NoInstanceFound {
                                    span: first_span,
                                    class_name: unqualified_ident("Partial"),
                                    type_args: vec![],
                                });
                            }
                        }
                        ctx.has_partial_lambda = false;
                        ctx.non_exhaustive_errors.clear();

                        errors.extend(ctx.drain_pending_holes());

                        result_types.insert(*name, zonked);
                    }
                } else if let Some(sig_ty) = sig {
                    errors.extend(ctx.drain_pending_holes());
                    let scheme = Scheme::mono(ctx.state.zonk(sig_ty.clone()));
                    env.insert_scheme(*name, scheme.clone());
                    local_values.insert(*name, scheme);
                }
                ctx.scoped_type_vars = prev_scoped_multi;
            }
        }

        // Deferred generalization for mutual recursion SCC
        if is_mutual {
            for cv in &checked_values {
                let cv_span = value_groups
                    .iter()
                    .find(|(n, _)| *n == cv.name)
                    .and_then(|(_, decls)| decls.first())
                    .and_then(|d| {
                        if let Decl::Value { span, .. } = d {
                            Some(*span)
                        } else {
                            None
                        }
                    })
                    .unwrap_or(crate::span::Span::new(0, 0));
                let scheme = if let Some(sig_ty) = &cv.sig {
                    Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                } else {
                    let zonked = ctx.state.zonk(cv.ty.clone());
                    // Check CannotGeneralizeRecursiveFunction for mutual recursion
                    if let Some(err) = check_cannot_generalize_recursive(
                        &mut ctx.state,
                        &ctx.deferred_constraints,
                        &ctx.op_deferred_constraints,
                        cv.name,
                        cv_span,
                        &zonked,
                    ) {
                        errors.push(err);
                    }
                    env.generalize_excluding(&mut ctx.state, zonked, cv.name)
                };
                let zonked = ctx.state.zonk(cv.ty.clone());
                env.insert_scheme(cv.name, scheme.clone());
                local_values.insert(cv.name, scheme);
                result_types.insert(cv.name, zonked);
            }
        }
    }

    // Pass 2.5: Process value-level fixity declarations for targets defined
    // as value decls (now typechecked in Pass 2) or imported values.
    for decl in &module.decls {
        if let Decl::Fixity {
            target,
            operator,
            is_type: false,
            ..
        } = decl
        {
            if let Some(scheme) = local_values.get(&target.name).cloned() {
                env.insert_scheme(operator.value, scheme.clone());
                local_values.insert(operator.value, scheme);
            } else if let Some(scheme) = env.lookup(target.name).cloned() {
                if ctx.state.free_unif_vars(&scheme.ty).is_empty() {
                    env.insert_scheme(operator.value, scheme.clone());
                    local_values.insert(operator.value, scheme);
                }
            }
        }
    }

    // Pass 2.5: Validate superclass constraints for locally-registered instances.
    // For each instance `C T1 T2`, check that all superclass constraints of `C`
    // are satisfied when substituting the class type vars with the instance types.
    // Only check classes that are locally defined — imported classes' instances
    // were validated in their source module.
    for (span, class_name, inst_types) in &registered_instances {
        if !local_class_names.contains(class_name) {
            continue;
        }
        if let Some((class_tvs, sc_constraints)) = class_superclasses.get(&qi(class_name.clone())) {
            if class_tvs.len() == inst_types.len() {
                let subst: HashMap<Symbol, Type> = class_tvs
                    .iter()
                    .copied()
                    .zip(inst_types.iter().cloned())
                    .collect();
                for (sc_class, sc_args) in sc_constraints {
                    // Only check superclasses that are locally defined or have
                    // zero instances (imported superclasses may have instances
                    // our resolution can't match, e.g. Profunctor Function).
                    let sc_is_local = sc_class.module == None;
                    let sc_has_no_instances = !instances.contains_key(sc_class)
                        || instances.get(sc_class).map_or(true, |v| v.is_empty());
                    if !sc_is_local && !sc_has_no_instances {
                        continue;
                    }
                    let concrete_args: Vec<Type> =
                        sc_args.iter().map(|t| apply_var_subst(&subst, t)).collect();
                    let has_vars = concrete_args.iter().any(|t| contains_type_var(t));
                    let has_unif = concrete_args
                        .iter()
                        .any(|t| !ctx.state.free_unif_vars(t).is_empty());
                    if !has_vars
                        && !has_unif
                        && !has_matching_instance_depth(
                            &instances,
                            &ctx.state.type_aliases,
                            sc_class,
                            &concrete_args,
                            0,
                            Some(&ctx.type_con_arities),
                        )
                    {
                        errors.push(TypeError::NoInstanceFound {
                            span: *span,
                            class_name: *sc_class,
                            type_args: concrete_args,
                        });
                    }
                }
            }
        }
    }

    // Pre-compute the set of "given" class names from instance declarations (given_class_names)
    // including transitive superclasses. Used by Pass 2.5 (sig_deferred_constraints).
    let mut given_classes_expanded: HashSet<Symbol> = HashSet::new();
    for gcn in &ctx.given_class_names {
        given_classes_expanded.insert(gcn.name);
        let mut stack = vec![gcn.name];
        while let Some(cls) = stack.pop() {
            if let Some((_, sc_constraints)) = class_superclasses.get(&qi(cls)) {
                for (sc_class, _) in sc_constraints {
                    if given_classes_expanded.insert(sc_class.name) {
                        stack.push(sc_class.name);
                    }
                }
            }
        }
    }

    // Extended set for Pass 3 zero-instance checks: includes classes from all function
    // signature_constraints. When a class method is called from a function that doesn't
    // have the class in its own signature, the constraint gets type-var args after
    // generalization. This set is used ONLY for zero-instance checks, NOT for chain
    // ambiguity — chain ambiguity must use the narrower given_classes_expanded to catch
    // cases like 3531 where `C a` is ambiguous through an instance chain.
    let mut given_classes_for_zero_instance: HashSet<Symbol> = given_classes_expanded.clone();
    for constraints in ctx.signature_constraints.values() {
        for (class_name, _) in constraints {
            given_classes_for_zero_instance.insert(class_name.name);
            let mut stack = vec![class_name.name];
            while let Some(cls) = stack.pop() {
                if let Some((_, sc_constraints)) = class_superclasses.get(&qi(cls)) {
                    for (sc_class, _) in sc_constraints {
                        if given_classes_for_zero_instance.insert(sc_class.name) {
                            stack.push(sc_class.name);
                        }
                    }
                }
            }
        }
    }

    // Pass 2.5: Check signature-propagated constraints for zero-instance classes.
    // These constraints come from type signatures (e.g. `Foo a => ...`) and are only
    // checked for the case where the class has absolutely zero instances, since our
    // instance resolution may not handle complex imported instances correctly.
    for (span, class_name, type_args) in &ctx.sig_deferred_constraints {
        let zonked_args: Vec<Type> = type_args
            .iter()
            .map(|t| ctx.state.zonk(t.clone()))
            .collect();

        let all_pure_unif = zonked_args.iter().all(|t| matches!(t, Type::Unif(_)));
        let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
        let class_has_instances = lookup_instances(&instances, class_name)
            .map_or(false, |insts| !insts.is_empty());
        if !class_has_instances {
            // Skip if the class is a "given" constraint from an enclosing function signature
            // (including transitive superclasses). These constraints are declared requirements
            // that callers must satisfy — they shouldn't be checked for local instances.
            let is_given_by_signature = given_classes_expanded.contains(&class_name.name);
            if is_given_by_signature {
                continue;
            }
            // If all args are unsolved, the constraint may be satisfied at a downstream call
            // site. Only fire when at least one arg is concrete and there are no type vars.
            if !all_pure_unif && !has_type_vars {
                // Skip compiler-magic classes that are resolved without explicit instances
                let is_magic = ctx.prim_class_names.contains(&class_name.name);
                if !is_magic {
                    errors.push(TypeError::NoInstanceFound {
                        span: *span,
                        class_name: *class_name,
                        type_args: zonked_args,
                    });
                }
            }
            continue;
        }

        // For chained classes with structured type args and polymorphic type vars,
        // use chain-aware ambiguity checking. This catches ambiguous instance chain
        // matches like Same (Proxy t) (Proxy Int) where the chain can't determine
        // which instance to use.
        if has_type_vars && chained_classes.contains(class_name) {
            let has_structured_arg = zonked_args
                .iter()
                .any(|t| matches!(t, Type::App(_, _) | Type::Record(_, _) | Type::Fun(_, _)));
            // Skip if the structured args themselves contain unif vars —
            // these constraints are not yet resolved enough for chain ambiguity checking
            let structured_args_have_unif = zonked_args.iter().any(|t| {
                matches!(t, Type::App(_, _) | Type::Record(_, _) | Type::Fun(_, _))
                    && !ctx.state.free_unif_vars(t).is_empty()
            });
            // Skip when all args are purely polymorphic (no concrete type constructors).
            // Fully polymorphic constraints like `ToRecordObj codecsRL { | codecs } { | values }`
            // can't be resolved at the definition site — they'll be satisfied by callers.
            let has_any_concrete = zonked_args.iter().any(|t| type_has_concrete_con(t));
            if has_structured_arg && !structured_args_have_unif && has_any_concrete {
                if let Some(known) = lookup_instances(&instances, class_name) {
                    match check_chain_ambiguity(known, &zonked_args) {
                        ChainResult::Resolved => {}
                        ChainResult::Ambiguous | ChainResult::NoMatch => {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name,
                                type_args: zonked_args,
                            });
                        }
                    }
                }
            }
        }
    }

    // Pass 2.75: Solve type-level constraints (ToString, Add, Mul).
    // Run before Pass 3 so that solved constraints produce unification errors
    // when the computed result conflicts with existing types.
    // Multiple iterations handle chains like Mul -> Add -> ToString.
    for _ in 0..3 {
        let mut solved_any = false;
        for i in 0..ctx.deferred_constraints.len() {
            let (span, class_name, _) = ctx.deferred_constraints[i];
            let class_str = crate::interner::resolve(class_name.name).unwrap_or_default();
            let zonked_args: Vec<Type> = ctx.deferred_constraints[i]
                .2
                .iter()
                .map(|t| {
                    let z = ctx.state.zonk(t.clone());
                    // Expand type aliases so e.g. Common.NegOne becomes TypeInt(-1)
                    expand_type_aliases_limited(&z, &ctx.state.type_aliases, 0)
                })
                .collect();
            match class_str.as_str() {
                "ToString" if zonked_args.len() == 2 => {
                    if let Type::TypeInt(n) = &zonked_args[0] {
                        let expected = Type::TypeString(crate::interner::intern(&n.to_string()));
                        if let Err(e) = ctx.state.unify(span, &zonked_args[1], &expected) {
                            errors.push(e);
                        } else {
                            solved_any = true;
                        }
                    }
                }
                "Add" if zonked_args.len() == 3 => {
                    if let (Type::TypeInt(a), Type::TypeInt(b)) = (&zonked_args[0], &zonked_args[1])
                    {
                        let result = Type::TypeInt(a.wrapping_add(*b));
                        if let Err(e) = ctx.state.unify(span, &zonked_args[2], &result) {
                            errors.push(e);
                        } else {
                            solved_any = true;
                        }
                    }
                }
                "Mul" if zonked_args.len() == 3 => {
                    if let (Type::TypeInt(a), Type::TypeInt(b)) = (&zonked_args[0], &zonked_args[1])
                    {
                        let result = Type::TypeInt(a.wrapping_mul(*b));
                        if let Err(e) = ctx.state.unify(span, &zonked_args[2], &result) {
                            errors.push(e);
                        } else {
                            solved_any = true;
                        }
                    }
                }
                "Compare" if zonked_args.len() == 3 => {
                    if let (Type::TypeInt(a), Type::TypeInt(b)) = (&zonked_args[0], &zonked_args[1])
                    {
                        let ordering_str = match a.cmp(b) {
                            std::cmp::Ordering::Less => "LT",
                            std::cmp::Ordering::Equal => "EQ",
                            std::cmp::Ordering::Greater => "GT",
                        };
                        let result = Type::Con(qi(intern(ordering_str)));
                        if let Err(e) = ctx.state.unify(span, &zonked_args[2], &result) {
                            errors.push(e);
                        } else {
                            solved_any = true;
                        }
                    }
                }
                "Nub" if zonked_args.len() == 2 => {
                    // Row.Nub input output: compute the nub of the input row
                    // (remove duplicate labels) and unify with output.
                    if let Some(nubbed) = try_nub_row(&zonked_args[0]) {
                        if let Err(e) = ctx.state.unify(span, &zonked_args[1], &nubbed) {
                            errors.push(e);
                        } else {
                            solved_any = true;
                        }
                    }
                }
                "Append" if zonked_args.len() == 3 => {
                    // Symbol.Append left right output: concatenate two type-level symbols.
                    if let (Type::TypeString(a), Type::TypeString(b)) = (&zonked_args[0], &zonked_args[1]) {
                        let a_str = crate::interner::resolve(*a).unwrap_or_default();
                        let b_str = crate::interner::resolve(*b).unwrap_or_default();
                        let result = Type::TypeString(crate::interner::intern(&format!("{}{}", a_str, b_str)));
                        if let Err(e) = ctx.state.unify(span, &zonked_args[2], &result) {
                            errors.push(e);
                        } else {
                            solved_any = true;
                        }
                    }
                }
                "Union" if zonked_args.len() == 3 => {
                    // Row.Union left right output: merge left and right rows into output.
                    // Only solve when left and right are concrete record rows.
                    if let Some(merged) = try_union_rows(&zonked_args[0], &zonked_args[1]) {
                        if let Err(e) = ctx.state.unify(span, &zonked_args[2], &merged) {
                            errors.push(e);
                        } else {
                            solved_any = true;
                        }
                    }
                }
                _ => {}
            }
        }
        if !solved_any {
            break;
        }
    }

    timed_pass!(2, "done", "");

    // Pass 2.8: Solve Reflectable constraints by unifying the value type.
    // Reflectable is compiler-magic: `Reflectable "foo" v` implies `v ~ String`, etc.
    // This must happen before Pass 3's general constraint checking so that downstream
    // constraints (like `Show { field :: v }`) see the solved type.
    for (_span, class_name, type_args) in ctx.deferred_constraints.iter() {
        let class_str = crate::interner::resolve(class_name.name).unwrap_or_default();
        if class_str != "Reflectable" { continue; }
        if type_args.len() != 2 { continue; }
        let zonked_0 = ctx.state.zonk(type_args[0].clone());
        let zonked_1 = ctx.state.zonk(type_args[1].clone());
        // Only solve when the second arg is still unsolved (Unif var)
        if !matches!(zonked_1, Type::Unif(_)) { continue; }
        let target_type = match &zonked_0 {
            Type::TypeString(_) => Some(Type::Con(qi(crate::interner::intern("String")))),
            Type::TypeInt(_) => Some(Type::Con(qi(crate::interner::intern("Int")))),
            Type::Con(c) => {
                let name = crate::interner::resolve(c.name).unwrap_or_default().to_string();
                match name.as_str() {
                    "True" | "False" => Some(Type::Con(qi(crate::interner::intern("Boolean")))),
                    "LT" | "EQ" | "GT" => Some(Type::Con(qi(crate::interner::intern("Ordering")))),
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(target) = target_type {
            let _ = ctx.state.unify(*_span, &zonked_1, &target);
        }
    }

    // Pass 3: Check deferred type class constraints
    for (span, class_name, type_args) in ctx.deferred_constraints.iter() {
        let zonked_args: Vec<Type> = type_args
            .iter()
            .map(|t| ctx.state.zonk(t.clone()))
            .collect();
        // Skip if any arg still contains unsolved unification variables or type variables
        // (polymorphic usage — no concrete instance needed).
        // We check deeply since unif vars can be nested inside App, e.g. Show ((?1 ?2) ?2).
        let has_unsolved = zonked_args
            .iter()
            .any(|t| !ctx.state.free_unif_vars(t).is_empty() || contains_type_var(t));

        if has_unsolved {
            // For classes with instance chains: check for ambiguous chain resolution.
            // Only when ALL args are bare type variables (Type::Var) — not Unif vars
            // and not structured types containing variables. This conservative check
            // catches the common case where `C a` is ambiguous for a chain like
            // `C String else C a`, without false-positiving on structured args like
            // `Inject f (Either f g)` where the chain can be definitively resolved.
            let all_bare_vars = zonked_args.iter().all(|t| matches!(t, Type::Var(_)));
            if all_bare_vars && chained_classes.contains(class_name) {
                // Skip if the class is "given" by an enclosing instance context
                // (including transitive superclasses) OR by an explicit type signature.
                // Instance context constraints are satisfied by callers.
                // Explicit signature constraints (e.g. `Axes n a => ...`) are declared
                // requirements — the constraint is intentionally polymorphic.
                // Inferred signature constraints (from body usage without explicit
                // declaration) are NOT skipped — those represent actual ambiguity.
                let is_given = given_classes_expanded.contains(&class_name.name)
                    || explicit_sig_classes.contains(&class_name.name);
                if !is_given {
                    if let Some(known) = lookup_instances(&instances, class_name) {
                        let has_concrete_instance = known.iter().any(|(inst_types, _, _)| {
                            inst_types.iter().any(|t| !matches!(t, Type::Var(_)))
                        });
                        if has_concrete_instance {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name,
                                type_args: zonked_args,
                            });
                        }
                    }
                }
                continue;
            }

            // For chained classes with structured args containing a mix of concrete
            // types and unsolved vars, try instance resolution. This catches cases
            // like C (X ?a Int) where instance chain `C (X x x) else Fail => C (X x y)`
            // can't be resolved. Only when at least one arg is a structured type
            // (App/Record/Fun) — bare Var/Unif/Con args alone shouldn't trigger this.
            let all_pure_unif = zonked_args.iter().all(|t| matches!(t, Type::Unif(_)));
            let has_structured_arg = zonked_args
                .iter()
                .any(|t| matches!(t, Type::App(_, _) | Type::Record(_, _) | Type::Fun(_, _)));
            if chained_classes.contains(class_name)
                && !all_bare_vars
                && !all_pure_unif
                && has_structured_arg
            {
                // Skip if the class is "given" by an enclosing function's type signature
                // (including transitive superclasses).
                let is_given = given_classes_expanded.contains(&class_name.name);
                if is_given {
                    continue;
                }

                // When args contain forall-bound type variables (Type::Var), use chain-aware
                // ambiguity checking. This properly handles cases like Inject g (Either f g)
                // where an earlier instance in the chain is "not Apart" (could match if g=f)
                // but our exact matcher says no-match and skips to a later instance.
                let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
                if has_type_vars {
                    // If there are also unsolved unification variables, skip the check —
                    // we can't determine chain ambiguity with partially-known types.
                    let has_unif_vars = zonked_args
                        .iter()
                        .any(|t| !ctx.state.free_unif_vars(t).is_empty());
                    if has_unif_vars {
                        continue;
                    }
                    if let Some(known) = lookup_instances(&instances, class_name) {
                        match check_chain_ambiguity(known, &zonked_args) {
                            ChainResult::Resolved => {}
                            ChainResult::Ambiguous | ChainResult::NoMatch => {
                                errors.push(TypeError::NoInstanceFound {
                                    span: *span,
                                    class_name: *class_name,
                                    type_args: zonked_args,
                                });
                            }
                        }
                    }
                } else {
                    // If any arg is a bare unif var, instance resolution can't
                    // match it against constructor-headed instance patterns (like
                    // RL.Cons/RL.Nil in RowList-based classes). Defer — the unif
                    // var may be resolved by another constraint (e.g., RowToList).
                    let has_bare_unif = zonked_args.iter().any(|t| matches!(t, Type::Unif(_)));
                    if has_bare_unif {
                        continue;
                    }
                    match check_instance_depth(
                        &instances,
                        &ctx.state.type_aliases,
                        class_name,
                        &zonked_args,
                        0,
                        Some(&known_classes),
                        Some(&ctx.type_con_arities),
                    ) {
                        InstanceResult::Match => {}
                        InstanceResult::NoMatch => {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name,
                                type_args: zonked_args,
                            });
                        }
                        InstanceResult::DepthExceeded => {
                            errors.push(TypeError::PossiblyInfiniteInstance {
                                span: *span,
                                class_name: *class_name,
                                type_args: zonked_args,
                            });
                        }
                        InstanceResult::UnknownClass(unknown) => {
                            errors.push(TypeError::UnknownClass {
                                span: *span,
                                name: unknown,
                            });
                        }
                    }
                }
                continue;
            }

            {
                let class_str = crate::interner::resolve(class_name.name).unwrap_or_default();
                let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
                if class_str == "Coercible" && zonked_args.len() == 2 && !has_type_vars {
                    // Skip Coercible solving when unif vars are in structural positions
                    // (bare Unif args, or inside App/Fun args). The solver can't handle
                    // partial types like Coercible ?543 (Array X) from GraphQL queries.
                    // But keep solving when unif vars are only in row tails — the solver
                    // CAN determine coercibility from the record field structure alone.
                    let has_structural_unif = zonked_args
                        .iter()
                        .any(|t| has_unif_outside_row_tails(t));
                    if has_structural_unif {
                        continue;
                    }
                    match solve_coercible(
                        &zonked_args[0],
                        &zonked_args[1],
                        &[],
                        &ctx.type_roles,
                        &ctx.newtype_names,
                        &ctx.state.type_aliases,
                        &ctx.ctor_details,
                        0,
                    ) {
                        CoercibleResult::Solved => {
                            ctx.resolved_dicts
                                .entry(*span)
                                .or_default()
                                .push((class_name.name, crate::typechecker::registry::DictExpr::ZeroCost));
                        }
                        CoercibleResult::NotCoercible => {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name,
                                type_args: zonked_args,
                            });
                        }
                        CoercibleResult::TypesDoNotUnify => {
                            errors.push(TypeError::UnificationError {
                                span: *span,
                                expected: zonked_args[0].clone(),
                                found: zonked_args[1].clone(),
                            });
                        }
                        CoercibleResult::DepthExceeded => {
                            errors.push(TypeError::PossiblyInfiniteCoercibleInstance {
                                span: *span,
                                class_name: *class_name,
                                type_args: zonked_args,
                            });
                        }
                        CoercibleResult::KindMismatch => {
                            errors.push(TypeError::KindsDoNotUnify {
                                span: *span,
                                expected: zonked_args[0].clone(),
                                found: zonked_args[1].clone(),
                            });
                        }
                    }
                    continue;
                }
            }

            // Check if the class has zero registered instances — if so, the constraint
            // is guaranteed unsatisfiable regardless of what the unsolved vars become.
            // Only fire when concrete types (no type variables) are present — constraints
            // from polymorphic contexts like `forall a. Foo a => ...` are satisfied by callers.
            // When all args are pure unsolved unif vars, only report if the constraint is NOT
            // "given" by a type signature (i.e., it arose from the body, not the declared type).
            // Given constraints (from signatures) will be discharged by callers, even if zero
            // instances are visible locally (instances may exist in downstream modules).
            let class_has_instances = instances
                .get(class_name)
                .map_or(false, |insts| !insts.is_empty());
            let all_pure_unif = zonked_args.iter().all(|t| matches!(t, Type::Unif(_)));
            let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
            // Check if any arg contains unsolved unif vars (mixed with concrete types).
            // When mixed unif vars are present, the constraint may be satisfiable through
            // superclass constraints not yet tracked in signature_constraints.
            // But reject pure-unif constraints (all args unknown) with zero instances.
            let has_mixed_unif = !all_pure_unif && zonked_args.iter().any(|t| !ctx.state.free_unif_vars(t).is_empty());
            let is_given = given_classes_for_zero_instance.contains(&class_name.name);
            // Also treat constraints as "given" if all their unif vars were generalized
            // in a let/where binding (e.g., `where bind = ibind` generalizes the class
            // method's constraint vars — they belong to the polymorphic scheme, not the
            // outer context, so the constraint is satisfied by callers).
            let all_generalized = all_pure_unif && zonked_args.iter().all(|t| {
                if let Type::Unif(id) = t {
                    ctx.state.generalized_vars.contains(id)
                } else {
                    false
                }
            });
            if !class_has_instances && !has_type_vars && !has_mixed_unif
                && (!all_pure_unif || (!is_given && !all_generalized))
            {
                // Skip compiler-magic classes that are resolved without explicit instances
                let is_magic = ctx.prim_class_names.contains(&class_name.name);
                if !is_magic {
                    errors.push(TypeError::NoInstanceFound {
                        span: *span,
                        class_name: *class_name,
                        type_args: zonked_args,
                    });
                }
            }
            continue;
        }

        // Skip type-level solver classes that are resolved by Pass 2.75 solving,
        // not by explicit instances. Without this, fully-resolved Add/Mul/ToString
        // constraints would fail instance resolution since they have no instances.
        // Note: Lacks is NOT skipped here — it's handled by check_instance_depth
        // which correctly rejects Lacks "x" (x :: Int, ...) for concrete rows.
        {
            let class_str = crate::interner::resolve(class_name.name).unwrap_or_default();
            if matches!(
                class_str.as_str(),
                "Add" | "Mul" | "ToString" | "Compare" | "Nub" | "Union"
            ) {
                continue;
            }
        }

        // Coercible solver: handle Coercible constraints with role-based decomposition.
        // Only solve when no type variables remain (polymorphic constraints are deferred).
        if !has_unsolved {
             // TODO: check module
            let class_str = crate::interner::resolve(class_name.name).unwrap_or_default();
            if class_str == "Coercible" && zonked_args.len() == 2 {
                match solve_coercible(
                    &zonked_args[0],
                    &zonked_args[1],
                    &[], // No givens for concrete-type constraints in Pass 3
                    &ctx.type_roles,
                    &ctx.newtype_names,
                    &ctx.state.type_aliases,
                    &ctx.ctor_details,
                    0,
                ) {
                    CoercibleResult::Solved => {
                        ctx.resolved_dicts
                            .entry(*span)
                            .or_default()
                            .push((class_name.name, crate::typechecker::registry::DictExpr::ZeroCost));
                    }
                    CoercibleResult::NotCoercible => {
                        errors.push(TypeError::NoInstanceFound {
                            span: *span,
                            class_name: *class_name,
                            type_args: zonked_args,
                        });
                    }
                    CoercibleResult::TypesDoNotUnify => {
                        errors.push(TypeError::UnificationError {
                            span: *span,
                            expected: zonked_args[0].clone(),
                            found: zonked_args[1].clone(),
                        });
                    }
                    CoercibleResult::DepthExceeded => {
                        errors.push(TypeError::PossiblyInfiniteCoercibleInstance {
                            span: *span,
                            class_name: *class_name,
                            type_args: zonked_args,
                        });
                    }
                    CoercibleResult::KindMismatch => {
                        errors.push(TypeError::KindsDoNotUnify {
                            span: *span,
                            expected: zonked_args[0].clone(),
                            found: zonked_args[1].clone(),
                        });
                    }
                }
                continue;
            }
        }

        // If the class itself is not known (not in any instance map and no
        // methods registered), produce UnknownClass instead of NoInstanceFound.
        // Use lookup_instances for qualified fallback (e.g. SimpleJson.WriteForeign → WriteForeign).
        // Also check known_classes / class_param_counts for zero-method marker classes
        // (e.g. `class AttendeeAuth` with no type params and no methods).
        let class_is_known = lookup_instances(&instances, class_name).is_some()
            || ctx.class_methods.values().any(|(cn, _)| cn == class_name || cn.name == class_name.name)
            || known_classes.contains(class_name);
        if !class_is_known {
            errors.push(TypeError::UnknownClass {
                span: *span,
                name: *class_name,
            });
        } else if zonked_args.is_empty() && given_classes_for_zero_instance.contains(&class_name.name) {
            // Zero-arg marker constraint (e.g. `AttendeeAuth =>`) that is declared
            // in a function signature — discharged by callers, not instance resolution.
        } else {
            // For chained classes with type variables in args, use chain-aware
            // ambiguity checking. A chain like `C String else C a` is ambiguous
            // when queried with `C a` (rigid type var) — the first instance
            // "could match" (a might be String) but doesn't "definitely match".
            let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
            if has_type_vars && chained_classes.contains(class_name) {
                if let Some(known) = lookup_instances(&instances, class_name) {
                    match check_chain_ambiguity(known, &zonked_args) {
                        ChainResult::Resolved => {}
                        ChainResult::Ambiguous | ChainResult::NoMatch => {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name,
                                type_args: zonked_args,
                            });
                        }
                    }
                }
            } else {
                match check_instance_depth(
                    &instances,
                    &ctx.state.type_aliases,
                    class_name,
                    &zonked_args,
                    0,
                    Some(&known_classes),
                    Some(&ctx.type_con_arities),
                ) {
                    InstanceResult::Match => {
                        // Kind-check the constraint type against the class's kind signature.
                        if type_args.len() == 1 {
                            if let Type::Unif(param_id) = &type_args[0] {
                                if let Some(app_args) = ctx.class_param_app_args.get(param_id) {
                                    let zonked_app_args: Vec<Type> =
                                        app_args.iter().map(|t| ctx.state.zonk(t.clone())).collect();
                                    if let Err(e) = check_class_param_kind_consistency(
                                        *span,
                                        *class_name,
                                        &zonked_args[0],
                                        &zonked_app_args,
                                        &saved_type_kinds,
                                        &saved_class_kinds,
                                    ) {
                                        errors.push(e);
                                    }
                                }
                            }
                        }
                    }
                    InstanceResult::NoMatch => {
                        errors.push(TypeError::NoInstanceFound {
                            span: *span,
                            class_name: *class_name,
                            type_args: zonked_args,
                        });
                    }
                    InstanceResult::DepthExceeded => {
                        errors.push(TypeError::PossiblyInfiniteInstance {
                            span: *span,
                            class_name: *class_name,
                            type_args: zonked_args,
                        });
                    }
                    InstanceResult::UnknownClass(unknown) => {
                        errors.push(TypeError::UnknownClass {
                            span: *span,
                            name: unknown,
                        });
                    }
                }
            }
        }
    }

    // Also check operator-deferred constraints for PossiblyInfiniteInstance only.
    // We don't check NoInstanceFound for operator constraints because our instance
    // resolver can't handle all valid cases (e.g., structural record Eq).
    for (span, class_name, type_args) in &ctx.op_deferred_constraints {
        let zonked_args: Vec<Type> = type_args
            .iter()
            .map(|t| ctx.state.zonk(t.clone()))
            .collect();
        let has_unsolved = zonked_args
            .iter()
            .any(|t| !ctx.state.free_unif_vars(t).is_empty() || contains_type_var(t));
        if has_unsolved {
            continue;
        }
        if let InstanceResult::DepthExceeded = check_instance_depth(
            &instances,
            &ctx.state.type_aliases,
            class_name,
            &zonked_args,
            0,
            None,
            Some(&ctx.type_con_arities),
        ) {
            errors.push(TypeError::PossiblyInfiniteInstance {
                span: *span,
                class_name: *class_name,
                type_args: zonked_args,
            });
        }
    }

    // Dict resolution for codegen: resolve concrete deferred constraints to instance dicts.
    // Build a combined instance registry from local instances + all imported modules.
    {
        let mut combined_registry: HashMap<(Symbol, Symbol), (Symbol, Option<Vec<Symbol>>)> = HashMap::new();
        // Add imported instances from registry
        for (mod_parts, mod_exports) in registry.iter_all() {
            for (&(class, head), &inst_name) in &mod_exports.instance_registry {
                combined_registry.entry((class, head))
                    .or_insert((inst_name, Some(mod_parts.to_vec())));
            }
        }
        // Add local instances (override imported)
        for (&(class, head), &inst_name) in &instance_registry_entries {
            combined_registry.insert((class, head), (inst_name, None));
        }
        // Build combined instance_var_kinds from imported modules + local
        let mut combined_instance_var_kinds: HashMap<Symbol, HashMap<Symbol, Symbol>> = HashMap::new();
        for (_, mod_exports) in registry.iter_all() {
            for (inst_name, kinds) in &mod_exports.instance_var_kinds {
                combined_instance_var_kinds.entry(*inst_name).or_insert_with(|| kinds.clone());
            }
        }
        for (inst_name, kinds) in &instance_var_kinds_entries {
            combined_instance_var_kinds.insert(*inst_name, kinds.clone());
        }

        // Also build combined registry for op_deferred_constraints
        let all_constraints: Vec<(usize, bool)> = (0..ctx.deferred_constraints.len())
            .map(|i| (i, false))
            .chain((0..ctx.op_deferred_constraints.len()).map(|i| (i, true)))
            .collect();

        for (idx, is_op) in &all_constraints {
            let (constraint_span_dbg, class_name, type_args) = if *is_op {
                &ctx.op_deferred_constraints[*idx]
            } else {
                &ctx.deferred_constraints[*idx]
            };

            let zonked_args: Vec<Type> = type_args
                .iter()
                .map(|t| ctx.state.zonk(t.clone()))
                .collect();

            // Skip if any arg has truly unsolved unif vars (not generalized).
            // Generalized unif vars (from finalize_scheme) are type parameters that
            // won't be solved further — they're safe to pass through to instance matching.
            let has_unsolved = zonked_args.iter().any(|t| {
                ctx.state
                    .free_unif_vars(t)
                    .iter()
                    .any(|v| !ctx.state.generalized_vars.contains(v))
            });

            if has_unsolved {
                // Even with unsolved vars, try to resolve the dict anyway.
                // Many instances like `Functor (ST h)` → `functorST` don't depend on
                // the unsolved vars. If resolution succeeds, use it.
                let dict_expr_result = resolve_dict_expr_from_registry(
                    &combined_registry,
                    &instances,
                    &ctx.state.type_aliases,
                    class_name,
                    &zonked_args,
                    Some(&ctx.type_con_arities),
                    &combined_instance_var_kinds,
                );
                if let Some(dict_expr) = dict_expr_result {
                    let (constraint_span, _, _) = if *is_op {
                        &ctx.op_deferred_constraints[*idx]
                    } else {
                        &ctx.deferred_constraints[*idx]
                    };
                    ctx.resolved_dicts
                        .entry(*constraint_span)
                        .or_insert_with(Vec::new)
                        .push((class_name.name, dict_expr));
                }
                continue;
            }

            // Try to resolve the dict
            let dict_expr_result = resolve_dict_expr_from_registry(
                &combined_registry,
                &instances,
                &ctx.state.type_aliases,
                class_name,
                &zonked_args,
                Some(&ctx.type_con_arities),
                &combined_instance_var_kinds,
            );
            if let Some(dict_expr) = dict_expr_result {
                let (constraint_span, _, _) = if *is_op {
                    &ctx.op_deferred_constraints[*idx]
                } else {
                    &ctx.deferred_constraints[*idx]
                };
                ctx.resolved_dicts
                    .entry(*constraint_span)
                    .or_insert_with(Vec::new)
                    .push((class_name.name, dict_expr));
            }
        }

        // Note: ConstraintArg resolution for instance method constraints is done in the
        // codegen_deferred_constraints block below, since "given" constraints go there.

        // Constraint parameter resolution for codegen_deferred_constraints (given/instance constraints).
        // Same logic as above, but for constraints that were resolved as "given" in instance scope.
        {
            use crate::typechecker::registry::DictExpr;
            use crate::typechecker::types::TyVarId;

            // Group entries by (instance_id, class_name) — this correctly merges entries from
            // multi-equation methods (which have different binding spans but the same instance ID).
            let mut unresolved_groups: HashMap<(usize, Symbol), Vec<(usize, Vec<TyVarId>, crate::span::Span)>> = HashMap::new();
            for (idx, (constraint_span, class_name, type_args, _is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
                // Only skip if THIS specific class was already resolved for this span
                if ctx.resolved_dicts.get(constraint_span).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name)) { continue; }
                let binding_span = if idx < ctx.codegen_deferred_constraint_bindings.len() {
                    ctx.codegen_deferred_constraint_bindings[idx]
                } else {
                    None
                };
                let Some(binding) = binding_span else { continue };
                let inst_constraints = match ctx.instance_method_constraints.get(&binding) {
                    Some(c) => c,
                    None => continue,
                };
                let same_class_count = inst_constraints.iter()
                    .filter(|(c, _)| c.name == class_name.name)
                    .count();
                if same_class_count <= 1 { continue; }
                let zonked_args: Vec<Type> = type_args.iter()
                    .map(|t| ctx.state.zonk(t.clone()))
                    .collect();
                let mut unif_ids: Vec<TyVarId> = Vec::new();
                for arg in &zonked_args {
                    if let Type::Unif(id) = arg {
                        unif_ids.push(*id);
                    }
                }
                if unif_ids.is_empty() { continue; }
                // Use instance ID for grouping (falls back to binding-based grouping if no instance ID)
                let instance_id = if idx < ctx.codegen_deferred_constraint_instance_ids.len() {
                    ctx.codegen_deferred_constraint_instance_ids[idx]
                } else {
                    None
                };
                let group_key = if let Some(iid) = instance_id {
                    (iid, class_name.name)
                } else {
                    // Fallback: use binding span start as pseudo-instance-id
                    (binding.start as usize, class_name.name)
                };
                unresolved_groups.entry(group_key)
                    .or_default()
                    .push((idx, unif_ids, binding));
            }

            for ((_, class_name_sym), entries) in unresolved_groups {
                let binding_span = entries[0].2;
                let inst_constraints = match ctx.instance_method_constraints.get(&binding_span) {
                    Some(c) => c,
                    None => continue,
                };
                let class_positions: Vec<usize> = inst_constraints.iter().enumerate()
                    .filter(|(_, (c, _))| c.name == class_name_sym)
                    .map(|(i, _)| i)
                    .collect();

                // Partition entries by zonked type — entries whose unif vars zonk to the
                // same type correspond to the same constraint position. This correctly
                // groups entries from different methods that reference the same type param.
                let mut partitions: HashMap<String, Vec<usize>> = HashMap::new();
                for (idx, unif_ids, _) in &entries {
                    if let Some(&first_unif) = unif_ids.first() {
                        let zonked = ctx.state.zonk(Type::Unif(first_unif));
                        let key = format!("{zonked:?}");
                        partitions.entry(key).or_default().push(*idx);
                    }
                }

                // Sort partitions by earliest span
                let mut partition_list: Vec<(String, Vec<usize>)> = partitions.into_iter().collect();
                partition_list.sort_by_key(|(_, indices)| {
                    indices.iter().map(|idx| {
                        let (span, _, _, _) = &ctx.codegen_deferred_constraints[*idx];
                        span.start
                    }).min().unwrap_or(0)
                });

                // Assign constraint positions to partitions
                for (i, (_, indices)) in partition_list.iter().enumerate() {
                    if i >= class_positions.len() { break; }
                    let constraint_position = class_positions[i];
                    for idx in indices {
                        let (constraint_span, _, _, _) = &ctx.codegen_deferred_constraints[*idx];
                        ctx.resolved_dicts
                            .entry(*constraint_span)
                            .or_insert_with(Vec::new)
                            .push((class_name_sym, DictExpr::ConstraintArg(constraint_position)));
                    }
                }
            }
        }

        // Pre-pass: bind Unif output params from multi-param instance matching.
        // For constraints like Generic (List a) Unif(?), find the matching instance and
        // unify Unif(?) with the instance's output type (e.g., the rep type for Generic).
        // This allows subsequent constraints (like GenericShow rep) to resolve.
        for (_constraint_span, class_name, type_args, _is_do_ado) in ctx.codegen_deferred_constraints.iter() {
            let zonked_args: Vec<Type> = type_args
                .iter()
                .map(|t| ctx.state.zonk(t.clone()))
                .collect();
            // Only process if some args are Unif (output params)
            let has_unif = zonked_args.iter().any(|t| matches!(t, Type::Unif(_)));
            if !has_unif { continue; }
            let head = zonked_args.first().and_then(|t| extract_head_from_type_tc(t));
            let Some(_head) = head else { continue };
            // Look up matching instance to determine output types
            if let Some(known) = lookup_instances(&instances, class_name) {
                for (inst_types, _, _) in known {
                    let mut expanding = HashSet::new();
                    let expanded_inst: Vec<Type> = inst_types
                        .iter()
                        .map(|t| expand_type_aliases_limited_inner(t, &ctx.state.type_aliases, Some(&ctx.type_con_arities), 0, &mut expanding, None))
                        .collect();
                    let mut expanding2 = HashSet::new();
                    let expanded_args: Vec<Type> = zonked_args
                        .iter()
                        .map(|t| expand_type_aliases_limited_inner(t, &ctx.state.type_aliases, Some(&ctx.type_con_arities), 0, &mut expanding2, None))
                        .collect();
                    if expanded_inst.len() != expanded_args.len() { continue; }
                    let mut subst: HashMap<Symbol, Type> = HashMap::new();
                    let matched = expanded_inst
                        .iter()
                        .zip(expanded_args.iter())
                        .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst));
                    if !matched { continue; }
                    // For each Unif in concrete args, bind it to the instance type (with subst applied)
                    let dummy_span = crate::span::Span { start: 0, end: 0 };
                    for (inst_ty, concrete_arg) in expanded_inst.iter().zip(zonked_args.iter()) {
                        if let Type::Unif(id) = concrete_arg {
                            let resolved_ty = apply_var_subst(&subst, inst_ty);
                            let _ = ctx.state.unify(dummy_span, &Type::Unif(*id), &resolved_ty);
                        }
                    }
                    break; // Use first matching instance
                }
            }
        }

        // Process codegen_deferred_constraints (imported function constraints, codegen-only).
        // Run two passes: first pass resolves what it can, second pass picks up constraints
        // whose type args are now resolved due to bindings from the pre-pass or first pass.
        for _pass in 0..2 {
        for (idx, (constraint_span, class_name, type_args, is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
            // Only skip if THIS specific class was already resolved for this span
            let already_resolved = ctx.resolved_dicts.get(constraint_span).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name));
            if already_resolved { continue; }
            let zonked_args: Vec<Type> = type_args
                .iter()
                .map(|t| ctx.state.zonk(t.clone()))
                .collect();

            if *is_do_ado {
                let head_extractable = zonked_args.first()
                    .and_then(|t| extract_head_from_type_tc(t))
                    .is_some();
                if !head_extractable {
                    continue;
                }
            }
            // For non-do/ado constraints, always attempt resolution even with unsolved
            // unif vars. Many imported function constraints (e.g. Show Number) have unif
            // vars that chain through operator desugaring (like $) but the concrete type
            // may be extractable by the resolver. If resolution fails, it just returns None.

            let binding_span = if idx < ctx.codegen_deferred_constraint_bindings.len() {
                ctx.codegen_deferred_constraint_bindings[idx]
            } else {
                None
            };
            let method_constraints = binding_span
                .and_then(|bs| ctx.instance_method_constraints.get(&bs));

            let dict_expr_result = resolve_dict_expr_from_registry_inner(
                &combined_registry,
                &instances,
                &ctx.state.type_aliases,
                class_name,
                &zonked_args,
                Some(&ctx.type_con_arities),
                method_constraints.map(|v| v.as_slice()),
                None,
                false,
                0,
                &combined_instance_var_kinds,
            );
            if let Some(dict_expr) = dict_expr_result {
                ctx.resolved_dicts
                    .entry(*constraint_span)
                    .or_insert_with(Vec::new)
                    .push((class_name.name, dict_expr));
            }
        }
        }
    }

    // Pass 4: Validate module exports and build export info
    // Collect locally declared type/class names
    let mut declared_types: Vec<Symbol> = Vec::new();
    let mut declared_classes: Vec<Symbol> = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::Data { name, .. } | Decl::Newtype { name, .. } => {
                declared_types.push(name.value);
            }
            Decl::TypeAlias { name, .. } => {
                declared_types.push(name.value);
            }
            Decl::Class { name, .. } => {
                declared_classes.push(name.value);
            }
            Decl::ForeignData { name, .. } => {
                declared_types.push(name.value);
            }
            _ => {}
        }
    }

    if let Some(ref export_list) = module.exports {
        for export in &export_list.value.exports {
            match export {
                Export::Value(name) => {
                    let sym = *name;
                    if !result_types.contains_key(&sym) && env.lookup(sym).is_none() {
                        errors.push(TypeError::UnkownExport {
                            span: export_list.span,
                            name: sym,
                        });
                    }
                }
                Export::Type(name, members) => {
                    if !declared_types.contains(name) {
                        errors.push(TypeError::UnkownExport {
                            span: export_list.span,
                            name: *name,
                        });
                    } else if let Some(crate::cst::DataMembers::Explicit(ctors)) = members {
                        // Check that each listed constructor actually belongs to this type
                        let valid_ctors = ctx.data_constructors.get(&qi(*name));
                        for ctor in ctors {
                            let is_valid = valid_ctors.map_or(false, |cs| cs.contains(&qi(ctor.value)));
                            if !is_valid {
                                errors.push(TypeError::UnkownExport {
                                    span: export_list.span,
                                    name: ctor.value,
                                });
                            }
                        }
                        // Check that ALL constructors are listed — partial constructor
                        // exports are not allowed in PureScript.
                        // T() (empty list) is valid — opaque type export.
                        if !ctors.is_empty() {
                            if let Some(all_ctors) = valid_ctors {
                                let exported_set: std::collections::HashSet<QualifiedIdent> =
                                    ctors.iter().map(|c| qi(c.value)).collect();
                                for ctor in all_ctors {
                                    if !exported_set.contains(ctor) {
                                        errors.push(TypeError::TransitiveExportError {
                                            span: export_list.span,
                                            exported: qi(*name),
                                            dependency: *ctor,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
                Export::Class(name) => {
                    if !declared_classes.contains(name) {
                        errors.push(TypeError::UnkownExport {
                            span: export_list.span,
                            name: *name,
                        });
                    }
                }
                Export::TypeOp(_) | Export::Module(_) => {
                    // Type operators and module re-exports: not validated yet
                }
            }
        }

        // Build operator → target maps from fixity declarations
        let mut value_op_targets: HashMap<Symbol, Symbol> = HashMap::new();
        let mut type_op_targets: HashMap<Symbol, Symbol> = HashMap::new();
        for decl in &module.decls {
            if let Decl::Fixity {
                target,
                operator,
                is_type,
                ..
            } = decl
            {
                if *is_type {
                    type_op_targets.insert(operator.value, target.name);
                } else {
                    value_op_targets.insert(operator.value, target.name);
                }
            }
        }

        // Transitive export checks: class members require their class, and vice versa
        let exported_values: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Value(n) => Some(*n),
                _ => None,
            })
            .collect();
        let exported_classes: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Class(n) => Some(*n),
                _ => None,
            })
            .collect();

        // Check: exporting a class member without its class
        for &val in &exported_values {
            if let Some((class_name, _)) = ctx.class_methods.get(&qi(val)) {
                // Only check locally-defined classes (not imported ones)
                if declared_classes.contains(&class_name.name) && !exported_classes.contains(&class_name.name) {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: qi(val),
                        dependency: *class_name,
                    });
                }
            }
        }

        // Check: exporting a class without its members
        for &cls in &exported_classes {
            for (method, (class_name, _)) in &ctx.class_methods {
                if *class_name == qi(cls) && !exported_values.contains(&method.name) {
                    // Only check locally-defined class methods
                    if local_values.contains_key(&method.name) {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(cls),
                            dependency: *method,
                        });
                        break; // One error per class is enough
                    }
                }
            }
        }

        // Check: exporting a class without its superclasses (transitive)
        let declared_class_set: HashSet<Symbol> = declared_classes.iter().copied().collect();
        for &cls in &exported_classes {
            if let Some((_, sc_constraints)) = class_superclasses.get(&qi(cls)) {
                for (sc_class, _) in sc_constraints {
                    // Only check locally-defined superclasses
                    if sc_class.module == None && declared_class_set.contains(&sc_class.name) && !exported_classes.contains(&sc_class.name)
                    {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(cls),
                            dependency: *sc_class,
                        });
                    }
                }
            }
        }

        // Check: exporting a value operator without its target function (local defs only)
        for &val in &exported_values {
            if let Some(&target) = value_op_targets.get(&val) {
                // Only check locally-defined constructors, not imported ones
                let is_local_ctor = ctx.ctor_details.contains_key(&qi(target))
                    && local_values.contains_key(&target);
                if is_local_ctor {
                    // Operator aliases a data constructor — check that the constructor
                    // is exported through its parent type's constructor list.
                    let target_qi = qi(target);
                    let ctor_exported = export_list.value.exports.iter().any(|e| {
                        if let Export::Type(ty_name, Some(members)) = e {
                            let type_ctors = ctx.data_constructors.get(&qi(*ty_name));
                            let has_this_ctor = type_ctors.map_or(false, |cs| cs.contains(&target_qi));
                            has_this_ctor
                                && match members {
                                    crate::cst::DataMembers::All => true,
                                    crate::cst::DataMembers::Explicit(cs) => cs.iter().any(|c| c.value == target),
                                }
                        } else {
                            false
                        }
                    });
                    if !ctor_exported {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(val),
                            dependency: qi(target),
                        });
                    }
                } else if local_values.contains_key(&target) && !exported_values.contains(&target) {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: qi(val),
                        dependency: qi(target),
                    });
                }
            }
        }

        // Check: exporting a type operator without its target type (local defs only)
        let exported_types: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Type(n, _) => Some(*n),
                _ => None,
            })
            .collect();
        let exported_type_ops: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::TypeOp(n) => Some(*n),
                _ => None,
            })
            .collect();
        let declared_type_set: HashSet<&Symbol> = declared_types.iter().collect();
        for &op in &exported_type_ops {
            if let Some(&target) = type_op_targets.get(&op) {
                if declared_type_set.contains(&target) && !exported_types.contains(&target) {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: qi(op),
                        dependency: qi(target),
                    });
                }
            }
        }

        // Check: exporting a type synonym that references a locally-defined type not in exports
        for &ty_name in &exported_types {
            if let Some((_, body)) = ctx.state.type_aliases.get(&ty_name) {
                let mut referenced = Vec::new();
                collect_type_constructors(body, &mut referenced);
                for dep in &referenced {
                    if declared_type_set.contains(dep) && !exported_types.contains(dep) {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(ty_name),
                            dependency: qi(*dep),
                        });
                        break;
                    }
                }
            }
        }

        // Check: exporting a data type with constructors (Type(..)) whose fields reference
        // a locally-defined type not in exports
        for export in &export_list.value.exports {
            if let Export::Type(ty_name, Some(crate::cst::DataMembers::All)) = export {
                // This type is exported with all constructors — check field types
                if let Some(ctors) = ctx.data_constructors.get(&qi(*ty_name)) {
                    'ctor_loop: for ctor in ctors {
                        if let Some((_, _, field_types)) = ctx.ctor_details.get(ctor) {
                            for field_ty in field_types {
                                let mut referenced = Vec::new();
                                collect_type_constructors(field_ty, &mut referenced);
                                for dep in &referenced {
                                    if declared_type_set.contains(dep)
                                        && !exported_types.contains(dep)
                                    {
                                        errors.push(TypeError::TransitiveExportError {
                                            span: export_list.span,
                                            exported: qi(*ty_name),
                                            dependency: qi(*dep),
                                        });
                                        break 'ctor_loop;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Check: exporting a data/newtype type whose kind annotations reference
        // a locally-defined type not in exports (e.g., `data TestProxy (p :: Test)`)
        for export in &export_list.value.exports {
            if let Export::Type(ty_name, _) = export {
                for decl in &module.decls {
                    if let Decl::Data {
                        name,
                        type_var_kind_anns,
                        ..
                    } = decl
                    {
                        if name.value == *ty_name {
                            for kind_ann in type_var_kind_anns.iter().flatten() {
                                let mut kind_refs = HashSet::new();
                                collect_type_refs(kind_ann, &mut kind_refs);
                                for dep in &kind_refs {
                                    if declared_type_set.contains(dep)
                                        && !exported_types.contains(dep)
                                    {
                                        errors.push(TypeError::TransitiveExportError {
                                            span: export_list.span,
                                            exported: qi(*ty_name),
                                            dependency: qi(*dep),
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Check: exporting a value whose type references a locally-defined type that is not exported.
    // Skip type aliases — PureScript doesn't require type aliases to be explicitly exported
    // for the transitive export check on values (aliases are transparent).
    if let Some(ref export_list) = module.exports {
        let exp_vals: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Value(n) => Some(*n),
                _ => None,
            })
            .collect();
        let exp_types: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Type(n, _) => Some(*n),
                _ => None,
            })
            .collect();
        // Collect local type alias names to exclude from the check
        let local_type_aliases: HashSet<Symbol> = module
            .decls
            .iter()
            .filter_map(|d| match d {
                Decl::TypeAlias { name, .. } => Some(name.value),
                _ => None,
            })
            .collect();
        for &val in &exp_vals {
            if let Some(scheme) = local_values.get(&val) {
                let zonked = ctx.state.zonk(scheme.ty.clone());
                let mut referenced_types = Vec::new();
                collect_type_constructors(&zonked, &mut referenced_types);
                for ty_name in &referenced_types {
                    // Only flag local non-alias types that are not exported
                    if declared_types.contains(ty_name)
                        && !exp_types.contains(ty_name)
                        && !local_type_aliases.contains(ty_name)
                    {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(val),
                            dependency: qi(*ty_name),
                        });
                        break; // One error per value is enough
                    }
                }
            }
        }
    }

    // Build module exports from locally-defined names
    // Only include data_constructors/ctor_details/class_methods/instances
    // for locally-declared types and classes.
    let local_type_set: HashSet<Symbol> = declared_types.iter().copied().collect();
    let local_class_set: HashSet<Symbol> = declared_classes.iter().copied().collect();

    // Build a filtered alias map for export expansion that excludes aliases from
    // qualified imports that collide with data types. This prevents wrong expansion
    // when e.g. `type GqlError = { ... }` alias (from a qualified import) would
    let mut export_data_constructors: HashMap<QualifiedIdent, Vec<QualifiedIdent>> = HashMap::new();
    let mut export_ctor_details: HashMap<QualifiedIdent, (QualifiedIdent, Vec<QualifiedIdent>, Vec<Type>)> = HashMap::new();
    for type_name in &declared_types {
        if let Some(ctors) = ctx.data_constructors.get(&qi(*type_name)) {
            export_data_constructors.insert(qi(*type_name), ctors.clone());
            for ctor in ctors {
                if let Some((parent, tvs, fields)) = ctx.ctor_details.get(ctor) {
                    // Expand type aliases in field types so downstream modules
                    // can resolve them even without importing the alias names
                    // (e.g. NutF wraps Nut' which is a local alias for Entity Int (Node payload)).
                    let expanded_fields: Vec<Type> = fields.iter()
                        .map(|f| expand_type_aliases(f, &ctx.state.type_aliases))
                        .collect();
                    export_ctor_details.insert(*ctor, (*parent, tvs.iter().map(|s| qi(*s)).collect(), expanded_fields));
                }
            }
        }
    }

    // Also export ctor_details for operator aliases (e.g. `:|` for `NonEmpty`, `:` for `Cons`).
    // These are registered during fixity processing but not in data_constructors.
    // Include both locally-defined and imported operators so downstream modules can
    // resolve operator aliases for exhaustiveness checking.
    for (name, (parent, tvs, fields)) in &ctx.ctor_details {
        if !export_ctor_details.contains_key(name) {
            let expanded_fields: Vec<Type> = fields.iter()
                .map(|f| expand_type_aliases(f, &ctx.state.type_aliases))
                .collect();
            export_ctor_details.insert(*name, (*parent, tvs.iter().map(|s| qi(*s)).collect(), expanded_fields));
        }
    }

    let mut export_class_methods: HashMap<QualifiedIdent, (QualifiedIdent, Vec<QualifiedIdent>)> = HashMap::new();
    for (method, (class_name, tvs)) in &ctx.class_methods {
        if local_class_set.contains(&class_name.name) {
            export_class_methods.insert(*method, (*class_name, tvs.iter().map(|s| qi(*s)).collect()));
        }
    }
    // Register locally-defined class names as types in data_constructors so they
    // participate in ExportConflict detection (classes are types in PureScript).
    for class_name in &declared_classes {
        export_data_constructors
            .entry(qi(*class_name))
            .or_insert_with(Vec::new);
    }

    let mut export_instances: HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>> =
        HashMap::new();
    for (class_name, insts) in &instances {
        // Export all instances (both for local and imported classes) since instances
        // are globally visible in PureScript.
        // Expand type aliases in instance types so that importing modules can match
        // against concrete types even without the alias in scope.
        let expanded_insts: Vec<_> = insts.iter().map(|(types, constraints, inst_name)| {
            let expanded_types: Vec<Type> = types.iter().map(|t| {
                expand_type_aliases_limited(t, &ctx.state.type_aliases, 0)
            }).collect();
            (expanded_types, constraints.clone(), *inst_name)
        }).collect();
        export_instances.insert(*class_name, expanded_insts);
    }

    let mut export_type_operators: HashMap<QualifiedIdent, QualifiedIdent> = HashMap::new();
    let mut export_type_fixities: HashMap<QualifiedIdent, (Associativity, u8)> = HashMap::new();
    let mut export_value_fixities: HashMap<QualifiedIdent, (Associativity, u8)> = HashMap::new();
    let mut export_function_op_aliases: HashSet<QualifiedIdent> = HashSet::new();
    let mut export_value_operator_targets: HashMap<QualifiedIdent, QualifiedIdent> = HashMap::new();
    for decl in &module.decls {
        if let Decl::Fixity {
            associativity,
            precedence,
            target,
            operator,
            is_type,
            ..
        } = decl
        {
            if *is_type {
                export_type_operators.insert(qi(operator.value), qi(target.name));
                export_type_fixities.insert(qi(operator.value), (*associativity, *precedence));
            } else {
                export_value_fixities.insert(qi(operator.value), (*associativity, *precedence));
                export_value_operator_targets.insert(qi(operator.value), qi(target.name));
                // Track operators that alias functions (not constructors)
                if !ctx.ctor_details.contains_key(&qi(target.name)) {
                    export_function_op_aliases.insert(qi(operator.value));
                }
            }
        }
    }

    // Pre-compute self-referential alias set (as QualifiedIdent) for export expansion.
    // Self-referential aliases like `type Thread = { state :: ShowRef Thread, ... }` must
    // not be expanded during export to prevent cross-module double-expansion.
    //
    // Two-tier check: only include aliases where the DIRECT body (before transitive
    // alias expansion) contains Con(name) with matching arity. Aliases where the
    // self-reference only appears after transitive expansion (e.g.,
    // `type Model = ModelExt(...)` where ModelExt body contains `AskForReview.Model`
    // data type that became Con("Model") after qualifier stripping) are excluded IF
    // a data type with the same name and arity exists. This allows one level of
    // expansion at export time. Downstream modules still inherit the self_referential
    // flag (from self_referential_aliases export), so their self_ref_qis prevents
    // re-expansion of the inner Con(name) — no cross-module type growth.
    let self_ref_qis: HashSet<QualifiedIdent> = ctx.state.self_referential_aliases
        .iter()
        .filter(|&&name| {
            // Check if the DIRECT body contains the self-reference
            if let Some((params, body)) = ctx.state.type_aliases.get(&name) {
                let param_count = params.len();
                if contains_self_referential_usage_in_type(body, name, param_count) {
                    // Direct self-reference → truly self-referential, keep in set
                    return true;
                }
                // Indirect only → check for data type collision
                let has_data_type_collision = ctx.type_con_arities.iter()
                    .any(|(k, &arity)| k.name == name && arity == param_count);
                // If collision exists, exclude from set (allow expansion)
                !has_data_type_collision
            } else {
                // Alias not found (shouldn't happen), keep in set for safety
                true
            }
        })
        .map(|s| qi(*s))
        .collect();

    // Collect type aliases for export, pre-expanding bodies so importing modules
    // don't need transitive access to aliases used in the bodies.
    // Use the depth-limited variant to avoid infinite recursion on cyclic aliases
    // (e.g. `type Effect = Effect` re-exports).
    // Only expand bodies of LOCALLY-DEFINED aliases. Imported alias bodies should
    // already be expanded from their source module. Re-expanding imported alias bodies
    // can cause name collisions (e.g. `type GqlError = { ... }` alias from one module
    // incorrectly expanding `Con(GqlError)` data type references in another alias body).
    // Also filter out aliases that were only imported via qualified imports — these should
    // not be re-exported since qualified imports don't make names available unqualified.
    //
    // Compute zero-arg blocker set for export alias body expansion.
    // Block zero-param alias expansion when the name appears as a type constructor
    // in IMPORTED (non-locally-defined) alias bodies. These type constructors were
    // already "resolved" in the source module — re-expanding them with a different
    // alias from the current module causes type mismatches across module boundaries.
    // E.g., `EventRec` from Data.Event contains `ProgramType` (a data type there),
    // but Effect.Update.Fn also imports `type ProgramType = { ... }` (a record alias).
    // Without blocking, the data type ref gets expanded as the record alias on export.
    //
    // Compute two related blocker sets:
    // 1. con_zero_blockers: for expand_type_aliases_limited_inner (existing mechanism)
    // 2. zonk_con_blockers: for zonk_ref's Type::Con branch (new mechanism)
    //
    // Both block zero-param alias expansion when the name collides with a data type
    // from a different module. The difference: con_zero_blockers is checked during
    // expand_type_aliases_limited_inner, zonk_con_blockers during zonk.
    //
    // To determine genuine data type collisions (vs blocked-alias cascades), check
    // the registry's type_con_arities: if a name exists as a data type in ANY
    // imported module, it's a genuine collision. Names that only appear because
    // a previous module's con_zero_blockers blocked expansion are NOT in any
    // module's type_con_arities.
    let con_zero_blockers: HashSet<Symbol> = {
        // Start with the original qualified-import-based blockers
        let mut blockers: HashSet<Symbol> = ctx
            .qualified_import_unqual_aliases
            .iter()
            .filter(|name| ctx.type_con_arities.iter().any(|(k, &v)| k.name == **name && v == 0))
            .copied()
            .collect();
        // Collect type constructor names from imported (non-locally-defined) alias bodies
        // that are GENUINELY data types in some registry module.
        let mut imported_body_cons: HashSet<Symbol> = HashSet::new();
        for (name, (_params, body)) in &ctx.state.type_aliases {
            if has_type_alias_def.contains(name) {
                continue; // Skip locally-defined aliases
            }
            collect_type_con_names_from_type(body, &mut imported_body_cons);
        }
        // Only block when the data type is actually in scope (present in ctx.type_con_arities
        // under the unqualified key). Previously we collected ALL data types from ALL imported
        // modules' type_con_arities, which was too broad — e.g. `data Time` from Data.Time
        // would block `type Time = Number` from Signal.Time even when Data.Time wasn't imported.
        for con_name in &imported_body_cons {
            // Only block if:
            // 1. There's a zero-param alias with this name in the current module
            // 2. The name is a genuine data type actually in scope (in type_con_arities under unqualified key)
            if let Some((params, _)) = ctx.state.type_aliases.get(con_name) {
                if params.is_empty()
                    && ctx.type_con_arities.contains_key(&qi(*con_name))
                    && !has_type_alias_def.contains(con_name)
                {
                    blockers.insert(*con_name);
                }
            }
        }
        blockers
    };
    // Build reverse qualifier map: canonical module path → import alias.
    // Used to de-canonicalize type constructors in imported alias bodies before
    // expansion, so references like `Components.AskForReview.Model` can be found
    // under their import-alias key `AskForReview.Model`.
    let reverse_qualifier_map: HashMap<Symbol, Symbol> = module.imports.iter()
        .filter_map(|import_decl| {
            let alias = import_decl.qualified.as_ref()?;
            let mod_sym = module_name_to_symbol(&import_decl.module);
            let alias_sym = module_name_to_symbol(alias);
            Some((mod_sym, alias_sym))
        })
        .collect();
    let export_type_aliases: HashMap<QualifiedIdent, (Vec<QualifiedIdent>, Type)> = ctx
        .state
        .type_aliases
        .iter()
        .filter(|(name, _)| {
            // Keep locally-defined aliases always
            if has_type_alias_def.contains(name) {
                return true;
            }
            // Exclude aliases that came only from qualified imports
            !ctx.qualified_import_unqual_aliases.contains(name)
        })
        .map(|(name, (params, body))| {
            let expanded_body = if has_type_alias_def.contains(name) {
                // De-canonicalize type constructors in the body before expansion,
                // so that `Components.AskForReview.Model` becomes `AskForReview.Model`
                // which can be found in type_aliases under the import-alias key.
                let body = if !reverse_qualifier_map.is_empty() {
                    resolve_type_qualifiers(body, &reverse_qualifier_map)
                } else {
                    body.clone()
                };
                let mut expanding = self_ref_qis.clone();
                expand_type_aliases_limited_inner(&body, &ctx.state.type_aliases, Some(&ctx.type_con_arities), 0, &mut expanding, Some(&con_zero_blockers))
            } else {
                body.clone()
            };
            (qi(*name), (params.iter().map(|p| qi(*p)).collect(), expanded_body))
        })
        .collect();

    // Expand type aliases in all exported values so importing modules don't
    // need transitive access to aliases like `type DriverStateRec = { component :: ComponentSpec ... }`.
    // Use the arities-aware variant to handle over-saturated aliases like `Except e a`
    // where `Except` has 1 param but appears with 2 args.
    // Pre-seed the expanding set with self-referential aliases to prevent cross-module
    // double-expansion (e.g. `type Thread = { state :: ShowRef Thread, ... }` would
    // be expanded at export time, then again at import time, creating ever-deeper types).
    // Set zonk_con_blockers on the UnifyState so that zonk_ref's Type::Con branch
    // skips expansion of zero-arg aliases that genuinely collide with data types.
    ctx.state.zonk_con_blockers = con_zero_blockers.clone();
    for (_val_name, scheme) in local_values.iter_mut() {
        scheme.ty = ctx.state.zonk(scheme.ty.clone());
        // De-canonicalize type constructors before expansion so that canonical
        // qualifiers (e.g. `Components.AskForReview.Model`) can be found under
        // their import-alias keys (e.g. `AskForReview.Model`) in type_aliases.
        if !reverse_qualifier_map.is_empty() {
            scheme.ty = resolve_type_qualifiers(&scheme.ty, &reverse_qualifier_map);
        }
        let mut expanding = self_ref_qis.clone();
        scheme.ty = expand_type_aliases_limited_inner(
            &scheme.ty,
            &ctx.state.type_aliases,
            Some(&ctx.type_con_arities),
            0,
            &mut expanding,
            Some(&con_zero_blockers),
        );
        // Replace any remaining unsolved Unif vars with fresh named type variables.
        // These can occur for unsolved row tails in open records (e.g. `{ x :: Int | ?331 }`)
        // that weren't generalized because they were also free in the environment.
        // If left as Unif, they cause panics in importing modules whose UnifyState
        // has fewer entries.
        let mut unif_to_var: HashMap<TyVarId, Symbol> = HashMap::new();
        collect_unif_var_ids(&scheme.ty, &mut unif_to_var);
        if !unif_to_var.is_empty() {
            scheme.ty = replace_unif_with_vars(&scheme.ty, &unif_to_var);
            for var_name in unif_to_var.values() {
                if !scheme.forall_vars.contains(var_name) {
                    scheme.forall_vars.push(*var_name);
                }
            }
        }
    }

    // Clear zonk_con_blockers after export-time zonking is done
    ctx.state.zonk_con_blockers.clear();

    // Build origin maps: all locally-defined names have origin = this module
    let current_mod_sym = module_name_to_symbol(&module.name.value);
    let mut value_origins: HashMap<Symbol, Symbol> = HashMap::new();
    let mut type_origins: HashMap<Symbol, Symbol> = HashMap::new();
    let mut class_origins: HashMap<Symbol, Symbol> = HashMap::new();
    for name in local_values.keys() {
        value_origins.insert(*name, current_mod_sym);
    }
    for name in export_data_constructors.keys() {
        type_origins.insert(name.name, current_mod_sym);
    }
    // Also include origins for imported types that may appear in exported value schemes.
    // Without this, types like `Response` (from JS.Fetch.Response, imported by JS.Fetch
    // but not in its explicit export list) wouldn't have origins, preventing downstream
    // modules from canonicalizing them to avoid local alias collisions.
    for import_decl in &module.imports {
        if is_prim_module(&import_decl.module) || is_prim_submodule(&import_decl.module) {
            continue;
        }
        if let Some(mod_exports) = registry.lookup(&import_decl.module.parts) {
            for (&name, &origin) in &mod_exports.type_origins {
                type_origins.entry(name).or_insert(origin);
            }
            // Also propagate value_origins and class_origins from imports.
            // Without this, re-exported values (like Tuple constructor from Prelude)
            // default to source_mod_sym, incorrectly marking them as locally defined
            // and causing false export conflicts.
            for (&name, &origin) in &mod_exports.value_origins {
                value_origins.entry(name).or_insert(origin);
            }
            for (&name, &origin) in &mod_exports.class_origins {
                class_origins.entry(name).or_insert(origin);
            }
        }
    }
    for class_name in &declared_classes {
        class_origins.insert(*class_name, current_mod_sym);
    }
    for (_, (class_name, _)) in &export_class_methods {
        class_origins.insert(class_name.name, current_mod_sym);
    }
    // Type aliases in local_values were already expanded at lines 7148-7158 using
    // expand_type_aliases_limited_inner (which handles qualified names correctly).
    // Do NOT re-expand here: expand_type_aliases uses unqualified lookup which would
    // incorrectly expand data type references (e.g. HATS.Easing) as aliases.
    let mut module_exports = ModuleExports {
        values: local_values.iter().map(|(&k, v)| {
            (qi(k), Scheme { forall_vars: v.forall_vars.clone(), ty: v.ty.clone() })
        }).collect(),
        class_methods: export_class_methods,
        data_constructors: export_data_constructors,
        ctor_details: export_ctor_details,
        instances: export_instances,
        type_operators: export_type_operators,
        type_fixities: export_type_fixities,
        value_fixities: export_value_fixities,
        function_op_aliases: export_function_op_aliases,
        value_operator_targets: export_value_operator_targets,
        constrained_class_methods: ctx.constrained_class_methods.iter().map(|s| qi(*s)).collect(),
        type_aliases: export_type_aliases,
        class_param_counts: class_param_counts.clone(),
        value_origins,
        type_origins,
        class_origins,
        operator_class_targets: ctx.operator_class_targets.iter().map(|(k, v)| (k.name, v.name)).collect(),
        class_fundeps: ctx.class_fundeps.iter().map(|(k, v)| (k.name, v.clone())).collect(),
        type_con_arities: ctx.type_con_arities.iter()
            .filter(|(k, _)| k.module.is_none())
            .map(|(k, v)| (*k, *v))
            .collect(),
        type_roles: ctx.type_roles.clone(),
        newtype_names: ctx.newtype_names.iter().map(|n| n.name).collect(),
        signature_constraints: {
            let mut sc = ctx.signature_constraints.clone();
            // Merge codegen_signature_constraints so re-exported functions
            // retain their constraints for downstream modules.
            for (name, constraints) in &ctx.codegen_signature_constraints {
                let entry = sc.entry(name.clone()).or_default();
                for constraint in constraints {
                    // Deduplicate by class name
                    if !entry.iter().any(|(cn, _)| cn.name == constraint.0.name) {
                        entry.push(constraint.clone());
                    }
                }
            }
            // Expand type aliases in exported constraint args so importing modules
            // don't need the defining module's import context (e.g. Common.NegOne → TypeInt(-1))
            for constraints in sc.values_mut() {
                for (_, args) in constraints.iter_mut() {
                    for arg in args.iter_mut() {
                        *arg = expand_type_aliases_limited(arg, &ctx.state.type_aliases, 0);
                    }
                }
            }
            sc
        },
        partial_dischargers: ctx.partial_dischargers.iter().map(|n| n.name).collect(),
        partial_value_names: HashSet::new(), // populated below from CST type signatures
        self_referential_aliases: ctx.state.self_referential_aliases.clone(),
        type_kinds: saved_type_kinds
            .iter()
            .filter(|(name, _)| local_type_names.contains(&name.name))
            .map(|(name, kind)| {
                let generalized = generalize_kind_for_export(kind);
                // Strip import-alias module qualifiers from exported kinds so downstream
                // modules can add their own qualifiers via qualify_kind_refs.
                (name.name, strip_kind_qualifiers(&generalized))
            })
            .collect(),
        class_type_kinds: saved_class_kinds
            .iter()
            .map(|(name, kind)| {
                let generalized = generalize_kind_for_export(kind);
                (name.name, strip_kind_qualifiers(&generalized))
            })
            .collect(),
        class_superclasses: class_superclasses.clone(),
        method_own_constraints: ctx.method_own_constraints.iter().map(|(k, v)| (qi(*k), v.clone())).collect(),
        module_doc: Vec::new(), // filled in by the outer CST-level wrapper
        instance_registry: instance_registry_entries,
        instance_modules: instance_module_entries,
        resolved_dicts: ctx.resolved_dicts.clone(),
        let_binding_constraints: ctx.let_binding_constraints.clone(),
        record_update_fields: ctx.record_update_fields.clone(),
        class_method_order: ctx.class_method_order.clone(),
        return_type_constraints: ctx.return_type_constraints.clone(),
        return_type_arrow_depth: ctx.return_type_arrow_depth.clone(),
        instance_var_kinds: instance_var_kinds_entries,
    };
    // Populate partial_value_names from AST type signatures
    for decl in &module.decls {
        if let Decl::TypeSignature { name, ty, .. } = decl {
            if has_partial_constraint(ty) {
                module_exports.partial_value_names.insert(name.value);
            }
        }
    }
    // Ensure operator targets (e.g. Tuple for /\) are included in exported values and
    // ctor_details, even when the target was imported rather than locally defined.
    for (_op, target) in &module_exports.value_operator_targets.clone() {
        if !module_exports.values.contains_key(target) {
            if let Some(scheme) = env.lookup(target.name) {
                let mut scheme = scheme.clone();
                scheme.ty = ctx.state.zonk(scheme.ty);
                // Replace any remaining Unif vars
                let mut unif_to_var: HashMap<TyVarId, Symbol> = HashMap::new();
                collect_unif_var_ids(&scheme.ty, &mut unif_to_var);
                if !unif_to_var.is_empty() {
                    scheme.ty = replace_unif_with_vars(&scheme.ty, &unif_to_var);
                    for var_name in unif_to_var.values() {
                        if !scheme.forall_vars.contains(var_name) {
                            scheme.forall_vars.push(*var_name);
                        }
                    }
                }
                module_exports.values.insert(*target, scheme);
            }
        }
        if !module_exports.ctor_details.contains_key(target) {
            if let Some(details) = ctx.ctor_details.get(target) {
                module_exports.ctor_details.insert(*target, (details.0, details.1.iter().map(|s| qi(*s)).collect(), details.2.clone()));
            }
        }
    }

    // Add constructor schemes to exported values so that `Type(..)` exports and
    // downstream `import M (Type(..))` can find constructor type schemes.
    // Constructors are registered in `env` during type checking but not in `local_values`.
    for (_type_name, ctors) in &module_exports.data_constructors.clone() {
        for ctor in ctors {
            if !module_exports.values.contains_key(ctor) {
                if let Some(scheme) = env.lookup(ctor.name) {
                    let mut scheme = scheme.clone();
                    scheme.ty = ctx.state.zonk(scheme.ty.clone());
                    let mut expanding = self_ref_qis.clone();
                    scheme.ty = expand_type_aliases_limited_inner(
                        &scheme.ty,
                        &ctx.state.type_aliases,
                        Some(&ctx.type_con_arities),
                        0,
                        &mut expanding,
                        None,
                    );
                    let mut unif_to_var: HashMap<TyVarId, Symbol> = HashMap::new();
                    collect_unif_var_ids(&scheme.ty, &mut unif_to_var);
                    if !unif_to_var.is_empty() {
                        scheme.ty = replace_unif_with_vars(&scheme.ty, &unif_to_var);
                        for var_name in unif_to_var.values() {
                            if !scheme.forall_vars.contains(var_name) {
                                scheme.forall_vars.push(*var_name);
                            }
                        }
                    }
                    module_exports.values.insert(*ctor, scheme);
                }
            }
        }
    }

    // Post-inference kind validation: check that inferred types are kind-consistent.
    // This catches kind mismatches like `TProxy "apple"` where TProxy expects Type but
    // "apple" has kind Symbol, which occur when type variables are instantiated to
    // type-level literals during inference.
    // Only check types that contain type-level literals, since those are the main
    // cases where kind mismatches arise from type inference.
    let saved_type_kinds_sym: HashMap<Symbol, Type> = saved_type_kinds.iter().map(|(k, v)| (k.name, v.clone())).collect();
    if !saved_type_kinds.is_empty() {
        fn contains_type_literal(ty: &Type) -> bool {
            match ty {
                Type::TypeString(_) | Type::TypeInt(_) => true,
                Type::App(f, a) => contains_type_literal(f) || contains_type_literal(a),
                Type::Fun(a, b) => contains_type_literal(a) || contains_type_literal(b),
                Type::Record(fields, tail) => {
                    fields.iter().any(|(_, t)| contains_type_literal(t))
                        || tail.as_ref().map_or(false, |t| contains_type_literal(t))
                }
                Type::Forall(_, body) => contains_type_literal(body),
                _ => false,
            }
        }
        for (&_name, ty) in &result_types {
            if !contains_type_literal(ty) {
                continue;
            }
            // Find span for this declaration
            let decl_span = module
                .decls
                .iter()
                .find_map(|d| match d {
                    Decl::Value { name: n, span, .. } if n.value == _name => Some(*span),
                    _ => None,
                })
                .unwrap_or(Span::new(0, 0));
            if let Err(e) =
                crate::typechecker::kind::check_inferred_type_kind(ty, &saved_type_kinds_sym, decl_span)
            {
                errors.push(e);
            }
        }

        // Also kind-check deferred lambda types. Lambda function types may contain
        // type-level literals in their domain after unification resolves type variables
        // (e.g., `"foo" -> String` when a polykinded type variable was unified with "foo").
        for (ty, span) in &ctx.deferred_kind_checks {
            let zonked = ctx.state.zonk(ty.clone());
            if !contains_type_literal(&zonked) {
                continue;
            }
            if let Err(e) = crate::typechecker::kind::check_inferred_type_kind(
                &zonked,
                &saved_type_kinds_sym,
                *span,
            ) {
                errors.push(e);
            }
        }
    }

    // If there's an explicit export list, filter exports accordingly
    if let Some(ref export_list) = module.exports {
        // Save lightweight metadata that must survive filtering
        let saved_instance_registry = std::mem::take(&mut module_exports.instance_registry);
        let saved_instance_modules = std::mem::take(&mut module_exports.instance_modules);
        // Save only locally-defined class_superclasses (not imported accumulation)
        let saved_class_superclasses = std::mem::take(&mut module_exports.class_superclasses);
        module_exports = filter_exports(
            &module_exports,
            &export_list.value,
            export_list.span,
            &local_type_set,
            &local_class_set,
            registry,
            &module.imports,
            &module.name.value,
            &mut errors,
            &ctx.scope_conflicts,
        );
        // Restore metadata
        module_exports.class_superclasses = saved_class_superclasses;
        module_exports.instance_registry = saved_instance_registry;
        module_exports.instance_modules = saved_instance_modules;
    }


    // Resolve import-qualifier-prefixed type constructors in exported schemes to their
    // canonical (full module path) form. This prevents import-local qualifiers like
    // `CoreResponse.Response` from leaking into other modules' scopes.
    {
        let mut qualifier_map: HashMap<Symbol, Symbol> = HashMap::new();
        for import_decl in &module.imports {
            if let Some(ref alias) = import_decl.qualified {
                let mod_sym = module_name_to_symbol(&import_decl.module);
                let alias_sym = module_name_to_symbol(alias);
                qualifier_map.insert(alias_sym, mod_sym);
            }
        }
        if !qualifier_map.is_empty() {
            for scheme in module_exports.values.values_mut() {
                scheme.ty = resolve_type_qualifiers(&scheme.ty, &qualifier_map);
            }
            for details in module_exports.ctor_details.values_mut() {
                for ty in &mut details.2 {
                    *ty = resolve_type_qualifiers(ty, &qualifier_map);
                }
            }
            // NOTE: Do NOT resolve type qualifiers in instance types.
            // Instance matching uses type_con_qi_eq which is lenient about
            // module qualifiers. Canonicalizing instance types (e.g.,
            // List.List → Data.List.Types.List) breaks matching against
            // local import aliases (e.g., List.List in the importing module).
            for alias in module_exports.type_aliases.values_mut() {
                alias.1 = resolve_type_qualifiers(&alias.1, &qualifier_map);
            }
        }
    }

    let span_types: HashMap<crate::span::Span, Type> = ctx.span_types.iter()
        .map(|(span, ty)| (*span, ctx.state.zonk(ty.clone())))
        .collect();

    let record_update_fields = std::mem::take(&mut ctx.record_update_fields);

    CheckResult {
        types: result_types,
        errors,
        exports: module_exports,
        span_types,
        record_update_fields,
    }
}

/// Collect all Type::Unif IDs in a type, assigning each a fresh named type variable.
fn collect_unif_var_ids(ty: &Type, map: &mut HashMap<TyVarId, Symbol>) {
    match ty {
        Type::Unif(id) => {
            map.entry(*id).or_insert_with(|| {
                crate::interner::intern(&format!("$r{}", id.0))
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
fn replace_unif_with_vars(ty: &Type, map: &HashMap<TyVarId, Symbol>) -> Type {
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
fn check_field_partially_applied_synonym(
    te: &crate::ast::TypeExpr,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    type_ops: &HashMap<QualifiedIdent, QualifiedIdent>,
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
            if type_aliases.contains_key(&name.name) {
                Some(name.name)
            } else {
                type_ops.get(name).and_then(|target| {
                    if type_aliases.contains_key(&target.name) {
                        Some(target.name)
                    } else {
                        None
                    }
                })
            }
        }
        _ => None,
    };
    if let Some(sym) = alias_sym {
        if let Some((params, _)) = type_aliases.get(&sym) {
            if arg_count < params.len() {
                return Some(TypeError::PartiallyAppliedSynonym {
                    span: te.span(),
                    name: QualifiedIdent { module: None, name: sym },
                });
            }
        }
    }
    None
}

/// Create a qualified symbol by combining a module alias with a name.
fn qualified_symbol(module: Symbol, name: Symbol) -> Symbol {
    crate::interner::intern_qualified(module, name)
}

/// Generalize unresolved Unif vars in a kind type into forall bindings.
/// Used when exporting type kinds to avoid leaking KindState-local var IDs
/// while preserving polykinds (e.g., `Proxy :: ?k -> Type` → `forall k0. k0 -> Type`).
fn generalize_kind_for_export(kind: &Type) -> Type {
    use crate::typechecker::types::TyVarId;
    let mut unif_ids: Vec<TyVarId> = Vec::new();
    collect_kind_unif_ids(kind, &mut unif_ids);
    unif_ids.sort_by_key(|id| id.0);
    unif_ids.dedup();
    if unif_ids.is_empty() {
        return kind.clone();
    }
    let mut subst: HashMap<TyVarId, Symbol> = HashMap::new();
    let mut forall_vars = Vec::new();
    for (i, id) in unif_ids.iter().enumerate() {
        let sym = crate::interner::intern(&format!("k{}", i));
        subst.insert(*id, sym);
        forall_vars.push((sym, false));
    }
    let body = replace_unif_with_var(kind, &subst);
    Type::Forall(forall_vars, Box::new(body))
}

fn collect_kind_unif_ids(kind: &Type, out: &mut Vec<crate::typechecker::types::TyVarId>) {
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

fn replace_unif_with_var(
    kind: &Type,
    subst: &HashMap<crate::typechecker::types::TyVarId, Symbol>,
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

/// Walk a kind type and qualify Con references that match exported type names.
/// Used when importing type kinds from other modules with a qualifier.
/// E.g., importing LibB's `DemoData :: DemoKind` as LibB produces `DemoData :: LibB.DemoKind`.
fn qualify_kind_refs(kind: &Type, qualifier: Symbol, exported_types: &HashSet<Symbol>) -> Type {
    match kind {
        Type::Con(name) => {
            // Don't qualify Prim kind names — these are built-in kinds, not module-specific types.
            let name_str = crate::interner::resolve(name.name).unwrap_or_default();
            if matches!(name_str.as_str(), "Type" | "Constraint" | "Symbol" | "Row" | "Int") {
                return kind.clone();
            }
            if name.module.is_none() && exported_types.contains(&name.name) {
                Type::Con(QualifiedIdent { module: Some(qualifier), name: name.name })
            } else {
                kind.clone()
            }
        }
        Type::Fun(a, b) => Type::fun(
            qualify_kind_refs(a, qualifier, exported_types),
            qualify_kind_refs(b, qualifier, exported_types),
        ),
        Type::App(a, b) => Type::app(
            qualify_kind_refs(a, qualifier, exported_types),
            qualify_kind_refs(b, qualifier, exported_types),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(qualify_kind_refs(body, qualifier, exported_types)),
        ),
        _ => kind.clone(),
    }
}

/// Strip module qualifiers from kind type constructors for export.
/// Exported kinds should use bare names so importing modules can add their own
/// qualifiers via `qualify_kind_refs`. Without this, internal import aliases
/// (e.g., `K.Subject`) would leak into exported kinds and be unresolvable by
/// downstream modules.
fn strip_kind_qualifiers(kind: &Type) -> Type {
    match kind {
        Type::Con(name) if name.module.is_some() => {
            Type::Con(qi(name.name))
        }
        Type::Fun(a, b) => Type::fun(
            strip_kind_qualifiers(a),
            strip_kind_qualifiers(b),
        ),
        Type::App(a, b) => Type::app(
            strip_kind_qualifiers(a),
            strip_kind_qualifiers(b),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(strip_kind_qualifiers(body)),
        ),
        _ => kind.clone(),
    }
}

/// Convert a ModuleName to a single symbol (joining parts with '.').
fn module_name_to_symbol(module_name: &crate::cst::ModuleName) -> Symbol {
    crate::interner::intern_module_name(&module_name.parts)
}

/// Optionally qualify a name: if qualifier is Some, prefix with "Q.", otherwise return as-is.
fn maybe_qualify_symbol(name: Symbol, qualifier: Option<Symbol>) -> Symbol {
    match qualifier {
        Some(q) => qualified_symbol(q, name),
        None => name,
    }
}

fn maybe_qualify_qualified_ident(
    ident: QualifiedIdent,
    qualifier: Option<Symbol>,
) -> QualifiedIdent {
    match qualifier {
        Some(q) => QualifiedIdent {
            module: Some(q),
            name: ident.name,
        },
        None => ident,
    }
}

/// Canonicalize unqualified type constructor references in an alias body.
/// For qualified imports (`import M as Q`), alias bodies may contain
/// `Type::Con(QualifiedIdent { module: None, name: "Bar" })` — unqualified
/// references to types from the source module. This function sets the module
/// qualifier to the source module's canonical name so that `try_expand_alias`
/// can find them via canonical key or canonical_to_qualifier fallback, and
/// so they won't be confused with local aliases of the same name.
fn canonicalize_alias_body_types(
    ty: &Type,
    source_module: Symbol,
    exported_type_names: &HashSet<Symbol>,
    exclude_name: Option<Symbol>,
) -> Type {
    match ty {
        Type::Con(qi) if qi.module.is_none()
            && exported_type_names.contains(&qi.name)
            && exclude_name.map_or(true, |ex| ex != qi.name) => {
            Type::Con(QualifiedIdent { module: Some(source_module), name: qi.name })
        }
        Type::App(f, a) => {
            Type::App(
                Box::new(canonicalize_alias_body_types(f, source_module, exported_type_names, exclude_name)),
                Box::new(canonicalize_alias_body_types(a, source_module, exported_type_names, exclude_name)),
            )
        }
        Type::Fun(a, b) => {
            Type::Fun(
                Box::new(canonicalize_alias_body_types(a, source_module, exported_type_names, exclude_name)),
                Box::new(canonicalize_alias_body_types(b, source_module, exported_type_names, exclude_name)),
            )
        }
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(canonicalize_alias_body_types(body, source_module, exported_type_names, exclude_name)))
        }
        Type::Record(fields, tail) => {
            let new_fields: Vec<_> = fields.iter()
                .map(|(label, ty)| (*label, canonicalize_alias_body_types(ty, source_module, exported_type_names, exclude_name)))
                .collect();
            let new_tail = tail.as_ref().map(|t| Box::new(canonicalize_alias_body_types(t, source_module, exported_type_names, exclude_name)));
            Type::Record(new_fields, new_tail)
        }
        _ => ty.clone(),
    }
}

type InstanceMap = HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>;

/// Look up instances for a class, falling back to unqualified name if needed.
/// Instance entries are stored under the exporting module's key (typically unqualified),
/// but constraints may reference the class through a qualified import (e.g. `Row.Nub`).
fn lookup_instances<'a>(
    instances: &'a InstanceMap,
    class_name: &QualifiedIdent,
) -> Option<&'a Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>> {
    instances.get(class_name).or_else(|| {
        if class_name.module.is_some() {
            // Qualified lookup failed — try unqualified
            instances.get(&QualifiedIdent { module: None, name: class_name.name })
        } else {
            // Unqualified lookup failed — search for any qualified variant with same name
            instances.iter()
                .find(|(k, _)| k.name == class_name.name)
                .map(|(_, v)| v)
        }
    })
}

/// Process all import declarations, bringing imported names into scope.
/// Returns the set of explicitly imported type names (for scope conflict detection
/// with local type declarations).
fn process_imports(
    module: &Module,
    registry: &ModuleRegistry,
    env: &mut Env,
    ctx: &mut InferCtx,
    instances: &mut HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    errors: &mut Vec<TypeError>,
) -> HashSet<Symbol> {
    let mut explicitly_imported_types: HashSet<Symbol> = HashSet::new();
    // Build Prim exports once so explicit `import Prim` / `import Prim as P` resolves.
    let prim = prim_exports();

    // Track which modules' instances have already been imported to avoid redundant dedup work.
    // Each module's exports contain all transitive instances, so we only need to import
    // instances from each unique module once.
    let mut imported_instance_modules: HashSet<Symbol> = HashSet::new();

    // Pre-scan local type alias names so import processing can detect collisions.
    // This is needed because local aliases aren't registered until Pass 1, but we need
    // to know about them during import processing to qualify conflicting imported types.
    let local_type_alias_names: HashSet<Symbol> = module.decls.iter()
        .filter_map(|d| match d {
            Decl::TypeAlias { name, .. } => Some(name.value),
            _ => None,
        })
        .collect();

    // Pre-scan local data/newtype/foreign data type names so import processing can
    // avoid registering imported type aliases that collide with local data types.
    // Without this, `type Thread = { ... }` (imported alias) overwrites the local
    // `newtype Thread = T Thread.Thread` in type_aliases, causing instance heads
    // like `Show Thread` to be incorrectly alias-expanded to a record type.
    let local_data_type_names: HashSet<Symbol> = module.decls.iter()
        .filter_map(|d| match d {
            Decl::Data { name, kind_sig, is_role_decl, .. }
                if *kind_sig == crate::cst::KindSigSource::None && !is_role_decl =>
                    Some(name.value),
            Decl::Newtype { name, .. } => Some(name.value),
            Decl::ForeignData { name, .. } => Some(name.value),
            _ => None,
        })
        .collect();

    // Pre-scan all imports to collect type alias names that will be imported
    // into the unqualified namespace. This is needed so qualified imports can
    // detect name collisions with type aliases even when the alias-providing
    // import appears later in the import list. Without this, import ordering
    // affects whether defined_types qualifies value scheme type constructors,
    // causing incorrect alias expansion (e.g., `Expiry` data type in a qualified
    // import's value scheme gets alias-expanded to `{ expiresIn :: Int }` from
    // an unqualified type alias import that hasn't been processed yet).
    let all_alias_names: HashSet<Symbol> = {
        let mut names = local_type_alias_names.clone();
        for import_decl in &module.imports {
            // Only unqualified imports add aliases to the unqualified namespace
            if import_decl.qualified.is_some() {
                continue;
            }
            let prim_sub_pre;
            let module_exports_pre = if is_prim_module(&import_decl.module) {
                prim
            } else if is_prim_submodule(&import_decl.module) {
                prim_sub_pre = prim_submodule_exports(&import_decl.module);
                &prim_sub_pre
            } else {
                match registry.lookup(&import_decl.module.parts) {
                    Some(exports) => exports,
                    None => continue,
                }
            };
            match &import_decl.imports {
                None => {
                    // import M — all type aliases imported unqualified
                    for name in module_exports_pre.type_aliases.keys() {
                        names.insert(name.name);
                    }
                }
                Some(ImportList::Explicit(items)) => {
                    // import M (x, y, ...) — check which are type aliases
                    for item in items {
                        let sym = import_name(item);
                        if module_exports_pre.type_aliases.keys().any(|n| n.name == sym) {
                            names.insert(sym);
                        }
                    }
                }
                Some(ImportList::Hiding(items)) => {
                    // import M hiding (x, y) — all aliases except hidden
                    let hidden_pre: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                    for name in module_exports_pre.type_aliases.keys() {
                        if !hidden_pre.contains(&name.name) {
                            names.insert(name.name);
                        }
                    }
                }
            }
        }
        names
    };

    // Track import origins for scope conflict detection.
    // Maps (possibly qualified) name → (origin module symbol, is_explicit).
    // A scope conflict occurs when a name is imported from two different origin modules
    // AND both imports have the same explicitness level. Explicit imports shadow open imports.
    let mut import_origins: HashMap<Symbol, (Symbol, bool)> = HashMap::new();

    for import_decl in &module.imports {
        // Handle Prim submodules (Prim.Coerce, Prim.Row, etc.) as built-in
        let prim_sub;
        let module_exports = if is_prim_module(&import_decl.module) {
            prim
        } else if is_prim_submodule(&import_decl.module) {
            prim_sub = prim_submodule_exports(&import_decl.module);
            &prim_sub
        } else {
            match registry.lookup(&import_decl.module.parts) {
                Some(exports) => exports,
                None => {
                    errors.push(TypeError::ModuleNotFound {
                        span: import_decl.span,
                        name: module_name_to_symbol(&import_decl.module),
                    });
                    continue;
                }
            }
        };

        let qualifier = import_decl.qualified.as_ref().map(module_name_to_symbol);
        let mod_sym = module_name_to_symbol(&import_decl.module);

        // Determine if this is an explicit import (import M (x)) vs open (import M)
        let is_explicit = matches!(&import_decl.imports, Some(ImportList::Explicit(_)));

        // Collect imported value names for scope conflict detection
        let imported_names: Vec<Symbol> = match (&import_decl.imports, qualifier) {
            (None, Some(q)) => {
                // import M as Q — qualified names
                module_exports
                    .values
                    .keys()
                    .map(|n| maybe_qualify_symbol(n.name, Some(q)))
                    .collect()
            }
            (None, None) => {
                // import M — all unqualified values
                module_exports.values.keys().map(|n| n.name).collect()
            }
            (Some(ImportList::Explicit(items)), _) => items
                .iter()
                .map(|i| maybe_qualify_symbol(import_name(i), qualifier))
                .collect(),
            (Some(ImportList::Hiding(items)), _) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                module_exports
                    .values
                    .keys()
                    .filter(|n| !hidden.contains(&n.name))
                    .map(|n| maybe_qualify_symbol(n.name, qualifier))
                    .collect()
            }
        };

        // Check for scope conflicts: same name from different defining modules.
        for name in &imported_names {
            // Look up the defining origin for this name (unqualified for origin lookup)
            let unqual = if qualifier.is_some() {
                // For qualified imports, extract unqualified name for origin lookup
                let name_str = crate::interner::resolve(*name).unwrap_or_default();
                if let Some(pos) = name_str.find('.') {
                    crate::interner::intern(&name_str[pos + 1..])
                } else {
                    *name
                }
            } else {
                *name
            };
            let found_origin = module_exports.value_origins.get(&unqual).copied();
            let origin = found_origin.unwrap_or(mod_sym);
            if let Some(&(existing_origin, existing_explicit)) = import_origins.get(name) {
                if existing_origin != origin {
                    if is_explicit && existing_explicit {
                        // Both explicitly import the same name from different modules → conflict
                        ctx.scope_conflicts.insert(*name);
                    } else if is_explicit && !existing_explicit {
                        // Explicit import shadows the open import → replace, no conflict
                        import_origins.insert(*name, (origin, true));
                    } else if !is_explicit && existing_explicit {
                        // Existing explicit import shadows this open import → no conflict
                    } else {
                        // Both open imports from different modules → conflict
                        ctx.scope_conflicts.insert(*name);
                    }
                }
            } else {
                import_origins.insert(*name, (origin, is_explicit));
            }
        }

        // Import instances once per unique module. In PureScript, type class instances are
        // globally visible — importing any item from a module imports all its instances.
        // Module-level dedup avoids redundant O(n²) per-instance comparison for reimports.
        if imported_instance_modules.insert(mod_sym) {
            for (class_name, insts) in &module_exports.instances {
                let existing = instances.entry(*class_name).or_default();
                for inst in insts {
                    if !existing.iter().any(|e| e.0 == inst.0) {
                        existing.push(inst.clone());
                    }
                }
            }
            // Import pre-computed self-referential aliases to avoid recomputing from scratch.
            ctx.state.self_referential_aliases.extend(&module_exports.self_referential_aliases);
        }

        // Compute canonical_origins for explicit/hiding import paths: maps unqualified
        // type names to their origin module when they collide with LOCAL type aliases.
        // Use all_alias_names (not just local_type_alias_names) for consistency with
        // import_all's canonical_origins. Without this, import_item value schemes have
        // bare type names while import_all alias bodies have canonicalized names, causing
        // unification mismatches (e.g., Time vs Data.Time.Time).
        let import_canonical_origins: Option<HashMap<Symbol, Symbol>> = {
            let mut origins: HashMap<Symbol, Symbol> = HashMap::new();
            for (&name, &origin) in &module_exports.type_origins {
                if all_alias_names.contains(&name) {
                    origins.insert(name, origin);
                }
            }
            if origins.is_empty() { None } else { Some(origins) }
        };

        match &import_decl.imports {
            None => {
                // import M — everything unqualified; import M as Q — everything qualified only
                import_all(Some(import_decl.module.clone()), module_exports, env, ctx, qualifier, &all_alias_names, &local_type_alias_names, &local_data_type_names);
            }
            Some(ImportList::Explicit(items)) => {
                // import M (x) — listed items unqualified
                // import M (x) as Q — listed items qualified only
                for item in items {
                    // Track explicitly imported type names (unqualified)
                    if qualifier.is_none() {
                        if let Import::Type(name, _) | Import::Class(name) = item {
                            explicitly_imported_types.insert(name.value);
                        }
                    }
                    import_item(
                        &import_decl.module,
                        item,
                        module_exports,
                        env,
                        ctx,
                        instances,
                        qualifier,
                        import_decl.span,
                        errors,
                        &import_canonical_origins,
                    );
                }
                // Import type_con_arities from the source module for names referenced
                // in imported alias bodies. This ensures data type arities are known
                // for alias expansion disambiguation (e.g., `type GqlData = RemoteData GqlError`
                // where GqlError is a data type in the source module but also an alias
                // from a different qualified import in the consuming module).
                {
                    let mut alias_body_names: HashSet<Symbol> = HashSet::new();
                    for item in items {
                        let item_name = import_name(item);
                        let item_qi = qi(item_name);
                        if let Some(alias) = module_exports.type_aliases.get(&item_qi) {
                            collect_type_con_names_from_type(&alias.1, &mut alias_body_names);
                        }
                    }
                    if !alias_body_names.is_empty() {
                        for (name, arity) in &module_exports.type_con_arities {
                            if alias_body_names.contains(&name.name) {
                                ctx.type_con_arities.entry(maybe_qualify_qualified_ident(*name, qualifier)).or_insert(*arity);
                            }
                        }
                    }
                }
            }
            Some(ImportList::Hiding(items)) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                import_all_except(Some(import_decl.module.clone()), module_exports, &hidden, env, ctx, instances, qualifier, &local_data_type_names, &import_canonical_origins);
            }
        }
    }

    explicitly_imported_types
}


/// Resolve import-qualifier-prefixed type constructors to canonical module names.
/// E.g., `Con(CoreResponse.Response)` → `Con(JS.Fetch.Response.Response)` when
/// `CoreResponse` maps to `JS.Fetch.Response` in the qualifier map.
fn resolve_type_qualifiers(ty: &Type, qualifier_map: &HashMap<Symbol, Symbol>) -> Type {
    match ty {
        Type::Con(name) => {
            if let Some(q) = name.module {
                if let Some(&canonical) = qualifier_map.get(&q) {
                    return Type::Con(QualifiedIdent { module: Some(canonical), name: name.name });
                }
            }
            ty.clone()
        }
        Type::Fun(a, b) => Type::fun(
            resolve_type_qualifiers(a, qualifier_map),
            resolve_type_qualifiers(b, qualifier_map),
        ),
        Type::App(f, a) => Type::app(
            resolve_type_qualifiers(f, qualifier_map),
            resolve_type_qualifiers(a, qualifier_map),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(resolve_type_qualifiers(body, qualifier_map)),
        ),
        Type::Record(fields, tail) => {
            let fields = fields.iter()
                .map(|(l, t)| (*l, resolve_type_qualifiers(t, qualifier_map)))
                .collect();
            let tail = tail.as_ref()
                .map(|t| Box::new(resolve_type_qualifiers(t, qualifier_map)));
            Type::Record(fields, tail)
        }
        _ => ty.clone(),
    }
}

/// Qualify unqualified type constructor names in a type using canonical module names.
/// For each unqualified `Con(X)` that has an entry in `canonical_origins`, replace with
/// `Con(CanonicalModule.X)`. This prevents local type aliases from incorrectly expanding
/// imported type constructors that share the same name.
fn canonicalize_type_cons(ty: &Type, canonical_origins: &HashMap<Symbol, Symbol>) -> Type {
    match ty {
        Type::Con(name) => {
            if name.module.is_none() {
                if let Some(&origin) = canonical_origins.get(&name.name) {
                    return Type::Con(QualifiedIdent { module: Some(origin), name: name.name });
                }
            }
            ty.clone()
        }
        Type::Fun(a, b) => Type::fun(
            canonicalize_type_cons(a, canonical_origins),
            canonicalize_type_cons(b, canonical_origins),
        ),
        Type::App(f, a) => Type::app(
            canonicalize_type_cons(f, canonical_origins),
            canonicalize_type_cons(a, canonical_origins),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(canonicalize_type_cons(body, canonical_origins)),
        ),
        Type::Record(fields, tail) => {
            let fields = fields.iter()
                .map(|(l, t)| (*l, canonicalize_type_cons(t, canonical_origins)))
                .collect();
            let tail = tail.as_ref()
                .map(|t| Box::new(canonicalize_type_cons(t, canonical_origins)));
            Type::Record(fields, tail)
        }
        _ => ty.clone(),
    }
}

fn canonicalize_scheme_type_cons(scheme: &Scheme, canonical_origins: &HashMap<Symbol, Symbol>) -> Scheme {
    Scheme {
        forall_vars: scheme.forall_vars.clone(),
        ty: canonicalize_type_cons(&scheme.ty, canonical_origins),
    }
}

/// Import all names from a module's exports.
/// If `qualifier` is Some, env entries are stored with qualified keys (e.g. "Q.foo").
/// Internal maps (class_methods, data_constructors, etc.) are always unqualified.
fn import_all(
    from: Option<ModuleName>,
    exports: &ModuleExports,
    env: &mut Env,
    ctx: &mut InferCtx,
    qualifier: Option<Symbol>,
    all_alias_names: &HashSet<Symbol>,
    _local_type_alias_names: &HashSet<Symbol>,
    local_data_type_names: &HashSet<Symbol>,
) {
    // For qualified imports, qualify imported type constructors defined in the source
    // module to prevent local alias collisions within this module's scope.
    // E.g., `import JS.Fetch.Response as CoreResponse` qualifies `Con(Response)` to
    // `Con(CoreResponse.Response)` so local `type Response = { ... }` won't expand it.
    // IMPORTANT: only qualify types that actually collide with local type aliases,
    // otherwise instance resolution breaks (instances use unqualified names).
    // Uses all_alias_names (including imported aliases) for ordering independence.
    let defined_types: Option<(HashSet<Symbol>, Symbol)> = qualifier.and_then(|q| {
        let mod_sym = from.as_ref().map(module_name_to_symbol)?;
        let dt: HashSet<Symbol> = exports.type_origins.iter()
            .filter(|(_, &origin)| origin == mod_sym)
            .filter(|(&name, _)| {
                ctx.state.type_aliases.contains_key(&name)
                    || all_alias_names.contains(&name)
            })
            .map(|(&name, _)| name)
            .collect();
        if dt.is_empty() { None } else { Some((dt, q)) }
    });

    // Also canonicalize unqualified type names that collide with existing local aliases.
    // This handles re-exported types: `Con(Response)` from JS.Fetch (where Response
    // originates from JS.Fetch.Response) becomes `Con(JS.Fetch.Response.Response)`.
    // If the exporting module itself defines a name as a type alias, its value schemes
    // use the alias, not the data type. Don't canonicalize in that case — canonicalizing
    // would turn alias references into data type references (e.g., Time=Number into
    // Data.Time.Time, or ResponseUpdate into its qualified form).
    let canonical_origins: Option<HashMap<Symbol, Symbol>> = {
        let mut origins: HashMap<Symbol, Symbol> = HashMap::new();
        for (&name, &origin) in &exports.type_origins {
            // If the exporting module itself has this as a type alias, its value
            // schemes use the alias meaning. Don't canonicalize.
            if exports.type_aliases.iter().any(|(k, _)| k.name == name) {
                continue;
            }
            let has_alias_collision = ctx.state.type_aliases.contains_key(&name)
                || all_alias_names.contains(&name);
            if !has_alias_collision {
                continue;
            }
            origins.insert(name, origin);
        }
        if origins.is_empty() { None } else { Some(origins) }
    };

    // Import class method info first so we can detect conflicts.
    // For qualified imports (import M as Q), only insert under the qualified key
    // so we don't pollute the unqualified class_methods map. This prevents
    // `import Prelude as Prelude` from re-registering `top` as a class method
    // after `import Prelude hiding (top)` correctly hid it.
    for (name, info) in &exports.class_methods {
        let key = maybe_qualify_qualified_ident(*name, qualifier);
        ctx.class_methods.insert(key, (info.0, info.1.iter().map(|s| s.name).collect()));
        // Populate class_method_schemes so instance expected-type lookups use the canonical
        // class type even if the method name later gets shadowed in env by another import.
        if let Some(scheme) = exports.values.get(name) {
            ctx.class_method_schemes.entry(name.name).or_insert_with(|| scheme.clone());
        }
    }
    for (name, scheme) in &exports.values {
        // Don't let a non-class value overwrite a class method's env entry.
        // E.g. Data.Function.apply must not shadow Control.Apply.apply.
        // Only applies to unqualified imports — qualified names (Q.foo) can't conflict.
        if qualifier.is_none()
            && ctx.class_methods.contains_key(name)
            && !exports.class_methods.contains_key(name)
        {
            continue;
        }
        // Apply two fixes to prevent alias expansion collisions:
        // 1. For qualified imports, qualify type cons defined in source module with qualifier
        // 2. Canonicalize type cons that collide with existing local aliases
        let mut scheme = scheme.clone();
        if let Some((dt, q)) = &defined_types {
            scheme = Scheme {
                forall_vars: scheme.forall_vars,
                ty: canonicalize_type_cons(&scheme.ty, &dt.iter().map(|&n| (n, *q)).collect()),
            };
        }
        if let Some(co) = &canonical_origins {
            scheme = canonicalize_scheme_type_cons(&scheme, co);
        }
        env.insert_scheme(maybe_qualify_symbol(name.name, qualifier), scheme);
    }
    for (name, ctors) in &exports.data_constructors {
        ctx.data_constructors.insert(*name, ctors.clone());
        if let Some(q) = qualifier {
            ctx.data_constructors.insert(QualifiedIdent { module: Some(q), name: name.name }, ctors.clone());
        }
    }
    for (name, details) in &exports.ctor_details {
        let entry = (details.0, details.1.iter().map(|s| s.name).collect(), details.2.clone());
        if let Some(q) = qualifier {
            // Qualified import: store under qualified key only (e.g. M.Leaf)
            // Don't insert unqualified — qualified imports don't make names
            // available unqualified, and doing so overwrites correct entries
            // from explicit unqualified imports (e.g. Left from Data.Either).
            ctx.ctor_details.insert(QualifiedIdent { module: Some(q), name: name.name }, entry);
        } else {
            ctx.ctor_details.insert(*name, entry);
        }
    }
    // Instances are imported centrally in process_imports with module-level dedup.
    for (op, target) in &exports.type_operators {
        ctx.type_operators.insert(*op, *target);
    }
    for (op, fixity) in &exports.value_fixities {
        ctx.value_fixities.insert(op.name, *fixity);
    }
    for op in &exports.function_op_aliases {
        ctx.function_op_aliases.insert(*op);
    }
    // For constructor operators (not function aliases), also import the target
    // constructor's scheme under its target name, because Binder::Constructor
    // uses the target name (e.g. `:|` → `NonEmpty`, `:` → `Cons`).
    // Function operator targets (e.g. `$` → `apply`) are NOT imported under their
    // target names to avoid collisions (Data.Function.apply vs Control.Apply.apply).
    for (op, target) in &exports.value_operator_targets {
        if !exports.function_op_aliases.contains(op) {
            if let Some(scheme) = exports.values.get(target) {
                env.insert_scheme(maybe_qualify_symbol(target.name, qualifier), scheme.clone());
            }
        }
    }
    for (op, target) in &exports.operator_class_targets {
        ctx.operator_class_targets.insert(maybe_qualify_qualified_ident(qi(*op), qualifier), maybe_qualify_qualified_ident(qi(*target), qualifier));
    }
    for name in &exports.constrained_class_methods {
        ctx.constrained_class_methods.insert(name.name);
    }
    for (name, constraints) in &exports.method_own_constraints {
        ctx.method_own_constraints.entry(name.name).or_insert_with(|| constraints.clone());
    }
    // For qualified imports, build the set of type names that ORIGINATE from the source
    // module. We only canonicalize these in alias bodies — re-exported types (like String,
    // Maybe from Prim) should stay unqualified to avoid OaComponents.Table.String mismatches.
    let (source_module_sym, exported_type_names) = if qualifier.is_some() {
        let mod_sym = from.as_ref().map(module_name_to_symbol);
        let mut type_names: HashSet<Symbol> = HashSet::new();
        if let Some(mod_sym) = mod_sym {
            for (&name, &origin) in &exports.type_origins {
                if origin == mod_sym {
                    type_names.insert(name);
                }
            }
        }
        (mod_sym, type_names)
    } else {
        (None, HashSet::new())
    };
    for (name, alias) in &exports.type_aliases {
        let sym_params: Vec<Symbol> = alias.0.iter().map(|p| p.name).collect();
        // Canonicalize alias body with canonical_origins to prevent local aliases
        // from intercepting type constructor references in imported alias bodies.
        // E.g., an alias body containing `Time` (the Data.Time data type) must not
        // be expanded by a local `type Time = Number` alias.
        let body_canonicalized = if let Some(co) = &canonical_origins {
            canonicalize_type_cons(&alias.1, co)
        } else {
            alias.1.clone()
        };
        if qualifier.is_none() {
            // Unqualified import: register under unqualified key as before.
            // Don't register if it collides with a locally-defined data/newtype name.
            let collides_with_local_data = local_data_type_names.contains(&name.name);
            if !collides_with_local_data {
                ctx.state.type_aliases.insert(name.name, (sym_params.clone(), body_canonicalized.clone()));
                ctx.qualified_import_unqual_aliases.remove(&name.name);
            }
        }
        // For qualified imports, canonicalize alias body so unqualified type refs
        // from the source module use the canonical module name. This allows
        // try_expand_alias to find them via canonical_to_qualifier fallback.
        let body_for_qualified = if let Some(mod_sym) = source_module_sym {
            canonicalize_alias_body_types(&body_canonicalized, mod_sym, &exported_type_names, Some(name.name))
        } else {
            body_canonicalized.clone()
        };
        let qualified_name = maybe_qualify_symbol(name.name, qualifier);
        // Store under qualified key so alias expansion can disambiguate
        // when multiple modules export the same alias name with different bodies.
        if qualifier.is_some() {
            ctx.state.type_aliases.insert(qualified_name, (sym_params.clone(), body_for_qualified.clone()));
            ctx.qualified_type_alias_names.insert(maybe_qualify_qualified_ident(*name, qualifier));
        }
        // Register under canonical qualified key (origin_module.name) so alias expansion
        // works after canonicalize_type_cons qualifies type constructors to avoid
        // local alias collisions. E.g., Con("Model") canonicalized to
        // Con("AdminDashboard.Model.Model") needs to find the alias under that key.
        // Skip canonical key registration for zero-param aliases: their body often
        // references the canonical form of the same name (e.g. type X = Canon.X a b c),
        // creating a self-referential zero-arg alias under the canonical key.
        if !sym_params.is_empty() {
            if let Some(co) = &canonical_origins {
                if let Some(&origin) = co.get(&name.name) {
                    let origin_str = crate::interner::resolve(origin).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let canonical_key = crate::interner::intern(&format!("{}.{}", origin_str, name_str));
                    let body = if qualifier.is_some() { body_for_qualified.clone() } else { body_canonicalized.clone() };
                    ctx.state.type_aliases.entry(canonical_key)
                        .or_insert((sym_params.clone(), body));
                }
            }
        }
        // Also register under defined_types qualified key for qualified imports.
        if let Some((dt, q)) = &defined_types {
            if dt.contains(&name.name) {
                let q_str = crate::interner::resolve(*q).unwrap_or_default();
                let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                let dt_key = crate::interner::intern(&format!("{}.{}", q_str, name_str));
                let body = if qualifier.is_some() { body_for_qualified.clone() } else { body_canonicalized.clone() };
                ctx.state.type_aliases.entry(dt_key)
                    .or_insert((sym_params.clone(), body));
            }
        }
    }
    for (name, arity) in &exports.type_con_arities {
        ctx.type_con_arities.insert(maybe_qualify_qualified_ident(*name, qualifier), *arity);
    }
    for (name, roles) in &exports.type_roles {
        ctx.type_roles.insert(*name, roles.clone());
    }
    for name in &exports.newtype_names {
        ctx.newtype_names.insert(maybe_qualify_qualified_ident(qi(*name), qualifier));
    }
    for name in &exports.partial_dischargers {
        ctx.partial_dischargers.insert(maybe_qualify_qualified_ident(qi(*name), qualifier));
    }
    for (name, constraints) in &exports.signature_constraints {
        // Import Coercible and solver-class constraints for typechecking.
        // Solver-class constraints (Union, Nub, etc.) need to reach deferred_constraints
        // so Pass 2.75 can solve them. Other constraints are handled locally via
        // extract_type_signature_constraints on CST types.
        let solver_constraints: Vec<_> = constraints
            .iter()
            .filter(|(cn, _)| {
                let name_str = crate::interner::resolve(cn.name).unwrap_or_default();
                matches!(name_str.as_str(),
                    "Coercible" | "Union" | "Nub"
                    | "Add" | "Mul" | "ToString" | "Compare" | "Append"
                    | "CompareSymbol" | "RowToList"
                )
            })
            .cloned()
            .collect();
        if !solver_constraints.is_empty() {
            ctx.signature_constraints
                .entry(maybe_qualify_qualified_ident(*name, qualifier))
                .or_default()
                .extend(solver_constraints);
        }
        // Import ALL constraints for codegen dict resolution (deduplicate by class name)
        if !constraints.is_empty() {
            let entry = ctx.codegen_signature_constraints
                .entry(maybe_qualify_qualified_ident(*name, qualifier))
                .or_default();
            for constraint in constraints {
                if !entry.iter().any(|(cn, _)| cn.name == constraint.0.name) {
                    entry.push(constraint.clone());
                }
            }
        }
    }
    // Also register codegen_signature_constraints AND signature_constraints under operator names.
    // When `>>>` targets `composeFlipped` which has Semigroupoid constraint,
    // the operator name needs to look up those constraints too.
    for (op, target) in &exports.value_operator_targets {
        // Look up constraints under both the target name AND the operator name.
        // Re-exporting modules may store constraints under the operator name
        // (when the target function wasn't explicitly imported, only the operator was).
        let constraints = exports.signature_constraints.get(target)
            .or_else(|| exports.signature_constraints.get(op));
        if let Some(constraints) = constraints {
            if !constraints.is_empty() {
                ctx.codegen_signature_constraints
                    .entry(maybe_qualify_qualified_ident(*op, qualifier))
                    .or_default()
                    .extend(constraints.iter().cloned());
                // Also register in signature_constraints so that infer_var's Forall
                // branch pushes to deferred_constraints (not just codegen_deferred_constraints).
                // This ensures the constraint's unif vars participate in unification and get
                // resolved at Pass 3.
                ctx.signature_constraints
                    .entry(maybe_qualify_qualified_ident(*op, qualifier))
                    .or_default()
                    .extend(constraints.iter().cloned());
            }
        }
    }
}

/// Import a single item from a module's exports.
/// If `qualifier` is Some, env entries are stored with qualified keys.
fn import_item(
    _module_name: &ModuleName,
    item: &Import,
    exports: &ModuleExports,
    env: &mut Env,
    ctx: &mut InferCtx,
    _instances: &mut HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    qualifier: Option<Symbol>,
    import_span: crate::span::Span,
    errors: &mut Vec<TypeError>,
    canonical_origins: &Option<HashMap<Symbol, Symbol>>,
) {
    match item {
        Import::Value(name_spanned) => {
            let name = name_spanned.value;
            let name_qi = qi(name);
            if exports.values.get(&name_qi).is_none() && exports.class_methods.get(&name_qi).is_none() {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name,
                });
                return;
            }
            // Import class method info first if applicable
            if let Some((class_name, tvs)) = exports.class_methods.get(&name_qi) {
                ctx.class_methods.insert(name_qi, (*class_name, tvs.iter().map(|s| s.name).collect()));
            }
            if let Some(scheme) = exports.values.get(&name_qi) {
                // Explicit imports always win — the user specifically asked for this value.
                // Canonicalize type constructors that collide with local type aliases
                // to prevent incorrect alias expansion. E.g., if the local module defines
                // `type File = { ... }`, imported `getMediaType :: File -> String` must
                // have its `File` qualified to `Web.File.File.File` to avoid expansion.
                let scheme = if let Some(co) = canonical_origins {
                    canonicalize_scheme_type_cons(scheme, co)
                } else {
                    scheme.clone()
                };
                env.insert_scheme(maybe_qualify_symbol(name, qualifier), scheme);
            }
            // Instances are imported centrally in process_imports with module-level dedup.
            // Import fixity if this is an operator
            if let Some(fixity) = exports.value_fixities.get(&name_qi) {
                ctx.value_fixities.insert(name, *fixity);
            }
            if exports.function_op_aliases.contains(&name_qi) {
                ctx.function_op_aliases.insert(name_qi);
            }
            if let Some(target) = exports.operator_class_targets.get(&name) {
                ctx.operator_class_targets.insert(qi(name), qi(*target));
                // Also import the target's class method info so the class_method_lookup
                // in infer_var can resolve the constraint (e.g. <> → append → Semigroup).
                if let Some((class_name, tvs)) = exports.class_methods.get(&qi(*target)) {
                    ctx.class_methods.entry(qi(*target))
                        .or_insert_with(|| (*class_name, tvs.iter().map(|s| s.name).collect()));
                }
            }
            if exports.constrained_class_methods.contains(&name_qi) {
                ctx.constrained_class_methods.insert(name);
            }
            if let Some(constraints) = exports.method_own_constraints.get(&name_qi) {
                ctx.method_own_constraints.entry(name).or_insert_with(|| constraints.clone());
            }
            // Import ctor_details if this is a constructor alias (e.g. `:|` for `NonEmpty`)
            if let Some(details) = exports.ctor_details.get(&name_qi) {
                ctx.ctor_details.insert(name_qi, (details.0, details.1.iter().map(|s| s.name).collect(), details.2.clone()));
            }
            // Import solver-class constraints for typechecking (Coercible, Union, Nub, etc.)
            if let Some(constraints) = exports.signature_constraints.get(&name_qi) {
                let solver_only: Vec<_> = constraints
                    .iter()
                    .filter(|(cn, _)| {
                        let name_str = crate::interner::resolve(cn.name).unwrap_or_default();
                        matches!(name_str.as_str(),
                            "Coercible" | "Union" | "Nub"
                            | "Add" | "Mul" | "ToString" | "Compare" | "Append"
                            | "CompareSymbol" | "RowToList"
                        )
                    })
                    .cloned()
                    .collect();
                if !solver_only.is_empty() {
                    ctx.signature_constraints
                        .entry(name_qi)
                        .or_default()
                        .extend(solver_only);
                }
                // Import ALL constraints for codegen dict resolution
                if !constraints.is_empty() {
                    ctx.codegen_signature_constraints
                        .entry(name_qi)
                        .or_default()
                        .extend(constraints.iter().cloned());
                }
            }
            // For operators, also import their target's codegen constraints under the operator name
            if let Some(target) = exports.value_operator_targets.get(&name_qi) {
                let constraints = exports.signature_constraints.get(target)
                    .or_else(|| exports.signature_constraints.get(&name_qi));
                if let Some(constraints) = constraints {
                    if !constraints.is_empty() {
                        ctx.codegen_signature_constraints
                            .entry(name_qi)
                            .or_default()
                            .extend(constraints.iter().cloned());
                        // Also add to signature_constraints for deferred_constraints path
                        ctx.signature_constraints
                            .entry(name_qi)
                            .or_default()
                            .extend(constraints.iter().cloned());
                    }
                }
            }
            // Import partial discharger info (functions with Partial in param position)
            if exports.partial_dischargers.contains(&name) {
                ctx.partial_dischargers
                    .insert(maybe_qualify_qualified_ident(qi(name), qualifier));
            }
            // Import ctor_details if the operator targets a constructor (e.g. `:` → Cons)
            // Use the TARGET name as key since Binder::Constructor uses the target name
            if let Some(target) = exports.value_operator_targets.get(&name_qi) {
                if let Some(details) = exports.ctor_details.get(target) {
                    ctx.ctor_details.insert(*target, (details.0, details.1.iter().map(|s| s.name).collect(), details.2.clone()));
                }
                // For constructor operators, also import the target constructor's scheme
                // under its target name (e.g. `:|` → import `NonEmpty` constructor scheme)
                if !exports.function_op_aliases.contains(&name_qi) {
                    if let Some(scheme) = exports.values.get(target) {
                        env.insert_scheme(maybe_qualify_symbol(target.name, qualifier), scheme.clone());
                    }
                }
            }
        }
        Import::Type(name_spanned, members) => {
            let name = name_spanned.value;
            let name_qi = qi(name);
            if let Some(ctors) = exports.data_constructors.get(&name_qi) {
                ctx.data_constructors.insert(name_qi, ctors.clone());
                if let Some(q) = qualifier {
                    ctx.data_constructors.insert(QualifiedIdent { module: Some(q), name: name_qi.name }, ctors.clone());
                }
                if let Some(arity) = exports.type_con_arities.get(&name_qi) {
                    ctx.type_con_arities.insert(name_qi, *arity);
                }
                if let Some(roles) = exports.type_roles.get(&name) {
                    ctx.type_roles.insert(name, roles.clone());
                }
                if exports.newtype_names.contains(&name) {
                    ctx.newtype_names.insert(name_qi);
                }

                let import_ctors: Vec<QualifiedIdent> = match members {
                    Some(DataMembers::All) => ctors.clone(),
                    Some(DataMembers::Explicit(listed)) => {
                        // Validate that each listed constructor actually exists
                        for ctor_name in listed {
                            if !ctors.iter().any(|c| c.name == ctor_name.value) {
                                errors.push(TypeError::UnknownImportDataConstructor {
                                    span: import_span,
                                    name: ctor_name.value,
                                });
                            }
                        }
                        listed.iter().map(|n| qi(n.value)).collect()
                    }
                    None => Vec::new(), // Just the type, no constructors
                };

                for ctor in &import_ctors {
                    if let Some(scheme) = exports.values.get(ctor) {
                        let scheme = if let Some(co) = canonical_origins {
                            canonicalize_scheme_type_cons(scheme, co)
                        } else {
                            scheme.clone()
                        };
                        env.insert_scheme(maybe_qualify_symbol(ctor.name, qualifier), scheme);
                    }
                }
                // Import ctor_details for ALL constructors when at least some are imported,
                // so the exhaustiveness checker can resolve operator aliases.
                // e.g. `import Data.List (List(Nil), (:))` needs Cons ctor_details
                // to match `:` against `Cons` during exhaustiveness checking.
                // But DON'T import ctor_details for type-only imports (members=None),
                // as the Coercible solver uses ctor_details availability to check
                // constructor accessibility for newtype unwrapping.
                if members.is_some() {
                    for ctor in ctors {
                        if let Some(details) = exports.ctor_details.get(ctor) {
                            let entry = (details.0, details.1.iter().map(|s| s.name).collect(), details.2.clone());
                            if let Some(q) = qualifier {
                                // Qualified import: store under qualified key only
                                ctx.ctor_details.insert(QualifiedIdent { module: Some(q), name: ctor.name }, entry);
                            } else {
                                ctx.ctor_details.insert(*ctor, entry);
                            }
                        }
                    }
                }
                // Also import the type alias if one exists with the same name
                // (kind signatures create data_constructors entries for type aliases)
                if let Some(alias) = exports.type_aliases.get(&name_qi) {
                    let sym_params: Vec<Symbol> = alias.0.iter().map(|p| p.name).collect();
                    if qualifier.is_none() {
                        let body = if let Some(co) = canonical_origins {
                            canonicalize_type_cons(&alias.1, co)
                        } else {
                            alias.1.clone()
                        };
                        ctx.state.type_aliases.insert(name, (sym_params.clone(), body));
                        ctx.qualified_import_unqual_aliases.remove(&name);
                    }
                    if let Some(q) = qualifier {
                        // Canonicalize body for qualified import
                        let mod_sym = module_name_to_symbol(_module_name);
                        let mut type_names: HashSet<Symbol> = HashSet::new();
                        for (&n, &origin) in &exports.type_origins {
                            if origin == mod_sym { type_names.insert(n); }
                        }
                        let body = canonicalize_alias_body_types(&alias.1, mod_sym, &type_names, Some(name));
                        let qualified_name = maybe_qualify_symbol(name, Some(q));
                        ctx.state.type_aliases.insert(qualified_name, (sym_params.clone(), body.clone()));
                        ctx.qualified_type_alias_names.insert(maybe_qualify_qualified_ident(name_qi, Some(q)));
                        // Register under canonical key
                        if let Some(co) = canonical_origins {
                            if let Some(&origin) = co.get(&name) {
                                let origin_str = crate::interner::resolve(origin).unwrap_or_default();
                                let name_str = crate::interner::resolve(name).unwrap_or_default();
                                let canonical_key = crate::interner::intern(&format!("{}.{}", origin_str, name_str));
                                ctx.state.type_aliases.entry(canonical_key)
                                    .or_insert((sym_params.clone(), body));
                            }
                        }
                    } else {
                        // Register under canonical key (unqualified import)
                        // Skip for zero-param aliases to avoid self-referential expansion loops.
                        if !sym_params.is_empty() {
                            if let Some(co) = canonical_origins {
                                if let Some(&origin) = co.get(&name) {
                                    let origin_str = crate::interner::resolve(origin).unwrap_or_default();
                                    let name_str = crate::interner::resolve(name).unwrap_or_default();
                                    let canonical_key = crate::interner::intern(&format!("{}.{}", origin_str, name_str));
                                    ctx.state.type_aliases.entry(canonical_key)
                                        .or_insert((sym_params.clone(), alias.1.clone()));
                                }
                            }
                        }
                    }
                }
            } else if let Some(alias) = exports.type_aliases.get(&name_qi) {
                // Type alias import
                let sym_params: Vec<Symbol> = alias.0.iter().map(|p| p.name).collect();
                if qualifier.is_none() {
                    // Canonicalize alias body to avoid collisions with local type aliases.
                    // E.g., `type HasuraClient = Client ...` where `Client` is from
                    // GraphQL.Client.Types — if the importing module also defines
                    // `type Client = { ... }`, the unqualified `Client` in the alias body
                    // must be qualified to prevent incorrect expansion.
                    let body = if let Some(co) = canonical_origins {
                        canonicalize_type_cons(&alias.1, co)
                    } else {
                        alias.1.clone()
                    };
                    ctx.state.type_aliases.insert(name, (sym_params.clone(), body));
                    ctx.qualified_import_unqual_aliases.remove(&name);
                }
                if qualifier.is_some() {
                    // Canonicalize body for qualified import
                    let mod_sym = module_name_to_symbol(_module_name);
                    let alias_names: HashSet<Symbol> = exports.type_aliases.keys().map(|k| k.name).collect();
                    let body = canonicalize_alias_body_types(&alias.1, mod_sym, &alias_names, Some(name));
                    let qualified_name = maybe_qualify_symbol(name, qualifier);
                    ctx.state.type_aliases.insert(qualified_name, (sym_params.clone(), body.clone()));
                    ctx.qualified_type_alias_names.insert(maybe_qualify_qualified_ident(name_qi, qualifier));
                    // Register under canonical key (skip zero-param to avoid self-ref loops)
                    if !sym_params.is_empty() {
                        if let Some(co) = canonical_origins {
                            if let Some(&origin) = co.get(&name) {
                                let origin_str = crate::interner::resolve(origin).unwrap_or_default();
                                let name_str = crate::interner::resolve(name).unwrap_or_default();
                                let canonical_key = crate::interner::intern(&format!("{}.{}", origin_str, name_str));
                                ctx.state.type_aliases.entry(canonical_key)
                                    .or_insert((sym_params.clone(), body));
                            }
                        }
                    }
                } else {
                    // Register under canonical key (unqualified import, skip zero-param)
                    if !sym_params.is_empty() {
                        if let Some(co) = canonical_origins {
                            if let Some(&origin) = co.get(&name) {
                                let origin_str = crate::interner::resolve(origin).unwrap_or_default();
                                let name_str = crate::interner::resolve(name).unwrap_or_default();
                                let canonical_key = crate::interner::intern(&format!("{}.{}", origin_str, name_str));
                                ctx.state.type_aliases.entry(canonical_key)
                                    .or_insert((sym_params.clone(), alias.1.clone()));
                            }
                        }
                    }
                }
            } else {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name,
                });
            }
        }
        Import::Class(name_spanned) => {
            let name = name_spanned.value;
            let name_qi = qi(name);
            // Check if the class exists in the exports: it may have methods,
            // instances, or be a constraint-only class (no methods, e.g. `class (A a, B a) <= C a`).
            let has_class = exports.class_methods.values().any(|(cn, _)| cn.name == name)
                || exports.instances.get(&name_qi).is_some()
                || exports.class_param_counts.contains_key(&name_qi);
            if !has_class {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name,
                });
                return;
            }
            for (method_name, (class_name, tvs)) in &exports.class_methods {
                if class_name.name == name {
                    ctx.class_methods
                        .insert(*method_name, (*class_name, tvs.iter().map(|s| s.name).collect()));
                    if exports.constrained_class_methods.contains(method_name) {
                        ctx.constrained_class_methods.insert(method_name.name);
                    }
                    if let Some(constraints) = exports.method_own_constraints.get(method_name) {
                        ctx.method_own_constraints.entry(method_name.name).or_insert_with(|| constraints.clone());
                    }
                    // Also populate class_method_schemes so instance expected-type
                    // lookups can use the canonical class type even if the method
                    // name gets shadowed in env by a later value import.
                    if let Some(scheme) = exports.values.get(method_name) {
                        ctx.class_method_schemes.insert(method_name.name, scheme.clone());
                    }
                }
            }
            // Instances are imported centrally in process_imports with module-level dedup.
        }
        Import::TypeOp(name_spanned) => {
            let name = name_spanned.value;
            let name_qi = qi(name);
            if let Some(target) = exports.type_operators.get(&name_qi) {
                ctx.type_operators.insert(name_qi, *target);
                // Import the target's type alias definition if it exists
                if let Some(alias) = exports.type_aliases.get(target) {
                    let sym_params: Vec<Symbol> = alias.0.iter().map(|p| p.name).collect();
                    if qualifier.is_none() {
                        ctx.state.type_aliases.insert(target.name, (sym_params.clone(), alias.1.clone()));
                    } else {
                        let mod_sym = module_name_to_symbol(_module_name);
                        let mut type_names: HashSet<Symbol> = HashSet::new();
                        for (&n, &origin) in &exports.type_origins {
                            if origin == mod_sym { type_names.insert(n); }
                        }
                        let body = canonicalize_alias_body_types(&alias.1, mod_sym, &type_names, Some(target.name));
                        let qualified_name = maybe_qualify_symbol(target.name, qualifier);
                        ctx.state.type_aliases.insert(qualified_name, (sym_params, body));
                    }
                }
            } else {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name,
                });
            }
        }
    }
}

/// Import all names except those in the hidden set.
/// If `qualifier` is Some, env entries are stored with qualified keys.
fn import_all_except(
    from: Option<ModuleName>,
    exports: &ModuleExports,
    hidden: &HashSet<Symbol>,
    env: &mut Env,
    ctx: &mut InferCtx,
    _instances: &mut HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    qualifier: Option<Symbol>,
    local_data_type_names: &HashSet<Symbol>,
    canonical_origins: &Option<HashMap<Symbol, Symbol>>,
) {
    // Import class method info first so we can detect conflicts
    for (name, info) in &exports.class_methods {
        if !hidden.contains(&name.name) {
            ctx.class_methods.insert(*name, (info.0, info.1.iter().map(|s| s.name).collect()));
        }
    }
    for (name, scheme) in &exports.values {
        if !hidden.contains(&name.name) {
            // Don't let a non-class value overwrite a class method's env entry.
            // Only applies to unqualified imports — qualified names (Q.foo) can't conflict.
            if qualifier.is_none()
                && ctx.class_methods.contains_key(name)
                && !exports.class_methods.contains_key(name)
            {
                continue;
            }
            // Canonicalize type constructors that collide with local type aliases
            let scheme = if let Some(co) = canonical_origins {
                canonicalize_scheme_type_cons(scheme, co)
            } else {
                scheme.clone()
            };
            env.insert_scheme(maybe_qualify_symbol(name.name, qualifier), scheme);
        }
    }
    for (name, ctors) in &exports.data_constructors {
        if !hidden.contains(&name.name) {
            ctx.data_constructors.insert(*name, ctors.clone());
            if let Some(q) = qualifier {
                ctx.data_constructors.insert(QualifiedIdent { module: Some(q), name: name.name }, ctors.clone());
            }
            for ctor in ctors {
                if !hidden.contains(&ctor.name) {
                    if let Some(details) = exports.ctor_details.get(ctor) {
                        let entry = (details.0, details.1.iter().map(|s| s.name).collect(), details.2.clone());
                        if let Some(q) = qualifier {
                            ctx.ctor_details.insert(QualifiedIdent { module: Some(q), name: ctor.name }, entry);
                        } else {
                            ctx.ctor_details.insert(*ctor, entry);
                        }
                    }
                }
            }
        }
    }
    // Instances are imported centrally in process_imports with module-level dedup.
    for (op, target) in &exports.type_operators {
        if !hidden.contains(&op.name) {
            ctx.type_operators.insert(*op, *target);
        }
    }
    for (op, fixity) in &exports.value_fixities {
        if !hidden.contains(&op.name) {
            ctx.value_fixities.insert(op.name, *fixity);
        }
    }
    for op in &exports.function_op_aliases {
        if !hidden.contains(&op.name) {
            ctx.function_op_aliases.insert(*op);
        }
    }
    // For constructor operators, also import the target constructor's scheme
    for (op, target) in &exports.value_operator_targets {
        if !hidden.contains(&op.name) && !exports.function_op_aliases.contains(op) {
            if let Some(scheme) = exports.values.get(target) {
                env.insert_scheme(maybe_qualify_symbol(target.name, qualifier), scheme.clone());
            }
        }
    }
    for (op, target) in &exports.operator_class_targets {
        if !hidden.contains(op) {
            ctx.operator_class_targets.insert(maybe_qualify_qualified_ident(qi(*op), qualifier), maybe_qualify_qualified_ident(qi(*target), qualifier));
        }
    }
    for name in &exports.constrained_class_methods {
        if !hidden.contains(&name.name) {
            ctx.constrained_class_methods.insert(name.name);
        }
    }
    for (name, constraints) in &exports.method_own_constraints {
        if !hidden.contains(&name.name) {
            ctx.method_own_constraints.entry(name.name).or_insert_with(|| constraints.clone());
        }
    }
    // For qualified imports, build set of type names originating from source module.
    let (source_module_sym, exported_type_names) = if qualifier.is_some() {
        let mod_sym = from.as_ref().map(module_name_to_symbol);
        let mut type_names: HashSet<Symbol> = HashSet::new();
        if let Some(mod_sym) = mod_sym {
            for (&name, &origin) in &exports.type_origins {
                if origin == mod_sym {
                    type_names.insert(name);
                }
            }
        }
        (mod_sym, type_names)
    } else {
        (None, HashSet::new())
    };
    for (name, alias) in &exports.type_aliases {
        if !hidden.contains(&name.name) {
            let sym_params: Vec<Symbol> = alias.0.iter().map(|p| p.name).collect();
            // Canonicalize alias body with canonical_origins to prevent local aliases
            // from intercepting type constructor references in imported alias bodies.
            let body_canonicalized = if let Some(co) = canonical_origins {
                canonicalize_type_cons(&alias.1, co)
            } else {
                alias.1.clone()
            };
            if qualifier.is_none() {
                // Unqualified import: register under unqualified key.
                let collides_with_local_data = local_data_type_names.contains(&name.name);
                if !collides_with_local_data {
                    ctx.state.type_aliases.insert(name.name, (sym_params.clone(), body_canonicalized.clone()));
                    ctx.qualified_import_unqual_aliases.remove(&name.name);
                }
            }
            // Canonicalize alias body for qualified imports.
            let body_for_qualified = if let Some(mod_sym) = source_module_sym {
                canonicalize_alias_body_types(&body_canonicalized, mod_sym, &exported_type_names, Some(name.name))
            } else {
                body_canonicalized.clone()
            };
            if qualifier.is_some() {
                let qualified_name = maybe_qualify_symbol(name.name, qualifier);
                ctx.state.type_aliases.insert(qualified_name, (sym_params.clone(), body_for_qualified.clone()));
                ctx.qualified_type_alias_names.insert(maybe_qualify_qualified_ident(*name, qualifier));
            }
            // Register under canonical qualified key so alias expansion works after
            // canonicalize_type_cons qualifies type constructors.
            // Skip for zero-param aliases to avoid self-referential expansion loops.
            if !sym_params.is_empty() {
            if let Some(co) = canonical_origins {
                if let Some(&origin) = co.get(&name.name) {
                    let origin_str = crate::interner::resolve(origin).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let canonical_key = crate::interner::intern(&format!("{}.{}", origin_str, name_str));
                    let body = if qualifier.is_some() { body_for_qualified.clone() } else { body_canonicalized.clone() };
                    ctx.state.type_aliases.entry(canonical_key)
                        .or_insert((sym_params.clone(), body));
                }
            }
            }
        }
    }
    for (name, arity) in &exports.type_con_arities {
        if !hidden.contains(&name.name) {
            ctx.type_con_arities.insert(maybe_qualify_qualified_ident(*name, qualifier), *arity);
        }
    }
    // Roles, newtype info, and signature constraints are always imported (non-hideable)
    for (name, roles) in &exports.type_roles {
        ctx.type_roles.insert(*name, roles.clone());
    }
    for name in &exports.newtype_names {
        ctx.newtype_names.insert(maybe_qualify_qualified_ident(qi(*name), qualifier));
    }
    for name in &exports.partial_dischargers {
        if !hidden.contains(name) {
            ctx.partial_dischargers
                .insert(maybe_qualify_qualified_ident(qi(*name), qualifier));
        }
    }
    for (name, constraints) in &exports.signature_constraints {
        if !hidden.contains(&name.name) {
            let solver_only: Vec<_> = constraints
                .iter()
                .filter(|(cn, _)| {
                    let name_str = crate::interner::resolve(cn.name).unwrap_or_default();
                    matches!(name_str.as_str(),
                        "Coercible" | "Union" | "Nub"
                        | "Add" | "Mul" | "ToString" | "Compare" | "Append"
                        | "CompareSymbol" | "RowToList"
                    )
                })
                .cloned()
                .collect();
            if !solver_only.is_empty() {
                ctx.signature_constraints
                    .entry(maybe_qualify_qualified_ident(*name, qualifier))
                    .or_default()
                    .extend(solver_only);
            }
            // Import ALL constraints for codegen dict resolution
            if !constraints.is_empty() {
                ctx.codegen_signature_constraints
                    .entry(maybe_qualify_qualified_ident(*name, qualifier))
                    .or_default()
                    .extend(constraints.iter().cloned());
            }
        }
    }
    // Also register codegen_signature_constraints AND signature_constraints under operator names
    for (op, target) in &exports.value_operator_targets {
        if !hidden.contains(&op.name) {
            let constraints = exports.signature_constraints.get(target)
                .or_else(|| exports.signature_constraints.get(op));
            if let Some(constraints) = constraints {
                if !constraints.is_empty() {
                    ctx.codegen_signature_constraints
                        .entry(maybe_qualify_qualified_ident(*op, qualifier))
                        .or_default()
                        .extend(constraints.iter().cloned());
                    ctx.signature_constraints
                        .entry(maybe_qualify_qualified_ident(*op, qualifier))
                        .or_default()
                        .extend(constraints.iter().cloned());
                }
            }
        }
    }
}

/// Get the primary symbol name from an Import item.
fn import_name(item: &Import) -> Symbol {
    item.name()
}

/// Determines which names from a module's exports should be re-exported,
/// based on the import declaration. In PureScript, `module X` in an export
/// list only re-exports what was actually imported from X in this module.
struct ImportFilter {
    /// None = import all (no filtering). Some = only these names allowed.
    values: Option<HashSet<Symbol>>,
    types: Option<HashSet<Symbol>>,
    classes: Option<HashSet<Symbol>>,
    type_ops: Option<HashSet<Symbol>>,
}

fn build_import_filter(
    import_decl: &crate::cst::ImportDecl,
    mod_exports: &ModuleExports,
) -> ImportFilter {
    match &import_decl.imports {
        None => ImportFilter {
            values: None,
            types: None,
            classes: None,
            type_ops: None,
        },
        Some(crate::cst::ImportList::Explicit(imports)) => {
            let mut values: HashSet<Symbol> = HashSet::new();
            let mut types: HashSet<Symbol> = HashSet::new();
            let mut classes: HashSet<Symbol> = HashSet::new();
            let mut type_ops: HashSet<Symbol> = HashSet::new();
            for imp in imports {
                match imp {
                    crate::cst::Import::Value(name) => {
                        values.insert(name.value);
                        // Importing an operator also imports its target value into the env
                        // so the typechecker can look up its type (AST desugars `1 + 2` to `add 1 2`).
                        // The AST converter gates user-visible scoping separately.
                        if let Some(target) = mod_exports.value_operator_targets.get(&qi(name.value)) {
                            values.insert(target.name);
                        }
                    }
                    crate::cst::Import::Type(name, members) => {
                        types.insert(name.value);
                        // Importing Type(..) also imports its constructors as values
                        if let Some(crate::cst::DataMembers::All) = members {
                            if let Some(ctors) = mod_exports.data_constructors.get(&qi(name.value)) {
                                for ctor in ctors {
                                    values.insert(ctor.name);
                                }
                            }
                        } else if let Some(crate::cst::DataMembers::Explicit(ctor_names)) = members
                        {
                            for ctor in ctor_names {
                                values.insert(ctor.value);
                            }
                        }
                    }
                    crate::cst::Import::Class(name) => {
                        classes.insert(name.value);
                        // Importing a class also imports all its methods
                        for (method_name, (class_name, _)) in &mod_exports.class_methods {
                            if class_name.name == name.value {
                                values.insert(method_name.name);
                            }
                        }
                    }
                    crate::cst::Import::TypeOp(name) => {
                        type_ops.insert(name.value);
                    }
                }
            }
            ImportFilter {
                values: Some(values),
                types: Some(types),
                classes: Some(classes),
                type_ops: Some(type_ops),
            }
        }
        Some(crate::cst::ImportList::Hiding(imports)) => {
            // For hiding, build exclusion sets and invert to "everything except hidden"
            let mut hidden_values: HashSet<Symbol> = HashSet::new();
            let mut hidden_types: HashSet<Symbol> = HashSet::new();
            let mut hidden_classes: HashSet<Symbol> = HashSet::new();
            let mut hidden_type_ops: HashSet<Symbol> = HashSet::new();
            for imp in imports {
                match imp {
                    crate::cst::Import::Value(name) => {
                        hidden_values.insert(name.value);
                    }
                    crate::cst::Import::Type(name, members) => {
                        hidden_types.insert(name.value);
                        if let Some(crate::cst::DataMembers::All) = members {
                            if let Some(ctors) = mod_exports.data_constructors.get(&qi(name.value)) {
                                for ctor in ctors {
                                    hidden_values.insert(ctor.name);
                                }
                            }
                        } else if let Some(crate::cst::DataMembers::Explicit(ctor_names)) = members
                        {
                            for ctor in ctor_names {
                                hidden_values.insert(ctor.value);
                            }
                        }
                    }
                    crate::cst::Import::Class(name) => {
                        hidden_classes.insert(name.value);
                        for (method_name, (class_name, _)) in &mod_exports.class_methods {
                            if class_name.name == name.value {
                                hidden_values.insert(method_name.name);
                            }
                        }
                    }
                    crate::cst::Import::TypeOp(name) => {
                        hidden_type_ops.insert(name.value);
                    }
                }
            }
            // Build allowed sets = everything in mod_exports minus hidden
            let values: HashSet<Symbol> = mod_exports
                .values
                .keys()
                .map(|n| n.name)
                .filter(|n| !hidden_values.contains(n))
                .collect();
            let types: HashSet<Symbol> = mod_exports
                .data_constructors
                .keys()
                .map(|n| n.name)
                .chain(mod_exports.type_aliases.keys().map(|n| n.name))
                .filter(|n| !hidden_types.contains(n))
                .collect();
            let classes: HashSet<Symbol> = mod_exports
                .class_methods
                .values()
                .map(|(c, _)| c.name)
                .filter(|n| !hidden_classes.contains(n))
                .collect();
            let type_ops: HashSet<Symbol> = mod_exports
                .type_operators
                .keys()
                .map(|n| n.name)
                .filter(|n| !hidden_type_ops.contains(n))
                .collect();
            ImportFilter {
                values: Some(values),
                types: Some(types),
                classes: Some(classes),
                type_ops: Some(type_ops),
            }
        }
    }
}

/// Filter a module's exports according to an explicit export list.
fn filter_exports(
    all: &ModuleExports,
    export_list: &crate::cst::ExportList,
    export_span: crate::span::Span,
    _local_types: &HashSet<Symbol>,
    _local_classes: &HashSet<Symbol>,
    registry: &ModuleRegistry,
    imports: &[crate::cst::ImportDecl],
    current_module: &crate::cst::ModuleName,
    errors: &mut Vec<TypeError>,
    _scope_conflicts: &HashSet<Symbol>,
) -> ModuleExports {
    let mut result = ModuleExports::default();

    // Track the original defining module for each exported name (for conflict detection).
    // When two different re-export modules contribute the same name, it's only a conflict
    // if the names have different origins (i.e. independently defined in different modules).
    // Re-exporting the same definition through different paths is allowed (ModuleExportDupes).
    // We also track the import qualifier to distinguish ScopeConflict (same qualifier) from
    // ExportConflict (different qualifiers).
    // Each entry stores (origin_module, import_qualifier, is_locally_defined_in_source).
    // The is_locally_defined flag indicates whether the name was defined in the source module
    // (origin == source) vs. re-exported through it. Conflicts are only genuine when BOTH
    // names are locally defined in different modules. Re-exported names may trace to the same
    // definition but through different import paths, which is not a conflict.
    let mut value_origins: HashMap<Symbol, (Symbol, Option<Symbol>, bool)> = HashMap::new();
    let mut type_origins: HashMap<Symbol, (Symbol, Option<Symbol>, bool)> = HashMap::new();
    let mut class_origins: HashMap<Symbol, (Symbol, Option<Symbol>, bool)> = HashMap::new();

    for export in &export_list.exports {
        match export {
            Export::Value(name) => {
                let name_qi = qi(*name);
                if let Some(scheme) = all.values.get(&name_qi) {
                    result.values.insert(name_qi, scheme.clone());
                }
                // Also export class method info if applicable
                if let Some(info) = all.class_methods.get(&name_qi) {
                    result.class_methods.insert(name_qi, info.clone());
                }
                // Also export fixity if applicable
                if let Some(fixity) = all.value_fixities.get(&name_qi) {
                    result.value_fixities.insert(name_qi, *fixity);
                }
                if all.function_op_aliases.contains(&name_qi) {
                    result.function_op_aliases.insert(name_qi);
                }
                if let Some(target) = all.operator_class_targets.get(name) {
                    result.operator_class_targets.insert(*name, *target);
                }
                if all.constrained_class_methods.contains(&name_qi) {
                    result.constrained_class_methods.insert(name_qi);
                }
                if let Some(constraints) = all.method_own_constraints.get(&name_qi) {
                    result.method_own_constraints.insert(name_qi, constraints.clone());
                }
                // Also export ctor_details if this is a constructor alias (e.g. `:|`)
                if let Some(details) = all.ctor_details.get(&name_qi) {
                    result.ctor_details.insert(name_qi, details.clone());
                }
                // Also export operator target mapping (e.g. + → add) and the target's value scheme
                if let Some(target) = all.value_operator_targets.get(&name_qi) {
                    result.value_operator_targets.insert(name_qi, target.clone());
                    // Include the target value's scheme so importers can look up its type
                    // (AST desugars `1 + 2` to `add 1 2`, which needs `add`'s type).
                    if let Some(target_scheme) = all.values.get(target) {
                        result.values.insert(*target, target_scheme.clone());
                    }
                    // Also export target's ctor_details if it's a constructor
                    if let Some(details) = all.ctor_details.get(target) {
                        result.ctor_details.insert(*target, details.clone());
                    }
                }
                // Export signature constraints for Coercible propagation
                if let Some(constraints) = all.signature_constraints.get(&name_qi) {
                    result.signature_constraints.insert(name_qi, constraints.clone());
                }
                // Export partial discharger info
                if all.partial_dischargers.contains(name) {
                    result.partial_dischargers.insert(*name);
                }
                // Export partial value names
                if all.partial_value_names.contains(name) {
                    result.partial_value_names.insert(*name);
                }
            }
            Export::Type(name, members) => {
                let name_qi = qi(*name);
                if let Some(ctors) = all.data_constructors.get(&name_qi) {
                    let export_ctors: Vec<QualifiedIdent> = match members {
                        Some(DataMembers::All) => ctors.clone(),
                        Some(DataMembers::Explicit(listed)) => listed.iter().map(|n| qi(n.value)).collect(),
                        None => {
                            // Don't overwrite existing constructor list with empty
                            // (handles `module X (A(..), A)` where second A has no members)
                            if !result.data_constructors.contains_key(&name_qi) {
                                result.data_constructors.insert(name_qi, Vec::new());
                            }
                            // Still need to export type aliases below
                            if let Some(alias) = all.type_aliases.get(&name_qi) {
                                result.type_aliases.insert(name_qi, alias.clone());
                            }
                            // Export type kind, arities, and roles
                            if let Some(kind) = all.type_kinds.get(name) {
                                result.type_kinds.insert(*name, kind.clone());
                            }
                            if let Some(arity) = all.type_con_arities.get(&name_qi) {
                                result.type_con_arities.insert(name_qi, *arity);
                            }
                            if let Some(roles) = all.type_roles.get(name) {
                                result.type_roles.insert(*name, roles.clone());
                            }
                            continue;
                        }
                    };

                    result.data_constructors.insert(name_qi, export_ctors.clone());

                    for ctor in &export_ctors {
                        if let Some(scheme) = all.values.get(ctor) {
                            result.values.insert(*ctor, scheme.clone());
                        }
                        if let Some(details) = all.ctor_details.get(ctor) {
                            result.ctor_details.insert(*ctor, details.clone());
                        }
                    }
                }
                // Also export type aliases with this name
                if let Some(alias) = all.type_aliases.get(&name_qi) {
                    result.type_aliases.insert(name_qi, alias.clone());
                }
                // Also export type kind
                if let Some(kind) = all.type_kinds.get(name) {
                    result.type_kinds.insert(*name, kind.clone());
                }
                // Also export type con arities
                if let Some(arity) = all.type_con_arities.get(&name_qi) {
                    result.type_con_arities.insert(name_qi, *arity);
                }
                // Also export type roles
                if let Some(roles) = all.type_roles.get(name) {
                    result.type_roles.insert(*name, roles.clone());
                }
            }
            Export::Class(name) => {
                let name_qi = qi(*name);
                // Export class metadata (for constraint generation) but NOT methods as values.
                // In PureScript, `module M (class C) where` only exports the class —
                // methods must be listed separately: `module M (class C, methodName) where`.
                for (method_name, (class_name, tvs)) in &all.class_methods {
                    if class_name.name == *name {
                        result
                            .class_methods
                            .insert(*method_name, (*class_name, tvs.clone()));
                        if all.constrained_class_methods.contains(method_name) {
                            result.constrained_class_methods.insert(*method_name);
                        }
                        if let Some(constraints) = all.method_own_constraints.get(method_name) {
                            result.method_own_constraints.insert(*method_name, constraints.clone());
                        }
                    }
                }
                // Export instances for this class
                if let Some(insts) = all.instances.get(&name_qi) {
                    result.instances.insert(name_qi, insts.clone());
                }
                // Export class param count (needed for orphan detection and arity checking)
                if let Some(count) = all.class_param_counts.get(&name_qi) {
                    result.class_param_counts.insert(name_qi, *count);
                }
                if let Some(fd) = all.class_fundeps.get(name) {
                    result.class_fundeps.insert(*name, fd.clone());
                }
            }
            Export::TypeOp(name) => {
                let name_qi = qi(*name);
                if let Some(target) = all.type_operators.get(&name_qi) {
                    result.type_operators.insert(name_qi, *target);
                }
                if let Some(fixity) = all.type_fixities.get(&name_qi) {
                    result.type_fixities.insert(name_qi, *fixity);
                }
            }
            Export::Module(mod_name) => {
                // Self-re-export: `module A (module A)` exports everything
                // defined locally in A. The module doesn't import itself,
                // so we copy all items from `all` directly.
                if module_name_to_symbol(mod_name) == module_name_to_symbol(current_module) {
                    for (name, scheme) in &all.values {
                        result.values.insert(*name, scheme.clone());
                    }
                    for (name, ctors) in &all.data_constructors {
                        // Don't overwrite entries already set by explicit Export::Type
                        result.data_constructors.entry(*name).or_insert_with(|| ctors.clone());
                    }
                    for (name, details) in &all.ctor_details {
                        result.ctor_details.entry(*name).or_insert_with(|| details.clone());
                    }
                    for (name, info) in &all.class_methods {
                        result.class_methods.insert(*name, info.clone());
                    }
                    for (name, target) in &all.type_operators {
                        result.type_operators.insert(*name, *target);
                    }
                    for (name, fixity) in &all.type_fixities {
                        result.type_fixities.insert(*name, *fixity);
                    }
                    for (name, fixity) in &all.value_fixities {
                        result.value_fixities.insert(*name, *fixity);
                    }
                    for name in &all.function_op_aliases {
                        result.function_op_aliases.insert(*name);
                    }
                    for (op, target) in &all.operator_class_targets {
                        result.operator_class_targets.insert(*op, *target);
                    }
                    for (op, target) in &all.value_operator_targets {
                        result.value_operator_targets.insert(*op, target.clone());
                    }
                    for name in &all.constrained_class_methods {
                        result.constrained_class_methods.insert(*name);
                    }
                    for (name, constraints) in &all.method_own_constraints {
                        result.method_own_constraints.insert(*name, constraints.clone());
                    }
                    for (name, alias) in &all.type_aliases {
                        result.type_aliases.insert(*name, alias.clone());
                    }
                    for (name, count) in &all.class_param_counts {
                        result.class_param_counts.insert(*name, *count);
                    }
                    for (name, fd) in &all.class_fundeps {
                        result.class_fundeps.insert(*name, fd.clone());
                    }
                    continue;
                }
                // Re-export everything from the named module.
                // `module X` in the export list matches an import whose *effective qualifier* equals X.
                // The effective qualifier is the alias if present, otherwise the module name.
                // e.g. `import Data.Foo` has effective qualifier `Data.Foo`
                // e.g. `import Data.Foo as Foo` has effective qualifier `Foo`
                // So `module Data.Foo` matches the first but NOT the second.
                let reexport_mod_sym = module_name_to_symbol(mod_name);
                for import_decl in imports {
                    let effective_qualifier = import_decl
                        .qualified
                        .as_ref()
                        .map(|q| module_name_to_symbol(q))
                        .unwrap_or_else(|| module_name_to_symbol(&import_decl.module));
                    if effective_qualifier == reexport_mod_sym {
                        // Look up from registry; also check Prim submodules
                        let prim_sub;
                        let full_exports = if is_prim_module(&import_decl.module) {
                            Some(prim_exports())
                        } else if is_prim_submodule(&import_decl.module) {
                            prim_sub = prim_submodule_exports(&import_decl.module);
                            Some(&prim_sub)
                        } else {
                            registry.lookup(&import_decl.module.parts)
                        };
                        if let Some(mod_exports) = full_exports {
                            // Resolve the actual source module for origin tracking.
                            // For Prim modules, use reexport_mod_sym directly.
                            let source_mod_sym = module_name_to_symbol(&import_decl.module);

                            // Build import filter: only names actually imported participate
                            // in conflict detection, but all items are re-exported.
                            let filter = build_import_filter(import_decl, mod_exports);

                            // The import qualifier determines whether a conflict is
                            // a ScopeConflict (same qualifier) or ExportConflict (different qualifiers).
                            let import_qual = import_decl.qualified.as_ref().map(|q| module_name_to_symbol(q));

                            // Check for conflicts: class methods
                            for (name, info) in &mod_exports.class_methods {
                                let (class_name, _) = info;
                                let imported = filter
                                    .classes
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&class_name.name));
                                if imported {
                                    let origin = mod_exports
                                        .class_origins
                                        .get(&class_name.name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = class_origins.get(&class_name.name) {
                                        // Only flag genuine conflicts: both names must be locally
                                        // defined in their respective source modules. Re-exported
                                        // names through different paths are likely the same definition.
                                        if prev_origin != origin && prev_local && is_local_def {
                                            if prev_qual == import_qual {
                                                errors.push(TypeError::ScopeConflict {
                                                    span: export_span,
                                                    name: class_name.name,
                                                });
                                            } else {
                                                errors.push(TypeError::ExportConflict {
                                                    span: export_span,
                                                    name: class_name.name,
                                                });
                                            }
                                        }
                                    } else {
                                        class_origins.insert(class_name.name, (origin, import_qual, is_local_def));
                                    }
                                }
                                result.class_methods.insert(*name, info.clone());
                            }
                            for (name, scheme) in &mod_exports.values {
                                // Don't let a non-class value overwrite a class method's entry
                                if result.class_methods.contains_key(name)
                                    && !mod_exports.class_methods.contains_key(name)
                                {
                                    continue;
                                }
                                let origin = mod_exports
                                    .value_origins
                                    .get(&name.name)
                                    .copied()
                                    .unwrap_or(source_mod_sym);
                                let imported = filter
                                    .values
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&name.name));
                                if imported {
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = value_origins.get(&name.name) {
                                        if prev_origin != origin && prev_local && is_local_def {
                                            let both_are_class_methods =
                                                mod_exports.class_methods.contains_key(name)
                                                && result.class_methods.contains_key(name);
                                            if !both_are_class_methods {
                                                if prev_qual == import_qual {
                                                    errors.push(TypeError::ScopeConflict {
                                                        span: export_span,
                                                        name: name.name,
                                                    });
                                                } else {
                                                    errors.push(TypeError::ExportConflict {
                                                        span: export_span,
                                                        name: name.name,
                                                    });
                                                }
                                            }
                                        }
                                    } else {
                                        value_origins.insert(name.name, (origin, import_qual, is_local_def));
                                    }
                                }
                                if imported {
                                    result.values.insert(*name, scheme.clone());
                                }
                            }
                            for (name, ctors) in &mod_exports.data_constructors {
                                let imported = filter
                                    .types
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&name.name));
                                if imported {
                                    let origin = mod_exports
                                        .type_origins
                                        .get(&name.name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = type_origins.get(&name.name) {
                                        if prev_origin != origin && prev_local && is_local_def {
                                            if prev_qual == import_qual {
                                                errors.push(TypeError::ScopeConflict {
                                                    span: export_span,
                                                    name: name.name,
                                                });
                                            } else {
                                                errors.push(TypeError::ExportConflict {
                                                    span: export_span,
                                                    name: name.name,
                                                });
                                            }
                                        }
                                    } else {
                                        type_origins.insert(name.name, (origin, import_qual, is_local_def));
                                    }
                                }
                                // Don't overwrite data_constructors already set by an explicit
                                // Export::Type — the explicit export has the correct constructor
                                // list for the locally-defined type, while a module re-export
                                // may carry a same-named type from a different module.
                                result.data_constructors.entry(*name).or_insert_with(|| ctors.clone());
                            }
                            for (name, details) in &mod_exports.ctor_details {
                                // Don't overwrite ctor_details already set by Export::Type
                                result.ctor_details.entry(*name).or_insert_with(|| details.clone());
                            }
                            for (name, target) in &mod_exports.type_operators {
                                let imported = filter
                                    .type_ops
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&name.name));
                                if imported {
                                    let origin = mod_exports
                                        .value_origins
                                        .get(&name.name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = value_origins.get(&name.name) {
                                        if prev_origin != origin && prev_local && is_local_def {
                                            if prev_qual == import_qual {
                                                errors.push(TypeError::ScopeConflict {
                                                    span: export_span,
                                                    name: name.name,
                                                });
                                            } else {
                                                errors.push(TypeError::ExportConflict {
                                                    span: export_span,
                                                    name: name.name,
                                                });
                                            }
                                        }
                                    } else {
                                        value_origins.insert(name.name, (origin, import_qual, is_local_def));
                                    }
                                }
                                result.type_operators.insert(*name, *target);
                            }
                            for (name, fixity) in &mod_exports.type_fixities {
                                result.type_fixities.insert(*name, *fixity);
                            }
                            for (name, fixity) in &mod_exports.value_fixities {
                                result.value_fixities.insert(*name, *fixity);
                            }
                            for name in &mod_exports.function_op_aliases {
                                result.function_op_aliases.insert(*name);
                            }
                            for (op, target) in &mod_exports.operator_class_targets {
                                result.operator_class_targets.insert(*op, *target);
                            }
                            for (op, target) in &mod_exports.value_operator_targets {
                                result.value_operator_targets.insert(*op, target.clone());
                            }
                            for name in &mod_exports.constrained_class_methods {
                                result.constrained_class_methods.insert(*name);
                            }
                            for (name, constraints) in &mod_exports.method_own_constraints {
                                result.method_own_constraints.insert(*name, constraints.clone());
                            }
                            for (name, alias) in &mod_exports.type_aliases {
                                // Don't overwrite locally-defined aliases with re-exported ones.
                                // E.g. `module Table (module ColFilterControls, Input, ...)` should
                                // keep Table's own `Input` (7 params) rather than overwriting it
                                // with ColFilterControls' `Input` (3 params).
                                result.type_aliases.entry(*name).or_insert_with(|| alias.clone());
                            }
                            for (name, count) in &mod_exports.class_param_counts {
                                result.class_param_counts.insert(*name, *count);
                            }
                            for (name, fd) in &mod_exports.class_fundeps {
                                result.class_fundeps.insert(*name, fd.clone());
                            }
                            for (name, kind) in &mod_exports.type_kinds {
                                // Don't overwrite existing type_kinds entries — an explicit
                                // Export::Type may have already set the correct kind (e.g.
                                // a 1-param alias kind), and a `module X` re-export from a
                                // different module may carry a data type with the same
                                // unqualified name but a different kind.
                                result.type_kinds.entry(*name).or_insert_with(|| kind.clone());
                            }
                            for (name, kind) in &mod_exports.class_type_kinds {
                                result.class_type_kinds.entry(*name).or_insert_with(|| kind.clone());
                            }
                            for (name, arity) in &mod_exports.type_con_arities {
                                result.type_con_arities.insert(*name, *arity);
                            }
                            for (name, roles) in &mod_exports.type_roles {
                                result.type_roles.insert(*name, roles.clone());
                            }
                        }
                    }
                }
            }
        }
    }

    // Always export all instances (PureScript instances are globally visible)
    for (class_name, insts) in &all.instances {
        result
            .instances
            .entry(*class_name)
            .or_default()
            .extend(insts.clone());
    }

    // Carry forward origin tracking into the result so downstream modules
    // can also detect export conflicts correctly.
    // For locally-exported names (Export::Value/Type/Class), use all's origins.
    // For re-exported names (Export::Module), use the origins we tracked.
    for (name, origin) in &all.value_origins {
        if result.values.contains_key(&qi(*name)) {
            result.value_origins.entry(*name).or_insert(*origin);
        }
    }
    for (name, origin) in &all.type_origins {
        if result.data_constructors.contains_key(&qi(*name)) {
            result.type_origins.entry(*name).or_insert(*origin);
        }
    }
    // Also propagate type_origins for types that appear in exported value schemes
    // but aren't in data_constructors. This covers cases like `fetchWithOptions :: ...
    // Promise Response` where Response is a foreign import data type from another module
    // that isn't directly exported as a type.
    {
        let mut scheme_type_names: HashSet<Symbol> = HashSet::new();
        for scheme in result.values.values() {
            collect_unqualified_type_cons(&scheme.ty, &mut scheme_type_names);
        }
        for name in &scheme_type_names {
            if !result.type_origins.contains_key(name) {
                if let Some(origin) = all.type_origins.get(name) {
                    result.type_origins.insert(*name, *origin);
                }
            }
        }
    }
    for (name, origin) in &all.class_origins {
        result.class_origins.entry(*name).or_insert(*origin);
    }
    // Also include origins from re-exported modules
    for (name, (origin, _, _)) in &value_origins {
        result.value_origins.entry(*name).or_insert(*origin);
    }
    for (name, (origin, _, _)) in &type_origins {
        result.type_origins.entry(*name).or_insert(*origin);
    }
    for (name, (origin, _, _)) in &class_origins {
        result.class_origins.entry(*name).or_insert(*origin);
    }

    // Role info, newtype names, and signature constraints are always propagated
    result.type_roles = all.type_roles.clone();
    result.newtype_names = all.newtype_names.clone();
    result.signature_constraints = all.signature_constraints.clone();
    result.partial_dischargers = all.partial_dischargers.clone();
    result.partial_value_names = all.partial_value_names.clone();
    result.type_con_arities = all.type_con_arities.clone();
    result.method_own_constraints = all.method_own_constraints.clone();
    result.resolved_dicts = all.resolved_dicts.clone();
    result.let_binding_constraints = all.let_binding_constraints.clone();
    result.record_update_fields = all.record_update_fields.clone();
    result.class_method_order = all.class_method_order.clone();
    result.instance_var_kinds = all.instance_var_kinds.clone();

    result
}

/// Collect unqualified type constructor names from a type.
/// Used to find type names in exported value schemes that need origin tracking.
fn collect_unqualified_type_cons(ty: &Type, out: &mut HashSet<Symbol>) {
    match ty {
        Type::Con(name) if name.module.is_none() => { out.insert(name.name); }
        Type::Fun(a, b) => {
            collect_unqualified_type_cons(a, out);
            collect_unqualified_type_cons(b, out);
        }
        Type::App(f, a) => {
            collect_unqualified_type_cons(f, out);
            collect_unqualified_type_cons(a, out);
        }
        Type::Forall(_, body) => collect_unqualified_type_cons(body, out),
        Type::Record(fields, tail) => {
            for (_, t) in fields { collect_unqualified_type_cons(t, out); }
            if let Some(t) = tail { collect_unqualified_type_cons(t, out); }
        }
        _ => {}
    }
}

/// Check exhaustiveness for multi-equation function definitions.
/// Peels `func_ty` to extract parameter types, then for each binder position,
/// checks if all constructors of the corresponding type are covered.
/// Check if a binder contains array patterns which are inherently non-exhaustive
/// (can never be exhaustive because arrays have infinite possible lengths).
/// Literal patterns (Boolean, Int, etc.) are NOT included because Boolean patterns
/// can be exhaustive across multiple equations (true + false).
/// Constructor patterns are NOT included because multiple equations can together
/// cover all constructors of a data type.
fn contains_inherently_partial_binder(binder: &Binder) -> bool {
    match unwrap_binder(binder) {
        Binder::Array { .. } => true,
        Binder::Record { fields, .. } => fields.iter().any(|f| {
            f.binder
                .as_ref()
                .map_or(false, |b| contains_inherently_partial_binder(b))
        }),
        Binder::Constructor { args, .. } => {
            args.iter().any(|b| contains_inherently_partial_binder(b))
        }
        _ => false,
    }
}

/// Check if a binder is irrefutable when considering single-constructor types.
/// A constructor pattern like `Path trace` is irrefutable if `Path` is the only
/// constructor of its type (newtype or single-ctor data) and all its args are
/// also irrefutable (wildcards/vars, or recursively single-ctor patterns).
/// This is used by the array-binder check to avoid false Partial errors for
/// patterns like `dashed (Path []) = ... ; dashed (Path trace) = ...`.
fn is_single_ctor_irrefutable(binder: &Binder, ctx: &InferCtx) -> bool {
    match unwrap_binder(binder) {
        Binder::Wildcard { .. } | Binder::Var { .. } => true,
        Binder::Constructor { name, args, .. } => {
            // Check if this constructor's type has exactly one constructor
            if let Some((parent_type, _, _)) = ctx.ctor_details.get(name) {
                if let Some(ctors) = ctx.data_constructors.get(parent_type) {
                    if ctors.len() == 1 {
                        return args.iter().all(|a| is_single_ctor_irrefutable(a, ctx));
                    }
                }
            }
            false
        }
        Binder::Record { fields, .. } => {
            fields.iter().all(|f| {
                f.binder.as_ref().map_or(true, |b| is_single_ctor_irrefutable(b, ctx))
            })
        }
        _ => false,
    }
}

fn check_multi_eq_exhaustiveness(
    ctx: &InferCtx,
    span: crate::span::Span,
    func_ty: &Type,
    arity: usize,
    decls: &[&Decl],
    errors: &mut Vec<TypeError>,
) {
    // Peel parameter types from the function type
    let mut param_types = Vec::new();
    let mut remaining = func_ty.clone();
    for _ in 0..arity {
        match remaining {
            Type::Fun(param, ret) => {
                param_types.push(*param);
                remaining = *ret;
            }
            _ => return, // can't peel — skip check
        }
    }

    // For each binder position, check exhaustiveness (with nested pattern support)
    for (idx, param_ty) in param_types.iter().enumerate() {
        // Check for array binder patterns which are inherently non-exhaustive
        // (can never cover all cases since arrays have infinite possible lengths).
        // If any position has array binders without a wildcard/var fallback, it needs Partial.
        let has_irrefutable_at_position = decls.iter().any(|decl| {
            if let Decl::Value {
                binders, guarded, ..
            } = decl
            {
                if is_unconditional_for_exhaustiveness(guarded) {
                    if let Some(binder) = binders.get(idx) {
                        return !is_refutable(binder) || is_single_ctor_irrefutable(binder, ctx);
                    }
                }
            }
            false
        });
        if !has_irrefutable_at_position {
            let has_array_binder = decls.iter().any(|decl| {
                if let Decl::Value { binders, .. } = decl {
                    binders
                        .get(idx)
                        .map_or(false, |b| contains_inherently_partial_binder(b))
                } else {
                    false
                }
            });
            if has_array_binder {
                // Only emit Partial for array binders when the type at this position
                // is NOT a known ADT. For ADTs, the constructor exhaustiveness check
                // below handles coverage correctly — an array binder inside a
                // constructor (e.g., `Node [x, y] _`) is harmless if another equation
                // catches all cases for that constructor (e.g., `Node arr w`).
                //
                // Similarly, if any other unconditional equation at this position
                // doesn't itself contain array patterns, the array binder is covered.
                // E.g., `f { success: [] } = ...; f { error: Nothing } = ...` — the
                // second equation covers all cases regardless of `success`, so the
                // array binder in the first doesn't cause partiality.
                let array_covered_by_other_eq = decls.iter().any(|decl| {
                    if let Decl::Value { binders, guarded, .. } = decl {
                        if is_unconditional_for_exhaustiveness(guarded) {
                            if let Some(binder) = binders.get(idx) {
                                return !contains_inherently_partial_binder(binder);
                            }
                        }
                    }
                    false
                });
                let is_known_adt = extract_type_con(param_ty)
                    .map_or(false, |tn| ctx.data_constructors.contains_key(&tn));
                if !is_known_adt && !array_covered_by_other_eq {
                    let partial_sym = crate::interner::intern("Partial");
                    errors.push(TypeError::NoInstanceFound {
                        span,
                        class_name: qi(partial_sym),
                        type_args: vec![],
                    });
                    return;
                }
            }
        }

        if let Some(type_name) = extract_type_con(param_ty) {
            if ctx.data_constructors.contains_key(&type_name) {
                // Only count binders from unconditional equations (or those
                // with a trivially-true guard fallback). Guarded equations
                // might not match even if the pattern does.
                let binder_refs: Vec<&Binder> = decls
                    .iter()
                    .filter_map(|decl| {
                        if let Decl::Value {
                            binders, guarded, ..
                        } = decl
                        {
                            if is_unconditional_for_exhaustiveness(guarded) {
                                binders.get(idx)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect();

                if let Some(missing) = check_exhaustiveness(
                    &binder_refs,
                    param_ty,
                    &ctx.data_constructors,
                    &ctx.ctor_details,
                ) {
                    errors.push(TypeError::NonExhaustivePattern {
                        span,
                        type_name,
                        missing,
                    });
                }
            }
        }
    }
}

/// Check a single value declaration equation.
fn check_value_decl(
    ctx: &mut InferCtx,
    env: &Env,
    _name: Symbol,
    span: crate::span::Span,
    binders: &[Binder],
    guarded: &crate::ast::GuardedExpr,
    where_clause: &[crate::ast::LetBinding],
    expected: Option<&Type>,
) -> Result<Type, TypeError> {
    // Set scoped type variables from the expected type.
    // This enables ScopedTypeVariables: where clause signatures can reference
    // type vars from the enclosing function's forall AND from instance heads.
    let prev_scoped = ctx.scoped_type_vars.clone();
    if let Some(ty) = expected {
        fn collect_all_type_vars(ty: &Type, vars: &mut std::collections::HashSet<Symbol>) {
            match ty {
                Type::Var(v) => {
                    vars.insert(*v);
                }
                Type::Forall(bound_vars, body) => {
                    for &(v, _) in bound_vars {
                        vars.insert(v);
                    }
                    collect_all_type_vars(body, vars);
                }
                Type::Fun(a, b) => {
                    collect_all_type_vars(a, vars);
                    collect_all_type_vars(b, vars);
                }
                Type::App(f, a) => {
                    collect_all_type_vars(f, vars);
                    collect_all_type_vars(a, vars);
                }
                Type::Record(fields, tail) => {
                    for (_, t) in fields {
                        collect_all_type_vars(t, vars);
                    }
                    if let Some(t) = tail {
                        collect_all_type_vars(t, vars);
                    }
                }
                _ => {}
            }
        }
        collect_all_type_vars(ty, &mut ctx.scoped_type_vars);
    }
    let result = check_value_decl_inner(
        ctx,
        env,
        _name,
        span,
        binders,
        guarded,
        where_clause,
        expected,
    );
    ctx.scoped_type_vars = prev_scoped;
    result
}

fn check_value_decl_inner(
    ctx: &mut InferCtx,
    env: &Env,
    _name: Symbol,
    span: crate::span::Span,
    binders: &[Binder],
    guarded: &crate::ast::GuardedExpr,
    where_clause: &[crate::ast::LetBinding],
    expected: Option<&Type>,
) -> Result<Type, TypeError> {
    // Reject bare `_` as the entire body — it's not a valid anonymous argument context.
    if binders.is_empty() {
        if let crate::ast::GuardedExpr::Unconditional(body) = guarded {
            if matches!(body.as_ref(), crate::ast::Expr::Wildcard { .. })
            {
                return Err(TypeError::IncorrectAnonymousArgument { span });
            }
        }
    }

    let mut local_env = env.child();

    if binders.is_empty() {
        // No binders — process where clause then infer body
        let saved_codegen_sigs_where = if !where_clause.is_empty() {
            let saved_codegen_sigs = ctx.codegen_signature_constraints.clone();
            ctx.process_let_bindings(&mut local_env, where_clause)?;
            // Store let-binding constraints keyed by span for codegen.
            // Check both codegen_signature_constraints (populated during inference)
            // and signature_constraints (populated from type signatures in Pass 1).
            for wb in where_clause {
                if let crate::ast::LetBinding::Value { span: bs, binder: crate::ast::Binder::Var { name: bn, .. }, .. } = wb {
                    let qi = QualifiedIdent { module: None, name: bn.value };
                    let constraints = ctx.codegen_signature_constraints.get(&qi)
                        .or_else(|| ctx.signature_constraints.get(&qi));
                    if let Some(constraints) = constraints {
                        if !constraints.is_empty() {
                            ctx.let_binding_constraints.insert(*bs, constraints.clone());
                        }
                    }
                }
            }
            // Don't restore codegen_sigs yet — body needs them for dict resolution
            Some(saved_codegen_sigs)
        } else {
            None
        };

        // Bidirectional checking: when the body is unconditional and we have a type
        // signature, use check_against to push expected types into the body.
        // This enables higher-rank lambda params and per-field record error spans.
        // For lambda bodies, pass the FULL type (with Forall) so check_against can
        // push higher-rank types into lambda params.
        // For non-lambda bodies, skolemize (strip_forall) so that constraint args
        // resolve to rigid Var types that match signature_constraints. Without this,
        // the unifier creates fresh unif vars for the Forall, disconnecting deferred
        // constraint args from the signature's type variables.
        if let Some(sig_ty) = expected {
            if let crate::ast::GuardedExpr::Unconditional(body) = guarded {
                let check_ty = if matches!(body.as_ref(), crate::ast::Expr::Lambda { .. }) {
                    sig_ty.clone()
                } else {
                    strip_forall(sig_ty.clone())
                };
                let body_ty = ctx.check_against(&local_env, body, &check_ty)?;
                if let Some(saved) = saved_codegen_sigs_where {
                    ctx.codegen_signature_constraints = saved;
                }
                return Ok(body_ty);
            }
            let skolemized = strip_forall(sig_ty.clone());
            let body_ty = ctx.infer_guarded(&local_env, guarded)?;
            ctx.state.unify(span, &body_ty, &skolemized)?;
            if let Some(saved) = saved_codegen_sigs_where {
                ctx.codegen_signature_constraints = saved;
            }
            return Ok(body_ty);
        }

        let body_ty = ctx.infer_guarded(&local_env, guarded)?;
        if let Some(saved) = saved_codegen_sigs_where {
            ctx.codegen_signature_constraints = saved;
        }
        Ok(body_ty)
    } else {
        // Has binders — process binders first so they're in scope for where clause
        let mut param_types = Vec::new();

        if let Some(sig_ty) = expected {
            // Peel parameter types from the signature.
            // Use skolemization (keep rigid Type::Var) rather than instantiation
            // (unification variables) so that `forall a. a -> Int` with body `x`
            // correctly fails: Var(a) ≠ Con(Int).
            let mut remaining_sig = strip_forall(sig_ty.clone());

            for binder in binders {
                // Zonk to expand type aliases (e.g. NaturalTransformation f g → forall a. f a -> g a)
                remaining_sig = ctx.state.zonk(remaining_sig);
                // Strip any resulting Forall so we can peel Fun args
                remaining_sig = strip_forall(remaining_sig);
                match remaining_sig {
                    Type::Fun(param_ty, ret_ty) => {
                        ctx.infer_binder(&mut local_env, binder, &param_ty)?;
                        param_types.push(*param_ty);
                        remaining_sig = *ret_ty;
                    }
                    _ => {
                        // Signature doesn't have enough arrows — use fresh vars
                        let param_ty = Type::Unif(ctx.state.fresh_var());
                        ctx.infer_binder(&mut local_env, binder, &param_ty)?;
                        param_types.push(param_ty);
                    }
                }
            }

            // Process where clause after binders are in scope
            let saved_codegen_sigs_where2 = if !where_clause.is_empty() {
                let saved_codegen_sigs = ctx.codegen_signature_constraints.clone();
                ctx.process_let_bindings(&mut local_env, where_clause)?;
                for wb in where_clause {
                    if let crate::ast::LetBinding::Value { span: bs, binder: crate::ast::Binder::Var { name: bn, .. }, .. } = wb {
                        let qi = QualifiedIdent { module: None, name: bn.value };
                        if let Some(constraints) = ctx.codegen_signature_constraints.get(&qi) {
                            if !constraints.is_empty() {
                                ctx.let_binding_constraints.insert(*bs, constraints.clone());
                            }
                        }
                    }
                }
                Some(saved_codegen_sigs)
            } else {
                None
            };

            let body_ty = ctx.infer_guarded(&local_env, guarded)?;
            if let Some(saved) = saved_codegen_sigs_where2 {
                ctx.codegen_signature_constraints = saved;
            }
            ctx.state.unify(span, &body_ty, &remaining_sig)?;

            // Rebuild the full function type
            let mut result = body_ty;
            for param_ty in param_types.into_iter().rev() {
                result = Type::fun(param_ty, result);
            }
            Ok(result)
        } else {
            // No signature — infer everything
            for binder in binders {
                let param_ty = Type::Unif(ctx.state.fresh_var());
                ctx.infer_binder(&mut local_env, binder, &param_ty)?;
                param_types.push(param_ty);
            }

            // Process where clause after binders are in scope
            let saved_codegen_sigs_where3 = if !where_clause.is_empty() {
                let saved_codegen_sigs = ctx.codegen_signature_constraints.clone();
                ctx.process_let_bindings(&mut local_env, where_clause)?;
                for wb in where_clause {
                    if let crate::ast::LetBinding::Value { span: bs, binder: crate::ast::Binder::Var { name: bn, .. }, .. } = wb {
                        let qi = QualifiedIdent { module: None, name: bn.value };
                        if let Some(constraints) = ctx.codegen_signature_constraints.get(&qi) {
                            if !constraints.is_empty() {
                                ctx.let_binding_constraints.insert(*bs, constraints.clone());
                            }
                        }
                    }
                }
                Some(saved_codegen_sigs)
            } else {
                None
            };

            let body_ty = ctx.infer_guarded(&local_env, guarded)?;
            if let Some(saved) = saved_codegen_sigs_where3 {
                ctx.codegen_signature_constraints = saved;
            }

            let mut result = body_ty;
            for param_ty in param_types.into_iter().rev() {
                result = Type::fun(param_ty, result);
            }
            Ok(result)
        }
    }
}

/// Recursively check if a type contains any `Type::Var` (rigid type variables).
fn contains_type_var(ty: &Type) -> bool {
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
fn contains_type_var_or_unif(ty: &Type) -> bool {
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
fn type_has_concrete_con(ty: &Type) -> bool {
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
fn check_derive_position(
    ty: &Type,
    var: Symbol,
    positive: bool,
    want_covariant: bool,
    allow_forall: bool,
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    tyvar_classes: &HashMap<Symbol, Vec<Symbol>>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
    data_constructors: &HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
    local_concrete_type_names: &HashSet<Symbol>,
    depth: usize,
) -> bool {
    if depth > 50 {
        return true;
    } // avoid infinite recursion
      // If the variable doesn't appear in this type, it's always fine
    if !type_var_occurs_in(var, ty) {
        return true;
    }

    let functor_sym = crate::interner::intern("Functor");
    let foldable_sym = crate::interner::intern("Foldable");
    let traversable_sym = crate::interner::intern("Traversable");
    let contravariant_sym = crate::interner::intern("Contravariant");
    let bifunctor_sym = crate::interner::intern("Bifunctor");
    let profunctor_sym = crate::interner::intern("Profunctor");

    match ty {
        Type::Var(v) if *v == var => {
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
            if vars.iter().any(|(v, _)| *v == var) {
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
                let has_functor = has_class_instance_for(instances, qi(functor_sym), *head_con)
                    || has_class_instance_for(instances, qi(foldable_sym), *head_con)
                    || has_class_instance_for(instances, qi(traversable_sym), *head_con);
                let has_contravariant =
                    has_class_instance_for(instances, qi(contravariant_sym), *head_con);
                let has_bifunctor = has_class_instance_for(instances, qi(bifunctor_sym), *head_con);
                let has_profunctor = has_class_instance_for(instances, qi(profunctor_sym), *head_con);

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
                    if !type_var_occurs_in(var, arg) {
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
                            || data_constructors.iter().any(|(k, v)| k.name == head_con.name && !v.is_empty())
                            || local_concrete_type_names.contains(&head_con.name)
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
                            || local_concrete_type_names.contains(&head_con.name)
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
                        || local_concrete_type_names.contains(&head_con.name)
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
                    if !type_var_occurs_in(var, arg) {
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
fn try_expand_type_constructors(
    head_con: QualifiedIdent,
    args: &[&Type],
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
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
    let subst: HashMap<Symbol, Type> = type_vars
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
fn has_class_instance_for(
    instances: &HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)>>,
    class: QualifiedIdent,
    type_con: QualifiedIdent,
) -> bool {
    // Try both the exact class key and unqualified fallback
    let class_instances = instances.get(&class).or_else(|| {
        if class.module.is_some() {
            instances.get(&qi(class.name))
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
                    // Match by exact QualifiedIdent or by unqualified name
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
fn get_type_constructor_head(ty: &Type) -> Option<QualifiedIdent> {
    match ty {
        Type::Con(s) => Some(*s),
        Type::App(f, _) => get_type_constructor_head(f),
        _ => None,
    }
}

/// Check if a specific type variable (Symbol) appears in a type.
fn type_var_occurs_in(var: Symbol, ty: &Type) -> bool {
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

/// Try to solve a Coercible constraint using given interactions.
///
/// This implements a simplified version of the original PureScript compiler's
/// interaction system. For canonical givens (where LHS is a type var that
/// doesn't occur in the RHS), we can rewrite the wanted by substituting
/// the type var. For transitive cases (Coercible a b, Coercible b c => Coercible a c),
/// we also try combining canonical givens that share a type var.
fn try_solve_coercible_with_interactions(
    wanted_a: &Type,
    wanted_b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<Symbol, Vec<Role>>,
    newtype_names: &HashSet<QualifiedIdent>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
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
    let mut canonical_subst: HashMap<Symbol, Type> = HashMap::new();
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
fn canonical_lhs_var(given: &(Type, Type)) -> Vec<(Symbol, Type)> {
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
fn decompose_given_pair(
    a: &Type,
    b: &Type,
    type_roles: &HashMap<Symbol, Vec<Role>>,
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
fn free_named_type_vars(ty: &Type) -> HashSet<Symbol> {
    let mut vars = HashSet::new();
    collect_free_named_vars(ty, &HashSet::new(), &mut vars);
    vars
}

fn collect_free_named_vars(ty: &Type, bound: &HashSet<Symbol>, vars: &mut HashSet<Symbol>) {
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

/// Expand type aliases in a type (standalone version for use outside unification).
/// Repeatedly expands until no more aliases apply.
/// Eta-reduce a type alias: for `type F a b = G H a b`, strip trailing params
/// from the body to produce `G H`. Returns None if not eta-reducible (params
/// don't appear as trailing args in order).
fn eta_reduce_alias(params: &[Symbol], body: &Type) -> Option<Type> {
    if params.is_empty() {
        return None;
    }
    let mut current = body;
    let mut remaining_params: Vec<Symbol> = params.to_vec();
    // Strip trailing App(_, Var(param)) from back to front
    let mut stripped = Vec::new();
    while let Type::App(f, a) = current {
        if let Some(&last_param) = remaining_params.last() {
            if let Type::Var(v) = a.as_ref() {
                if *v == last_param {
                    stripped.push(());
                    remaining_params.pop();
                    current = f.as_ref();
                    continue;
                }
            }
        }
        break;
    }
    // Must strip ALL params for full eta-reduction
    if remaining_params.is_empty() {
        Some(current.clone())
    } else {
        None
    }
}

fn expand_type_aliases(ty: &Type, type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>) -> Type {
    let mut expanding = HashSet::new();
    expand_type_aliases_inner(ty, type_aliases, 0, &mut expanding)
}

fn expand_type_aliases_inner(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    depth: u32,
    expanding: &mut HashSet<QualifiedIdent>,
) -> Type {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    expand_type_aliases_inner_impl(ty, type_aliases, depth, expanding)
    })
}

fn expand_type_aliases_inner_impl(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    depth: u32,
    expanding: &mut HashSet<QualifiedIdent>,
) -> Type {
    if depth > 100 || type_aliases.is_empty() {
        return ty.clone();
    }

    // For App types, collect the full spine first to determine the total arg count.
    // This prevents inner App nodes from being independently expanded as aliases
    // when they're part of a larger application (e.g., Codec with 5 args where
    // Codec also has a 1-param alias — expanding the inner App(Con("Codec"), X)
    // would incorrectly treat it as the alias).
    if let Type::App(_, _) = ty {
        let mut raw_args: Vec<&Type> = Vec::new();
        let mut head = ty;
        while let Type::App(f, a) = head {
            raw_args.push(a.as_ref());
            head = f.as_ref();
        }
        raw_args.reverse();

        if let Type::Con(name) = head {
            if !expanding.contains(name) {
                // Use qualified key for qualified types to avoid expanding a data type
                // (e.g. HATS.Easing) using an alias from a different module with the same
                // unqualified name (e.g. Tick's type Easing = Number -> Number).
                let alias_entry = if let Some(module) = name.module {
                    let mod_str = crate::interner::resolve(module).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let qualified = crate::interner::intern(&format!("{}.{}", mod_str, name_str));
                    type_aliases.get(&qualified)
                } else {
                    type_aliases.get(&name.name)
                };
                if let Some((params, body)) = alias_entry {
                    if raw_args.len() == params.len() {
                        // Exactly saturated: expand args, substitute, recurse
                        let expanded_args: Vec<Type> = raw_args
                            .iter()
                            .map(|a| {
                                expand_type_aliases_inner(a, type_aliases, depth + 1, expanding)
                            })
                            .collect();
                        let subst: HashMap<Symbol, Type> = params
                            .iter()
                            .copied()
                            .zip(expanded_args.into_iter())
                            .collect();
                        expanding.insert(*name);
                        let result = expand_type_aliases_inner(
                            &apply_var_subst(&subst, body),
                            type_aliases,
                            depth + 1,
                            expanding,
                        );
                        expanding.remove(name);
                        return result;
                    }
                }
            }
        }

        // Not an expandable alias — expand each arg independently.
        // For the head: if it's a bare Con, don't recurse (not saturated).
        let expanded_args: Vec<Type> = raw_args
            .iter()
            .map(|a| expand_type_aliases_inner(a, type_aliases, depth + 1, expanding))
            .collect();
        let expanded_head = match head {
            Type::Con(_) => head.clone(),
            _ => expand_type_aliases_inner(head, type_aliases, depth + 1, expanding),
        };
        let mut result = expanded_head;
        for arg in expanded_args {
            result = Type::app(result, arg);
        }
        return result;
    }

    match ty {
        Type::Fun(a, b) => Type::fun(
            expand_type_aliases_inner(a, type_aliases, depth + 1, expanding),
            expand_type_aliases_inner(b, type_aliases, depth + 1, expanding),
        ),
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| {
                    (
                        *l,
                        expand_type_aliases_inner(t, type_aliases, depth + 1, expanding),
                    )
                })
                .collect();
            let tail = tail.as_ref().map(|t| {
                Box::new(expand_type_aliases_inner(
                    t,
                    type_aliases,
                    depth + 1,
                    expanding,
                ))
            });
            Type::Record(fields, tail)
        }
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(expand_type_aliases_inner(
                body,
                type_aliases,
                depth + 1,
                expanding,
            )),
        ),
        Type::Con(name) => {
            // Zero-arg alias expansion — use qualified key for qualified types
            if !expanding.contains(name) {
                let alias_entry = if let Some(module) = name.module {
                    let mod_str = crate::interner::resolve(module).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let qualified = crate::interner::intern(&format!("{}.{}", mod_str, name_str));
                    type_aliases.get(&qualified)
                } else {
                    type_aliases.get(&name.name)
                };
                if let Some((params, body)) = alias_entry {
                    if params.is_empty() {
                        expanding.insert(*name);
                        let result =
                            expand_type_aliases_inner(body, type_aliases, depth + 1, expanding);
                        expanding.remove(name);
                        return result;
                    }
                    // Eta-reduce partially applied aliases: `type Tree a = Cofree Array a`
                    // as a bare `Tree` (0 args) → try to produce `Cofree Array`.
                    // This works when the alias body ends with exactly the params in order.
                    if let Some(reduced) = eta_reduce_alias(params, body) {
                        expanding.insert(*name);
                        let result = expand_type_aliases_inner(&reduced, type_aliases, depth + 1, expanding);
                        expanding.remove(name);
                        return result;
                    }
                }
            }
            ty.clone()
        }
        _ => ty.clone(),
    }
}

/// Result of instance resolution with depth tracking.
enum InstanceResult {
    Match,
    NoMatch,
    DepthExceeded,
    UnknownClass(QualifiedIdent),
}

/// Like `has_matching_instance_depth` but returns a tri-state result to distinguish
/// "no instance found" from "possibly infinite instance" (depth exceeded).
fn check_instance_depth(
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

fn check_instance_depth_impl(
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
                                crate::interner::resolve(*f).unwrap_or_default() == label_str
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

        let mut subst: HashMap<Symbol, Type> = HashMap::new();
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
                fn has_var_or_unif(ty: &Type, subst: &HashMap<Symbol, Type>) -> bool {
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

fn has_matching_instance_depth(
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
        let mut subst: HashMap<Symbol, Type> = HashMap::new();
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
fn collect_type_constructors(ty: &Type, out: &mut Vec<Symbol>) {
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

fn type_has_vars(ty: &Type) -> bool {
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

fn type_contains_record(ty: &Type) -> bool {
    // Flag record types at the top level that have concrete fields or are closed.
    // Open records like `{ | r }` are fine (equivalent to `Record r` which is nominal).
    // Records nested inside type constructors (e.g. `Maybe { x :: Int }`) are also fine.
    match ty {
        Type::Record(fields, tail) => !fields.is_empty() || tail.is_none(),
        _ => false,
    }
}

fn type_has_local_con(ty: &Type, local_types: &HashSet<Symbol>) -> bool {
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
fn check_orphan_with_fundeps(
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
fn compute_covering_sets(n: usize, fundeps: &[(Vec<usize>, Vec<usize>)]) -> Vec<Vec<usize>> {
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
fn fundep_closure(initial: &[usize], fundeps: &[(Vec<usize>, Vec<usize>)]) -> HashSet<usize> {
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
fn combinations(n: usize, size: usize) -> Vec<Vec<usize>> {
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

fn type_expr_has_kinded(ty: &crate::ast::TypeExpr) -> bool {
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
fn extract_kind_annotations(types: &[TypeExpr]) -> HashMap<Symbol, Symbol> {
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
fn extract_kind_name_ast(kind: &TypeExpr) -> Option<Symbol> {
    match kind {
        TypeExpr::Constructor { name, .. } => Some(name.name),
        TypeExpr::Var { name, .. } => Some(name.value),
        _ => None,
    }
}

/// Check if two lists of CST TypeExprs are alpha-equivalent (including kind annotations).
/// Used for overlap detection when kind annotations are present, since the internal Type
/// representation strips kind info.
fn type_exprs_alpha_eq_list(a: &[crate::ast::TypeExpr], b: &[crate::ast::TypeExpr]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut var_map: HashMap<Symbol, Symbol> = HashMap::new();
    a.iter()
        .zip(b.iter())
        .all(|(x, y)| type_expr_alpha_eq(x, y, &mut var_map))
}

/// Check if two CST TypeExprs are alpha-equivalent (variables map consistently).
fn type_expr_alpha_eq(
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
fn instance_heads_overlap(
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
    let mut var_map: HashMap<Symbol, Symbol> = HashMap::new();
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
    let mut subst_ab: HashMap<Symbol, Type> = HashMap::new();
    let a_subsumes_b = expanded_a
        .iter()
        .zip(expanded_b.iter())
        .all(|(a, b)| match_instance_type_strict(a, b, &mut subst_ab));
    if a_subsumes_b {
        return true;
    }
    let mut subst_ba: HashMap<Symbol, Type> = HashMap::new();
    expanded_b
        .iter()
        .zip(expanded_a.iter())
        .all(|(b, a)| match_instance_type_strict(b, a, &mut subst_ba))
}

/// Check if two instance types are alpha-equivalent (identical up to variable renaming).
/// Var matches Var (with consistent renaming), Con matches Con, but Var does NOT match Con.
fn instance_types_alpha_eq(a: &Type, b: &Type, var_map: &mut HashMap<Symbol, Symbol>) -> bool {
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
fn type_con_names_eq(a: Symbol, b: Symbol) -> bool {
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
fn type_con_qi_eq(a: &QualifiedIdent, b: &QualifiedIdent) -> bool {
    // When both have module qualifiers and they match, that's a strong positive.
    // When they differ, DON'T return false — the difference may be due to
    // import aliases vs canonical module names (e.g., "FO" vs "Foreign.Object"
    // both referring to Foreign.Object.Object). Always fall back to name comparison.
    type_con_names_eq(a.name, b.name)
}

/// Strict module-aware type constructor comparison for overlap checking.
/// Unlike `type_con_qi_eq`, when one type has a module qualifier and the other
/// doesn't, treats them as distinct (e.g., `List` vs `Lazy.List`).
fn type_con_qi_eq_strict(a: &QualifiedIdent, b: &QualifiedIdent) -> bool {
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
fn types_eq_lenient(a: &Type, b: &Type) -> bool {
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
fn match_instance_type(inst_ty: &Type, concrete: &Type, subst: &mut HashMap<Symbol, Type>) -> bool {
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
            let mut remaining2: Vec<(Symbol, Type)> = f2.to_vec();
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
fn type_matches_kind(ty: &Type, kind_name: &str) -> bool {
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
fn match_instance_type_strict(inst_ty: &Type, concrete: &Type, subst: &mut HashMap<Symbol, Type>) -> bool {
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

/// Check if a type variable (Symbol) occurs in a type — used for infinite type detection.
fn occurs_var(v: Symbol, ty: &Type) -> bool {
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
fn could_unify_types(a: &Type, b: &Type) -> bool {
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
fn could_match_instance_type(
    inst_ty: &Type,
    concrete: &Type,
    subst: &mut HashMap<Symbol, Type>,
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
enum ChainResult {
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
fn check_chain_ambiguity(
    instances: &[(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>, Option<Symbol>)],
    concrete_args: &[Type],
) -> ChainResult {
    for (inst_types, _inst_constraints, _) in instances {
        if inst_types.len() != concrete_args.len() {
            continue;
        }

        // Check if this instance could potentially match (liberal check)
        let mut liberal_subst: HashMap<Symbol, Type> = HashMap::new();
        let could_match = inst_types
            .iter()
            .zip(concrete_args.iter())
            .all(|(inst_ty, arg)| could_match_instance_type(inst_ty, arg, &mut liberal_subst));

        if !could_match {
            // Instance is Apart — skip to next in chain
            continue;
        }

        // Instance could match. Check if it definitely matches (exact check).
        let mut exact_subst: HashMap<Symbol, Type> = HashMap::new();
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
fn solve_compare_graph(
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

/// Apply a variable substitution (Type::Var → Type) to a type.
/// Fully capture-avoiding: when a forall-bound variable would capture a free
/// variable in a substitution value, the forall-bound variable is alpha-renamed.
fn apply_var_subst(subst: &HashMap<Symbol, Type>, ty: &Type) -> Type {
    apply_var_subst_inner(subst, ty, &mut 0u32)
}

fn apply_var_subst_inner(subst: &HashMap<Symbol, Type>, ty: &Type, counter: &mut u32) -> Type {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || apply_var_subst_inner_impl(subst, ty, counter))
}

fn apply_var_subst_inner_impl(subst: &HashMap<Symbol, Type>, ty: &Type, counter: &mut u32) -> Type {
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
            let mut renames: HashMap<Symbol, Symbol> = HashMap::new();
            let mut new_vars = vars.clone();
            for (i, (v, _vis)) in vars.iter().enumerate() {
                let captured = inner_subst.values().any(|val| type_has_free_var(val, *v));
                if captured {
                    let fresh = crate::interner::intern(&format!("$r{}", *counter));
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
fn type_has_free_var(ty: &Type, name: Symbol) -> bool {
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
fn rename_type_vars(ty: &Type, renames: &HashMap<Symbol, Symbol>) -> Type {
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
fn check_cannot_generalize_recursive(
    state: &mut crate::typechecker::unify::UnifyState,
    deferred_constraints: &[(crate::span::Span, QualifiedIdent, Vec<Type>)],
    op_deferred_constraints: &[(crate::span::Span, QualifiedIdent, Vec<Type>)],
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
                    name,
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
fn check_ambiguous_type_variables(
    state: &mut crate::typechecker::unify::UnifyState,
    deferred_constraints: &[(crate::span::Span, QualifiedIdent, Vec<Type>)],
    constraint_start: usize,
    span: crate::span::Span,
    zonked_ty: &Type,
    class_fundeps: &HashMap<QualifiedIdent, (Vec<Symbol>, Vec<(Vec<usize>, Vec<usize>)>)>,
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
        let cn = crate::interner::resolve(class_name.name).unwrap_or_default();
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
    for (ci, (_, class_name, constraint_args)) in constraints.iter().enumerate() {
        let mut ambiguous_names: Vec<Symbol> = Vec::new();
        for (i, _) in constraint_args.iter().enumerate() {
            if i >= all_zonked[ci].len() { continue; }
            if let (_, Some(id)) = &all_zonked[ci][i] {
                // Skip vars reachable through fundep constraints — they may be
                // resolved through instance improvement during constraint solving.
                if !known_vars.contains(id) && !fundep_reachable_vars.contains(id) {
                    ambiguous_names.push(crate::interner::intern(&format!("t{}", id.0)));
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
fn compute_generic_rep_type(
    target_name: &QualifiedIdent,
    data_constructors: &HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
) -> Option<Type> {
    let ctors = data_constructors.get(target_name)
        .or_else(|| {
            data_constructors.iter()
                .find(|(k, _)| k.name == target_name.name)
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
        let ctor_name_str = crate::interner::resolve(ctor_qi.name).unwrap_or_default().to_string();
        let ctor_name_type_sym = intern(&ctor_name_str);

        let fields = ctor_details.get(ctor_qi)
            .or_else(|| ctor_details.iter().find(|(k, _)| k.name == ctor_qi.name).map(|(_, v)| v))
            .map(|(_, _, fields)| fields.as_slice())
            .unwrap_or(&[]);

        let args_rep = if fields.is_empty() {
            Type::Con(qi(no_arguments_sym))
        } else {
            // Right-nested Product of Argument types
            let arg_types: Vec<Type> = fields.iter()
                .map(|t| Type::App(Box::new(Type::Con(qi(argument_sym))), Box::new(t.clone())))
                .collect();
            arg_types.into_iter().rev().reduce(|acc, arg| {
                Type::App(
                    Box::new(Type::App(Box::new(Type::Con(qi(product_sym))), Box::new(arg))),
                    Box::new(acc),
                )
            }).unwrap()
        };

        // Constructor "Name" args
        let ctor_rep = Type::App(
            Box::new(Type::App(
                Box::new(Type::Con(qi(constructor_sym))),
                Box::new(Type::TypeString(ctor_name_type_sym)),
            )),
            Box::new(args_rep),
        );
        ctor_reps.push(ctor_rep);
    }

    // Right-nested Sum of constructors
    Some(ctor_reps.into_iter().rev().reduce(|acc, ctor| {
        Type::App(
            Box::new(Type::App(Box::new(Type::Con(qi(sum_sym))), Box::new(ctor))),
            Box::new(acc),
        )
    }).unwrap())
}

/// Generate an instance name part from a Type (for anonymous instance registry entries).
/// Mirrors the logic in codegen's `type_expr_to_name` but works on `Type` instead of `TypeExpr`.
fn type_to_instance_name_part(ty: &Type) -> String {
    match ty {
        Type::Con(qi) => {
            let name = crate::interner::resolve(qi.name).unwrap_or_default().to_string();
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
            let s = crate::interner::resolve(*v).unwrap_or_default().to_string();
            s
        }
        _ => String::new(),
    }
}

fn extract_head_type_con(inst_types: &[Type]) -> Option<Symbol> {
    // Try all type args, not just the first — multi-param type classes like
    // `MonadState s m` may have the useful head in the last arg (e.g. `m = StateT ...`)
    for t in inst_types {
        if let Some(head) = extract_head_from_type_tc(t) {
            return Some(head);
        }
    }
    None
}

/// Extract head type constructors from ALL type args (for multi-param classes).
fn extract_all_head_type_cons(inst_types: &[Type]) -> Vec<Symbol> {
    inst_types.iter().filter_map(|t| extract_head_from_type_tc(t)).collect()
}

fn extract_head_from_type_tc(ty: &Type) -> Option<Symbol> {
    match ty {
        Type::Con(qi) => Some(qi.name),
        Type::App(f, _) => extract_head_from_type_tc(f),
        Type::Record(_, _) => Some(intern("Record")),
        Type::Fun(_, _) => Some(intern("Function")),
        _ => None,
    }
}

// ============================================================================
// Role inference and Coercible solver
// ============================================================================

/// Infer roles for a type's parameters based on how they're used in constructor fields.
/// For each type variable, compute the most restrictive role required by any field.
fn infer_roles_from_fields(
    type_vars: &[Symbol],
    constructor_fields: &[Vec<Type>],
    known_roles: &HashMap<Symbol, Vec<Role>>,
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
fn unapply_type_args(ty: &Type) -> (&Type, Vec<&Type>) {
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
fn mark_all_type_vars_nominal(
    ty: &Type,
    type_vars: &[Symbol],
    roles: &mut [Role],
    bound: &HashSet<Symbol>,
) {
    match ty {
        Type::Var(v) => {
            if !bound.contains(v) {
                if let Some(idx) = type_vars.iter().position(|tv| tv == v) {
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
fn update_roles_from_type(
    ty: &Type,
    type_vars: &[Symbol],
    roles: &mut [Role],
    known_roles: &HashMap<Symbol, Vec<Role>>,
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
            if let Some(idx) = type_vars.iter().position(|tv| tv == v) {
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
            if let Some(idx) = type_vars.iter().position(|tv| tv == v) {
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
            let bound: HashSet<Symbol> = vars.iter().map(|(v, _)| *v).collect();
            if !type_vars.iter().any(|tv| bound.contains(tv)) {
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
fn mark_constrained_vars_nominal_cst(
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
fn mark_all_cst_vars_nominal(
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
fn unapply_type(ty: &Type) -> (Type, Vec<&Type>) {
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
enum CoercibleResult {
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
fn has_unif_outside_row_tails(ty: &Type) -> bool {
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
fn solve_coercible(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<Symbol, Vec<Role>>,
    newtype_names: &HashSet<QualifiedIdent>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    ctor_details:  &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
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

fn solve_coercible_with_visited(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<Symbol, Vec<Role>>,
    newtype_names: &HashSet<QualifiedIdent>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
    depth: u32,
    visited: &mut HashSet<(String, String)>,
) -> CoercibleResult {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    solve_coercible_with_visited_impl(a, b, givens, type_roles, newtype_names, type_aliases, ctor_details, depth, visited)
    })
}

fn solve_coercible_with_visited_impl(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<Symbol, Vec<Role>>,
    newtype_names: &HashSet<QualifiedIdent>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
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

fn solve_coercible_inner(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<Symbol, Vec<Role>>,
    newtype_names: &HashSet<QualifiedIdent>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
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

fn solve_coercible_inner_impl(
    a: &Type,
    b: &Type,
    givens: &[(Type, Type)],
    type_roles: &HashMap<Symbol, Vec<Role>>,
    newtype_names: &HashSet<QualifiedIdent>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
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
    let is_newtype = |c: &QualifiedIdent| -> bool {
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
            let mut subst: HashMap<Symbol, Type> = HashMap::new();
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
fn solve_coercible_records(
    fields_a: &[(Symbol, Type)],
    tail_a: &Option<Box<Type>>,
    fields_b: &[(Symbol, Type)],
    tail_b: &Option<Box<Type>>,
    givens: &[(Type, Type)],
    type_roles: &HashMap<Symbol, Vec<Role>>,
    newtype_names: &HashSet<QualifiedIdent>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
    depth: u32,
    visited: &mut HashSet<(String, String)>,
) -> CoercibleResult {
    // Build label maps
    let map_a: HashMap<Symbol, &Type> = fields_a.iter().map(|(l, t)| (*l, t)).collect();
    let map_b: HashMap<Symbol, &Type> = fields_b.iter().map(|(l, t)| (*l, t)).collect();

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
fn unwrap_newtype(
    type_name: &QualifiedIdent,
    args: &[&Type],
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
) -> Option<Type> {
    // Find a constructor for this newtype.
    // Match by name only (ignoring module qualifier) to handle qualified vs
    // unqualified references to the same type (e.g., C.Node vs Node).
    for (_, (parent, type_vars, field_types)) in ctor_details {
        if parent.name == type_name.name && field_types.len() == 1 {
            // Single-field constructor = newtype
            let wrapped_ty = &field_types[0];
            let subst: HashMap<Symbol, Type> = type_vars
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
fn types_structurally_equal(a: &Type, b: &Type) -> bool {
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
fn types_match_up_to_vars(pattern: &Type, target: &Type, subst: &mut HashMap<Symbol, Type>) -> bool {
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

/// Walks through Forall → Constrained patterns, converting constraint args to internal Types.
/// Skips Partial and Warn (which are handled separately).
pub(crate) fn extract_type_signature_constraints(
    ty: &crate::ast::TypeExpr,
    type_ops: &HashMap<QualifiedIdent, QualifiedIdent>,
) -> Vec<(QualifiedIdent, Vec<Type>)> {
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
                let class_str = crate::interner::resolve(c.class.name).unwrap_or_default();
                let is_auto_satisfied = matches!(
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
                if ok {
                    result.push((c.class, args));
                } else if crate::interner::symbol_eq(c.class.name, "Fail") {
                    // Fail constraints should always be recorded even if args can't
                    // be converted (e.g. type-level Text/Quote from Prim.TypeError).
                    // The args aren't needed for error detection — any use of Fail
                    // means the constraint is deliberately unsatisfiable.
                    result.push((c.class, Vec::new()));
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
pub fn extract_return_type_constraints(
    ty: &crate::ast::TypeExpr,
    type_ops: &HashMap<QualifiedIdent, QualifiedIdent>,
) -> Vec<(QualifiedIdent, Vec<Type>)> {
    use crate::ast::TypeExpr;
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
pub fn count_return_type_arrow_depth(ty: &crate::ast::TypeExpr) -> usize {
    use crate::ast::TypeExpr;
    let ty = strip_outer_forall_and_constraints(ty);
    count_arrows(ty)
}

fn count_arrows(ty: &crate::ast::TypeExpr) -> usize {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Function { to, .. } => 1 + count_arrows(to),
        _ => 0,
    }
}

/// Strip outer Forall and Constrained wrappers.
fn strip_outer_forall_and_constraints(ty: &crate::ast::TypeExpr) -> &crate::ast::TypeExpr {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Forall { ty, .. } => strip_outer_forall_and_constraints(ty),
        TypeExpr::Constrained { ty, .. } => strip_outer_forall_and_constraints(ty),
        other => other,
    }
}

/// Walk past function arrows (rightward) to find the return type.
fn find_return_type_expr(ty: &crate::ast::TypeExpr) -> &crate::ast::TypeExpr {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Function { to, .. } => find_return_type_expr(to),
        other => other,
    }
}

/// Extract constraints from a type that is `Forall { Constrained { ... } }` or just `Constrained`.
fn extract_inner_forall_constraints_from_type_expr(
    ty: &crate::ast::TypeExpr,
    type_ops: &HashMap<QualifiedIdent, QualifiedIdent>,
) -> Vec<(QualifiedIdent, Vec<Type>)> {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Forall { ty, .. } => extract_inner_forall_constraints_from_type_expr(ty, type_ops),
        TypeExpr::Constrained { constraints, .. } => {
            let mut result = Vec::new();
            for c in constraints {
                let class_str = crate::interner::resolve(c.class.name).unwrap_or_default();
                let is_auto_satisfied = matches!(
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
pub fn has_partial_constraint(ty: &crate::ast::TypeExpr) -> bool {
    match ty {
        crate::ast::TypeExpr::Constrained { constraints, .. } => constraints
            .iter()
            .any(|c| crate::interner::resolve(c.class.name).unwrap_or_default() == "Partial"),
        crate::ast::TypeExpr::Forall { ty, .. } => has_partial_constraint(ty),
        _ => false,
    }
}

/// Check if a function type's parameter has a Partial constraint.
/// E.g. `(Partial => a) -> a` or `forall a. (Partial => a) -> a` returns true.
/// Check if a CST TypeExpr has a Partial constraint (for populating partial_value_names).
fn has_partial_constraint_cst(ty: &crate::cst::TypeExpr) -> bool {
    use crate::cst::TypeExpr;
    match ty {
        TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                let class_str = crate::interner::resolve(c.class.name).unwrap_or_default();
                if class_str == "Partial" {
                    return true;
                }
            }
            has_partial_constraint_cst(ty)
        }
        TypeExpr::Forall { ty, .. } => has_partial_constraint_cst(ty),
        _ => false,
    }
}

/// Used to detect functions that discharge the Partial constraint (like unsafePartial).
fn has_partial_in_function_param(ty: &crate::ast::TypeExpr) -> bool {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Forall { ty, .. } => has_partial_in_function_param(ty),
        TypeExpr::Constrained { ty, .. } => has_partial_in_function_param(ty),
        TypeExpr::Function { from, .. } => has_partial_constraint(from),
        _ => false,
    }
}

/// Check if a type expression contains a wildcard `_` anywhere.
fn find_wildcard_span(ty: &crate::ast::TypeExpr) -> Option<crate::span::Span> {
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
fn is_direct_var_ref(expr: &crate::ast::Expr, names: &HashSet<Symbol>) -> bool {
    use crate::ast::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => names.contains(&name.name),
        Expr::TypeAnnotation { expr, .. } => is_direct_var_ref(expr, names),
        _ => false,
    }
}

/// Extract the "application head" of an expression — the leftmost function in an application chain.
/// Returns the unqualified variable name if the head is a simple Var, None otherwise.
/// Used for instance method cycle detection: only the head of the application matters,
/// not arguments (which may dispatch to different typeclass instances).
fn expr_app_head_name(expr: &crate::ast::Expr) -> Option<Symbol> {
    use crate::ast::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => Some(name.name),
        Expr::App { func, .. } => expr_app_head_name(func),
        Expr::TypeAnnotation { expr, .. } => expr_app_head_name(expr),
        _ => None,
    }
}

/// Try to compute the nub of a row type (remove duplicate labels, keeping the first occurrence).
/// Returns `Some(nubbed_row)` if the row can be flattened and nubbed, `None` if the row
/// has unsolved parts (type variables, unif vars) that prevent nubbing.
fn try_nub_row(ty: &Type) -> Option<Type> {
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
    let nubbed_fields: Vec<(Symbol, Type)> = fields
        .into_iter()
        .filter(|(label, _)| seen.insert(*label))
        .collect();

    Some(Type::Record(nubbed_fields, None))
}

/// Try to compute the union of two row types (merge fields from left and right).
/// Returns `Some(merged_row)` if both rows can be flattened, `None` if they have unsolved parts.
fn try_union_rows(left: &Type, right: &Type) -> Option<Type> {
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
fn flatten_row(ty: &Type) -> (Vec<(Symbol, Type)>, Option<Box<Type>>) {
    match ty {
        Type::Record(fields, tail) => {
            let mut all_fields: Vec<(Symbol, Type)> = fields.clone();
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
fn check_class_param_kind_consistency(
    span: crate::span::Span,
    class_name: QualifiedIdent,
    constraint_type: &Type,
    app_args: &[Type],
    saved_type_kinds: &HashMap<QualifiedIdent, Type>,
    saved_class_kinds: &HashMap<QualifiedIdent, Type>,
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
        ks.register_type(name.name, remapped);
    }
    for (name, kind_val) in saved_class_kinds {
        let remapped = kind::remap_unif_vars(kind_val, &mut old_to_new, &mut ks);
        ks.class_kinds.insert(name.name, remapped);
    }

    // Look up the class kind and instantiate it (replacing Forall vars with fresh unif vars).
    // This ensures both occurrences of `ix` in `forall ix. (ix -> ix -> ...) -> Constraint`
    // map to the SAME unif var, creating the kind equality constraint.
    let class_kind = match ks.lookup_class_kind_fresh(class_name.name) {
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
fn kind_has_shared_type_vars(ty: &Type) -> bool {
    let mut seen = std::collections::HashSet::new();
    kind_collect_type_vars_shared(ty, &mut seen)
}

fn kind_collect_type_vars_shared(ty: &Type, seen: &mut std::collections::HashSet<Symbol>) -> bool {
    match ty {
        Type::Var(name) => !seen.insert(*name), // Returns true if already seen (duplicate)
        Type::Unif(id) => {
            // Also check Unif vars (for remapped kinds)
            let fake_sym = crate::interner::intern(&format!("__unif_{}", id.0));
            !seen.insert(fake_sym)
        }
        Type::Fun(a, b) | Type::App(a, b) => {
            kind_collect_type_vars_shared(a, seen) || kind_collect_type_vars_shared(b, seen)
        }
        Type::Forall(_, body) => kind_collect_type_vars_shared(body, seen),
        _ => false,
    }
}

/// Check if a type expression has any type class constraint (at the top level, under forall/parens).
fn has_any_constraint(ty: &crate::ast::TypeExpr) -> Option<crate::span::Span> {
    use crate::ast::TypeExpr;
    match ty {
        TypeExpr::Constrained { span, .. } => Some(*span),
        TypeExpr::Forall { ty, .. } => has_any_constraint(ty),
        _ => None,
    }
}

fn is_compare(class_name: &QualifiedIdent) -> bool {
    class_name.name == intern("Compare")
}

/// Resolve a type class constraint to a DictExpr for codegen.
/// Returns Some(DictExpr) if the constraint can be resolved to a concrete instance.
fn resolve_dict_expr_from_registry(
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

fn resolve_dict_expr_from_registry_inner(
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
    if class_str == "IsSymbol" {
        if let Some(Type::TypeString(sym)) = concrete_args.first() {
            let label = crate::interner::resolve(*sym).unwrap_or_default().to_string();
            return Some(DictExpr::InlineIsSymbol(label));
        }
        return None;
    }

    // Handle Reflectable constraints — generate inline dictionaries from type-level literals.
    if class_str == "Reflectable" {
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

    match class_str.as_str() {
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

    let (effective_args, head_opt) = if let Some(ref expanded) = expanded_concrete_args {
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
        for (inst_idx_dbg, (inst_types, inst_constraints, matched_inst_name)) in known.iter().enumerate() {
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
            let mut subst: HashMap<Symbol, Type> = HashMap::new();
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
                if matches!(c_class_str.as_str(),
                    "Partial" | "Coercible" | "Nub" | "Union" | "Lacks"
                    | "Warn" | "Fail" | "CompareSymbol" | "Compare" | "Add" | "Mul"
                    | "ToString" | "Reflectable" | "Reifiable"
                ) {
                    continue;
                }

                // Handle Row.Cons specially: compute row tail from row decomposition.
                // Row.Cons key focus rowTail row means row = { key: focus | rowTail }
                // We need to bind rowTail so downstream constraints can use it.
                if c_class_str == "Cons" && c_args.len() == 4 {
                    let key_ty = apply_var_subst(&subst, &c_args[0]);
                    let row_ty = apply_var_subst(&subst, &c_args[3]);
                    if let Type::TypeString(key_sym) = &key_ty {
                        if let Type::Record(fields, tail) = &row_ty {
                            let key_str = crate::interner::resolve(*key_sym).unwrap_or_default();
                            // Compute rowTail = row \ key
                            let tail_fields: Vec<_> = fields.iter()
                                .filter(|(name, _)| {
                                    let n = crate::interner::resolve(*name).unwrap_or_default();
                                    n != key_str
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
                                    crate::interner::resolve(*name).unwrap_or_default() == key_str
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
                if c_class_str == "RowToList" {
                    // RowToList has args: [row, list]
                    if c_args.len() == 2 {
                        let row_ty = apply_var_subst(&subst, &c_args[0]);
                        if let Type::Record(fields, _) = &row_ty {
                            // Compute RowList from record fields (sorted alphabetically)
                            let mut sorted_fields = fields.clone();
                            sorted_fields.sort_by(|(a, _), (b, _)| {
                                let a_str = crate::interner::resolve(*a).unwrap_or_default();
                                let b_str = crate::interner::resolve(*b).unwrap_or_default();
                                a_str.cmp(&b_str)
                            });
                            let nil_sym = crate::interner::intern("Nil");
                            let cons_sym = crate::interner::intern("Cons");
                            let mut list_ty = Type::Con(qi(nil_sym));
                            for (label, field_ty) in sorted_fields.iter().rev() {
                                let label_str = crate::interner::resolve(*label).unwrap_or_default().to_string();
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
                if c_class_str == "IsSymbol" {
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
                if c_class_str == "Reflectable" {
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
fn types_equal_ignoring_row_tails(a: &Type, b: &Type) -> bool {
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

/// Check if a type contains any free type variables (Type::Var).
fn has_free_type_vars(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Unif(_) => false,
        Type::Con(_) => false,
        Type::TypeString(_) => false,
        Type::TypeInt(_) => false,
        Type::App(a, b) => has_free_type_vars(a) || has_free_type_vars(b),
        Type::Fun(a, b) => has_free_type_vars(a) || has_free_type_vars(b),
        Type::Forall(_, body) => has_free_type_vars(body),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| has_free_type_vars(t))
                || tail.as_ref().map_or(false, |t| has_free_type_vars(t))
        }
    }
}

/// Check if a type contains any unification variables (Type::Unif).
fn has_unif_vars(ty: &Type) -> bool {
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

/// Extract the head type constructor from a type, stripping App wrappers.
/// E.g., App(App(Con(ST), Var(r)), Var(a)) → Con(ST)
/// Unif(x) → Unif(x)
/// Fun(a, b) → Fun(a, b) (function type, treated as concrete head)
fn extract_type_head(ty: &Type) -> &Type {
    match ty {
        Type::App(f, _) => extract_type_head(f),
        _ => ty,
    }
}
