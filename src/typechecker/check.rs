use std::collections::{HashMap, HashSet};

use crate::ast::span::Span;
use crate::cst::{Associativity, Binder, DataMembers, Decl, Export, Import, ImportList, KindSigSource, Module, Spanned, TypeExpr};
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::{
    check_exhaustiveness, extract_type_con, is_unconditional_for_exhaustiveness, InferCtx,
};
use crate::typechecker::types::{Scheme, Type};

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
fn collect_type_refs(ty: &crate::cst::TypeExpr, refs: &mut HashSet<Symbol>) {
    match ty {
        crate::cst::TypeExpr::Constructor { name, .. } => {
            // Only track unqualified references as local alias dependencies.
            // Qualified refs (e.g. P.Number) point to external modules, not local aliases.
            if name.module.is_none() {
                refs.insert(name.name);
            }
        }
        crate::cst::TypeExpr::App {
            constructor, arg, ..
        } => {
            collect_type_refs(constructor, refs);
            collect_type_refs(arg, refs);
        }
        crate::cst::TypeExpr::Function { from, to, .. } => {
            collect_type_refs(from, refs);
            collect_type_refs(to, refs);
        }
        crate::cst::TypeExpr::Forall { ty, .. } => {
            collect_type_refs(ty, refs);
        }
        crate::cst::TypeExpr::Constrained {
            constraints, ty, ..
        } => {
            for constraint in constraints {
                for arg in &constraint.args {
                    collect_type_refs(arg, refs);
                }
            }
            collect_type_refs(ty, refs);
        }
        crate::cst::TypeExpr::Parens { ty, .. } => {
            collect_type_refs(ty, refs);
        }
        crate::cst::TypeExpr::Kinded { ty, kind, .. } => {
            collect_type_refs(ty, refs);
            collect_type_refs(kind, refs);
        }
        crate::cst::TypeExpr::TypeOp { left, right, .. } => {
            collect_type_refs(left, refs);
            collect_type_refs(right, refs);
        }
        crate::cst::TypeExpr::Record { fields, .. } => {
            for field in fields {
                collect_type_refs(&field.ty, refs);
            }
        }
        crate::cst::TypeExpr::Row { fields, tail, .. } => {
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
fn collect_type_expr_vars(ty: &TypeExpr, bound: &HashSet<Symbol>, errors: &mut Vec<TypeError>) {
    match ty {
        TypeExpr::Var { span, name } => {
            if !bound.contains(&name.value) {
                errors.push(TypeError::UndefinedTypeVariable {
                    span: *span,
                    name: name.value,
                });
            }
        }
        TypeExpr::App { constructor, arg, .. } => {
            collect_type_expr_vars(constructor, bound, errors);
            collect_type_expr_vars(arg, bound, errors);
        }
        TypeExpr::Function { from, to, .. } => {
            collect_type_expr_vars(from, bound, errors);
            collect_type_expr_vars(to, bound, errors);
        }
        TypeExpr::Forall { vars, ty, .. } => {
            let mut inner_bound = bound.clone();
            for v in vars {
                inner_bound.insert(v.value);
            }
            collect_type_expr_vars(ty, &inner_bound, errors);
        }
        TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for arg in &c.args {
                    collect_type_expr_vars(arg, bound, errors);
                }
            }
            collect_type_expr_vars(ty, bound, errors);
        }
        TypeExpr::Parens { ty, .. } => {
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
        TypeExpr::TypeOp { left, right, .. } => {
            collect_type_expr_vars(left, bound, errors);
            collect_type_expr_vars(right, bound, errors);
        }
        _ => {} // Constructor, Wildcard, Hole, StringLiteral, IntLiteral
    }
}

/// Check if a CST TypeExpr contains `forall` or wildcards (invalid in constraint args).
/// Returns the span of the first invalid node found.
fn has_forall_or_wildcard(ty: &TypeExpr) -> Option<crate::ast::span::Span> {
    match ty {
        TypeExpr::Forall { span, .. } => Some(*span),
        TypeExpr::Wildcard { span, .. } => Some(*span),
        TypeExpr::App { constructor, arg, .. } => {
            has_forall_or_wildcard(constructor).or_else(|| has_forall_or_wildcard(arg))
        }
        TypeExpr::Parens { ty, .. } => has_forall_or_wildcard(ty),
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
        TypeExpr::App { constructor, arg, .. } => {
            has_invalid_instance_head_type_expr(constructor)
                || has_invalid_instance_head_type_expr(arg)
        }
        TypeExpr::Parens { ty, .. } => has_invalid_instance_head_type_expr(ty),
        _ => false,
    }
}

/// Walk a CST TypeExpr and validate that all constraint class names are known.
/// Emits UnknownClass for unqualified constraints referencing undefined classes.
fn check_constraint_class_names(
    ty: &TypeExpr,
    known_classes: &HashSet<Symbol>,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        TypeExpr::Constrained { constraints, ty, .. } => {
            for constraint in constraints {
                if constraint.class.module.is_none()
                    && !known_classes.contains(&constraint.class.name)
                {
                    errors.push(TypeError::UnknownClass {
                        span: constraint.span,
                        name: constraint.class.name,
                    });
                }
            }
            check_constraint_class_names(ty, known_classes, errors);
        }
        TypeExpr::Forall { ty, .. } | TypeExpr::Parens { ty, .. } => {
            check_constraint_class_names(ty, known_classes, errors);
        }
        TypeExpr::Function { from, to, .. } => {
            check_constraint_class_names(from, known_classes, errors);
            check_constraint_class_names(to, known_classes, errors);
        }
        _ => {}
    }
}

/// Check if a type used in an instance head is a type synonym that expands to
/// a non-nominal type (record, function). Synonyms expanding to data types are fine.
fn is_non_nominal_instance_head(ty: &Type, type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>) -> bool {
    if !has_synonym_head(ty, type_aliases) {
        return false;
    }
    let expanded = expand_type_aliases_limited(ty, type_aliases, 0);
    matches!(expanded, Type::Record(..) | Type::Fun(..))
}

/// Check if a type is non-nominal for derive instance heads.
/// Derive requires a data/newtype constructor — records, functions, and
/// type synonyms expanding to them are all invalid.
fn is_non_nominal_for_derive(ty: &Type, type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>) -> bool {
    if matches!(ty, Type::Record(..) | Type::Fun(..)) {
        return true;
    }
    is_non_nominal_instance_head(ty, type_aliases)
}

/// Check if the outermost constructor of a type is a known type synonym.
fn has_synonym_head(ty: &Type, type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>) -> bool {
    match ty {
        Type::Con(name) => type_aliases.contains_key(name),
        Type::App(f, _) => has_synonym_head(f, type_aliases),
        _ => false,
    }
}

/// Expand type aliases with a depth limit to prevent stack overflow.
fn expand_type_aliases_limited(ty: &Type, type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>, depth: u32) -> Type {
    if depth > 50 || type_aliases.is_empty() {
        return ty.clone();
    }
    let expanded = match ty {
        Type::App(f, a) => {
            let f2 = expand_type_aliases_limited(f, type_aliases, depth + 1);
            let a2 = expand_type_aliases_limited(a, type_aliases, depth + 1);
            Type::app(f2, a2)
        }
        Type::Fun(a, b) => {
            Type::fun(
                expand_type_aliases_limited(a, type_aliases, depth + 1),
                expand_type_aliases_limited(b, type_aliases, depth + 1),
            )
        }
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| (*l, expand_type_aliases_limited(t, type_aliases, depth + 1)))
                .collect();
            let tail = tail
                .as_ref()
                .map(|t| Box::new(expand_type_aliases_limited(t, type_aliases, depth + 1)));
            Type::Record(fields, tail)
        }
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(expand_type_aliases_limited(body, type_aliases, depth + 1)))
        }
        _ => ty.clone(),
    };
    let mut args = Vec::new();
    let mut head = &expanded;
    loop {
        match head {
            Type::App(f, a) => {
                args.push(a.as_ref().clone());
                head = f.as_ref();
            }
            _ => break,
        }
    }
    if let Type::Con(name) = head {
        if let Some((params, body)) = type_aliases.get(name) {
            args.reverse();
            if args.len() == params.len() {
                let subst: HashMap<Symbol, Type> =
                    params.iter().copied().zip(args.into_iter()).collect();
                return expand_type_aliases_limited(&apply_var_subst(&subst, body), type_aliases, depth + 1);
            }
        }
    }
    expanded
}

/// Check a type for partially applied type synonyms after expanding all aliases.
/// After expansion, any remaining synonym reference with too few args is partial.
fn check_type_for_partial_synonyms(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    span: Span,
    errors: &mut Vec<TypeError>,
) {
    let expanded = expand_type_aliases_limited(ty, type_aliases, 0);
    check_partially_applied_synonyms_inner(&expanded, type_aliases, span, errors);
}

/// Walk a (post-expansion) type looking for partially applied synonyms.
fn check_partially_applied_synonyms_inner(
    ty: &Type,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    span: Span,
    errors: &mut Vec<TypeError>,
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
                if let Some((params, _)) = type_aliases.get(name) {
                    if args.len() < params.len() {
                        errors.push(TypeError::PartiallyAppliedSynonym { span, name: *name });
                        return;
                    } else if args.len() > params.len() {
                        errors.push(TypeError::KindsDoNotUnify {
                            span,
                            name: *name,
                            expected: params.len(),
                            found: args.len(),
                        });
                        return;
                    }
                }
            } else {
                check_partially_applied_synonyms_inner(head, type_aliases, span, errors);
            }
            // Recurse into each argument
            for arg in args {
                check_partially_applied_synonyms_inner(arg, type_aliases, span, errors);
            }
        }
        Type::Con(name) => {
            if let Some((params, _)) = type_aliases.get(name) {
                if !params.is_empty() {
                    errors.push(TypeError::PartiallyAppliedSynonym { span, name: *name });
                }
            }
        }
        Type::Fun(a, b) => {
            check_partially_applied_synonyms_inner(a, type_aliases, span, errors);
            check_partially_applied_synonyms_inner(b, type_aliases, span, errors);
        }
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                check_partially_applied_synonyms_inner(t, type_aliases, span, errors);
            }
            if let Some(t) = tail {
                check_partially_applied_synonyms_inner(t, type_aliases, span, errors);
            }
        }
        Type::Forall(_, body) => {
            check_partially_applied_synonyms_inner(body, type_aliases, span, errors);
        }
        _ => {}
    }
}

/// Check a type expression for type-level operator fixity issues.
/// Detects non-associative operators used in chains and mixed associativity.
fn check_type_op_fixity(
    ty: &TypeExpr,
    type_fixities: &HashMap<Symbol, (Associativity, u8)>,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        TypeExpr::TypeOp { left, op, right, .. } => {
            check_type_op_fixity(left, type_fixities, errors);
            check_type_op_fixity(right, type_fixities, errors);
            // Check if right is also a TypeOp at the same precedence
            if let TypeExpr::TypeOp { op: right_op, .. } = right.as_ref() {
                let (assoc_l, prec_l) = type_fixities
                    .get(&op.value.name)
                    .copied()
                    .unwrap_or((Associativity::Left, 9));
                let (assoc_r, prec_r) = type_fixities
                    .get(&right_op.value.name)
                    .copied()
                    .unwrap_or((Associativity::Left, 9));
                if prec_l == prec_r {
                    if assoc_l != assoc_r {
                        errors.push(TypeError::MixedAssociativityError {
                            span: op.span,
                        });
                    } else if assoc_l == Associativity::None {
                        errors.push(TypeError::NonAssociativeError {
                            span: op.span,
                            op: op.value.name,
                        });
                    }
                }
            }
        }
        TypeExpr::App { constructor, arg, .. } => {
            check_type_op_fixity(constructor, type_fixities, errors);
            check_type_op_fixity(arg, type_fixities, errors);
        }
        TypeExpr::Function { from, to, .. } => {
            check_type_op_fixity(from, type_fixities, errors);
            check_type_op_fixity(to, type_fixities, errors);
        }
        TypeExpr::Forall { ty, .. } => check_type_op_fixity(ty, type_fixities, errors),
        TypeExpr::Constrained { ty, .. } => check_type_op_fixity(ty, type_fixities, errors),
        TypeExpr::Parens { ty, .. } => check_type_op_fixity(ty, type_fixities, errors),
        TypeExpr::Kinded { ty, kind, .. } => {
            check_type_op_fixity(ty, type_fixities, errors);
            check_type_op_fixity(kind, type_fixities, errors);
        }
        TypeExpr::Record { fields, .. } => {
            for field in fields {
                check_type_op_fixity(&field.ty, type_fixities, errors);
            }
        }
        TypeExpr::Row { fields, tail, .. } => {
            for field in fields {
                check_type_op_fixity(&field.ty, type_fixities, errors);
            }
            if let Some(tail) = tail {
                check_type_op_fixity(tail, type_fixities, errors);
            }
        }
        _ => {} // Var, Constructor, Wildcard, Hole, StringLiteral, IntLiteral
    }
}

/// Detect cycles in type synonym definitions.
fn check_type_synonym_cycles(
    type_aliases: &HashMap<Symbol, (Span, &crate::cst::TypeExpr)>,
    errors: &mut Vec<TypeError>,
) {
    let alias_names: HashSet<Symbol> = type_aliases.keys().copied().collect();

    // Build adjacency: alias → set of other aliases it references
    let mut deps: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for (&name, (_, ty)) in type_aliases {
        let mut refs = HashSet::new();
        collect_type_refs(ty, &mut refs);
        // Only keep references to other aliases
        refs.retain(|r| alias_names.contains(r));
        deps.insert(name, refs);
    }

    // DFS cycle detection
    let mut visited: HashSet<Symbol> = HashSet::new();
    let mut on_stack: HashSet<Symbol> = HashSet::new();

    for &name in type_aliases.keys() {
        if !visited.contains(&name) {
            let mut path = Vec::new();
            if let Some(cycle) = dfs_find_cycle(name, &deps, &mut visited, &mut on_stack, &mut path)
            {
                let (span, _) = type_aliases[&name];
                let cycle_spans: Vec<Span> = cycle
                    .iter()
                    .filter_map(|n| type_aliases.get(n).map(|(s, _)| *s))
                    .collect();
                errors.push(TypeError::CycleInTypeSynonym {
                    name,
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
    match binder {
        Binder::Var { name, .. } => {
            seen.entry(name.value).or_default().push(name.span);
        }
        Binder::Constructor { args, .. } => {
            for arg in args {
                collect_binder_vars(arg, seen);
            }
        }
        Binder::Parens { binder, .. } => collect_binder_vars(binder, seen),
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
        Binder::Op { left, right, .. } => {
            collect_binder_vars(left, seen);
            collect_binder_vars(right, seen);
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

/// Exported information from a type-checked module, available for import by other modules.
#[derive(Debug, Clone, Default)]
pub struct ModuleExports {
    /// Value/constructor/method schemes
    pub values: HashMap<Symbol, Scheme>,
    /// Class method info: method_name → (class_name, class_type_vars)
    pub class_methods: HashMap<Symbol, (Symbol, Vec<Symbol>)>,
    /// Data type → constructor names
    pub data_constructors: HashMap<Symbol, Vec<Symbol>>,
    /// Constructor details: ctor_name → (parent_type, type_vars, field_types)
    pub ctor_details: HashMap<Symbol, (Symbol, Vec<Symbol>, Vec<Type>)>,
    /// Class instances: class_name → [(types, constraints)]
    pub instances: HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    /// Type-level operators: op → target type name
    pub type_operators: HashMap<Symbol, Symbol>,
    /// Value-level operator fixities: operator → (associativity, precedence)
    pub value_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// Value-level operators that alias functions (not constructors)
    pub function_op_aliases: HashSet<Symbol>,
    /// Class methods whose declared type has extra constraints (e.g. `Applicative m =>`).
    /// Used for CycleInDeclaration detection across module boundaries.
    pub constrained_class_methods: HashSet<Symbol>,
    /// Type aliases: alias_name → (params, body_type)
    pub type_aliases: HashMap<Symbol, (Vec<Symbol>, Type)>,
    /// Class definitions: class_name → param_count (for arity checking and orphan detection)
    pub class_param_counts: HashMap<Symbol, usize>,
    /// Origin tracking: name → original defining module symbol.
    /// Used to distinguish re-exports of the same definition from
    /// independently defined names that happen to have the same type.
    pub value_origins: HashMap<Symbol, Symbol>,
    pub type_origins: HashMap<Symbol, Symbol>,
    pub class_origins: HashMap<Symbol, Symbol>,
}

/// Registry of compiled modules, used to resolve imports.
///
/// Supports layering: a child registry can be created with `with_base()`,
/// which shares an immutable base via `Arc` (zero-copy) and stores new
/// modules in a local overlay. Lookups check the overlay first, then the base.
#[derive(Debug, Clone, Default)]
pub struct ModuleRegistry {
    modules: HashMap<Vec<Symbol>, ModuleExports>,
    base: Option<std::sync::Arc<ModuleRegistry>>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a child registry layered on top of a shared base.
    /// New modules are stored locally; lookups fall through to the base.
    pub fn with_base(base: std::sync::Arc<ModuleRegistry>) -> Self {
        Self {
            modules: HashMap::new(),
            base: Some(base),
        }
    }

    pub fn register(&mut self, name: &[Symbol], exports: ModuleExports) {
        self.modules.insert(name.to_vec(), exports);
    }

    pub fn lookup(&self, name: &[Symbol]) -> Option<&ModuleExports> {
        self.modules
            .get(name)
            .or_else(|| self.base.as_ref().and_then(|b| b.lookup(name)))
    }

    pub fn contains(&self, name: &[Symbol]) -> bool {
        self.modules.contains_key(name)
            || self.base.as_ref().map_or(false, |b| b.contains(name))
    }
}

/// Result of typechecking a module: partial type map + accumulated errors + exports.
pub struct CheckResult {
    pub types: HashMap<Symbol, Type>,
    pub errors: Vec<TypeError>,
    pub exports: ModuleExports,
}

// Build the exports for the built-in Prim module.
// Prim provides core types (Int, Number, String, Char, Boolean, Array, Function, Record)
// and is implicitly imported unqualified in every module.
thread_local! {
    static PRIM_EXPORTS_CACHE: std::cell::RefCell<Option<ModuleExports>> = const { std::cell::RefCell::new(None) };
}

fn prim_exports() -> ModuleExports {
    PRIM_EXPORTS_CACHE.with(|cache| {
        let mut borrow = cache.borrow_mut();
        if let Some(ref cached) = *borrow {
            return cached.clone();
        }
        let exports = prim_exports_inner();
        *borrow = Some(exports.clone());
        exports
    })
}

fn prim_exports_inner() -> ModuleExports {
    use crate::interner::intern;
    let mut exports = ModuleExports::default();

    // Register Prim types as known types (empty constructor lists since they're opaque).
    // This makes them findable by the import system (import_item looks up data_constructors).
    // Core value types
    for name in &[
        "Int", "Number", "String", "Char", "Boolean", "Array", "Function", "Record", "->",
    ] {
        exports.data_constructors.insert(intern(name), Vec::new());
    }

    // Kind types: Type, Constraint, Symbol, Row
    for name in &["Type", "Constraint", "Symbol", "Row"] {
        exports.data_constructors.insert(intern(name), Vec::new());
    }

    // class Partial
    exports.instances.insert(intern("Partial"), Vec::new());

    exports
}

/// Check if a CST ModuleName matches "Prim".
fn is_prim_module(module_name: &crate::cst::ModuleName) -> bool {
    module_name.parts.len() == 1
        && crate::interner::resolve(module_name.parts[0]).unwrap_or_default() == "Prim"
}

/// Check if a CST ModuleName is a Prim submodule (e.g. Prim.Coerce, Prim.Row).
fn is_prim_submodule(module_name: &crate::cst::ModuleName) -> bool {
    module_name.parts.len() >= 2
        && crate::interner::resolve(module_name.parts[0]).unwrap_or_default() == "Prim"
}

/// Build exports for Prim submodules (Prim.Coerce, Prim.Row, Prim.RowList, etc.).
/// These are built-in modules with compiler-magic classes and types.
fn prim_submodule_exports(module_name: &crate::cst::ModuleName) -> ModuleExports {
    use crate::interner::intern;
    let mut exports = ModuleExports::default();

    let sub = if module_name.parts.len() >= 2 {
        crate::interner::resolve(module_name.parts[1]).unwrap_or_default()
    } else {
        return exports;
    };

    match sub.as_str() {
        "Boolean" => {
            // Type-level booleans: True, False
            exports.data_constructors.insert(intern("True"), Vec::new());
            exports.data_constructors.insert(intern("False"), Vec::new());
        }
        "Coerce" => {
            // class Coercible (no user-visible methods)
            exports.instances.insert(intern("Coercible"), Vec::new());
        }
        "Int" => {
            // Compiler-solved type classes for type-level Ints
            // class Add, class Compare, class Mul, class ToString
            for class in &["Add", "Compare", "Mul", "ToString"] {
                exports.instances.insert(intern(class), Vec::new());
            }
        }
        "Ordering" => {
            // type Ordering with constructors LT, EQ, GT
            exports.data_constructors.insert(intern("Ordering"), vec![intern("LT"), intern("EQ"), intern("GT")]);
            exports.data_constructors.insert(intern("LT"), Vec::new());
            exports.data_constructors.insert(intern("EQ"), Vec::new());
            exports.data_constructors.insert(intern("GT"), Vec::new());
        }
        "Row" => {
            // classes: Lacks, Cons, Nub, Union
            for class in &["Lacks", "Cons", "Nub", "Union"] {
                exports.instances.insert(intern(class), Vec::new());
            }
        }
        "RowList" => {
            // type RowList with constructors Cons, Nil; class RowToList
            exports.data_constructors.insert(intern("RowList"), vec![intern("Cons"), intern("Nil")]);
            exports.data_constructors.insert(intern("Cons"), Vec::new());
            exports.data_constructors.insert(intern("Nil"), Vec::new());
            exports.instances.insert(intern("RowToList"), Vec::new());
        }
        "Symbol" => {
            // classes: Append, Compare, Cons
            for class in &["Append", "Compare", "Cons"] {
                exports.instances.insert(intern(class), Vec::new());
            }
        }
        "TypeError" => {
            // classes: Fail, Warn; type constructors: Text, Beside, Above, Quote, QuoteLabel
            for class in &["Fail", "Warn"] {
                exports.instances.insert(intern(class), Vec::new());
            }
            for ty in &["Doc", "Text", "Beside", "Above", "Quote", "QuoteLabel"] {
                exports.data_constructors.insert(intern(ty), Vec::new());
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
            Type::Var(v) => { vars.insert(*v); }
            Type::Fun(a, b) => { collect_vars(a, vars); collect_vars(b, vars); }
            Type::App(f, a) => { collect_vars(f, vars); collect_vars(a, vars); }
            Type::Forall(bound, body) => {
                let mut inner_vars = HashSet::new();
                collect_vars(body, &mut inner_vars);
                for v in &inner_vars {
                    if !bound.contains(v) {
                        vars.insert(*v);
                    }
                }
            }
            Type::Record(fields, tail) => {
                for (_, t) in fields { collect_vars(t, vars); }
                if let Some(t) = tail { collect_vars(t, vars); }
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
                        if *name == function_sym {
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
            Type::Forall(vars, body) => Type::Forall(
                vars,
                Box::new(normalize_function(*body, function_sym)),
            ),
            Type::Record(fields, tail) => {
                let fields = fields.into_iter()
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
            let subst: HashMap<Symbol, Type> = vars.iter()
                .map(|&v| (v, Type::Unif(ctx.state.fresh_var())))
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
        let subst: HashMap<Symbol, Type> = free_vars.into_iter()
            .map(|v| (v, Type::Unif(ctx.state.fresh_var())))
            .collect();
        apply_var_subst(&subst, &ty)
    }
}

/// Extract the head type constructor name from a CST TypeExpr,
/// peeling through type applications and parentheses.
/// E.g. `Maybe Int` → Some("Maybe"), `(Foo a b)` → Some("Foo")
fn extract_head_constructor(ty: &crate::cst::TypeExpr) -> Option<Symbol> {
    match ty {
        crate::cst::TypeExpr::Constructor { name, .. } => Some(name.name),
        crate::cst::TypeExpr::App { constructor, .. } => extract_head_constructor(constructor),
        crate::cst::TypeExpr::Parens { ty, .. } => extract_head_constructor(ty),
        _ => None,
    }
}

// ===== Binding group analysis =====
// Collects value references from CST expressions to build a dependency graph
// for top-level declarations. This enables correct processing order so that
// forward references and mutual recursion are handled properly.

/// Collect references to top-level value names from an expression.
fn collect_expr_refs(expr: &crate::cst::Expr, top: &HashSet<Symbol>, refs: &mut HashSet<Symbol>) {
    use crate::cst::Expr;
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
        Expr::Op { left, op, right, .. } => {
            collect_expr_refs(left, top, refs);
            if op.value.module.is_none() && top.contains(&op.value.name) {
                refs.insert(op.value.name);
            }
            collect_expr_refs(right, top, refs);
        }
        Expr::OpParens { op, .. } => {
            if op.value.module.is_none() && top.contains(&op.value.name) {
                refs.insert(op.value.name);
            }
        }
        Expr::If { cond, then_expr, else_expr, .. } => {
            collect_expr_refs(cond, top, refs);
            collect_expr_refs(then_expr, top, refs);
            collect_expr_refs(else_expr, top, refs);
        }
        Expr::Case { exprs, alts, .. } => {
            for e in exprs { collect_expr_refs(e, top, refs); }
            for alt in alts {
                collect_guarded_refs(&alt.result, top, refs);
            }
        }
        Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let crate::cst::LetBinding::Value { expr, .. } = b {
                    collect_expr_refs(expr, top, refs);
                }
            }
            collect_expr_refs(body, top, refs);
        }
        Expr::Do { statements, .. } | Expr::Ado { statements, .. } => {
            for stmt in statements {
                match stmt {
                    crate::cst::DoStatement::Bind { expr, .. } => collect_expr_refs(expr, top, refs),
                    crate::cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let crate::cst::LetBinding::Value { expr, .. } = b {
                                collect_expr_refs(expr, top, refs);
                            }
                        }
                    }
                    crate::cst::DoStatement::Discard { expr, .. } => collect_expr_refs(expr, top, refs),
                }
            }
            if let Expr::Ado { result, .. } = expr {
                collect_expr_refs(result, top, refs);
            }
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value { collect_expr_refs(v, top, refs); }
            }
        }
        Expr::RecordAccess { expr, .. } => collect_expr_refs(expr, top, refs),
        Expr::RecordUpdate { expr, updates, .. } => {
            collect_expr_refs(expr, top, refs);
            for u in updates { collect_expr_refs(&u.value, top, refs); }
        }
        Expr::Parens { expr, .. } => collect_expr_refs(expr, top, refs),
        Expr::TypeAnnotation { expr, .. } => collect_expr_refs(expr, top, refs),
        Expr::Array { elements, .. } => {
            for e in elements { collect_expr_refs(e, top, refs); }
        }
        Expr::Negate { expr, .. } => collect_expr_refs(expr, top, refs),
        Expr::Literal { lit, .. } => {
            if let crate::cst::Literal::Array(elems) = lit {
                for e in elems { collect_expr_refs(e, top, refs); }
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
fn collect_guarded_refs(guarded: &crate::cst::GuardedExpr, top: &HashSet<Symbol>, refs: &mut HashSet<Symbol>) {
    match guarded {
        crate::cst::GuardedExpr::Unconditional(e) => collect_expr_refs(e, top, refs),
        crate::cst::GuardedExpr::Guarded(guards) => {
            for g in guards {
                for p in &g.patterns {
                    match p {
                        crate::cst::GuardPattern::Boolean(e) => collect_expr_refs(e, top, refs),
                        crate::cst::GuardPattern::Pattern(_, e) => collect_expr_refs(e, top, refs),
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
        if let Decl::Value { guarded, where_clause, .. } = decl {
            collect_guarded_refs(guarded, top, &mut refs);
            for wb in where_clause {
                if let crate::cst::LetBinding::Value { expr, .. } = wb {
                    collect_expr_refs(expr, top, &mut refs);
                }
            }
        }
    }
    refs
}

/// Compute strongly connected components using Tarjan's algorithm.
/// Returns SCCs in reverse topological order (leaves first).
fn tarjan_scc(
    nodes: &[Symbol],
    edges: &HashMap<Symbol, HashSet<Symbol>>,
) -> Vec<Vec<Symbol>> {
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
                        strongconnect(w, nodes, edges, idx_of, index_counter, stack, on_stack, index, lowlink, sccs);
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
                if w == v { break; }
            }
            sccs.push(scc);
        }
    }

    for i in 0..n {
        if index[i] == usize::MAX {
            strongconnect(i, nodes, edges, &idx_of, &mut index_counter, &mut stack, &mut on_stack, &mut index, &mut lowlink, &mut sccs);
        }
    }

    sccs
}

/// Typecheck an entire module, returning a map of top-level names to their types
/// and a list of any errors encountered. Checking continues past errors so that
/// partial results are available for tooling (e.g. IDE hover types).
pub fn check_module(module: &Module, registry: &ModuleRegistry) -> CheckResult {
    let mut ctx = InferCtx::new();
    ctx.module_mode = true;
    let mut env = Env::new();
    let mut signatures: HashMap<Symbol, (crate::ast::span::Span, Type)> = HashMap::new();
    let mut result_types: HashMap<Symbol, Type> = HashMap::new();
    let mut errors: Vec<TypeError> = Vec::new();

    // Track class info for instance checking
    // Each instance stores (type_args, constraints) where constraints are (class_name, constraint_type_args)
    let mut instances: HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>> = HashMap::new();

    // Track locally-defined instance heads for overlap checking
    let mut local_instance_heads: HashMap<Symbol, Vec<Vec<Type>>> = HashMap::new();

    // Track locally-defined names for export computation
    let mut local_values: HashMap<Symbol, Scheme> = HashMap::new();

    // Track names with Partial constraint (intentionally non-exhaustive)
    let mut partial_names: HashSet<Symbol> = HashSet::new();

    // Track class declaration spans for duplicate detection
    let mut seen_classes: HashMap<Symbol, Vec<Span>> = HashMap::new();

    // Track named instance spans for duplicate detection
    let mut seen_instance_names: HashMap<Symbol, Vec<Span>> = HashMap::new();

    // Track which type names are declared as newtypes (for derive validation)
    let mut newtype_names: HashSet<Symbol> = HashSet::new();

    // Track type alias definitions for cycle detection
    let mut type_alias_defs: HashMap<Symbol, (Span, &crate::cst::TypeExpr)> = HashMap::new();

    // Track class definitions for superclass cycle detection: name → (span, superclass class names)
    let mut class_defs: HashMap<Symbol, (Span, Vec<Symbol>)> = HashMap::new();

    // Track superclass constraints per class for instance validation:
    // class name → (class type var names, superclass constraints as (class_name, type_args))
    let mut class_superclasses: HashMap<Symbol, (Vec<Symbol>, Vec<(Symbol, Vec<Type>)>)> = HashMap::new();

    // Track class type parameter counts for instance arity validation.
    let mut class_param_counts: HashMap<Symbol, usize> = HashMap::new();

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
    let local_type_names: HashSet<Symbol> = module.decls.iter().filter_map(|d| match d {
        Decl::Data { name, .. } | Decl::Newtype { name, .. } | Decl::TypeAlias { name, .. } | Decl::ForeignData { name, .. } => Some(name.value),
        _ => None,
    }).collect();
    let local_class_names: HashSet<Symbol> = module.decls.iter().filter_map(|d| match d {
        Decl::Class { name, is_kind_sig, .. } if !*is_kind_sig => Some(name.value),
        _ => None,
    }).collect();

    // Track locally-registered instances for superclass validation: (span, class_name, inst_types)
    let mut registered_instances: Vec<(Span, Symbol, Vec<Type>)> = Vec::new();

    // Deferred instance method bodies: checked after Pass 1.5 so foreign imports and fixity are available.
    // Tuple: (method_name, span, binders, guarded, where_clause, expected_type)
    let mut deferred_instance_methods: Vec<(Symbol, Span, &[Binder], &crate::cst::GuardedExpr, &[crate::cst::LetBinding], Option<Type>)> = Vec::new();
    // Instance method groups: each entry is the list of method names for one instance.
    // Used for CycleInDeclaration detection among sibling methods.
    let mut instance_method_groups: Vec<Vec<Symbol>> = Vec::new();

    // Import Prim unqualified. Prim is implicitly available in all modules,
    // BUT if the module has an explicit `import Prim (...)` or `import Prim hiding (...)`,
    // skip the automatic full import and let process_imports handle the selective import.
    let has_explicit_prim_import = module.imports.iter().any(|imp| {
        is_prim_module(&imp.module) && imp.imports.is_some() && imp.qualified.is_none()
    });
    if !has_explicit_prim_import {
        let prim = prim_exports();
        import_all(&prim, &mut env, &mut ctx, &mut instances, None);
    }

    // Process imports: bring imported names into scope
    process_imports(
        module,
        registry,
        &mut env,
        &mut ctx,
        &mut instances,
        &mut errors,
    );

    // Pre-populate class param counts from imported class methods and class definitions.
    for (_method, (class_name, tvs)) in &ctx.class_methods {
        class_param_counts.entry(*class_name).or_insert(tvs.len());
    }
    // Also populate from explicitly exported class_param_counts (catches classes without methods)
    for import_decl in &module.imports {
        let prim_sub;
        let module_exports = if is_prim_module(&import_decl.module) {
            Some(&prim_exports())
        } else if is_prim_submodule(&import_decl.module) {
            prim_sub = prim_submodule_exports(&import_decl.module);
            Some(&prim_sub)
        } else {
            registry.lookup(&import_decl.module.parts)
        };
        if let Some(exports) = module_exports {
            for (class_name, count) in &exports.class_param_counts {
                class_param_counts.entry(*class_name).or_insert(*count);
            }
        }
    }

    // Mark known_types as active (non-empty) so convert_type_expr performs
    // unknown type checking. Use a sentinel that can't collide with real names.
    ctx.known_types.insert(crate::interner::intern("$module_scope_active"));

    // Pre-scan: Register all locally declared type names so they are known
    // before any type expressions are converted. This mirrors PureScript's
    // non-order-dependent module scoping for types.
    for decl in &module.decls {
        match decl {
            Decl::Data { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::TypeAlias { name, .. }
            | Decl::ForeignData { name, .. } => {
                ctx.known_types.insert(name.value);
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
                Decl::Data { span, name, constructors, kind_sig, is_role_decl, .. } => {
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
                            } else if let Some((existing_kind, _)) = declared_classes.get(&ctor.name.value) {
                                errors.push(TypeError::DeclConflict {
                                    span: ctor.span,
                                    name: ctor.name.value,
                                    new_kind: "data constructor",
                                    existing_kind,
                                });
                            } else {
                                declared_ctors.insert(ctor.name.value, ("data constructor", ctor.span));
                            }
                        }
                    }
                }
                Decl::Newtype { span, name, constructor, .. } => {
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
                    } else if let Some((existing_kind, _)) = declared_classes.get(&constructor.value) {
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
                Decl::Class { span, name, is_kind_sig, .. } => {
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

    // Pass 0: Collect fixity declarations and check for duplicates.
    let mut seen_value_ops: HashMap<Symbol, Vec<crate::ast::span::Span>> = HashMap::new();
    let mut seen_type_ops: HashMap<Symbol, Vec<crate::ast::span::Span>> = HashMap::new();
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
                ctx.type_operators.insert(operator.value, target.name);
                type_fixities.insert(operator.value, (*associativity, *precedence));
            } else {
                seen_value_ops
                    .entry(operator.value)
                    .or_default()
                    .push(*span);
                ctx.value_fixities.insert(operator.value, (*associativity, *precedence));
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

    // Check type-level operator fixity in all type expressions
    if !type_fixities.is_empty() {
        for decl in &module.decls {
            match decl {
                Decl::TypeSignature { ty, .. } => {
                    check_type_op_fixity(ty, &type_fixities, &mut errors);
                }
                Decl::Data { constructors, .. } => {
                    for ctor in constructors {
                        for field_ty in &ctor.fields {
                            check_type_op_fixity(field_ty, &type_fixities, &mut errors);
                        }
                    }
                }
                Decl::TypeAlias { ty, .. } => {
                    check_type_op_fixity(ty, &type_fixities, &mut errors);
                }
                Decl::Foreign { ty, .. } => {
                    check_type_op_fixity(ty, &type_fixities, &mut errors);
                }
                _ => {}
            }
        }
    }

    // Clone so we don't hold an immutable borrow on ctx across mutable uses.
    let type_ops = ctx.type_operators.clone();

    // Build set of known class names for constraint validation (from all sources).
    let mut known_classes: HashSet<Symbol> = class_param_counts.keys().copied().collect();
    for class_name in instances.keys() {
        known_classes.insert(*class_name);
    }
    for (_, (class_name, _)) in &ctx.class_methods {
        known_classes.insert(*class_name);
    }
    for name in &local_class_names {
        known_classes.insert(*name);
    }

    // Pass 1: Collect type signatures and data constructors
    for decl in &module.decls {
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
                // Validate constraint class names in the type signature
                check_constraint_class_names(ty, &known_classes, &mut errors);
                match convert_type_expr(ty, &type_ops, &ctx.known_types) {
                    Ok(converted) => {
                        // Check for partially applied synonyms in type signature
                        check_type_for_partial_synonyms(&converted, &ctx.state.type_aliases, *span, &mut errors);
                        // Replace wildcard `_` with fresh unification variables so
                        // signatures like `main :: Effect _` work correctly.
                        let converted = ctx.instantiate_wildcards(&converted);
                        signatures.insert(name.value, (*span, converted));
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
                let mut result_type = Type::Con(name.value);
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(tv));
                }

                // Register constructors for exhaustiveness checking.
                // Skip if this is a kind/role annotation (empty constructors) and
                // the type already has constructors registered (e.g. from a Newtype).
                let ctor_names: Vec<Symbol> = constructors.iter().map(|c| c.name.value).collect();
                if !ctor_names.is_empty() || !ctx.data_constructors.contains_key(&name.value) {
                    ctx.data_constructors.insert(name.value, ctor_names);
                }

                for ctor in constructors {
                    // Reject type wildcards in data constructor fields
                    for f in &ctor.fields {
                        if let Some(wc_span) = find_wildcard_span(f) {
                            errors.push(TypeError::WildcardInTypeDefinition { span: wc_span });
                        }
                    }

                    // Build constructor type: field1 -> field2 -> ... -> result_type
                    let field_results: Vec<Result<Type, TypeError>> = ctor
                        .fields
                        .iter()
                        .map(|f| convert_type_expr(f, &type_ops, &ctx.known_types))
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
                        check_type_for_partial_synonyms(field_ty, &ctx.state.type_aliases, *span, &mut errors);
                    }

                    // Save field types for nested exhaustiveness checking
                    ctx.ctor_details.insert(
                        ctor.name.value,
                        (name.value, type_var_syms.clone(), field_types.clone()),
                    );

                    let mut ctor_ty = result_type.clone();
                    for field_ty in field_types.into_iter().rev() {
                        ctor_ty = Type::fun(field_ty, ctor_ty);
                    }

                    // Wrap in Forall if there are type variables
                    if !type_var_syms.is_empty() {
                        ctor_ty = Type::Forall(type_var_syms.clone(), Box::new(ctor_ty));
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

                // Track as a newtype for derive validation
                newtype_names.insert(name.value);

                // Register constructor for exhaustiveness checking
                ctx.data_constructors
                    .insert(name.value, vec![constructor.value]);

                let type_var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();

                let mut result_type = Type::Con(name.value);
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(tv));
                }

                match convert_type_expr(ty, &type_ops, &ctx.known_types) {
                    Ok(field_ty) => {
                        // Check for partially applied synonyms in field type
                        check_type_for_partial_synonyms(&field_ty, &ctx.state.type_aliases, *span, &mut errors);

                        // Save field type for nested exhaustiveness checking
                        ctx.ctor_details.insert(
                            constructor.value,
                            (name.value, type_var_syms.clone(), vec![field_ty.clone()]),
                        );

                        let mut ctor_ty = Type::fun(field_ty, result_type);

                        if !type_var_syms.is_empty() {
                            ctor_ty = Type::Forall(type_var_syms, Box::new(ctor_ty));
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
                // Reject constraints in foreign import types
                if let Some(c_span) = has_any_constraint(ty) {
                    errors.push(TypeError::ConstraintInForeignImport { span: c_span });
                }
                match convert_type_expr(ty, &type_ops, &ctx.known_types) {
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
                is_kind_sig,
                ..
            } => {
                // Track kind signatures vs real definitions for orphan detection
                if *is_kind_sig {
                    kind_sigs.entry(name.value).or_insert((*span, KindSigSource::Class));
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
                                errors.push(TypeError::InvalidConstraintArgument { span: bad_span });
                            }
                        }
                    }

                    // Track superclass constraints with converted type args for instance validation
                    let tvs: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                    let mut sc_constraints = Vec::new();
                    for constraint in constraints {
                        let mut sc_args = Vec::new();
                        let mut ok = true;
                        for arg in &constraint.args {
                            match convert_type_expr(arg, &type_ops, &ctx.known_types) {
                                Ok(ty) => sc_args.push(ty),
                                Err(_) => { ok = false; break; }
                            }
                        }
                        if ok {
                            sc_constraints.push((constraint.class.name, sc_args));
                        }
                    }
                    class_superclasses.insert(name.value, (tvs, sc_constraints));

                    // Track class type parameter count for arity checking
                    class_param_counts.insert(name.value, type_vars.len());
                    known_classes.insert(name.value);
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
                            let sc_known = class_param_counts.contains_key(&constraint.class.name)
                                || instances.contains_key(&constraint.class.name)
                                || local_class_names.contains(&constraint.class.name);
                            if !sc_known {
                                errors.push(TypeError::UnknownClass {
                                    span: *span,
                                    name: constraint.class.name,
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
                    if has_any_constraint(&member.ty).is_some() {
                        ctx.constrained_class_methods.insert(member.name.value);
                    }
                    match convert_type_expr(&member.ty, &type_ops, &ctx.known_types) {
                        Ok(member_ty) => {
                            let scheme_ty = if !type_var_syms.is_empty() {
                                Type::Forall(type_var_syms.clone(), Box::new(member_ty))
                            } else {
                                member_ty
                            };
                            let scheme = Scheme::mono(scheme_ty);
                            env.insert_scheme(member.name.value, scheme.clone());
                            local_values.insert(member.name.value, scheme.clone());
                            // Track that this method belongs to this class
                            ctx.class_methods
                                .insert(member.name.value, (name.value, type_var_syms.clone()));
                        }
                        Err(e) => errors.push(e),
                    }
                }
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

                // Register this instance's types and constraints
                let mut inst_types = Vec::new();
                let mut inst_ok = true;
                for ty_expr in types {
                    match convert_type_expr(ty_expr, &type_ops, &ctx.known_types) {
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
                    if let Some(&expected_count) = class_param_counts.get(&class_name.name) {
                        if inst_types.len() != expected_count {
                            errors.push(TypeError::ClassInstanceArityMismatch {
                                span: *span,
                                class_name: class_name.name,
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
                // Check for non-nominal types in instance heads (records, functions,
                // or type synonyms that expand to such types)
                if inst_ok {
                    for inst_ty in &inst_types {
                        if is_non_nominal_instance_head(inst_ty, &ctx.state.type_aliases) {
                            errors.push(TypeError::InvalidInstanceHead { span: *span });
                            inst_ok = false;
                            break;
                        }
                    }
                }
                // Check for partially applied synonyms in instance types
                if inst_ok {
                    for inst_ty in &inst_types {
                        check_type_for_partial_synonyms(inst_ty, &ctx.state.type_aliases, *span, &mut errors);
                    }
                }
                // Validate constraint arguments: reject forall and wildcards
                if inst_ok {
                    for constraint in constraints {
                        for arg in &constraint.args {
                            if let Some(bad_span) = has_forall_or_wildcard(arg) {
                                errors.push(TypeError::InvalidConstraintArgument { span: bad_span });
                                inst_ok = false;
                                break;
                            }
                        }
                        if !inst_ok { break; }
                    }
                }
                // Convert constraints (e.g., `A a =>` part)
                let mut inst_constraints = Vec::new();
                if inst_ok {
                    for constraint in constraints {
                        let mut c_args = Vec::new();
                        let mut c_ok = true;
                        for arg in &constraint.args {
                            match convert_type_expr(arg, &type_ops, &ctx.known_types) {
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
                            inst_constraints.push((constraint.class.name, c_args));
                        }
                    }
                }
                // Check if the class is known (either via param counts or instances)
                let class_known = class_param_counts.contains_key(&class_name.name)
                    || instances.contains_key(&class_name.name)
                    || local_class_names.contains(&class_name.name);

                // If the class doesn't exist at all, report it
                if inst_ok && !class_known && class_name.module.is_none() {
                    errors.push(TypeError::UnknownClass {
                        span: *span,
                        name: class_name.name,
                    });
                }

                // Check for orphan instances: the instance must be in a module that
                // defines either the class or at least one type in the instance head.
                if inst_ok && !*is_chain && class_known {
                    let class_is_local = local_class_names.contains(&class_name.name);
                    if !class_is_local {
                        let has_local_type = inst_types.iter().any(|ty| type_has_local_con(ty, &local_type_names));
                        // For nullary classes (no type args), it's always orphan if class is imported
                        if inst_types.is_empty() || !has_local_type {
                            errors.push(TypeError::OrphanInstance {
                                span: *span,
                                class_name: class_name.name,
                            });
                        }
                    }
                }

                // Build substitution from class type vars → instance types for method type checking.
                // Must be computed before inst_types is moved into instances.
                let inst_subst: HashMap<Symbol, Type> = if inst_ok {
                    let class_tvs: Option<&Vec<Symbol>> = ctx.class_methods.values()
                        .find(|(cn, _)| *cn == class_name.name)
                        .map(|(_, tvs)| tvs);
                    if let Some(tvs) = class_tvs {
                        tvs.iter().zip(inst_types.iter()).map(|(tv, ty)| (*tv, ty.clone())).collect()
                    } else {
                        HashMap::new()
                    }
                } else {
                    HashMap::new()
                };

                if inst_ok {
                    // Check for overlapping instances at definition time
                    // Skip if this instance is part of an instance chain (else keyword),
                    // if the class is qualified (from a different module's namespace),
                    // or if any type argument has kind annotations (can't distinguish without kind checking)
                    let has_kind_ann = types.iter().any(|t| type_expr_has_kinded(t));
                    if !is_chain && class_name.module.is_none() && !has_kind_ann {
                        let mut found_overlap = false;
                        // Check against other local instances
                        if let Some(existing) = local_instance_heads.get(&class_name.name) {
                            for existing_types in existing {
                                if instance_heads_overlap(&inst_types, existing_types, &ctx.state.type_aliases) {
                                    errors.push(TypeError::OverlappingInstances {
                                        span: *span,
                                        class_name: class_name.name,
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
                        // positives from instances that appear in imported set via re-exports).
                        if !found_overlap
                            && !local_class_names.contains(&class_name.name)
                            && inst_types.iter().all(|t| !type_has_vars(t))
                        {
                            if let Some(imported) = instances.get(&class_name.name) {
                                for (existing_types, _) in imported {
                                    if instance_heads_overlap(&inst_types, existing_types, &ctx.state.type_aliases) {
                                        errors.push(TypeError::OverlappingInstances {
                                            span: *span,
                                            class_name: class_name.name,
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
                        .push(inst_types.clone());
                    registered_instances.push((*span, class_name.name, inst_types.clone()));
                    instances
                        .entry(class_name.name)
                        .or_default()
                        .push((inst_types, inst_constraints));
                }

                // Check for missing/extraneous class members in this instance
                {
                    // Collect method names expected for this class
                    let expected_methods: Vec<Symbol> = ctx.class_methods.iter()
                        .filter(|(_, (cn, _))| *cn == class_name.name)
                        .map(|(method, _)| *method)
                        .collect();

                    // Collect method names provided in this instance
                    let mut provided_methods: HashSet<Symbol> = HashSet::new();
                    let mut provided_method_spans: HashMap<Symbol, Vec<Span>> = HashMap::new();
                    for member_decl in members.iter() {
                        if let Decl::Value { name: mname, span: mspan, .. } = member_decl {
                            provided_methods.insert(mname.value);
                            provided_method_spans.entry(mname.value).or_default().push(*mspan);
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
                                errors.push(TypeError::ExtraneousClassMember {
                                    span: *span,
                                    class_name: class_name.name,
                                    member_name: *method_name,
                                });
                            }
                        }

                        // Check for missing members (expected but not provided)
                        let missing: Vec<(Symbol, Type)> = expected_methods.iter()
                            .filter(|m| !provided_methods.contains(m))
                            .filter_map(|m| {
                                env.lookup(*m).map(|scheme| (*m, scheme.ty.clone()))
                            })
                            .collect();
                        if !missing.is_empty() {
                            errors.push(TypeError::MissingClassMember {
                                span: *span,
                                class_name: class_name.name,
                                members: missing,
                            });
                        }
                    }
                }

                // Validate instance type signatures and detect orphans
                let expected_methods: HashSet<Symbol> = ctx.class_methods.iter()
                    .filter(|(_, (cn, _))| *cn == class_name.name)
                    .map(|(method, _)| *method)
                    .collect();

                for member_decl in members.iter() {
                    if let Decl::TypeSignature { name: sig_name, span: sig_span, .. } = member_decl {
                        if !expected_methods.contains(&sig_name.value) {
                            // Orphan type declaration inside instance — not a class method
                            errors.push(TypeError::OrphanTypeSignature {
                                span: *sig_span,
                                name: sig_name.value,
                            });
                        } else if inst_ok && !inst_subst.is_empty() {
                            // Check that instance method signature matches the class-derived type
                            if let Some(scheme) = env.lookup(sig_name.value) {
                                let class_ty = scheme.ty.clone();
                                // Strip outer forall (class type vars) and substitute
                                let inner = match &class_ty {
                                    Type::Forall(_, body) => (**body).clone(),
                                    other => other.clone(),
                                };
                                let expected_ty = apply_var_subst(&inst_subst, &inner);
                                // Convert the instance signature type
                                if let Decl::TypeSignature { ty, .. } = member_decl {
                                    if let Ok(sig_ty) = convert_type_expr(ty, &type_ops, &ctx.known_types) {
                                        // Unify the declared instance sig with the class-derived type
                                        if let Err(e) = ctx.state.unify(*sig_span, &sig_ty, &expected_ty) {
                                            errors.push(e);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // Collect instance method bodies for deferred checking (after foreign imports
                // and fixity declarations are processed, so all values are in scope)
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
                        // Compute the expected type for 0-binder methods from class definition.
                        // Only for 0-binder methods: with binders, pre-inserted monomorphic
                        // values and env shadowing can cause false unification failures.
                        let expected_ty = if inst_ok && !inst_subst.is_empty() && binders.is_empty() {
                            if let Some(scheme) = env.lookup(name.value) {
                                let class_ty = scheme.ty.clone();
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

                        method_names.push(name.value);
                        deferred_instance_methods.push((
                            name.value,
                            *span,
                            binders as &[_],
                            guarded,
                            where_clause as &[_],
                            expected_ty,
                        ));
                    }
                }
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
            } => {
                has_real_definition.insert(name.value);
                has_type_alias_def.insert(name.value);
                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Reject type wildcards in type alias bodies
                if let Some(wc_span) = find_wildcard_span(ty) {
                    errors.push(TypeError::WildcardInTypeDefinition { span: wc_span });
                }

                // Convert and register type alias for expansion during unification
                match convert_type_expr(ty, &type_ops, &ctx.known_types) {
                    Ok(body_ty) => {
                        // Check for partially applied synonyms in the body
                        check_type_for_partial_synonyms(&body_ty, &ctx.state.type_aliases, *span, &mut errors);
                        let params: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                        ctx.state.type_aliases.insert(name.value, (params, body_ty));
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
                ctx.data_constructors.insert(name.value, Vec::new());
            }
            Decl::Derive {
                span,
                newtype,
                class_name,
                types,
                constraints,
                ..
            } => {
                // Check if the class exists
                let derive_class_known = class_param_counts.contains_key(&class_name.name)
                    || instances.contains_key(&class_name.name)
                    || local_class_names.contains(&class_name.name);
                if !derive_class_known && class_name.module.is_none() {
                    errors.push(TypeError::UnknownClass {
                        span: *span,
                        name: class_name.name,
                    });
                }

                // Check for invalid instance heads: bare record/row/function types
                // at the top level of type arguments (wildcards are ok in derive, e.g. Newtype T _)
                for ty_expr in types {
                    let is_record_or_row = matches!(
                        ty_expr,
                        TypeExpr::Record { .. } | TypeExpr::Row { .. } | TypeExpr::Function { .. }
                    ) || matches!(ty_expr, TypeExpr::Parens { ty, .. } if matches!(ty.as_ref(), TypeExpr::Record { .. } | TypeExpr::Row { .. } | TypeExpr::Function { .. }));
                    if is_record_or_row {
                        errors.push(TypeError::InvalidInstanceHead { span: *span });
                        break;
                    }
                }

                // Extract the target type name from the type arguments.
                // Try the last arg first (for multi-param classes like FunctorWithIndex Int NonEmptyArray,
                // the newtype is the last arg), then fall back to any arg with a constructor head
                // (e.g. `derive instance Newtype (Pair Int Int) _` where last arg is wildcard).
                let target_type_name = types.last().and_then(|t| extract_head_constructor(t))
                    .or_else(|| types.iter().rev().find_map(|t| extract_head_constructor(t)));

                if let Some(target_name) = target_type_name {
                    // InvalidNewtypeInstance: derive instance Newtype X _
                    // where X is not actually a newtype
                    let newtype_sym = crate::interner::intern("Newtype");
                    if class_name.name == newtype_sym && !newtype_names.contains(&target_name) {
                        errors.push(TypeError::InvalidNewtypeInstance {
                            span: *span,
                            name: target_name,
                        });
                    }

                    // InvalidNewtypeDerivation: derive newtype instance SomeClass X
                    // where X is not actually a newtype
                    if *newtype && !newtype_names.contains(&target_name) {
                        errors.push(TypeError::InvalidNewtypeDerivation {
                            span: *span,
                            name: target_name,
                        });
                    }
                } else if *newtype {
                    // derive newtype instance with no type arguments (e.g. derive newtype instance Nullary)
                    // — there's no target type to be a newtype
                    errors.push(TypeError::InvalidNewtypeInstance {
                        span: *span,
                        name: class_name.name,
                    });
                }

                // Register derived instance types and constraints for instance resolution
                let mut inst_types = Vec::new();
                let mut inst_ok = true;
                for ty_expr in types {
                    match convert_type_expr(ty_expr, &type_ops, &ctx.known_types) {
                        Ok(ty) => inst_types.push(ty),
                        Err(_) => {
                            inst_ok = false;
                            break;
                        }
                    }
                }
                // Check derived instance arity matches class parameter count
                if inst_ok {
                    if let Some(&expected_count) = class_param_counts.get(&class_name.name) {
                        if inst_types.len() != expected_count {
                            errors.push(TypeError::ClassInstanceArityMismatch {
                                span: *span,
                                class_name: class_name.name,
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
                        check_type_for_partial_synonyms(inst_ty, &ctx.state.type_aliases, *span, &mut errors);
                    }
                }
                // Check for non-nominal types in derived instance heads (records, functions,
                // or type synonyms expanding to them). Derive requires a data/newtype.
                if inst_ok {
                    for inst_ty in &inst_types {
                        if is_non_nominal_for_derive(inst_ty, &ctx.state.type_aliases) {
                            errors.push(TypeError::InvalidInstanceHead { span: *span });
                            inst_ok = false;
                            break;
                        }
                    }
                }
                // Orphan check for derived instances: expand type aliases first,
                // then check if any type constructor in the instance head is locally defined.
                if inst_ok && class_name.module.is_none() {
                    let class_is_local = local_class_names.contains(&class_name.name);
                    if !class_is_local {
                        let expanded: Vec<Type> = inst_types.iter()
                            .map(|t| expand_type_aliases(t, &ctx.state.type_aliases))
                            .collect();
                        let has_local_type = expanded.iter().any(|ty| type_has_local_con(ty, &local_type_names));
                        if expanded.is_empty() || !has_local_type {
                            errors.push(TypeError::OrphanInstance {
                                span: *span,
                                class_name: class_name.name,
                            });
                        }
                    }
                }
                let mut inst_constraints = Vec::new();
                if inst_ok {
                    for constraint in constraints {
                        let mut c_args = Vec::new();
                        let mut c_ok = true;
                        for arg in &constraint.args {
                            match convert_type_expr(arg, &type_ops, &ctx.known_types) {
                                Ok(ty) => c_args.push(ty),
                                Err(_) => {
                                    c_ok = false;
                                    inst_ok = false;
                                    break;
                                }
                            }
                        }
                        if c_ok {
                            inst_constraints.push((constraint.class.name, c_args));
                        }
                    }
                }
                if inst_ok {
                    registered_instances.push((*span, class_name.name, inst_types.clone()));
                    instances
                        .entry(class_name.name)
                        .or_default()
                        .push((inst_types, inst_constraints));
                }
            }
            Decl::Value { .. } => {
                // Handled in Pass 2
            }
        }
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
            TypeExpr::Parens { ty, .. } => count_kind_arity(ty),
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
                Decl::Data { name, type_vars, is_role_decl: true, kind_sig, .. } => {
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
                Decl::Data { name, type_vars, is_role_decl: false, kind_sig, .. } => {
                    if *kind_sig == KindSigSource::None {
                        prev_decl = Some((name.value, "data", type_vars.len()));
                    } else {
                        prev_decl = None;
                    }
                    prev_was_role_for = None;
                }
                Decl::Newtype { name, type_vars, .. } => {
                    prev_decl = Some((name.value, "data", type_vars.len()));
                    prev_was_role_for = None;
                }
                Decl::ForeignData { name, kind, .. } => {
                    let arity = count_kind_arity(kind);
                    prev_decl = Some((name.value, "foreign", arity));
                    prev_was_role_for = None;
                }
                Decl::TypeAlias { name, type_vars, .. } => {
                    prev_decl = Some((name.value, "synonym", type_vars.len()));
                    prev_was_role_for = None;
                }
                Decl::Class { name, type_vars, .. } => {
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

    // Check for cycles in type synonyms
    check_type_synonym_cycles(&type_alias_defs, &mut errors);

    // Check for cycles in kind declarations (data kind sigs and foreign data kinds)
    {
        let mut kind_decls: HashMap<Symbol, (Span, &crate::cst::TypeExpr)> = HashMap::new();
        for decl in &module.decls {
            match decl {
                Decl::Data { name, kind_sig, kind_type: Some(kind_ty), .. } if *kind_sig != KindSigSource::None => {
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
                    if let Some(cycle) = dfs_find_cycle(name, &deps, &mut visited, &mut on_stack, &mut path) {
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
            }
            // If the target is a data constructor, register the operator→constructor mapping
            // so exhaustiveness checking recognizes operator patterns (e.g. `:` for `Cons`).
            if ctx.ctor_details.contains_key(&target.name) {
                ctx.ctor_details.insert(operator.value, ctx.ctor_details[&target.name].clone());
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
        if let Decl::Fixity { target, operator, is_type: false, .. } = decl {
            if ctx.ctor_details.contains_key(&target.name) {
                // Constructor target: remove any inherited function alias flag
                ctx.function_op_aliases.remove(&operator.value);
            } else {
                ctx.function_op_aliases.insert(operator.value);
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
    // We also exclude names that exist as top-level values in the module,
    // since the RHS refers to the top-level function, not the sibling method
    // (e.g. `chooseInt = chooseInt` delegates to a top-level function).
    let top_level_values: HashSet<Symbol> = module.decls.iter().filter_map(|d| {
        match d {
            Decl::Value { name, .. } | Decl::TypeSignature { name, .. } => Some(name.value),
            Decl::Foreign { name, .. } => Some(name.value),
            _ => None,
        }
    }).collect();
    let mut cycle_methods: HashSet<Symbol> = HashSet::new();
    for group in &instance_method_groups {
        let sibling_set: HashSet<Symbol> = group.iter().copied().collect();
        for (name, span, binders, guarded, _where, _expected) in &deferred_instance_methods {
            if !sibling_set.contains(name) || !binders.is_empty() {
                continue;
            }
            // Skip methods whose class type has extra constraints (e.g. Applicative m =>).
            // These get implicit dictionary parameters, making them functions even with
            // 0 explicit binders, so sibling references are deferred under a lambda.
            if ctx.constrained_class_methods.contains(name) {
                continue;
            }
            // Check if the application head is a sibling method name
            let head_is_sibling = |expr: &crate::cst::Expr| -> bool {
                if let Some(head) = expr_app_head_name(expr) {
                    sibling_set.contains(&head) && !top_level_values.contains(&head)
                } else {
                    false
                }
            };
            let is_cycle = match guarded {
                crate::cst::GuardedExpr::Unconditional(expr) => head_is_sibling(expr),
                crate::cst::GuardedExpr::Guarded(guards) => {
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
    for (name, span, binders, guarded, where_clause, expected_ty) in &deferred_instance_methods {
        // Instance methods should NOT use top-level signatures — their types come
        // from the class definition. Using top-level sigs causes bugs when a module
        // has a value with the same name as a class method (e.g. Foreign.Object.foldMap).
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
    }

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
    let group_idx: HashMap<Symbol, usize> =
        value_groups.iter().enumerate().map(|(i, (n, _))| (*n, i)).collect();

    // Process each SCC in dependency order
    for scc in &sccs {
        let is_mutual = scc.len() > 1;

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
                dep_edges.get(&name).map_or(false, |refs| refs.contains(&name))
            };

            if is_cyclic {
                // For each member with 0 explicit binders, check if the body
                // contains a strict (not under lambda) reference to any SCC member.
                let scc_set: HashSet<Symbol> = scc.iter().copied().collect();
                let mut non_func_members: Vec<(Symbol, crate::ast::span::Span)> = Vec::new();
                for &name in scc {
                    if let Some(&idx) = group_idx.get(&name) {
                        let (_, decls) = &value_groups[idx];
                        // Bindings with type signatures are OK — the signature
                        // provides the type even for self-referential values.
                        if signatures.contains_key(&name) {
                            continue;
                        }
                        let has_binders = decls.iter().any(|d| {
                            if let Decl::Value { binders, .. } = d { !binders.is_empty() } else { false }
                        });
                        if has_binders {
                            continue; // Function with explicit arguments — OK
                        }
                        // Check if the body is directly a reference to an SCC member
                        let has_strict_cycle = decls.iter().any(|d| {
                            if let Decl::Value { guarded, .. } = d {
                                if let crate::cst::GuardedExpr::Unconditional(expr) = guarded {
                                    is_direct_var_ref(expr, &scc_set)
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        });
                        if has_strict_cycle {
                            let span = if let Decl::Value { span, .. } = decls[0] { *span } else { crate::ast::span::Span { start: 0, end: 0 } };
                            non_func_members.push((name, span));
                        }
                    }
                }

                if !non_func_members.is_empty() {
                    // Report cycle for the first non-function member
                    let (name, span) = non_func_members[0];
                    let others: Vec<(Symbol, crate::ast::span::Span)> = non_func_members[1..].to_vec();
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
            let sig = signatures.get(name).map(|(_, ty)| ty);

            // Check for duplicate value declarations: multiple equations with 0 binders
            if decls.len() > 1 {
                let zero_arity_spans: Vec<crate::ast::span::Span> = decls
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
                if let Decl::Value { span, binders, .. } = decl {
                    if !binders.is_empty() {
                        check_overlapping_arg_names(*span, binders, &mut errors);
                    }
                }
            }

            // Pre-insert for self-recursion. Reuse SCC pre-var if available.
            let self_ty = if let Some(pre_var) = scc_pre_vars.get(name) {
                pre_var.clone()
            } else {
                let var = Type::Unif(ctx.state.fresh_var());
                env.insert_mono(*name, var.clone());
                var
            };

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
                            if is_mutual {
                                // Defer generalization for mutual recursion
                                checked_values.push(CheckedValue {
                                    name: *name,
                                    ty,
                                    self_ty,
                                    sig: sig.cloned(),
                                });
                            } else {
                                let scheme = if let Some(sig_ty) = sig {
                                    Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                                } else {
                                    let zonked = ctx.state.zonk(ty.clone());
                                    env.generalize_excluding(&mut ctx.state, zonked, *name)
                                };
                                let zonked = ctx.state.zonk(ty.clone());
                                env.insert_scheme(*name, scheme.clone());
                                local_values.insert(*name, scheme.clone());
                                result_types.insert(*name, zonked);
                            }
                        }
                        Err(e) => {
                            errors.push(e);
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

                let func_ty = match sig {
                    Some(sig_ty) => match ctx.instantiate_forall_type(sig_ty.clone()) {
                        Ok(ty) => ty,
                        Err(e) => {
                            errors.push(e);
                            continue;
                        }
                    },
                    None => Type::Unif(ctx.state.fresh_var()),
                };

                let mut group_failed = false;
                for decl in decls {
                    if let Decl::Value {
                        span,
                        binders,
                        guarded,
                        where_clause,
                        ..
                    } = decl
                    {
                        match check_value_decl(
                            &mut ctx,
                            &env,
                            *name,
                            *span,
                            binders,
                            guarded,
                            where_clause,
                            None,
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
                    }
                }

                if !group_failed {
                    let first_span = if let Decl::Value { span, .. } = decls[0] {
                        *span
                    } else {
                        crate::ast::span::Span::new(0, 0)
                    };
                    if let Err(e) = ctx.state.unify(first_span, &self_ty, &func_ty) {
                        errors.push(e);
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
                        let scheme = if let Some(sig_ty) = sig {
                            Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                        } else {
                            env.generalize_excluding(&mut ctx.state, zonked.clone(), *name)
                        };
                        env.insert_scheme(*name, scheme.clone());
                        local_values.insert(*name, scheme);

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

                        result_types.insert(*name, zonked);
                    }
                }
            }
        }

        // Deferred generalization for mutual recursion SCC
        if is_mutual {
            for cv in &checked_values {
                let scheme = if let Some(sig_ty) = &cv.sig {
                    Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                } else {
                    let zonked = ctx.state.zonk(cv.ty.clone());
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
        if let Some((class_tvs, sc_constraints)) = class_superclasses.get(class_name) {
            if class_tvs.len() == inst_types.len() {
                let subst: HashMap<Symbol, Type> = class_tvs.iter().copied()
                    .zip(inst_types.iter().cloned())
                    .collect();
                for (sc_class, sc_args) in sc_constraints {
                    // Only check superclasses that are locally defined or have
                    // zero instances (imported superclasses may have instances
                    // our resolution can't match, e.g. Profunctor Function).
                    let sc_is_local = local_class_names.contains(sc_class);
                    let sc_has_no_instances = !instances.contains_key(sc_class)
                        || instances.get(sc_class).map_or(true, |v| v.is_empty());
                    if !sc_is_local && !sc_has_no_instances {
                        continue;
                    }
                    let concrete_args: Vec<Type> = sc_args.iter()
                        .map(|t| apply_var_subst(&subst, t))
                        .collect();
                    // Skip if any arg still has type variables (polymorphic instance)
                    let has_vars = concrete_args.iter().any(|t| contains_type_var(t));
                    if !has_vars && !has_matching_instance_depth(&instances, &ctx.state.type_aliases, sc_class, &concrete_args, 0) {
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

    // Pass 3: Check deferred type class constraints
    for (span, class_name, type_args) in &ctx.deferred_constraints {
        let zonked_args: Vec<Type> = type_args
            .iter()
            .map(|t| ctx.state.zonk(t.clone()))
            .collect();

        // Skip if any arg still contains unsolved unification variables or type variables
        // (polymorphic usage — no concrete instance needed).
        // We check deeply since unif vars can be nested inside App, e.g. Show ((?1 ?2) ?2).
        let has_unsolved = zonked_args.iter().any(|t| {
            !ctx.state.free_unif_vars(t).is_empty() || contains_type_var(t)
        });
        if has_unsolved {
            continue;
        }

        // If the class itself is not known (not in any instance map and no
        // methods registered), produce UnknownClass instead of NoInstanceFound.
        let class_is_known = instances.contains_key(class_name)
            || ctx.class_methods.values().any(|(cn, _)| cn == class_name);
        if !class_is_known {
            errors.push(TypeError::UnknownClass {
                span: *span,
                name: *class_name,
            });
        } else if !has_matching_instance_depth(&instances, &ctx.state.type_aliases, class_name, &zonked_args, 0) {
            errors.push(TypeError::NoInstanceFound {
                span: *span,
                class_name: *class_name,
                type_args: zonked_args,
            });
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
                        let valid_ctors = ctx.data_constructors.get(name);
                        for ctor in ctors {
                            let is_valid = valid_ctors
                                .map_or(false, |cs| cs.contains(ctor));
                            if !is_valid {
                                errors.push(TypeError::UnkownExport {
                                    span: export_list.span,
                                    name: *ctor,
                                });
                            }
                        }
                        // Check that ALL constructors are listed — partial constructor
                        // exports are not allowed in PureScript.
                        // T() (empty list) is valid — opaque type export.
                        if !ctors.is_empty() {
                            if let Some(all_ctors) = valid_ctors {
                                let exported_set: std::collections::HashSet<_> = ctors.iter().copied().collect();
                                for ctor in all_ctors {
                                    if !exported_set.contains(ctor) {
                                        errors.push(TypeError::TransitiveExportError {
                                            span: export_list.span,
                                            exported: *name,
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
            if let Decl::Fixity { target, operator, is_type, .. } = decl {
                if *is_type {
                    type_op_targets.insert(operator.value, target.name);
                } else {
                    value_op_targets.insert(operator.value, target.name);
                }
            }
        }

        // Transitive export checks: class members require their class, and vice versa
        let exported_values: HashSet<Symbol> = export_list.value.exports.iter()
            .filter_map(|e| match e { Export::Value(n) => Some(*n), _ => None })
            .collect();
        let exported_classes: HashSet<Symbol> = export_list.value.exports.iter()
            .filter_map(|e| match e { Export::Class(n) => Some(*n), _ => None })
            .collect();

        // Check: exporting a class member without its class
        for &val in &exported_values {
            if let Some((class_name, _)) = ctx.class_methods.get(&val) {
                // Only check locally-defined classes (not imported ones)
                if declared_classes.contains(class_name) && !exported_classes.contains(class_name) {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: val,
                        dependency: *class_name,
                    });
                }
            }
        }

        // Check: exporting a class without its members
        for &cls in &exported_classes {
            for (method, (class_name, _)) in &ctx.class_methods {
                if *class_name == cls && !exported_values.contains(method) {
                    // Only check locally-defined class methods
                    if local_values.contains_key(method) {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: cls,
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
            if let Some((_, sc_constraints)) = class_superclasses.get(&cls) {
                for (sc_class, _) in sc_constraints {
                    // Only check locally-defined superclasses
                    if declared_class_set.contains(sc_class) && !exported_classes.contains(sc_class) {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: cls,
                            dependency: *sc_class,
                        });
                    }
                }
            }
        }

        // Check: exporting a value operator without its target function (local defs only)
        for &val in &exported_values {
            if let Some(&target) = value_op_targets.get(&val) {
                if ctx.ctor_details.contains_key(&target) {
                    // Operator aliases a data constructor — check that the constructor
                    // is exported through its parent type's constructor list.
                    let ctor_exported = export_list.value.exports.iter().any(|e| {
                        if let Export::Type(ty_name, Some(members)) = e {
                            let type_ctors = ctx.data_constructors.get(ty_name);
                            let has_this_ctor = type_ctors.map_or(false, |cs| cs.contains(&target));
                            has_this_ctor && match members {
                                crate::cst::DataMembers::All => true,
                                crate::cst::DataMembers::Explicit(cs) => cs.contains(&target),
                            }
                        } else {
                            false
                        }
                    });
                    if !ctor_exported {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: val,
                            dependency: target,
                        });
                    }
                } else if local_values.contains_key(&target)
                    && !exported_values.contains(&target)
                {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: val,
                        dependency: target,
                    });
                }
            }
        }

        // Check: exporting a type operator without its target type (local defs only)
        let exported_types: HashSet<Symbol> = export_list.value.exports.iter()
            .filter_map(|e| match e { Export::Type(n, _) => Some(*n), _ => None })
            .collect();
        let exported_type_ops: HashSet<Symbol> = export_list.value.exports.iter()
            .filter_map(|e| match e { Export::TypeOp(n) => Some(*n), _ => None })
            .collect();
        let declared_type_set: HashSet<&Symbol> = declared_types.iter().collect();
        for &op in &exported_type_ops {
            if let Some(&target) = type_op_targets.get(&op) {
                if declared_type_set.contains(&target) && !exported_types.contains(&target) {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: op,
                        dependency: target,
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
                            exported: ty_name,
                            dependency: *dep,
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
                if let Some(ctors) = ctx.data_constructors.get(ty_name) {
                    'ctor_loop: for ctor in ctors {
                        if let Some((_, _, field_types)) = ctx.ctor_details.get(ctor) {
                            for field_ty in field_types {
                                let mut referenced = Vec::new();
                                collect_type_constructors(field_ty, &mut referenced);
                                for dep in &referenced {
                                    if declared_type_set.contains(dep) && !exported_types.contains(dep) {
                                        errors.push(TypeError::TransitiveExportError {
                                            span: export_list.span,
                                            exported: *ty_name,
                                            dependency: *dep,
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
    }

    // Check: exporting a value whose type references a locally-defined type that is not exported
    if let Some(ref export_list) = module.exports {
        let exp_vals: HashSet<Symbol> = export_list.value.exports.iter()
            .filter_map(|e| match e { Export::Value(n) => Some(*n), _ => None })
            .collect();
        let exp_types: HashSet<Symbol> = export_list.value.exports.iter()
            .filter_map(|e| match e { Export::Type(n, _) => Some(*n), _ => None })
            .collect();
        for &val in &exp_vals {
            if let Some(scheme) = local_values.get(&val) {
                let zonked = ctx.state.zonk(scheme.ty.clone());
                let mut referenced_types = Vec::new();
                collect_type_constructors(&zonked, &mut referenced_types);
                for ty_name in &referenced_types {
                    // Only flag local types that are not exported
                    if declared_types.contains(ty_name) && !exp_types.contains(ty_name) {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: val,
                            dependency: *ty_name,
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

    let mut export_data_constructors: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    let mut export_ctor_details: HashMap<Symbol, (Symbol, Vec<Symbol>, Vec<Type>)> = HashMap::new();
    for type_name in &declared_types {
        if let Some(ctors) = ctx.data_constructors.get(type_name) {
            export_data_constructors.insert(*type_name, ctors.clone());
            for ctor in ctors {
                if let Some(details) = ctx.ctor_details.get(ctor) {
                    export_ctor_details.insert(*ctor, details.clone());
                }
            }
        }
    }

    // Also export ctor_details for operator aliases (e.g. `:|` for `NonEmpty`).
    // These are registered during fixity processing but not in data_constructors.
    for (name, details) in &ctx.ctor_details {
        if local_values.contains_key(name) && !export_ctor_details.contains_key(name) {
            export_ctor_details.insert(*name, details.clone());
        }
    }

    let mut export_class_methods: HashMap<Symbol, (Symbol, Vec<Symbol>)> = HashMap::new();
    for (method, (class_name, tvs)) in &ctx.class_methods {
        if local_class_set.contains(class_name) {
            export_class_methods.insert(*method, (*class_name, tvs.clone()));
        }
    }
    // Register locally-defined class names as types in data_constructors so they
    // participate in ExportConflict detection (classes are types in PureScript).
    for class_name in &declared_classes {
        export_data_constructors.entry(*class_name).or_insert_with(Vec::new);
    }

    let mut export_instances: HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>> =
        HashMap::new();
    for (class_name, insts) in &instances {
        // Export all instances (both for local and imported classes) since instances
        // are globally visible in PureScript
        export_instances.insert(*class_name, insts.clone());
    }

    let mut export_type_operators: HashMap<Symbol, Symbol> = HashMap::new();
    let mut export_value_fixities: HashMap<Symbol, (Associativity, u8)> = HashMap::new();
    let mut export_function_op_aliases: HashSet<Symbol> = HashSet::new();
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
                export_type_operators.insert(operator.value, target.name);
            } else {
                export_value_fixities.insert(operator.value, (*associativity, *precedence));
                // Track operators that alias functions (not constructors)
                if !ctx.ctor_details.contains_key(&target.name) {
                    export_function_op_aliases.insert(operator.value);
                }
            }
        }
    }

    // Collect type aliases for export
    let export_type_aliases: HashMap<Symbol, (Vec<Symbol>, Type)> = ctx.state.type_aliases.clone();

    // Expand type aliases in all exported values so importing modules don't
    // need access to module-local aliases like `type Size = Int`.
    for scheme in local_values.values_mut() {
        scheme.ty = ctx.state.zonk(scheme.ty.clone());
    }

    // Build origin maps: all locally-defined names have origin = this module
    let current_mod_sym = module_name_to_symbol(&module.name.value);
    let mut value_origins: HashMap<Symbol, Symbol> = HashMap::new();
    let mut type_origins: HashMap<Symbol, Symbol> = HashMap::new();
    let mut class_origins: HashMap<Symbol, Symbol> = HashMap::new();
    for name in local_values.keys() {
        value_origins.insert(*name, current_mod_sym);
    }
    for name in export_data_constructors.keys() {
        type_origins.insert(*name, current_mod_sym);
    }
    for class_name in &declared_classes {
        class_origins.insert(*class_name, current_mod_sym);
    }
    for (_, (class_name, _)) in &export_class_methods {
        class_origins.insert(*class_name, current_mod_sym);
    }

    let mut module_exports = ModuleExports {
        values: local_values,
        class_methods: export_class_methods,
        data_constructors: export_data_constructors,
        ctor_details: export_ctor_details,
        instances: export_instances,
        type_operators: export_type_operators,
        value_fixities: export_value_fixities,
        function_op_aliases: export_function_op_aliases,
        constrained_class_methods: ctx.constrained_class_methods.clone(),
        type_aliases: export_type_aliases,
        class_param_counts: class_param_counts.clone(),
        value_origins,
        type_origins,
        class_origins,
    };

    // If there's an explicit export list, filter exports accordingly
    if let Some(ref export_list) = module.exports {
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
        );
    }


    CheckResult {
        types: result_types,
        errors,
        exports: module_exports,
    }
}

/// Create a qualified symbol by combining a module alias with a name.
fn qualified_symbol(module: Symbol, name: Symbol) -> Symbol {
    let mod_str = crate::interner::resolve(module).unwrap_or_default();
    let name_str = crate::interner::resolve(name).unwrap_or_default();
    crate::interner::intern(&format!("{}.{}", mod_str, name_str))
}

/// Convert a ModuleName to a single symbol (joining parts with '.').
fn module_name_to_symbol(module_name: &crate::cst::ModuleName) -> Symbol {
    let parts: Vec<String> = module_name
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect();
    crate::interner::intern(&parts.join("."))
}

/// Optionally qualify a name: if qualifier is Some, prefix with "Q.", otherwise return as-is.
fn maybe_qualify(name: Symbol, qualifier: Option<Symbol>) -> Symbol {
    match qualifier {
        Some(q) => qualified_symbol(q, name),
        None => name,
    }
}

/// Process all import declarations, bringing imported names into scope.
fn process_imports(
    module: &Module,
    registry: &ModuleRegistry,
    env: &mut Env,
    ctx: &mut InferCtx,
    instances: &mut HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    errors: &mut Vec<TypeError>,
) {
    // Build Prim exports once so explicit `import Prim` / `import Prim as P` resolves.
    let prim = prim_exports();

    // Track import origins for scope conflict detection.
    // Maps (possibly qualified) name → (origin module symbol, is_explicit).
    // A scope conflict occurs when a name is imported from two different origin modules
    // AND both imports have the same explicitness level. Explicit imports shadow open imports.
    let mut import_origins: HashMap<Symbol, (Symbol, bool)> = HashMap::new();

    for import_decl in &module.imports {
        // Handle Prim submodules (Prim.Coerce, Prim.Row, etc.) as built-in
        let prim_sub;
        let module_exports = if is_prim_module(&import_decl.module) {
            &prim
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
                module_exports.values.keys()
                    .map(|n| maybe_qualify(*n, Some(q)))
                    .collect()
            }
            (None, None) => {
                // import M — all unqualified values
                module_exports.values.keys().copied().collect()
            }
            (Some(ImportList::Explicit(items)), _) => {
                items.iter().map(|i| maybe_qualify(import_name(i), qualifier)).collect()
            }
            (Some(ImportList::Hiding(items)), _) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                module_exports.values.keys().copied()
                    .filter(|n| !hidden.contains(n))
                    .map(|n| maybe_qualify(n, qualifier))
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
                    crate::interner::intern(&name_str[pos+1..])
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

        match &import_decl.imports {
            None => {
                // import M — everything unqualified; import M as Q — everything qualified only
                import_all(module_exports, env, ctx, instances, qualifier);
            }
            Some(ImportList::Explicit(items)) => {
                // import M (x) — listed items unqualified
                // import M (x) as Q — listed items qualified only
                for item in items {
                    import_item(
                        item,
                        module_exports,
                        env,
                        ctx,
                        instances,
                        qualifier,
                        import_decl.span,
                        errors,
                    );
                }
                // Always import all instances from the module.
                // In PureScript, type class instances are globally visible —
                // importing any item from a module imports all its instances.
                // Deduplicate to avoid combinatorial explosion in constraint checking.
                for (class_name, insts) in &module_exports.instances {
                    let existing = instances.entry(*class_name).or_default();
                    for inst in insts {
                        if !existing.iter().any(|e| e.0 == inst.0) {
                            existing.push(inst.clone());
                        }
                    }
                }
            }
            Some(ImportList::Hiding(items)) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                import_all_except(module_exports, &hidden, env, ctx, instances, qualifier);
            }
        }
    }

}

/// Import all names from a module's exports.
/// If `qualifier` is Some, env entries are stored with qualified keys (e.g. "Q.foo").
/// Internal maps (class_methods, data_constructors, etc.) are always unqualified.
fn import_all(
    exports: &ModuleExports,
    env: &mut Env,
    ctx: &mut InferCtx,
    instances: &mut HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    qualifier: Option<Symbol>,
) {
    // Import class method info first so we can detect conflicts
    for (name, info) in &exports.class_methods {
        ctx.class_methods.insert(*name, info.clone());
    }
    for (name, scheme) in &exports.values {
        // Don't let a non-class value overwrite a class method's env entry.
        // E.g. Data.Function.apply must not shadow Control.Apply.apply.
        // Only applies to unqualified imports — qualified names (Q.foo) can't conflict.
        if qualifier.is_none() && ctx.class_methods.contains_key(name) && !exports.class_methods.contains_key(name) {
            continue;
        }
        env.insert_scheme(maybe_qualify(*name, qualifier), scheme.clone());
    }
    for (name, ctors) in &exports.data_constructors {
        ctx.data_constructors.insert(*name, ctors.clone());
        ctx.known_types.insert(maybe_qualify(*name, qualifier));
    }
    for (name, details) in &exports.ctor_details {
        ctx.ctor_details.insert(*name, details.clone());
    }
    for (name, insts) in &exports.instances {
        let existing = instances.entry(*name).or_default();
        for inst in insts {
            if !existing.contains(inst) {
                existing.push(inst.clone());
            }
        }
    }
    for (op, target) in &exports.type_operators {
        ctx.type_operators.insert(*op, *target);
    }
    for (op, fixity) in &exports.value_fixities {
        ctx.value_fixities.insert(*op, *fixity);
    }
    for op in &exports.function_op_aliases {
        ctx.function_op_aliases.insert(*op);
    }
    for name in &exports.constrained_class_methods {
        ctx.constrained_class_methods.insert(*name);
    }
    for (name, alias) in &exports.type_aliases {
        ctx.state.type_aliases.insert(*name, alias.clone());
        ctx.known_types.insert(maybe_qualify(*name, qualifier));
    }
}

/// Import a single item from a module's exports.
/// If `qualifier` is Some, env entries are stored with qualified keys.
fn import_item(
    item: &Import,
    exports: &ModuleExports,
    env: &mut Env,
    ctx: &mut InferCtx,
    instances: &mut HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    qualifier: Option<Symbol>,
    import_span: crate::ast::span::Span,
    errors: &mut Vec<TypeError>,
) {
    match item {
        Import::Value(name) => {
            if exports.values.get(name).is_none() && exports.class_methods.get(name).is_none() {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: *name,
                });
                return;
            }
            // Import class method info first if applicable
            if let Some((class_name, tvs)) = exports.class_methods.get(name) {
                ctx.class_methods.insert(*name, (*class_name, tvs.clone()));
            }
            if let Some(scheme) = exports.values.get(name) {
                // Explicit imports always win — the user specifically asked for this value.
                // (The class method shadow check only applies to bulk import_all.)
                env.insert_scheme(maybe_qualify(*name, qualifier), scheme.clone());
            }
            // Also import instances if this is a class method
            if let Some((class_name, _)) = exports.class_methods.get(name) {
                // Import instances for the method's class so constraints can be resolved
                if let Some(insts) = exports.instances.get(class_name) {
                    instances
                        .entry(*class_name)
                        .or_default()
                        .extend(insts.clone());
                }
            }
            // Import fixity if this is an operator
            if let Some(fixity) = exports.value_fixities.get(name) {
                ctx.value_fixities.insert(*name, *fixity);
            }
            if exports.function_op_aliases.contains(name) {
                ctx.function_op_aliases.insert(*name);
            }
            if exports.constrained_class_methods.contains(name) {
                ctx.constrained_class_methods.insert(*name);
            }
            // Import ctor_details if this is a constructor alias (e.g. `:|` for `NonEmpty`)
            if let Some(details) = exports.ctor_details.get(name) {
                ctx.ctor_details.insert(*name, details.clone());
            }
        }
        Import::Type(name, members) => {
            if let Some(ctors) = exports.data_constructors.get(name) {
                ctx.data_constructors.insert(*name, ctors.clone());
                ctx.known_types.insert(maybe_qualify(*name, qualifier));

                let import_ctors: Vec<Symbol> = match members {
                    Some(DataMembers::All) => ctors.clone(),
                    Some(DataMembers::Explicit(listed)) => {
                        // Validate that each listed constructor actually exists
                        for ctor_name in listed {
                            if !ctors.contains(ctor_name) {
                                errors.push(TypeError::UnknownImportDataConstructor {
                                    span: import_span,
                                    name: *ctor_name,
                                });
                            }
                        }
                        listed.clone()
                    }
                    None => Vec::new(), // Just the type, no constructors
                };

                for ctor in &import_ctors {
                    if let Some(scheme) = exports.values.get(ctor) {
                        env.insert_scheme(maybe_qualify(*ctor, qualifier), scheme.clone());
                    }
                    if let Some(details) = exports.ctor_details.get(ctor) {
                        ctx.ctor_details.insert(*ctor, details.clone());
                    }
                }
            } else if let Some(alias) = exports.type_aliases.get(name) {
                // Type alias import
                ctx.state.type_aliases.insert(*name, alias.clone());
                ctx.known_types.insert(maybe_qualify(*name, qualifier));
            } else {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: *name,
                });
            }
        }
        Import::Class(name) => {
            // Check if the class exists in the exports
            let has_class = exports.class_methods.values().any(|(cn, _)| cn == name);
            if !has_class && exports.instances.get(name).is_none() {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: *name,
                });
                return;
            }
            for (method_name, (class_name, tvs)) in &exports.class_methods {
                if class_name == name {
                    ctx.class_methods
                        .insert(*method_name, (*class_name, tvs.clone()));
                    if exports.constrained_class_methods.contains(method_name) {
                        ctx.constrained_class_methods.insert(*method_name);
                    }
                }
            }
            if let Some(insts) = exports.instances.get(name) {
                instances.entry(*name).or_default().extend(insts.clone());
            }
        }
        Import::TypeOp(name) => {
            if let Some(target) = exports.type_operators.get(name) {
                ctx.type_operators.insert(*name, *target);
                // Also add the target type to known_types so it passes validation in convert_type_expr
                ctx.known_types.insert(*target);
                // Import the target's type alias definition if it exists
                if let Some(alias) = exports.type_aliases.get(target) {
                    ctx.state.type_aliases.insert(*target, alias.clone());
                }
            } else {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: *name,
                });
            }
        }
    }
}

/// Import all names except those in the hidden set.
/// If `qualifier` is Some, env entries are stored with qualified keys.
fn import_all_except(
    exports: &ModuleExports,
    hidden: &HashSet<Symbol>,
    env: &mut Env,
    ctx: &mut InferCtx,
    instances: &mut HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    qualifier: Option<Symbol>,
) {
    // Import class method info first so we can detect conflicts
    for (name, info) in &exports.class_methods {
        if !hidden.contains(name) {
            ctx.class_methods.insert(*name, info.clone());
        }
    }
    for (name, scheme) in &exports.values {
        if !hidden.contains(name) {
            // Don't let a non-class value overwrite a class method's env entry.
            // Only applies to unqualified imports — qualified names (Q.foo) can't conflict.
            if qualifier.is_none() && ctx.class_methods.contains_key(name) && !exports.class_methods.contains_key(name) {
                continue;
            }
            env.insert_scheme(maybe_qualify(*name, qualifier), scheme.clone());
        }
    }
    for (name, ctors) in &exports.data_constructors {
        if !hidden.contains(name) {
            ctx.data_constructors.insert(*name, ctors.clone());
            ctx.known_types.insert(maybe_qualify(*name, qualifier));
            for ctor in ctors {
                if !hidden.contains(ctor) {
                    if let Some(details) = exports.ctor_details.get(ctor) {
                        ctx.ctor_details.insert(*ctor, details.clone());
                    }
                }
            }
        }
    }
    for (name, insts) in &exports.instances {
        let existing = instances.entry(*name).or_default();
        for inst in insts {
            if !existing.contains(inst) {
                existing.push(inst.clone());
            }
        }
    }
    for (op, target) in &exports.type_operators {
        if !hidden.contains(op) {
            ctx.type_operators.insert(*op, *target);
        }
    }
    for (op, fixity) in &exports.value_fixities {
        if !hidden.contains(op) {
            ctx.value_fixities.insert(*op, *fixity);
        }
    }
    for op in &exports.function_op_aliases {
        if !hidden.contains(op) {
            ctx.function_op_aliases.insert(*op);
        }
    }
    for name in &exports.constrained_class_methods {
        if !hidden.contains(name) {
            ctx.constrained_class_methods.insert(*name);
        }
    }
    for (name, alias) in &exports.type_aliases {
        if !hidden.contains(name) {
            ctx.state.type_aliases.insert(*name, alias.clone());
            ctx.known_types.insert(maybe_qualify(*name, qualifier));
        }
    }
}

/// Get the primary symbol name from an Import item.
fn import_name(item: &Import) -> Symbol {
    match item {
        Import::Value(name)
        | Import::Type(name, _)
        | Import::TypeOp(name)
        | Import::Class(name) => *name,
    }
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
                    crate::cst::Import::Value(name) => { values.insert(*name); }
                    crate::cst::Import::Type(name, members) => {
                        types.insert(*name);
                        // Importing Type(..) also imports its constructors as values
                        if let Some(crate::cst::DataMembers::All) = members {
                            if let Some(ctors) = mod_exports.data_constructors.get(name) {
                                for ctor in ctors {
                                    values.insert(*ctor);
                                }
                            }
                        } else if let Some(crate::cst::DataMembers::Explicit(ctor_names)) = members {
                            for ctor in ctor_names {
                                values.insert(*ctor);
                            }
                        }
                    }
                    crate::cst::Import::Class(name) => {
                        classes.insert(*name);
                        // Importing a class also imports all its methods
                        for (method_name, (class_name, _)) in &mod_exports.class_methods {
                            if *class_name == *name {
                                values.insert(*method_name);
                            }
                        }
                    }
                    crate::cst::Import::TypeOp(name) => { type_ops.insert(*name); }
                }
            }
            ImportFilter { values: Some(values), types: Some(types), classes: Some(classes), type_ops: Some(type_ops) }
        }
        Some(crate::cst::ImportList::Hiding(imports)) => {
            // For hiding, build exclusion sets and invert to "everything except hidden"
            let mut hidden_values: HashSet<Symbol> = HashSet::new();
            let mut hidden_types: HashSet<Symbol> = HashSet::new();
            let mut hidden_classes: HashSet<Symbol> = HashSet::new();
            let mut hidden_type_ops: HashSet<Symbol> = HashSet::new();
            for imp in imports {
                match imp {
                    crate::cst::Import::Value(name) => { hidden_values.insert(*name); }
                    crate::cst::Import::Type(name, members) => {
                        hidden_types.insert(*name);
                        if let Some(crate::cst::DataMembers::All) = members {
                            if let Some(ctors) = mod_exports.data_constructors.get(name) {
                                for ctor in ctors {
                                    hidden_values.insert(*ctor);
                                }
                            }
                        } else if let Some(crate::cst::DataMembers::Explicit(ctor_names)) = members {
                            for ctor in ctor_names {
                                hidden_values.insert(*ctor);
                            }
                        }
                    }
                    crate::cst::Import::Class(name) => {
                        hidden_classes.insert(*name);
                        for (method_name, (class_name, _)) in &mod_exports.class_methods {
                            if *class_name == *name {
                                hidden_values.insert(*method_name);
                            }
                        }
                    }
                    crate::cst::Import::TypeOp(name) => { hidden_type_ops.insert(*name); }
                }
            }
            // Build allowed sets = everything in mod_exports minus hidden
            let values: HashSet<Symbol> = mod_exports.values.keys().copied()
                .filter(|n| !hidden_values.contains(n)).collect();
            let types: HashSet<Symbol> = mod_exports.data_constructors.keys().copied()
                .chain(mod_exports.type_aliases.keys().copied())
                .filter(|n| !hidden_types.contains(n)).collect();
            let classes: HashSet<Symbol> = mod_exports.class_methods.values()
                .map(|(c, _)| *c)
                .filter(|n| !hidden_classes.contains(n)).collect();
            let type_ops: HashSet<Symbol> = mod_exports.type_operators.keys().copied()
                .filter(|n| !hidden_type_ops.contains(n)).collect();
            ImportFilter { values: Some(values), types: Some(types), classes: Some(classes), type_ops: Some(type_ops) }
        }
    }
}

/// Filter a module's exports according to an explicit export list.
fn filter_exports(
    all: &ModuleExports,
    export_list: &crate::cst::ExportList,
    export_span: crate::ast::span::Span,
    _local_types: &HashSet<Symbol>,
    _local_classes: &HashSet<Symbol>,
    registry: &ModuleRegistry,
    imports: &[crate::cst::ImportDecl],
    current_module: &crate::cst::ModuleName,
    errors: &mut Vec<TypeError>,
) -> ModuleExports {
    let mut result = ModuleExports::default();

    // Track the original defining module for each exported name (for conflict detection).
    // When two different re-export modules contribute the same name, it's only a conflict
    // if the names have different origins (i.e. independently defined in different modules).
    // Re-exporting the same definition through different paths is allowed (ModuleExportDupes).
    let mut value_origins: HashMap<Symbol, Symbol> = HashMap::new();
    let mut type_origins: HashMap<Symbol, Symbol> = HashMap::new();
    let mut class_origins: HashMap<Symbol, Symbol> = HashMap::new();

    for export in &export_list.exports {
        match export {
            Export::Value(name) => {
                if let Some(scheme) = all.values.get(name) {
                    result.values.insert(*name, scheme.clone());
                }
                // Also export class method info if applicable
                if let Some(info) = all.class_methods.get(name) {
                    result.class_methods.insert(*name, info.clone());
                }
                // Also export fixity if applicable
                if let Some(fixity) = all.value_fixities.get(name) {
                    result.value_fixities.insert(*name, *fixity);
                }
                if all.function_op_aliases.contains(name) {
                    result.function_op_aliases.insert(*name);
                }
                if all.constrained_class_methods.contains(name) {
                    result.constrained_class_methods.insert(*name);
                }
                // Also export ctor_details if this is a constructor alias (e.g. `:|`)
                if let Some(details) = all.ctor_details.get(name) {
                    result.ctor_details.insert(*name, details.clone());
                }
            }
            Export::Type(name, members) => {
                if let Some(ctors) = all.data_constructors.get(name) {
                    let export_ctors: Vec<Symbol> = match members {
                        Some(DataMembers::All) => ctors.clone(),
                        Some(DataMembers::Explicit(listed)) => listed.clone(),
                        None => {
                            // Don't overwrite existing constructor list with empty
                            // (handles `module X (A(..), A)` where second A has no members)
                            if !result.data_constructors.contains_key(name) {
                                result.data_constructors.insert(*name, Vec::new());
                            }
                            // Still need to export type aliases below
                            if let Some(alias) = all.type_aliases.get(name) {
                                result.type_aliases.insert(*name, alias.clone());
                            }
                            continue;
                        }
                    };

                    result.data_constructors.insert(*name, export_ctors.clone());

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
                if let Some(alias) = all.type_aliases.get(name) {
                    result.type_aliases.insert(*name, alias.clone());
                }
            }
            Export::Class(name) => {
                // Export class metadata (for constraint generation) but NOT methods as values.
                // In PureScript, `module M (class C) where` only exports the class —
                // methods must be listed separately: `module M (class C, methodName) where`.
                for (method_name, (class_name, tvs)) in &all.class_methods {
                    if class_name == name {
                        result
                            .class_methods
                            .insert(*method_name, (*class_name, tvs.clone()));
                        if all.constrained_class_methods.contains(method_name) {
                            result.constrained_class_methods.insert(*method_name);
                        }
                    }
                }
                // Export instances for this class
                if let Some(insts) = all.instances.get(name) {
                    result.instances.insert(*name, insts.clone());
                }
                // Export class param count (needed for orphan detection and arity checking)
                if let Some(count) = all.class_param_counts.get(name) {
                    result.class_param_counts.insert(*name, *count);
                }
            }
            Export::TypeOp(name) => {
                if let Some(target) = all.type_operators.get(name) {
                    result.type_operators.insert(*name, *target);
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
                        result.data_constructors.insert(*name, ctors.clone());
                    }
                    for (name, details) in &all.ctor_details {
                        result.ctor_details.insert(*name, details.clone());
                    }
                    for (name, info) in &all.class_methods {
                        result.class_methods.insert(*name, info.clone());
                    }
                    for (name, target) in &all.type_operators {
                        result.type_operators.insert(*name, *target);
                    }
                    for (name, fixity) in &all.value_fixities {
                        result.value_fixities.insert(*name, *fixity);
                    }
                    for name in &all.function_op_aliases {
                        result.function_op_aliases.insert(*name);
                    }
                    for name in &all.constrained_class_methods {
                        result.constrained_class_methods.insert(*name);
                    }
                    for (name, alias) in &all.type_aliases {
                        result.type_aliases.insert(*name, alias.clone());
                    }
                    for (name, count) in &all.class_param_counts {
                        result.class_param_counts.insert(*name, *count);
                    }
                    continue;
                }
                // Re-export everything from the named module.
                // `module X` in the export list matches either:
                // - an import whose module name equals X (e.g. `import Data.Foo`)
                // - an import whose qualified alias equals X (e.g. `import Prim.Ordering as PO` matches `module PO`)
                let reexport_mod_sym = module_name_to_symbol(mod_name);
                for import_decl in imports {
                    let matches_module = module_name_to_symbol(&import_decl.module) == reexport_mod_sym;
                    let matches_alias = import_decl.qualified.as_ref()
                        .map(|q| module_name_to_symbol(q) == reexport_mod_sym)
                        .unwrap_or(false);
                    if matches_module || matches_alias {
                        // Look up from registry; also check Prim submodules
                        let prim_sub;
                        let full_exports = if is_prim_module(&import_decl.module) {
                            Some(&prim_exports())
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

                            // Check for conflicts: class methods
                            for (name, info) in &mod_exports.class_methods {
                                let (class_name, _) = info;
                                let imported = filter.classes.as_ref()
                                    .map_or(true, |allowed| allowed.contains(class_name));
                                if imported {
                                    // Determine origin: use source module's origin if available,
                                    // otherwise the source module itself defined it
                                    let origin = mod_exports.class_origins.get(class_name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    if let Some(prev_origin) = class_origins.get(class_name) {
                                        if *prev_origin != origin {
                                            errors.push(TypeError::ExportConflict {
                                                span: export_span,
                                                name: *class_name,
                                            });
                                        }
                                    } else {
                                        class_origins.insert(*class_name, origin);
                                    }
                                }
                                result.class_methods.insert(*name, info.clone());
                            }
                            for (name, scheme) in &mod_exports.values {
                                // Don't let a non-class value overwrite a class method's entry
                                if result.class_methods.contains_key(name) && !mod_exports.class_methods.contains_key(name) {
                                    continue;
                                }
                                let origin = mod_exports.value_origins.get(name)
                                    .copied()
                                    .unwrap_or(source_mod_sym);
                                let imported = filter.values.as_ref()
                                    .map_or(true, |allowed| allowed.contains(name));
                                if imported {
                                    if let Some(prev_origin) = value_origins.get(name) {
                                        if *prev_origin != origin {
                                            errors.push(TypeError::ExportConflict {
                                                span: export_span,
                                                name: *name,
                                            });
                                        }
                                    } else {
                                        value_origins.insert(*name, origin);
                                    }
                                }
                                if imported {
                                    result.values.insert(*name, scheme.clone());
                                }
                            }
                            for (name, ctors) in &mod_exports.data_constructors {
                                let imported = filter.types.as_ref()
                                    .map_or(true, |allowed| allowed.contains(name));
                                if imported {
                                    let origin = mod_exports.type_origins.get(name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    if let Some(prev_origin) = type_origins.get(name) {
                                        if *prev_origin != origin {
                                            errors.push(TypeError::ExportConflict {
                                                span: export_span,
                                                name: *name,
                                            });
                                        }
                                    } else {
                                        type_origins.insert(*name, origin);
                                    }
                                }
                                result.data_constructors.insert(*name, ctors.clone());
                            }
                            for (name, details) in &mod_exports.ctor_details {
                                result.ctor_details.insert(*name, details.clone());
                            }
                            for (name, target) in &mod_exports.type_operators {
                                let imported = filter.type_ops.as_ref()
                                    .map_or(true, |allowed| allowed.contains(name));
                                if imported {
                                    // Use value_origins for type operators too
                                    let origin = mod_exports.value_origins.get(name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    if let Some(prev_origin) = value_origins.get(name) {
                                        if *prev_origin != origin {
                                            errors.push(TypeError::ExportConflict {
                                                span: export_span,
                                                name: *name,
                                            });
                                        }
                                    } else {
                                        value_origins.insert(*name, origin);
                                    }
                                }
                                result.type_operators.insert(*name, *target);
                            }
                            for (name, fixity) in &mod_exports.value_fixities {
                                result.value_fixities.insert(*name, *fixity);
                            }
                            for name in &mod_exports.function_op_aliases {
                                result.function_op_aliases.insert(*name);
                            }
                            for name in &mod_exports.constrained_class_methods {
                                result.constrained_class_methods.insert(*name);
                            }
                            for (name, alias) in &mod_exports.type_aliases {
                                result.type_aliases.insert(*name, alias.clone());
                            }
                            for (name, count) in &mod_exports.class_param_counts {
                                result.class_param_counts.insert(*name, *count);
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
        if result.values.contains_key(name) {
            result.value_origins.entry(*name).or_insert(*origin);
        }
    }
    for (name, origin) in &all.type_origins {
        if result.data_constructors.contains_key(name) {
            result.type_origins.entry(*name).or_insert(*origin);
        }
    }
    for (name, origin) in &all.class_origins {
        result.class_origins.entry(*name).or_insert(*origin);
    }
    // Also include origins from re-exported modules
    for (name, origin) in &value_origins {
        result.value_origins.entry(*name).or_insert(*origin);
    }
    for (name, origin) in &type_origins {
        result.type_origins.entry(*name).or_insert(*origin);
    }
    for (name, origin) in &class_origins {
        result.class_origins.entry(*name).or_insert(*origin);
    }

    result
}

/// Check exhaustiveness for multi-equation function definitions.
/// Peels `func_ty` to extract parameter types, then for each binder position,
/// checks if all constructors of the corresponding type are covered.
fn check_multi_eq_exhaustiveness(
    ctx: &InferCtx,
    span: crate::ast::span::Span,
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
    span: crate::ast::span::Span,
    binders: &[Binder],
    guarded: &crate::cst::GuardedExpr,
    where_clause: &[crate::cst::LetBinding],
    expected: Option<&Type>,
) -> Result<Type, TypeError> {
    // Reject bare `_` as the entire body — it's not a valid anonymous argument context.
    if binders.is_empty() {
        if let crate::cst::GuardedExpr::Unconditional(body) = guarded {
            if matches!(body.as_ref(), crate::cst::Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_") {
                return Err(TypeError::IncorrectAnonymousArgument { span });
            }
        }
    }

    let mut local_env = env.child();

    if binders.is_empty() {
        // No binders — process where clause then infer body
        if !where_clause.is_empty() {
            ctx.process_let_bindings(&mut local_env, where_clause)?;
        }

        let body_ty = ctx.infer_guarded(&local_env, guarded)?;

        if let Some(sig_ty) = expected {
            let skolemized = strip_forall(sig_ty.clone());
            ctx.state.unify(span, &body_ty, &skolemized)?;
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
            if !where_clause.is_empty() {
                ctx.process_let_bindings(&mut local_env, where_clause)?;
            }

            let body_ty = ctx.infer_guarded(&local_env, guarded)?;
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
            if !where_clause.is_empty() {
                ctx.process_let_bindings(&mut local_env, where_clause)?;
            }

            let body_ty = ctx.infer_guarded(&local_env, guarded)?;

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

/// Expand type aliases in a type (standalone version for use outside unification).
/// Repeatedly expands until no more aliases apply.
fn expand_type_aliases(ty: &Type, type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>) -> Type {
    if type_aliases.is_empty() {
        return ty.clone();
    }
    // First expand nested types
    let expanded = match ty {
        Type::App(f, a) => {
            let f2 = expand_type_aliases(f, type_aliases);
            let a2 = expand_type_aliases(a, type_aliases);
            Type::app(f2, a2)
        }
        Type::Fun(a, b) => {
            Type::fun(
                expand_type_aliases(a, type_aliases),
                expand_type_aliases(b, type_aliases),
            )
        }
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| (*l, expand_type_aliases(t, type_aliases)))
                .collect();
            let tail = tail
                .as_ref()
                .map(|t| Box::new(expand_type_aliases(t, type_aliases)));
            Type::Record(fields, tail)
        }
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(expand_type_aliases(body, type_aliases)))
        }
        _ => ty.clone(),
    };
    // Now try to expand the head if it's a saturated alias
    let mut args = Vec::new();
    let mut head = &expanded;
    loop {
        match head {
            Type::App(f, a) => {
                args.push(a.as_ref().clone());
                head = f.as_ref();
            }
            _ => break,
        }
    }
    if let Type::Con(name) = head {
        if let Some((params, body)) = type_aliases.get(name) {
            args.reverse();
            if args.len() == params.len() {
                let subst: HashMap<Symbol, Type> =
                    params.iter().copied().zip(args.into_iter()).collect();
                return expand_type_aliases(&apply_var_subst(&subst, body), type_aliases);
            }
        }
    }
    expanded
}

fn has_matching_instance_depth(
    instances: &HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
    class_name: &Symbol,
    concrete_args: &[Type],
    depth: u32,
) -> bool {
    if depth > 20 {
        // Avoid infinite recursion on circular constraint chains
        return false;
    }

    // Built-in solver instances for compiler-magic type classes
    let class_str = crate::interner::resolve(*class_name).unwrap_or_default().to_string();
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
                        crate::interner::resolve(*s).unwrap_or_default() == "String"
                    }
                    (Type::TypeInt(_), Type::Con(s)) => {
                        crate::interner::resolve(*s).unwrap_or_default() == "Int"
                    }
                    (Type::Con(c), Type::Con(s)) => {
                        let c_str = crate::interner::resolve(*c).unwrap_or_default().to_string();
                        let s_str = crate::interner::resolve(*s).unwrap_or_default().to_string();
                        (c_str == "True" || c_str == "False") && s_str == "Boolean"
                            || (c_str == "LT" || c_str == "EQ" || c_str == "GT") && s_str == "Ordering"
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
        _ => {}
    }

    // Expand type aliases in concrete args before matching
    let expanded_args: Vec<Type> = concrete_args
        .iter()
        .map(|t| expand_type_aliases(t, type_aliases))
        .collect();

    let known = match instances.get(class_name) {
        Some(k) => k,
        None => return false,
    };

    known.iter().any(|(inst_types, inst_constraints)| {
        // Also expand aliases in instance types (e.g. `instance Convert Int Words`
        // where `Words` is a type synonym for `String`)
        let expanded_inst_types: Vec<Type> = inst_types
            .iter()
            .map(|t| expand_type_aliases(t, type_aliases))
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

        // Check each constraint with substituted types (expand aliases after substitution)
        inst_constraints.iter().all(|(c_class, c_args)| {
            let substituted_args: Vec<Type> =
                c_args.iter().map(|t| apply_var_subst(&subst, t)).collect();
            has_matching_instance_depth(instances, type_aliases, c_class, &substituted_args, depth + 1)
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
        Type::Con(name) => out.push(*name),
        Type::App(f, arg) => { collect_type_constructors(f, out); collect_type_constructors(arg, out); }
        Type::Fun(a, b) => { collect_type_constructors(a, out); collect_type_constructors(b, out); }
        Type::Forall(_, body) => collect_type_constructors(body, out),
        Type::Record(fields, tail) => {
            for (_, ty) in fields { collect_type_constructors(ty, out); }
            if let Some(t) = tail { collect_type_constructors(t, out); }
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
            fields.iter().any(|(_, t)| type_has_vars(t)) || tail.as_ref().map_or(false, |t| type_has_vars(t))
        }
        Type::Forall(_, body) => type_has_vars(body),
        _ => false,
    }
}

fn type_has_local_con(ty: &Type, local_types: &HashSet<Symbol>) -> bool {
    match ty {
        Type::Con(name) => local_types.contains(name),
        Type::App(f, arg) => type_has_local_con(f, local_types) || type_has_local_con(arg, local_types),
        _ => false,
    }
}

fn type_expr_has_kinded(ty: &crate::cst::TypeExpr) -> bool {
    use crate::cst::TypeExpr;
    match ty {
        TypeExpr::Kinded { .. } => true,
        TypeExpr::App { constructor, arg, .. } => type_expr_has_kinded(constructor) || type_expr_has_kinded(arg),
        TypeExpr::Parens { ty, .. } => type_expr_has_kinded(ty),
        TypeExpr::Function { from, to, .. } => type_expr_has_kinded(from) || type_expr_has_kinded(to),
        TypeExpr::Forall { ty, .. } => type_expr_has_kinded(ty),
        TypeExpr::Constrained { ty, .. } => type_expr_has_kinded(ty),
        _ => false,
    }
}

/// Check if two instance heads are identical (alpha-equivalent after alias expansion).
/// This catches cases like `Convert String Bar` vs `Convert String String` (when Bar = String).
/// Does NOT match `Foo a` vs `Foo Int` — those are "overlapping" but valid at definition time.
fn instance_heads_overlap(
    types_a: &[Type],
    types_b: &[Type],
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, Type)>,
) -> bool {
    if types_a.len() != types_b.len() {
        return false;
    }
    let expanded_a: Vec<Type> = types_a.iter().map(|t| expand_type_aliases(t, type_aliases)).collect();
    let expanded_b: Vec<Type> = types_b.iter().map(|t| expand_type_aliases(t, type_aliases)).collect();
    // Check alpha-equivalence: type variables match other type variables (positionally),
    // but concrete types must be structurally identical.
    let mut var_map: HashMap<Symbol, Symbol> = HashMap::new();
    if expanded_a.iter().zip(expanded_b.iter()).all(|(a, b)| instance_types_alpha_eq(a, b, &mut var_map)) {
        return true;
    }
    // Also check subsumption: if one instance head is strictly more general than the other,
    // they overlap. E.g. `instance Test a` subsumes `instance Test Int`.
    // Check both directions: A subsumes B, or B subsumes A.
    let mut subst_ab: HashMap<Symbol, Type> = HashMap::new();
    let a_subsumes_b = expanded_a.iter().zip(expanded_b.iter())
        .all(|(a, b)| match_instance_type(a, b, &mut subst_ab));
    if a_subsumes_b {
        return true;
    }
    let mut subst_ba: HashMap<Symbol, Type> = HashMap::new();
    expanded_b.iter().zip(expanded_a.iter())
        .all(|(b, a)| match_instance_type(b, a, &mut subst_ba))
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
            if f1.len() != f2.len() { return false; }
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

/// Recursively match an instance type pattern against a concrete type, building a substitution.
/// E.g. matches `App(Array, Var(a))` against `App(Array, JSON)` with subst {a → JSON}.
fn match_instance_type(inst_ty: &Type, concrete: &Type, subst: &mut HashMap<Symbol, Type>) -> bool {
    match (inst_ty, concrete) {
        (Type::Var(v), _) => {
            if let Some(existing) = subst.get(v) {
                existing == concrete
            } else {
                subst.insert(*v, concrete.clone());
                true
            }
        }
        (Type::Con(a), Type::Con(b)) => a == b,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            match_instance_type(f1, f2, subst) && match_instance_type(a1, a2, subst)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            match_instance_type(a1, a2, subst) && match_instance_type(b1, b2, subst)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2)) => {
            if f1.len() != f2.len() { return false; }
            for ((l1, ty1), (l2, ty2)) in f1.iter().zip(f2.iter()) {
                if l1 != l2 || !match_instance_type(ty1, ty2, subst) {
                    return false;
                }
            }
            match (t1, t2) {
                (None, None) => true,
                (Some(a), Some(b)) => match_instance_type(a, b, subst),
                _ => false,
            }
        }
        (Type::TypeString(a), Type::TypeString(b)) => a == b,
        (Type::TypeInt(a), Type::TypeInt(b)) => a == b,
        _ => inst_ty == concrete,
    }
}

/// Apply a variable substitution (Type::Var → Type) to a type.
fn apply_var_subst(subst: &HashMap<Symbol, Type>, ty: &Type) -> Type {
    match ty {
        Type::Var(v) => subst.get(v).cloned().unwrap_or_else(|| ty.clone()),
        Type::Fun(a, b) => Type::fun(apply_var_subst(subst, a), apply_var_subst(subst, b)),
        Type::App(f, a) => Type::app(apply_var_subst(subst, f), apply_var_subst(subst, a)),
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(apply_var_subst(subst, body)))
        }
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| (*l, apply_var_subst(subst, t)))
                .collect();
            let tail = tail.as_ref().map(|t| Box::new(apply_var_subst(subst, t)));
            Type::Record(fields, tail)
        }
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
    }
}

/// Check if a TypeExpr has a Partial constraint.
fn has_partial_constraint(ty: &crate::cst::TypeExpr) -> bool {
    match ty {
        crate::cst::TypeExpr::Constrained { constraints, .. } => {
            constraints.iter().any(|c| {
                crate::interner::resolve(c.class.name).unwrap_or_default() == "Partial"
            })
        }
        crate::cst::TypeExpr::Forall { ty, .. } => has_partial_constraint(ty),
        crate::cst::TypeExpr::Parens { ty, .. } => has_partial_constraint(ty),
        _ => false,
    }
}

/// Check if a type expression contains a wildcard `_` anywhere.
fn find_wildcard_span(ty: &crate::cst::TypeExpr) -> Option<crate::ast::span::Span> {
    use crate::cst::TypeExpr;
    match ty {
        TypeExpr::Wildcard { span } => Some(*span),
        TypeExpr::App { constructor, arg, .. } => {
            find_wildcard_span(constructor).or_else(|| find_wildcard_span(arg))
        }
        TypeExpr::Function { from, to, .. } => {
            find_wildcard_span(from).or_else(|| find_wildcard_span(to))
        }
        TypeExpr::Forall { ty, .. } => find_wildcard_span(ty),
        TypeExpr::Constrained { ty, .. } => find_wildcard_span(ty),
        TypeExpr::Parens { ty, .. } => find_wildcard_span(ty),
        TypeExpr::Kinded { ty, kind, .. } => {
            find_wildcard_span(ty).or_else(|| find_wildcard_span(kind))
        }
        TypeExpr::Record { fields, .. } => {
            fields.iter().find_map(|f| find_wildcard_span(&f.ty))
        }
        TypeExpr::Row { fields, tail, .. } => {
            fields.iter().find_map(|f| find_wildcard_span(&f.ty))
                .or_else(|| tail.as_ref().and_then(|t| find_wildcard_span(t)))
        }
        TypeExpr::TypeOp { left, right, .. } => {
            find_wildcard_span(left).or_else(|| find_wildcard_span(right))
        }
        _ => None,
    }
}

/// Check if an expression is directly a variable reference to any name in the set.
/// Used for conservative cycle detection: `x = y` where y is in the set IS a direct
/// reference, but `x = f y` or `x = f <$> y` is NOT. The idea is to only flag the
/// simplest cycles like `x = x` or `x = y; y = x`, while allowing `x = f <$> z`
/// even if z is in the same SCC (since f creates a thunk/intermediate value).
fn is_direct_var_ref(expr: &crate::cst::Expr, names: &HashSet<Symbol>) -> bool {
    use crate::cst::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => names.contains(&name.name),
        Expr::Parens { expr, .. } => is_direct_var_ref(expr, names),
        Expr::TypeAnnotation { expr, .. } => is_direct_var_ref(expr, names),
        _ => false,
    }
}

/// Extract the "application head" of an expression — the leftmost function in an application chain.
/// Returns the unqualified variable name if the head is a simple Var, None otherwise.
/// Used for instance method cycle detection: only the head of the application matters,
/// not arguments (which may dispatch to different typeclass instances).
fn expr_app_head_name(expr: &crate::cst::Expr) -> Option<Symbol> {
    use crate::cst::Expr;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => Some(name.name),
        Expr::App { func, .. } => expr_app_head_name(func),
        Expr::Parens { expr, .. } | Expr::TypeAnnotation { expr, .. } => {
            expr_app_head_name(expr)
        }
        _ => None,
    }
}

/// Check if a type expression has any type class constraint (at the top level, under forall/parens).
fn has_any_constraint(ty: &crate::cst::TypeExpr) -> Option<crate::ast::span::Span> {
    use crate::cst::TypeExpr;
    match ty {
        TypeExpr::Constrained { span, .. } => Some(*span),
        TypeExpr::Forall { ty, .. } => has_any_constraint(ty),
        TypeExpr::Parens { ty, .. } => has_any_constraint(ty),
        _ => None,
    }
}
