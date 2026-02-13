use std::collections::{HashMap, HashSet};

use crate::ast::span::Span;
use crate::cst::{Associativity, Binder, DataMembers, Decl, Export, Import, ImportList, Module, Spanned};
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
            refs.insert(name.name);
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
    /// Type aliases: alias_name → (params, body_type)
    pub type_aliases: HashMap<Symbol, (Vec<Symbol>, Type)>,
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

    pub fn print_module_names(&self) {
        println!("Registered modules:");
        let mut names = Vec::new();
        if let Some(base) = &self.base {
            for name in base.modules.keys() {
                let name_str = name
                    .iter()
                    .map(|s| crate::interner::resolve(*s).unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(".");
                names.push(name_str);
            }
        }
        for name in self.modules.keys() {
            let name_str = name
                .iter()
                .map(|s| crate::interner::resolve(*s).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".");
            names.push(name_str);
        }
        names.sort();
        for name in names { println!(" {}", name); }
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

/// Typecheck an entire module, returning a map of top-level names to their types
/// and a list of any errors encountered. Checking continues past errors so that
/// partial results are available for tooling (e.g. IDE hover types).
pub fn check_module(module: &Module, registry: &ModuleRegistry) -> CheckResult {
    let mut ctx = InferCtx::new();
    let mut env = Env::new();
    let mut signatures: HashMap<Symbol, (crate::ast::span::Span, Type)> = HashMap::new();
    let mut result_types: HashMap<Symbol, Type> = HashMap::new();
    let mut errors: Vec<TypeError> = Vec::new();

    // Track class info for instance checking
    // Each instance stores (type_args, constraints) where constraints are (class_name, constraint_type_args)
    let mut instances: HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>> = HashMap::new();

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

    // Deferred instance method bodies: checked after Pass 1.5 so foreign imports and fixity are available
    let mut deferred_instance_methods: Vec<(Symbol, Span, &[Binder], &crate::cst::GuardedExpr, &[crate::cst::LetBinding])> = Vec::new();

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

    // Pass 0: Collect fixity declarations and check for duplicates.
    let mut seen_value_ops: HashMap<Symbol, Vec<crate::ast::span::Span>> = HashMap::new();
    let mut seen_type_ops: HashMap<Symbol, Vec<crate::ast::span::Span>> = HashMap::new();
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

    // Clone so we don't hold an immutable borrow on ctx across mutable uses.
    let type_ops = ctx.type_operators.clone();

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
                match convert_type_expr(ty, &type_ops, &ctx.known_types) {
                    Ok(converted) => {
                        signatures.insert(name.value, (*span, converted));
                    }
                    Err(e) => errors.push(e),
                }
            }
            Decl::Data {
                name,
                type_vars,
                constructors,
                ..
            } => {
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
                name,
                type_vars,
                constructor,
                ty,
                ..
            } => {
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
                ..
            } => {
                // Track class for duplicate detection (skip kind signatures which have no type_vars/members)
                let is_kind_sig = type_vars.is_empty() && members.is_empty();
                if !is_kind_sig {
                    seen_classes.entry(name.value).or_default().push(*span);

                    // Collect superclass names for cycle detection
                    let superclass_names: Vec<Symbol> =
                        constraints.iter().map(|c| c.class.name).collect();
                    class_defs.insert(name.value, (*span, superclass_names));
                }

                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Register class methods in the environment with their declared types
                let type_var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();
                for member in members {
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
                if inst_ok {
                    instances
                        .entry(class_name.name)
                        .or_default()
                        .push((inst_types, inst_constraints));
                }

                // Collect instance method bodies for deferred checking (after foreign imports
                // and fixity declarations are processed, so all values are in scope)
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
                        deferred_instance_methods.push((
                            name.value,
                            *span,
                            binders as &[_],
                            guarded,
                            where_clause as &[_],
                        ));
                    }
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
                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Convert and register type alias for expansion during unification
                match convert_type_expr(ty, &type_ops, &ctx.known_types) {
                    Ok(body_ty) => {
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

    // Check for cycles in type synonyms
    check_type_synonym_cycles(&type_alias_defs, &mut errors);

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

    // Now that foreign imports, fixity declarations, and value signatures have been
    // processed, all values are available in env for instance method checking.
    for (name, span, binders, guarded, where_clause) in &deferred_instance_methods {
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
            None,
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

    // Check each value group
    for (name, decls) in &value_groups {
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

        // Pre-insert a fresh unification variable so recursive references work
        let self_ty = Type::Unif(ctx.state.fresh_var());
        env.insert_mono(*name, self_ty.clone());

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
                        // Unify pre-inserted type with inferred type (for recursion)
                        if let Err(e) = ctx.state.unify(*span, &self_ty, &ty) {
                            errors.push(e);
                        }
                        // If there's an explicit signature, use it for the scheme
                        // to avoid leaking $u vars from where clauses.
                        // Zonk to expand type aliases (e.g. NaturalTransformation → forall a. f a -> g a)
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
                    Err(e) => {
                        errors.push(e);
                        // Leave the pre-inserted unif var so later decls don't get
                        // spurious UndefinedVariable errors
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

            // Create a fresh type for the function and check each equation against it
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
                // Unify pre-inserted type with multi-equation result (for recursion)
                let first_span = if let Decl::Value { span, .. } = decls[0] {
                    *span
                } else {
                    crate::ast::span::Span::new(0, 0)
                };
                if let Err(e) = ctx.state.unify(first_span, &self_ty, &func_ty) {
                    errors.push(e);
                }
                let zonked = ctx.state.zonk(func_ty);
                // If there's an explicit signature, use it for the scheme.
                // Where-clause annotations can introduce rigid Type::Var that
                // unify with the outer unification variables (scoped type variables),
                // which would not be generalized by generalize_excluding.
                let scheme = if let Some(sig_ty) = sig {
                    Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                } else {
                    env.generalize_excluding(&mut ctx.state, zonked.clone(), *name)
                };
                env.insert_scheme(*name, scheme.clone());
                local_values.insert(*name, scheme);

                // Exhaustiveness check for multi-equation functions.
                // Skip for Partial-constrained functions (intentionally non-exhaustive).
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

        if !has_matching_instance(&instances, class_name, &zonked_args) {
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
                Export::Type(name, _) => {
                    if !declared_types.contains(name) {
                        errors.push(TypeError::UnkownExport {
                            span: export_list.span,
                            name: *name,
                        });
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

    let mut export_instances: HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>> =
        HashMap::new();
    for (class_name, insts) in &instances {
        // Export all instances (both for local and imported classes) since instances
        // are globally visible in PureScript
        export_instances.insert(*class_name, insts.clone());
    }

    let mut export_type_operators: HashMap<Symbol, Symbol> = HashMap::new();
    let mut export_value_fixities: HashMap<Symbol, (Associativity, u8)> = HashMap::new();
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

    let mut module_exports = ModuleExports {
        values: local_values,
        class_methods: export_class_methods,
        data_constructors: export_data_constructors,
        ctor_details: export_ctor_details,
        instances: export_instances,
        type_operators: export_type_operators,
        value_fixities: export_value_fixities,
        type_aliases: export_type_aliases,
    };

    // If there's an explicit export list, filter exports accordingly
    if let Some(ref export_list) = module.exports {
        module_exports = filter_exports(
            &module_exports,
            &export_list.value,
            &local_type_set,
            &local_class_set,
            registry,
            &module.imports,
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
                }
            }
            if let Some(insts) = exports.instances.get(name) {
                instances.entry(*name).or_default().extend(insts.clone());
            }
        }
        Import::TypeOp(name) => {
            if let Some(target) = exports.type_operators.get(name) {
                ctx.type_operators.insert(*name, *target);
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

/// Filter a module's exports according to an explicit export list.
fn filter_exports(
    all: &ModuleExports,
    export_list: &crate::cst::ExportList,
    _local_types: &HashSet<Symbol>,
    _local_classes: &HashSet<Symbol>,
    registry: &ModuleRegistry,
    imports: &[crate::cst::ImportDecl],
) -> ModuleExports {
    let mut result = ModuleExports::default();

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
                        None => Vec::new(),
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
                    }
                }
                // Export instances for this class
                if let Some(insts) = all.instances.get(name) {
                    result.instances.insert(*name, insts.clone());
                }
            }
            Export::TypeOp(name) => {
                if let Some(target) = all.type_operators.get(name) {
                    result.type_operators.insert(*name, *target);
                }
            }
            Export::Module(mod_name) => {
                // Re-export everything from the named module.
                // `module X` in the export list matches either:
                // - an import whose module name equals X (e.g. `import Data.Foo`)
                // - an import whose qualified alias equals X (e.g. `import Prim.Ordering as PO` matches `module PO`)
                for import_decl in imports {
                    let matches_module = module_name_to_symbol(&import_decl.module) == module_name_to_symbol(mod_name);
                    let matches_alias = import_decl.qualified.as_ref()
                        .map(|q| module_name_to_symbol(q) == module_name_to_symbol(mod_name))
                        .unwrap_or(false);
                    if matches_module || matches_alias {
                        // Look up from registry; also check Prim submodules
                        let prim_sub;
                        let mod_exports = if is_prim_module(&import_decl.module) {
                            Some(&prim_exports())
                        } else if is_prim_submodule(&import_decl.module) {
                            prim_sub = prim_submodule_exports(&import_decl.module);
                            Some(&prim_sub)
                        } else {
                            registry.lookup(&import_decl.module.parts)
                        };
                        if let Some(mod_exports) = mod_exports {
                            // Import class methods first so we can detect conflicts
                            for (name, info) in &mod_exports.class_methods {
                                result.class_methods.insert(*name, info.clone());
                            }
                            for (name, scheme) in &mod_exports.values {
                                // Don't let a non-class value overwrite a class method's entry
                                if result.class_methods.contains_key(name) && !mod_exports.class_methods.contains_key(name) {
                                    continue;
                                }
                                result.values.insert(*name, scheme.clone());
                            }
                            for (name, ctors) in &mod_exports.data_constructors {
                                result.data_constructors.insert(*name, ctors.clone());
                            }
                            for (name, details) in &mod_exports.ctor_details {
                                result.ctor_details.insert(*name, details.clone());
                            }
                            for (name, target) in &mod_exports.type_operators {
                                result.type_operators.insert(*name, *target);
                            }
                            for (name, fixity) in &mod_exports.value_fixities {
                                result.value_fixities.insert(*name, *fixity);
                            }
                            for (name, alias) in &mod_exports.type_aliases {
                                result.type_aliases.insert(*name, alias.clone());
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

/// Check if a class has a matching instance for the given concrete type args.
/// Handles constrained instances by recursively checking that constraints are satisfied.
fn has_matching_instance(
    instances: &HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    class_name: &Symbol,
    concrete_args: &[Type],
) -> bool {
    has_matching_instance_depth(instances, class_name, concrete_args, 0)
}

fn has_matching_instance_depth(
    instances: &HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    class_name: &Symbol,
    concrete_args: &[Type],
    depth: u32,
) -> bool {
    if depth > 20 {
        // Avoid infinite recursion on circular constraint chains
        return false;
    }

    let known = match instances.get(class_name) {
        Some(k) => k,
        None => return false,
    };

    known.iter().any(|(inst_types, inst_constraints)| {
        if inst_types.len() != concrete_args.len() {
            return false;
        }

        // Try to match instance types against concrete args, building a substitution
        let mut subst: HashMap<Symbol, Type> = HashMap::new();
        let matched = inst_types
            .iter()
            .zip(concrete_args.iter())
            .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst));

        if !matched {
            return false;
        }

        // If there are no constraints, we're done
        if inst_constraints.is_empty() {
            return true;
        }

        // Check each constraint with substituted types
        inst_constraints.iter().all(|(c_class, c_args)| {
            let substituted_args: Vec<Type> =
                c_args.iter().map(|t| apply_var_subst(&subst, t)).collect();
            has_matching_instance_depth(instances, c_class, &substituted_args, depth + 1)
        })
    })
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
