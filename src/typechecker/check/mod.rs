use std::collections::{HashMap, HashSet};

use crate::span::Span;
use crate::ast::{
    Binder, Decl, Module, TypeExpr,
};
use crate::cst::{
    Associativity,
    Export, Import, ImportList, KindSigSource, QualifiedIdent,
};
mod prim;
pub use prim::*;
mod aliases;
pub(crate) use aliases::*;
mod imports;
pub(crate) use imports::*;
mod exhaustiveness;
pub(crate) use exhaustiveness::*;
mod coercible;
pub(crate) use coercible::*;
mod instances;
pub(crate) use instances::*;
mod type_utils;
pub(crate) use type_utils::*;

use crate::interner::intern;
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::{
    is_unconditional_for_exhaustiveness, InferCtx,
};
use crate::typechecker::registry::{DictExpr, ModuleExports, ModuleRegistry};
use crate::names::{self, ClassName, ConstructorName, OpName, Qualified, TypeName, TypeOpName, TypeVarName, ValueName, LabelName};
use crate::typechecker::types::{Role, Scheme, TyVarId, Type};

/// Wrap a bare Symbol as an unqualified QualifiedIdent. Only for local identifier, not for imports
#[inline]
fn qi(sym: Symbol) -> QualifiedIdent {
    QualifiedIdent {
        module: None,
        name: sym,
    }
}

// Typed equivalents of qi() for InferCtx fields that now use Qualified<N>
#[inline]
fn qi_type(sym: Symbol) -> Qualified<TypeName> {
    Qualified::unqualified(TypeName::new(sym))
}

#[inline]
fn qi_class(sym: Symbol) -> Qualified<ClassName> {
    Qualified::unqualified(ClassName::new(sym))
}

#[inline]
fn qi_value(sym: Symbol) -> Qualified<ValueName> {
    Qualified::unqualified(ValueName::new(sym))
}

#[inline]
fn qi_ctor(sym: Symbol) -> Qualified<ConstructorName> {
    Qualified::unqualified(ConstructorName::new(sym))
}

#[inline]
fn qi_op(sym: Symbol) -> Qualified<OpName> {
    Qualified::unqualified(OpName::new(sym))
}

#[inline]
fn qi_type_op(sym: Symbol) -> Qualified<TypeOpName> {
    Qualified::unqualified(TypeOpName::new(sym))
}

/// Convert Vec<Symbol> type var names to Vec<TypeVarName>
#[inline]
fn syms_to_tvs(syms: &[Symbol]) -> Vec<TypeVarName> {
    syms.iter().map(|&s| TypeVarName::new(s)).collect()
}

/// Qualify unqualified type constructors in a type with a module qualifier,
/// if they are locally-defined data/newtype/foreign types. This ensures that
/// exported instance types carry their defining module's name, so instances
/// from different modules with the same head type name (e.g., List in
/// Data.List.Types vs Data.List.Lazy.Types) remain distinguishable after import.
/// Qualify unqualified type constructors using a type origin map.
/// Recursively walks the type and adds module qualifiers to any
/// `Type::Con(Qualified { module: None, name })` where `name` appears in `origins`.
fn qualify_type_head(ty: &Type, origins: &HashMap<Symbol, names::ModuleQualifier>) -> Type {
    match ty {
        Type::Con(qi) if qi.module.is_none() => {
            if let Some(&mq) = origins.get(&qi.name.symbol()) {
                Type::Con(Qualified { module: Some(mq), name: qi.name })
            } else {
                ty.clone()
            }
        }
        Type::App(f, a) => {
            let qf = qualify_type_head(f, origins);
            let qa = qualify_type_head(a, origins);
            Type::app(qf, qa)
        }
        Type::Fun(a, b) => {
            let qa = qualify_type_head(a, origins);
            let qb = qualify_type_head(b, origins);
            Type::fun(qa, qb)
        }
        _ => ty.clone(),
    }
}

/// Result of typechecking a module: partial type map + accumulated errors + exports.
pub struct CheckResult {
    pub types: HashMap<ValueName, Type>,
    pub errors: Vec<TypeError>,
    pub exports: ModuleExports,
    /// Span→Type map for local variable bindings, for hover support.
    pub span_types: HashMap<crate::span::Span, Type>,
    /// Record update field info: span of RecordUpdate → all field names in the record type.
    /// Used by codegen to generate object literal copies instead of for-in loops.
    pub record_update_fields: HashMap<crate::span::Span, Vec<LabelName>>,
    /// Unfiltered ctor_details for ALL locally-declared types (including unexported ones).
    /// Codegen needs these for instanceof checks and derive newtype instances even when
    /// the type is not in the module's export list.
    pub all_ctor_details: HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)>,
    /// Unfiltered data_constructors for ALL locally-declared types.
    pub all_data_constructors: HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>>,
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
    instantiate_all_vars_inner(ctx, ty).0
}

fn instantiate_all_vars_inner(ctx: &mut InferCtx, ty: Type) -> (Type, HashMap<TypeVarName, Type>) {
    let function_sym = crate::interner::intern("Function");

    fn collect_vars(ty: &Type, vars: &mut HashSet<TypeVarName>) {
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
                        if name.name.matches_ident(function_sym) {
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
    let mut combined_subst: HashMap<TypeVarName, Type> = HashMap::new();
    let ty = match ty {
        Type::Forall(vars, body) => {
            let subst: HashMap<TypeVarName, Type> = vars
                .iter()
                .map(|&(v, _)| (v, Type::Unif(ctx.state.fresh_var())))
                .collect();
            combined_subst.extend(subst.iter().map(|(k, v)| (*k, v.clone())));
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
        (ty, combined_subst)
    } else {
        let subst: HashMap<TypeVarName, Type> = free_vars
            .into_iter()
            .map(|v| (v, Type::Unif(ctx.state.fresh_var())))
            .collect();
        combined_subst.extend(subst.iter().map(|(k, v)| (*k, v.clone())));
        (apply_var_subst(&subst, &ty), combined_subst)
    }
}

/// Typecheck an entire module, returning a map of top-level names to their types
/// and a list of any errors encountered. Checking continues past errors so that
/// partial results are available for tooling (e.g. IDE hover types).
pub fn check_module(module: &Module, registry: &ModuleRegistry) -> CheckResult {
    check_module_impl(module, registry, false, None)
}

pub fn check_module_with_cache(module: &Module, registry: &ModuleRegistry, cache: &crate::typechecker::registry::CodegenDictCache, collect_span_types: bool) -> CheckResult {
    check_module_impl(module, registry, collect_span_types, Some(cache))
}

pub fn check_module_for_ide(module: &Module, registry: &ModuleRegistry) -> CheckResult {
    check_module_impl(module, registry, true, None)
}

fn check_module_impl(module: &Module, registry: &ModuleRegistry, collect_span_types: bool, dict_cache: Option<&crate::typechecker::registry::CodegenDictCache>) -> CheckResult {
    let mut ctx = InferCtx::new();
    ctx.module_mode = true;
    ctx.collect_span_types = collect_span_types;
    let mut env = Env::new();
    let mut signatures: HashMap<ValueName, (crate::span::Span, Type)> = HashMap::new();
    let mut result_types: HashMap<ValueName, Type> = HashMap::new();
    let mut errors: Vec<TypeError> = Vec::new();
    // Classes that appear in explicit type signature constraints (not inferred).
    // Used to distinguish legitimate "given" constraints from inferred body constraints
    // for chain ambiguity checking in Pass 3.
    let mut explicit_sig_classes: HashSet<ClassName> = HashSet::new();

    // Track class info for instance checking
    // Each instance stores (type_args, constraints) where constraints are (class_name, constraint_type_args)
    let mut instances: HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>> =
        HashMap::new();

    // Track locally-defined instance heads for overlap checking
    // Stores (converted types, had_kind_annotations, CST types) for each instance
    let mut local_instance_heads: HashMap<
        Symbol,
        Vec<(Vec<Type>, bool, Vec<crate::ast::TypeExpr>)>,
    > = HashMap::new();

    // Track classes that have instance chains (else keyword).
    // Used during deferred constraint checking to detect ambiguous chain resolution.
    let mut chained_classes: HashSet<Qualified<ClassName>> = HashSet::new();

    // Track locally-defined names for export computation
    let mut local_values: HashMap<ValueName, Scheme> = HashMap::new();

    // Track names with Partial constraint (intentionally non-exhaustive)
    let mut partial_names: HashSet<ValueName> = HashSet::new();

    // Track class declaration spans for duplicate detection
    let mut seen_classes: HashMap<ClassName, Vec<Span>> = HashMap::new();

    // Track named instance spans for duplicate detection
    let mut seen_instance_names: HashMap<names::InstanceName, Vec<Span>> = HashMap::new();

    // newtype_names is now on ctx.newtype_names (shared via ModuleExports for Coercible)

    // Track type alias definitions for cycle detection
    let mut type_alias_defs: HashMap<TypeName, (Span, &crate::ast::TypeExpr)> = HashMap::new();

    // Track class definitions for superclass cycle detection: name → (span, superclass class names)
    let mut class_defs: HashMap<ClassName, (Span, Vec<ClassName>)> = HashMap::new();

    // Track superclass constraints per class for instance validation:
    // class name → (class type var names, superclass constraints as (class_name, type_args))
    let mut class_superclasses: HashMap<Qualified<ClassName>, (Vec<Symbol>, Vec<(Qualified<ClassName>, Vec<Type>)>)> = HashMap::new();

    // Track class type parameter counts for instance arity validation.
    let mut class_param_counts: HashMap<Qualified<ClassName>, usize> = HashMap::new();

    // Track kind signatures for orphan detection: name → span
    let mut kind_sigs: HashMap<TypeName, (Span, KindSigSource)> = HashMap::new();
    // Track names that have real definitions, categorized by declaration kind
    let mut has_real_definition: HashSet<TypeName> = HashSet::new();
    // More specific tracking: which kind of definition exists (for source-aware orphan check)
    let mut has_data_def: HashSet<TypeName> = HashSet::new();
    let mut has_type_alias_def: HashSet<TypeName> = HashSet::new();
    let mut has_newtype_def: HashSet<TypeName> = HashSet::new();
    let mut has_class_def: HashSet<ClassName> = HashSet::new();

    // Pre-scan: Collect locally-defined type and class names for orphan instance detection.
    // An instance is orphan if neither the class nor any type in the instance head is locally defined.
    let local_type_names: HashSet<TypeName> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Data { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::TypeAlias { name, .. }
            | Decl::ForeignData { name, .. } => Some(TypeName::new(name.value)),
            _ => None,
        })
        .collect();
    // Data/newtype names only (excludes type aliases) — used for orphan instance checks
    // where type aliases should be treated as transparent (expanded to their underlying type).
    let local_data_type_names: HashSet<TypeName> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Data { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::ForeignData { name, .. } => Some(TypeName::new(name.value)),
            _ => None,
        })
        .collect();
    // Concrete locally-defined data/newtype names only — excludes foreign data types.
    // Used in derive position checking to allow locally-defined types that haven't
    // been processed yet in Pass 1 declaration order to be treated as covariant.
    // Foreign data types are excluded because they're abstract and have unknown variance.
    let local_concrete_type_names: HashSet<TypeName> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Data { name, .. } | Decl::Newtype { name, .. } => Some(TypeName::new(name.value)),
            _ => None,
        })
        .collect();
    let local_class_names: HashSet<ClassName> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Class {
                name, is_kind_sig, ..
            } if !*is_kind_sig => Some(ClassName::new(name.value)),
            _ => None,
        })
        .collect();

    // Track locally-registered instances for superclass validation: (span, class_name, inst_types)
    let mut registered_instances: Vec<(Span, ClassName, Vec<Type>)> = Vec::new();
    // Instance registry: (class_name, head_type_con) → instance_name.
    // Populated during instance processing for codegen dictionary resolution.
    let mut instance_registry_entries: HashMap<(ClassName, TypeName), Symbol> = HashMap::new();
    let mut instance_module_entries: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    // Kind annotations for instance type variables (for polykinded dispatch).
    let mut instance_var_kinds_entries: HashMap<Symbol, HashMap<TypeVarName, Symbol>> = HashMap::new();

    // Deferred instance method bodies: checked after Pass 1.5 so foreign imports and fixity are available.
    // Tuple: (method_name, span, binders, guarded, where_clause, expected_type, scoped_vars, given_classes, instance_id, instance_constraints)
    let mut deferred_instance_methods: Vec<(
        ValueName,
        Span,
        &[Binder],
        &crate::ast::GuardedExpr,
        &[crate::ast::LetBinding],
        Option<Type>,
        HashSet<TypeVarName>,
        HashSet<Qualified<ClassName>>,
        usize, // instance_id: groups methods from the same instance
        Vec<(Qualified<ClassName>, Vec<Type>)>, // instance constraints (class_name, type_args)
    )> = Vec::new();
    let mut next_instance_id: usize = 0;
    // Instance method groups: each entry is the list of method names for one instance.
    // Used for CycleInDeclaration detection among sibling methods.
    let mut instance_method_groups: Vec<Vec<ValueName>> = Vec::new();

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
            let prim_qualified = Qualified::qualified(names::ModuleQualifier::new(prim_sym), TypeName::new(name.name_symbol()));
            ctx.type_con_arities.insert(prim_qualified, *prim.type_con_arities.get(name).unwrap());
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
            ctx.state.canonical_to_qualifier.insert(names::ModuleQualifier::new(canonical), names::ModuleQualifier::new(alias_sym));
            // Also register qualifier → qualifier (self-mapping) so try_expand_alias
            // recognizes the import alias as a known module when defined_types
            // canonicalization uses the qualifier (e.g. Con("Card.Action")).
            ctx.state.canonical_to_qualifier.entry(names::ModuleQualifier::new(alias_sym))
                .or_insert(names::ModuleQualifier::new(alias_sym));
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
                    let class_str = crate::interner::resolve(class_name.name_symbol()).unwrap_or_default();
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
                    .entry(qi_class(class_name.symbol()))
                    .or_insert_with(|| {
                        let (tvs, indices) = fd;
                        (tvs.clone(), indices.clone())
                    });
            }
            // Import superclass constraints for transitively expanding "given" constraints
            for (class_name, sc_info) in &exports.class_superclasses {
                class_superclasses.entry(*class_name).or_insert_with(|| {
                    let (tvs, constraints) = sc_info;
                    (tvs.iter().map(|tv| tv.symbol()).collect(), constraints.clone())
                });
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
                    ctx.type_con_arities.insert(qi_type(name.value), type_vars.len());
                }
            }
            Decl::Newtype {
                name, type_vars, ..
            } => {
                ctx.type_con_arities.insert(qi_type(name.value), type_vars.len());
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
                ctx.type_con_arities.insert(qi_type(name.value), count_kind_arrows(kind));
            }
            Decl::TypeAlias { name, .. } => {
                // Local type aliases shadow imported types, just like data/newtype declarations.
                // A ScopeConflict is only raised if the ambiguous name is actually referenced
                // (not merely declared or exported). Record the conflict for deferred checking.
                if explicitly_imported_types.contains(&crate::names::TypeName::new(name.value)) {
                    ctx.type_scope_conflicts.insert(TypeName::new(name.value));
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
                ctx.type_operators.insert(qi_type_op(operator.value), Qualified::<TypeName>::from_qi(target));
                type_fixities.insert(operator.value, (*associativity, *precedence));
            } else {
                seen_value_ops
                    .entry(operator.value)
                    .or_default()
                    .push(*span);
                ctx.value_fixities
                    .insert(OpName::new(operator.value), (*associativity, *precedence));
            }
        }
    }
    for (name, spans) in &seen_value_ops {
        if spans.len() > 1 {
            errors.push(TypeError::MultipleValueOpFixities {
                spans: spans.clone(),
                name: OpName::new(*name),
            });
        }
    }
    for (name, spans) in &seen_type_ops {
        if spans.len() > 1 {
            errors.push(TypeError::MultipleTypeOpFixities {
                spans: spans.clone(),
                name: TypeOpName::new(*name),
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
    let mut known_classes: HashSet<Qualified<ClassName>> = class_param_counts.keys().copied().collect();
    for (_, (class_name, _)) in &ctx.class_methods {
        known_classes.insert(*class_name);
    }
    for name in &local_class_names {
        known_classes.insert(Qualified::unqualified(*name));
    }

    // ===== Kind Pass: Infer and check kinds for all type declarations =====
    let saved_type_kinds: HashMap<Qualified<ClassName>, Type>;
    let saved_class_kinds: HashMap<Qualified<ClassName>, Type>;
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
                ks.qualifier_to_canonical.insert(names::ModuleQualifier::new(alias), names::ModuleQualifier::new(canonical));
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
                module_exports.type_kinds.keys().map(|k| k.symbol()).collect();

            // Compute which type names are actually imported (respecting explicit lists).
            // For `import M (Foo, Bar)`, only register kinds for Foo and Bar.
            // For `import M` or `import M hiding (...)`, register all (or filtered).
            let allowed_type_names: Option<HashSet<Symbol>> = match &import_decl.imports {
                Some(crate::cst::ImportList::Explicit(items)) => {
                    let names: HashSet<Symbol> = items.iter().filter_map(|item| match item {
                        crate::cst::Import::Type(name, _) => Some(name.value.symbol()),
                        crate::cst::Import::Class(name) => Some(name.value.symbol()),
                        _ => None,
                    }).collect();
                    Some(names)
                }
                Some(crate::cst::ImportList::Hiding(items)) => {
                    let hidden: HashSet<Symbol> = items.iter().filter_map(|item| match item {
                        crate::cst::Import::Type(name, _) => Some(name.value.symbol()),
                        crate::cst::Import::Class(name) => Some(name.value.symbol()),
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
                let type_sym = type_name.symbol();
                // Skip types not in the explicit import list
                if let Some(ref allowed) = allowed_type_names {
                    if !allowed.contains(&type_sym) {
                        continue;
                    }
                }

                if let Some(q) = qualifier {
                    // Qualify Con references in the kind to use the import qualifier
                    let qualified_kind = qualify_kind_refs(kind, q, &exported_type_names);
                    let qualified_name = qualified_symbol(q, type_sym);
                    ks.register_type(TypeName::new(qualified_name), qualified_kind);
                } else {
                    // Register under the bare name only for unqualified imports.
                    ks.register_type(TypeName::new(type_sym), kind.clone());
                }
            }
            // Import class kinds separately so they don't get overwritten by
            // data types with the same name (e.g., class Error vs data Error).
            for (&type_name, kind) in &module_exports.class_type_kinds {
                let class_sym = type_name.symbol();
                if let Some(ref allowed) = allowed_type_names {
                    if !allowed.contains(&class_sym) {
                        continue;
                    }
                }
                if let Some(q) = qualifier {
                    let qualified_kind = qualify_kind_refs(kind, q, &exported_type_names);
                    let qualified_name = qualified_symbol(q, class_sym);
                    ks.class_kinds.insert(ClassName::new(qualified_name), qualified_kind);
                } else {
                    ks.class_kinds.insert(ClassName::new(class_sym), kind.clone());
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
                let alias_sym = alias_name.name_symbol();
                // Skip aliases not in the explicit import list
                if let Some(ref allowed) = allowed_type_names {
                    if !allowed.contains(&alias_sym) {
                        continue;
                    }
                }
                let reg_sym = if let Some(q) = qualifier {
                    qualified_symbol(q, alias_sym)
                } else {
                    alias_sym
                };
                let reg_tn = TypeName::new(reg_sym);
                // Don't overwrite if already registered from type_kinds
                if ks.type_kinds.get(&reg_tn).is_none() {
                    // Build kind: ?k1 -> ?k2 -> ... -> ?kN -> ?k_result
                    let mut kind = ks.fresh_kind_var();
                    for _ in 0..params.len() {
                        kind = Type::fun(ks.fresh_kind_var(), kind);
                    }
                    ks.register_type(reg_tn, kind);
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
                ks.register_type(TypeName::new(name.value), k);
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
                let var_syms: Vec<TypeVarName> = type_vars.iter().map(|tv| TypeVarName::new(tv.value)).collect();
                if let Ok(body) = convert_type_expr(ty, &type_ops) {
                    ks.state.type_aliases.insert(Qualified::unqualified(TypeName::new(name.value)), (var_syms, body));
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
                    ks.register_type(TypeName::new(name.value), k);
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
                ks.register_class_kind(ClassName::new(name.value), k);
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
                        ks.register_type(TypeName::new(name.value), fresh);
                    }
                }
                Decl::Newtype { name, .. } => {
                    if !standalone_kinds.contains_key(&name.value) {
                        let fresh = ks.fresh_kind_var();
                        pre_assigned.insert(name.value, fresh.clone());
                        ks.register_type(TypeName::new(name.value), fresh);
                    }
                }
                Decl::TypeAlias { name, .. } => {
                    if !standalone_kinds.contains_key(&name.value) {
                        let fresh = ks.fresh_kind_var();
                        pre_assigned.insert(name.value, fresh.clone());
                        ks.register_type(TypeName::new(name.value), fresh);
                    }
                }
                Decl::Class {
                    name, is_kind_sig, ..
                } if !*is_kind_sig => {
                    if !standalone_kinds.contains_key(&name.value) {
                        let fresh = ks.fresh_kind_var();
                        pre_assigned.insert(name.value, fresh.clone());
                        ks.register_class_kind(ClassName::new(name.value), fresh);
                    }
                }
                _ => {}
            }
        }

        // Pass B: Infer actual kinds for each declaration and unify with pre-assigned vars.
        // Uses SCC analysis to identify binding groups — types in the same SCC share
        // kind variables (monomorphic inference) while independent types are freshened.
        let sccs = kind::compute_type_sccs(&module.decls);
        let scc_members: HashMap<TypeName, HashSet<TypeName>> = {
            let mut map = HashMap::new();
            for scc in &sccs {
                let set: HashSet<TypeName> = scc.iter().copied().collect();
                for &name in scc {
                    map.insert(name, set.clone());
                }
            }
            map
        };

        // Build SCC-ordered declaration list: declarations that participate in kind
        // inference are processed in SCC topological order (dependencies first) to ensure
        // kinds are resolved before use. Other declarations keep their source order.
        let scc_order: HashMap<TypeName, usize> = {
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
                    if *kind_sig == KindSigSource::None && !*is_role_decl => Some(TypeName::new(name.value)),
                Decl::Newtype { name, .. } => Some(TypeName::new(name.value)),
                Decl::TypeAlias { name, .. } => Some(TypeName::new(name.value)),
                Decl::Class { name, is_kind_sig, .. } if !*is_kind_sig => Some(TypeName::new(name.value)),
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
                } if *kind_sig == KindSigSource::None && !*is_role_decl => Some(TypeName::new(name.value)),
                Decl::Newtype { name, .. } => Some(TypeName::new(name.value)),
                Decl::TypeAlias { name, .. } => Some(TypeName::new(name.value)),
                Decl::Class {
                    name, is_kind_sig, ..
                } if !*is_kind_sig => Some(TypeName::new(name.value)),
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
                        TypeName::new(name.value),
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
                                    TypeName::new(name.value),
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
                        TypeName::new(name.value),
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
                                    TypeName::new(name.value),
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
                        TypeName::new(name.value),
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
                                ks.register_type(TypeName::new(name.value), zonked_kind);
                            } else {
                                let zonked_kind = ks.zonk_kind(inferred);
                                ks.register_type(TypeName::new(name.value), zonked_kind);
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
                        &mut ks, TypeName::new(name.value), type_vars, members, *span, &type_ops,
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
            let empty_var_kinds: HashMap<TypeVarName, Type> = HashMap::new();
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
                            let qualified = crate::interner::intern_qualified(m.symbol(), class_name.name_symbol());
                            ks.lookup_class_kind_fresh(ClassName::new(qualified))
                                .or_else(|| ks.lookup_class_kind_fresh(ClassName::new(class_name.name_symbol())))
                        } else {
                            ks.lookup_class_kind_fresh(ClassName::new(class_name.name_symbol()))
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
            .map(|(&name, kind)| (Qualified::unqualified(ClassName::new(name.symbol())), ks.state.zonk(kind.clone())))
            .collect();
        saved_class_kinds = ks
            .class_kinds
            .iter()
            .map(|(&name, kind)| (Qualified::unqualified(ClassName::new(name.symbol())), ks.state.zonk(kind.clone())))
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
            ctx.newtype_names.insert(qi_type(name.value));
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
                let params: Vec<TypeVarName> = type_vars.iter().map(|tv| TypeVarName::new(tv.value)).collect();
                // For re-exported aliases like `type X = M.X`, resolve the body
                // using the already-imported expanded alias instead of storing the
                // unexpandable qualified reference.
                let unqual_key = Qualified::unqualified(TypeName::new(name.value));
                let resolved_body = if is_alias_reexport(&body_ty, name.value, &params) {
                    if let Some((existing_params, existing_body)) = ctx.state.type_aliases.get(&unqual_key) {
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
                ctx.state.type_aliases.insert(unqual_key, (params, resolved_body));
                if matches!(ty, TypeExpr::Record { .. }) {
                    ctx.record_type_aliases.insert(qi_type(name.value));
                }
            }
        }
    }

    // Build map of type alias constraints: alias name → constraints from its definition.
    // These are stripped during convert_type_expr and lost from the Type representation,
    // but needed for codegen when a value's signature uses the alias (e.g. `three :: Expr Number`
    // where `type Expr a = forall e. E e => e a`).
    let mut type_alias_constraints: HashMap<Symbol, Vec<(Qualified<ClassName>, Vec<Type>)>> = HashMap::new();
    for decl in &module.decls {
        if let Decl::TypeAlias { name, ty, .. } = decl {
            let constraints = extract_type_signature_constraints(ty, &type_ops);
            if !constraints.is_empty() {
                type_alias_constraints.insert(name.value, constraints);
            }
        }
    }

    // Build newtype_field_constraints: for newtypes that wrap a constrained type alias,
    // map the constructor name to the alias's constraints.
    // E.g. `newtype Mailboxed = Mailboxed MailboxedT` where `MailboxedT = forall. Ord a => ...`
    // → `newtype_field_constraints["Mailboxed"] = [(Ord, [Var(a)])]`
    // Used in process_let_bindings and infer_binder to propagate hidden constraints.
    for decl in &module.decls {
        if let Decl::Newtype { constructor, ty, .. } = decl {
            use crate::ast::TypeExpr;
            let alias_sym = match ty {
                TypeExpr::Constructor { name, .. } => Some(name.name_symbol()),
                TypeExpr::App { constructor: head, .. } => {
                    fn get_head(te: &TypeExpr) -> Option<Symbol> {
                        match te {
                            TypeExpr::Constructor { name, .. } => Some(name.name_symbol()),
                            TypeExpr::App { constructor, .. } => get_head(constructor),
                            _ => None,
                        }
                    }
                    get_head(head)
                }
                _ => None,
            };
            if let Some(sym) = alias_sym {
                if let Some(alias_cs) = type_alias_constraints.get(&sym) {
                    ctx.newtype_field_constraints.insert(constructor.value, alias_cs.clone());
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
                if signatures.contains_key(&ValueName::new(name.value)) {
                    errors.push(TypeError::DuplicateTypeSignature {
                        span: *span,
                        name: ValueName::new(name.value),
                    });
                    continue;
                }
                // Check for Partial constraint (intentionally non-exhaustive functions)
                if has_partial_constraint(ty) {
                    partial_names.insert(ValueName::new(name.value));
                }
                // Check for Partial in function parameter (discharges Partial constraint)
                if has_partial_in_function_param(ty) {
                    ctx.partial_dischargers.insert(qi_value(name.value));
                }
                // Check for undefined type variables (all vars must be bound by forall)
                collect_type_expr_vars(ty, &HashSet::new(), &mut errors);
                // Validate constraint class names in the type signature
                check_constraint_class_names(ty, &known_classes, &class_param_counts, &mut errors);
                // Check for type-level scope conflicts (ambiguous type names)
                if let Some((conflict_span, conflict_name)) = crate::typechecker::convert::find_type_scope_conflict(ty, &ctx.type_scope_conflicts) {
                    errors.push(TypeError::ScopeConflict {
                        span: conflict_span,
                        name: conflict_name.symbol(),
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
                        signatures.insert(ValueName::new(name.value), (*span, converted));
                        // Extract constraints from the type signature for propagation
                        // to call sites (e.g., Lacks "x" r => ...)
                        let sig_constraints =
                            extract_type_signature_constraints(ty, &type_ops);
                        if !sig_constraints.is_empty() {
                            // Check for Fail constraints — these are deliberately unsatisfiable
                            // and should always produce NoInstanceFound at the definition site.
                            for (class_name, type_args) in &sig_constraints {
                                let cn =
                                    class_name.name.to_string();
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
                                .insert(qi_value(name.value), sig_constraints.clone());
                        }
                        // Extract return-type inner-forall constraints
                        let mut rt_constraints = extract_return_type_constraints(ty, &type_ops);
                        // Fallback: if CST-level extraction found nothing, check if the
                        // return type is a type alias that hides a forall+constraints.
                        // E.g. `foo :: forall a. a -> Foo a` where `type Foo a = forall f. Monad f => f a`
                        if rt_constraints.is_empty() {
                            let sig_ty = &signatures[&ValueName::new(name.value)].1;
                            // Only check return-type alias expansion when the sig has
                            // function arrows. For 0-arity values like `three :: Expr Number`,
                            // the constraint is top-level and goes into signature_constraints.
                            let has_arrows = matches!(find_return_type_depth(sig_ty), d if d > 0);
                            if has_arrows {
                                let ret_type = find_return_type(sig_ty);
                                let expanded_ret = expand_type_aliases_limited(ret_type, &ctx.state.type_aliases, 0);
                                if matches!(&expanded_ret, Type::Forall(..)) {
                                    if let Some(alias_name) = extract_type_head_name(ret_type) {
                                        if let Some(alias_cs) = type_alias_constraints.get(&alias_name) {
                                            rt_constraints = alias_cs.clone();
                                        }
                                    }
                                }
                            }
                        }
                        if !rt_constraints.is_empty() {
                            let depth = count_return_type_arrow_depth(ty);
                            ctx.return_type_constraints
                                .insert(qi_value(name.value), rt_constraints.clone());
                            ctx.return_type_arrow_depth
                                .insert(qi_value(name.value), depth);
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
                    kind_sigs.entry(TypeName::new(name.value)).or_insert((*span, *kind_sig));
                } else {
                    has_real_definition.insert(TypeName::new(name.value));
                    has_data_def.insert(TypeName::new(name.value));
                }

                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                let type_var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();

                // Build the result type: TypeName tv1 tv2 ...
                let mut result_type = Type::Con(qi_type(name.value));
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(TypeVarName::new(tv)));
                }

                // Register constructors for exhaustiveness checking.
                // Skip if this is a kind/role annotation (empty constructors) and
                // the type already has constructors registered (e.g. from a Newtype).
                let ctor_names: Vec<Qualified<ConstructorName>> =
                    constructors.iter().map(|c| qi_ctor(c.name.value)).collect();
                if !ctor_names.is_empty() || !ctx.data_constructors.contains_key(&qi_type(name.value)) {
                    ctx.data_constructors.insert(qi_type(name.value), ctor_names);
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
                        qi_ctor(ctor.name.value),
                        (qi_type(name.value), syms_to_tvs(&type_var_syms), field_types.clone()),
                    );

                    let mut ctor_ty = result_type.clone();
                    for field_ty in field_types.into_iter().rev() {
                        ctor_ty = Type::fun(field_ty, ctor_ty);
                    }

                    // Wrap in Forall if there are type variables
                    // Data constructor type vars are always visible for VTA
                    if !type_var_syms.is_empty() {
                        ctor_ty = Type::Forall(
                            type_var_syms.iter().map(|&v| (TypeVarName::new(v), true)).collect(),
                            Box::new(ctor_ty),
                        );
                    }

                    let scheme = Scheme::mono(ctor_ty);
                    env.insert_scheme(ValueName::new(ctor.name.value), scheme.clone());
                    local_values.insert(ValueName::new(ctor.name.value), scheme);
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
                has_real_definition.insert(TypeName::new(name.value));
                has_newtype_def.insert(TypeName::new(name.value));
                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Track as a newtype for derive validation and Coercible solving
                ctx.newtype_names.insert(qi_type(name.value));

                // Register constructor for exhaustiveness checking
                ctx.data_constructors
                    .insert(qi_type(name.value), vec![qi_ctor(constructor.value)]);

                let type_var_syms: Vec<Symbol> = type_vars.iter().map(|tv| tv.value).collect();

                let mut result_type = Type::Con(qi_type(name.value));
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(TypeVarName::new(tv)));
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
                            qi_ctor(constructor.value),
                            (
                                qi_type(name.value),
                                syms_to_tvs(&type_var_syms),
                                vec![field_ty.clone()],
                            ),
                        );

                        let mut ctor_ty = Type::fun(field_ty, result_type);

                        // Newtype constructor type vars are always visible for VTA
                        if !type_var_syms.is_empty() {
                            ctor_ty = Type::Forall(
                                type_var_syms.iter().map(|&v| (TypeVarName::new(v), true)).collect(),
                                Box::new(ctor_ty),
                            );
                        }

                        let scheme = Scheme::mono(ctor_ty);
                        env.insert_scheme(ValueName::new(constructor.value), scheme.clone());
                        local_values.insert(ValueName::new(constructor.value), scheme);
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
                        name: ValueName::new(name.value),
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
                        env.insert_scheme(ValueName::new(name.value), scheme.clone());
                        local_values.insert(ValueName::new(name.value), scheme);
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
                        .entry(TypeName::new(name.value))
                        .or_insert((*span, KindSigSource::Class));
                } else {
                    has_real_definition.insert(TypeName::new(name.value));
                    has_class_def.insert(ClassName::new(name.value));
                }

                // Track class for duplicate detection (skip kind signatures)
                if !is_kind_sig {
                    seen_classes.entry(ClassName::new(name.value)).or_default().push(*span);

                    // Collect superclass names for cycle detection
                    // Skip qualified superclass refs — P.Show refers to an
                    // imported class, not the locally-defined one.
                    let superclass_names: Vec<ClassName> = constraints
                        .iter()
                        .filter(|c| c.class.module.is_none())
                        .map(|c| c.class.name)
                        .collect();
                    class_defs.insert(ClassName::new(name.value), (*span, superclass_names));

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
                    let mut sc_constraints: Vec<(Qualified<ClassName>, Vec<Type>)> = Vec::new();
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
                    class_superclasses.insert(qi_class(name.value), (tvs.clone(), sc_constraints));

                    // Store functional dependencies as index pairs for orphan checking
                    if !fundeps.is_empty() {
                        let fd_indices: Vec<(Vec<usize>, Vec<usize>)> = fundeps
                            .iter()
                            .filter_map(|fd| {
                                let lhs: Vec<usize> = fd
                                    .lhs
                                    .iter()
                                    .filter_map(|v| tvs.iter().position(|tv| *tv == v.symbol()))
                                    .collect();
                                let rhs: Vec<usize> = fd
                                    .rhs
                                    .iter()
                                    .filter_map(|v| tvs.iter().position(|tv| *tv == v.symbol()))
                                    .collect();
                                if lhs.len() == fd.lhs.len() && rhs.len() == fd.rhs.len() {
                                    Some((lhs, rhs))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        ctx.class_fundeps
                            .insert(qi_class(name.value), (syms_to_tvs(&tvs), fd_indices));
                    }

                    // Track class type parameter count for arity checking
                    class_param_counts.insert(qi_class(name.value), type_vars.len());
                    known_classes.insert(qi_class(name.value));
                    // A locally-defined class shadows any Prim magic class with the same name
                    ctx.prim_class_names.remove(&ClassName::new(name.value));
                }

                // Check for duplicate type arguments
                check_duplicate_type_args(type_vars, &mut errors);

                // Check superclass constraints only reference bound type vars
                // and that superclass classes exist
                if !is_kind_sig {
                    let bound_vars: HashSet<TypeVarName> = type_vars.iter().map(|tv| TypeVarName::new(tv.value)).collect();
                    for constraint in constraints {
                        for arg in &constraint.args {
                            collect_type_expr_vars(arg, &bound_vars, &mut errors);
                        }
                        // Check that superclass is a known class
                        if constraint.class.module.is_none() {
                            let constraint_class_typed = constraint.class;
                            let sc_known = class_param_counts.contains_key(&constraint_class_typed)
                                || instances.contains_key(&constraint_class_typed)
                                || local_class_names.contains(&ClassName::new(constraint.class.name_symbol()));
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
                        let mut constraint_details: Vec<(Qualified<ClassName>, Vec<Type>)> = Vec::new();
                        fn extract_constraint_classes(ty: &crate::ast::TypeExpr, out: &mut Vec<Symbol>) {
                            match ty {
                                crate::ast::TypeExpr::Constrained { constraints, ty, .. } => {
                                    for c in constraints {
                                        out.push(c.class.name_symbol());
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
                            type_ops: &HashMap<Qualified<TypeOpName>, Qualified<TypeName>>,
                            out: &mut Vec<(Qualified<ClassName>, Vec<Type>)>,
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
                            ctx.constrained_class_methods.insert(ValueName::new(member.name.value));
                            ctx.method_own_constraints.insert(ValueName::new(member.name.value), constraint_classes.iter().map(|&s| ClassName::new(s)).collect());
                        }
                        if !constraint_details.is_empty() {
                            ctx.method_own_constraint_details.insert(ValueName::new(member.name.value), constraint_details.clone());
                        }
                    }
                    match convert_type_expr(&member.ty, &type_ops) {
                        Ok(member_ty) => {
                            // Class header type vars are always visible for VTA
                            let scheme_ty = if !type_var_syms.is_empty() {
                                Type::Forall(
                                    type_var_syms.iter().map(|&v| (TypeVarName::new(v), true)).collect(),
                                    Box::new(member_ty),
                                )
                            } else {
                                member_ty
                            };
                            let scheme = Scheme::mono(scheme_ty);
                            env.insert_scheme(ValueName::new(member.name.value), scheme.clone());
                            local_values.insert(ValueName::new(member.name.value), scheme.clone());
                            // Save the canonical scheme so instance method expected-type
                            // lookup can use it without being affected by later value
                            // imports that shadow the same name in the env.
                            ctx.class_method_schemes.insert(ValueName::new(member.name.value), scheme.clone());
                            // Track that this method belongs to this class
                            ctx.class_methods.insert(
                                qi_value(member.name.value),
                                (qi_class(name.value), syms_to_tvs(&type_var_syms)),
                            );
                        }
                        Err(e) => errors.push(e),
                    }
                }
                // Record class method declaration order for codegen
                let method_order: Vec<ValueName> = members.iter().map(|m| ValueName::new(m.name.value)).collect();
                ctx.class_method_order.insert(ClassName::new(name.value), method_order);
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
                        .entry(names::InstanceName::new(iname.value))
                        .or_default()
                        .push(*span);
                }

                // Reject user-written Coercible instances (compiler-solved only)
                {
                    if class_name.name.eq_str("Coercible")
                        && ctx.prim_class_names.contains(&class_name.name)
                    {
                        errors.push(TypeError::InvalidCoercibleInstanceDeclaration { span: *span });
                        continue;
                    }
                }

                // Convert class name to typed form early for all instance processing
                let class_name_typed = *class_name;
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
                    if let Some(&expected_count) = class_param_counts.get(&class_name_typed) {
                        if expected_count != usize::MAX && inst_types.len() != expected_count {
                            errors.push(TypeError::ClassInstanceArityMismatch {
                                span: *span,
                                class_name: class_name_typed,
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
                let mut inst_constraints: Vec<(Qualified<ClassName>, Vec<Type>)> = Vec::new();
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
                let constraint_scoped_vars: Vec<TypeVarName> = {
                    let mut vars = Vec::new();
                    fn collect_vars_from_type(ty: &Type, vars: &mut Vec<TypeVarName>) {
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
                let class_known = class_param_counts.contains_key(&class_name_typed)
                    || instances.contains_key(&class_name_typed)
                    || local_class_names.contains(&ClassName::new(class_name.name_symbol()));

                // If the class doesn't exist at all, report it
                if inst_ok && !class_known && class_name.module.is_none() {
                    errors.push(TypeError::UnknownClass {
                        span: *span,
                        name: class_name_typed,
                    });
                }

                // Check for orphan instances: the instance must be in a module that
                // defines either the class or at least one type in the instance head.
                // With functional dependencies, every covering set must have at least
                // one locally-defined type.
                if inst_ok && !*is_chain && class_known {
                    let class_is_local = local_class_names.contains(&ClassName::new(class_name.name_symbol()));
                    if !class_is_local {
                        let is_orphan = check_orphan_with_fundeps(
                            &inst_types,
                            &class_name_typed,
                            &ctx.class_fundeps,
                            &local_type_names,
                        );
                        if is_orphan {
                            errors.push(TypeError::OrphanInstance {
                                span: *span,
                                class_name: class_name_typed,
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
                            if let Some((_, fds)) = ctx.class_fundeps.get(&class_name_typed) {
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
                let inst_subst: HashMap<TypeVarName, Type> = if inst_ok {
                    let class_tvs: Option<&Vec<TypeVarName>> = ctx
                        .class_methods
                        .values()
                        .find(|(cn, _)| *cn == class_name_typed)
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
                        if let Some(existing) = local_instance_heads.get(&class_name.name_symbol()) {
                            for (existing_types, existing_has_kind, existing_cst) in existing {
                                // When kind annotations are present, compare CST types
                                // (which preserve kind info) to avoid false positives
                                // from instances that differ only in kind annotations
                                if has_kind_ann || *existing_has_kind {
                                    if type_exprs_alpha_eq_list(types, existing_cst) {
                                        errors.push(TypeError::OverlappingInstances {
                                            span: *span,
                                            class_name: class_name_typed,
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
                                        class_name: class_name_typed,
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
                            && !local_class_names.contains(&ClassName::new(class_name.name_symbol()))
                            && inst_types.iter().all(|t| !type_has_vars(t))
                        {
                            if let Some(imported) = lookup_instances(&instances, &class_name_typed) {
                                for (existing_types, _, _) in imported {
                                    // Skip if the imported instance uses a type constructor with the
                                    // same name as a locally-defined type — they're actually different
                                    // types from different modules that happen to share a short name.
                                    let imported_shadows_local = existing_types.iter().any(|t| {
                                        fn has_local_con(
                                            ty: &Type,
                                            locals: &HashSet<crate::names::TypeName>,
                                        ) -> bool {
                                            match ty {
                                                Type::Con(n) => {
                                                    n.module.is_none() && locals.contains(&crate::names::TypeName::new(n.name_symbol()))
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
                                            class_name: class_name_typed,
                                            type_args: inst_types.clone(),
                                        });
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    local_instance_heads
                        .entry(class_name.name_symbol())
                        .or_default()
                        .push((inst_types.clone(), has_kind_ann, types.clone()));
                    registered_instances.push((*span, ClassName::new(class_name.name_symbol()), inst_types.clone()));
                    // Store instances with unqualified class name key.
                    // Class names may have import alias qualifiers (e.g. Filterable.Filterable)
                    // but internal maps should use unqualified keys.
                    let unqual_class = qi_class(class_name.name_symbol());
                    // Populate instance_registry for codegen dict resolution.
                    // Register under all extractable head type constructors for
                    // multi-parameter type classes (e.g., MonadState s (State s)).
                    if let Some(iname) = inst_name {
                        for head in extract_all_head_type_cons(&inst_types) {
                            instance_registry_entries
                                .entry((ClassName::new(class_name.name_symbol()), TypeName::new(head)))
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
                            let class_str = class_name.name.resolve().unwrap_or_default();
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
                                    .entry((ClassName::new(class_name.name_symbol()), TypeName::new(*h)))
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
                        .filter(|(_, (cn, _))| *cn == class_name_typed)
                        .map(|(method, _)| method.name_symbol())
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
                                    name: ValueName::new(*method_name),
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
                                let is_known_class_method = ctx.class_methods.contains_key(&qi_value(*method_name));
                                if !is_known_class_method {
                                    errors.push(TypeError::ExtraneousClassMember {
                                        span: *span,
                                        class_name: *class_name,
                                        member_name: ValueName::new(*method_name),
                                    });
                                }
                            }
                        }

                        // Check for missing members (expected but not provided)
                        let missing: Vec<(ValueName, Type)> = expected_methods
                            .iter()
                            .filter(|m| !provided_methods.contains(m))
                            .filter_map(|m| env.lookup(ValueName::new(*m)).map(|scheme| (ValueName::new(*m), scheme.ty.clone())))
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
                    .filter(|(_, (cn, _))| *cn == class_name_typed)
                    .map(|(method, _)| method.name_symbol())
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
                                name: ValueName::new(sig_name.value),
                            });
                        } else if inst_ok && !inst_subst.is_empty() {
                            // Check that instance method signature matches the class-derived type.
                            // Use class_method_schemes (not env.lookup) so that an explicit value
                            // import like `import Data.Array (foldl)` doesn't shadow the class
                            // method's canonical type here.
                            let canon = ctx.class_method_schemes.get(&ValueName::new(sig_name.value))
                                .map(|s| s.ty.clone())
                                .or_else(|| env.lookup(ValueName::new(sig_name.value)).map(|s| s.ty.clone()));
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
                                                Type::Var(v) if v.matches_ident(wildcard) => Type::Unif(ctx.state.fresh_var()),
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
                let mut inst_scoped_vars: HashSet<TypeVarName> = HashSet::new();
                fn collect_free_vars_inst(ty: &Type, vars: &mut HashSet<TypeVarName>) {
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
                let mut method_sig_vars: HashMap<Symbol, HashSet<TypeVarName>> = HashMap::new();
                for member_decl in members {
                    if let Decl::TypeSignature { name, ty, .. } = member_decl {
                        let mut vars = HashSet::new();
                        fn collect_forall_vars_from_type_expr(ty: &TypeExpr, vars: &mut HashSet<TypeVarName>) {
                            match ty {
                                TypeExpr::Forall { vars: forall_vars, ty, .. } => {
                                    for (v, _, _) in forall_vars {
                                        vars.insert(TypeVarName::new(v.value));
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
                let inst_constraints_for_codegen: Vec<(Qualified<ClassName>, Vec<Type>)> = constraints.iter().filter_map(|c| {
                    let mut args = Vec::new();
                    for arg in &c.args {
                        match convert_type_expr(arg, &type_ops) {
                            Ok(ty) => args.push(ty),
                            Err(_) => return None,
                        }
                    }
                    Some((c.class, args))
                }).collect();
                let mut method_names: Vec<ValueName> = Vec::new();
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
                        let expected_ty_and_subst = if inst_ok && !inst_subst.is_empty()
                        {
                            let canon = ctx.class_method_schemes.get(&ValueName::new(name.value))
                                .map(|s| s.ty.clone())
                                .or_else(|| env.lookup(ValueName::new(name.value)).map(|s| s.ty.clone()));
                            if let Some(class_ty) = canon {
                                // Strip outer forall (class type vars)
                                let inner = match &class_ty {
                                    Type::Forall(_, body) => (**body).clone(),
                                    other => other.clone(),
                                };
                                // Apply class type var substitution
                                let substituted = apply_var_subst(&inst_subst, &inner);
                                // Instantiate method-level forall and remaining free type vars
                                // with fresh unif vars. Capture the TypeVar→Unif subst so we can
                                // convert given constraints to Unif form for ConstraintArg matching.
                                let (instantiated, inst_var_to_unif) = instantiate_all_vars_inner(&mut ctx, substituted);
                                Some((instantiated, inst_var_to_unif))
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        let (expected_ty, inst_var_to_unif) = match expected_ty_and_subst {
                            Some((ty, subst)) => (Some(ty), subst),
                            None => (None, HashMap::new()),
                        };

                        // Convert inst_constraints_for_codegen from TypeVar form to Unif form
                        // using the per-method TypeVar→Unif subst. This enables correct
                        // ConstraintArg matching in resolve_dict_expr_from_registry_inner when
                        // multiple same-class constraints exist (e.g., Show c, Show a, Show n).
                        let inst_constraints_unif: Vec<(Qualified<ClassName>, Vec<Type>)> =
                            if inst_var_to_unif.is_empty() {
                                inst_constraints_for_codegen.clone()
                            } else {
                                inst_constraints_for_codegen.iter().map(|(cls, args)| {
                                    let new_args = args.iter()
                                        .map(|t| apply_var_subst(&inst_var_to_unif, t))
                                        .collect();
                                    (cls.clone(), new_args)
                                }).collect()
                            };

                        // Include forall-bound vars from the method's explicit type annotation
                        let mut method_scoped = inst_scoped_vars.clone();
                        if let Some(sig_vars) = method_sig_vars.get(&name.value) {
                            method_scoped.extend(sig_vars);
                        }

                        let inst_given_classes: HashSet<Qualified<ClassName>> =
                            constraints.iter().map(|c| c.class).collect();
                        method_names.push(ValueName::new(name.value));
                        deferred_instance_methods.push((
                            ValueName::new(name.value),
                            *span,
                            binders as &[_],
                            guarded,
                            where_clause as &[_],
                            expected_ty,
                            method_scoped,
                            inst_given_classes,
                            next_instance_id,
                            inst_constraints_unif,
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
                has_real_definition.insert(TypeName::new(name.value));
                has_type_alias_def.insert(TypeName::new(name.value));
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
                        let params: Vec<TypeVarName> = type_vars.iter().map(|tv| TypeVarName::new(tv.value)).collect();
                        // Check that free type variables in the body are all declared parameters
                        let param_set: HashSet<TypeVarName> = params.iter().copied().collect();
                        let wildcard_tv = TypeVarName::new(crate::interner::intern("_"));
                        for fv in free_named_type_vars(&body_ty) {
                            if fv != wildcard_tv && !param_set.contains(&fv) {
                                errors.push(TypeError::UndefinedTypeVariable {
                                    span: *span,
                                    name: fv,
                                });
                            }
                        }
                        // For re-exported aliases, resolve the body using the
                        // already-imported expanded alias.
                        let unqual_key = Qualified::unqualified(TypeName::new(name.value));
                        let resolved_body = if is_alias_reexport(&body_ty, name.value, &params) {
                            if let Some((existing_params, existing_body)) = ctx.state.type_aliases.get(&unqual_key) {
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
                        ctx.state.type_aliases.insert(unqual_key, (params, resolved_body));
                        // Track if this is a record-kind alias (body is { } syntax, kind Type)
                        if matches!(ty, TypeExpr::Record { .. }) {
                            ctx.record_type_aliases.insert(qi_type(name.value));
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
                type_alias_defs.insert(TypeName::new(name.value), (*span, ty));
            }
            Decl::ForeignData { name, .. } => {
                has_real_definition.insert(TypeName::new(name.value));
                has_data_def.insert(TypeName::new(name.value));
                // Register foreign data types in data_constructors so they can be imported
                // as types (e.g. `import Data.Unit (Unit)`). They have no constructors.
                ctx.data_constructors.insert(qi_type(name.value), Vec::new());
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
                let derive_class_name_typed = *class_name;
                let derive_class_known = class_param_counts.contains_key(&derive_class_name_typed)
                    || instances.contains_key(&derive_class_name_typed)
                    || local_class_names.contains(&ClassName::new(class_name.name_symbol()));
                if !derive_class_known && class_name.module.is_none() {
                    errors.push(TypeError::UnknownClass {
                        span: *span,
                        name: derive_class_name_typed,
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
                if class_name.name_symbol() == newtype_ident && types.len() >= 2 {
                    if !matches!(types.last(), Some(TypeExpr::Wildcard { .. })) {
                        errors.push(TypeError::ExpectedWildcard {
                            span: *span,
                            name: class_name.map(names::class_as_type),
                        });
                    }
                }

                if let Some(target_name) = target_type_name {
                    let target_typed = target_name;
                    let is_newtype = ctx.newtype_names.contains(&target_typed)
                        || ctx.newtype_names.iter().any(|n| n.name_symbol() == target_name.name_symbol());

                    // InvalidNewtypeInstance: derive instance Newtype X _
                    // where X is not actually a newtype
                    if class_name.name_symbol() == newtype_ident && !is_newtype
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
                            if let Some(ctors) = ctx.data_constructors.get(&target_typed) {
                                if let Some(ctor_name) = ctors.first() {
                                    if let Some((_, _, field_types)) =
                                        ctx.ctor_details.get(ctor_name)
                                    {
                                        if let Some(inner_ty) = field_types.first() {
                                            if matches!(inner_ty, Type::Var(_)) {
                                                errors.push(TypeError::InvalidNewtypeInstance {
                                                    span: *span,
                                                    name: target_name,
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
                        name: class_name.map(names::class_as_type),
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
                    if let Some(&expected_count) = class_param_counts.get(&derive_class_name_typed) {
                        if expected_count != usize::MAX && inst_types.len() != expected_count {
                            errors.push(TypeError::ClassInstanceArityMismatch {
                                span: *span,
                                class_name: derive_class_name_typed,
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
                    let class_is_local = local_class_names.contains(&ClassName::new(class_name.name_symbol()));
                    if !class_is_local {
                        // Check unexpanded types first, using only data/newtype names
                        // (not type aliases, which are transparent for orphan checking).
                        let is_orphan_unexpanded = check_orphan_with_fundeps(
                            &inst_types,
                            &derive_class_name_typed,
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
                                &derive_class_name_typed,
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
                    if class_name.name_symbol() == eq_sym || class_name.name_symbol() == ord_sym {
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
                            let target_typed2 = target_name;
                            if let Some(ctors) = ctx.data_constructors.get(&target_typed2) {
                                'open_row_check: for ctor in ctors {
                                    if let Some((_, type_vars, field_types)) =
                                        ctx.ctor_details.get(ctor)
                                    {
                                        // Build substitution from data-decl type vars to instance args
                                        let subst: HashMap<TypeVarName, Type> = type_vars
                                            .iter()
                                            .zip(derive_args.iter())
                                            .map(|(v, t)| (*v, t.clone()))
                                            .collect();
                                        for field_ty in field_types {
                                            let concrete = apply_var_subst(&subst, field_ty);
                                            if has_open_record_row(&concrete) {
                                                errors.push(TypeError::NoInstanceFound {
                                                    span: *span,
                                                    class_name: *class_name,
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

                        if class_name.name_symbol() == functor_sym
                            || class_name.name_symbol() == foldable_sym
                            || class_name.name_symbol() == traversable_sym
                        {
                            // Single covariant: last var must be covariant
                            var_checks.push((0, true));
                        } else if class_name.name_symbol() == contravariant_sym {
                            // Single contravariant: last var must be contravariant
                            var_checks.push((0, false));
                        } else if class_name.name_symbol() == bifunctor_sym {
                            // Both last two vars must be covariant
                            var_checks.push((0, true));
                            var_checks.push((1, true));
                        } else if class_name.name_symbol() == profunctor_sym {
                            // Last var covariant, second-to-last contravariant
                            var_checks.push((0, true));
                            var_checks.push((1, false));
                        }

                        if !var_checks.is_empty() {
                            // Foldable/Traversable can't derive through forall types
                            // (can't extract values from quantified types), but
                            // Functor/Contravariant/Bifunctor/Profunctor can (wrap in lambda)
                            let allow_forall = class_name.name_symbol() != foldable_sym
                                && class_name.name_symbol() != traversable_sym;

                            // Build type variable → class constraint map from derive constraints
                            let mut tyvar_classes: HashMap<TypeVarName, Vec<Symbol>> = HashMap::new();
                            for constraint in constraints {
                                // Extract type vars from constraint args (e.g. `Functor f` → f → [Functor])
                                for arg in &constraint.args {
                                    if let crate::ast::TypeExpr::Var { name, .. } = arg {
                                        tyvar_classes
                                            .entry(TypeVarName::new(name.value))
                                            .or_default()
                                            .push(constraint.class.name_symbol());
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

                            let target_typed3 = target_name;
                            if let Some(ctors) = ctx.data_constructors.get(&target_typed3) {
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
                                        let mut field_subst: HashMap<TypeVarName, Type> = HashMap::new();
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
                                                        var.symbol(),
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

                let mut inst_constraints: Vec<(Qualified<ClassName>, Vec<Type>)> = Vec::new();
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
                    if class_name.name_symbol() == generic_sym {
                        if let Some(target_name) = target_type_name {
                            let wildcard_sym = crate::interner::intern("_");
                            if inst_types.iter().any(|t| matches!(t, Type::Var(v) if v.matches_ident(wildcard_sym))) {
                                if let Some(rep_type) = compute_generic_rep_type(
                                    &target_name,
                                    &ctx.data_constructors,
                                    &ctx.ctor_details,
                                ) {
                                    for ty in inst_types.iter_mut() {
                                        if matches!(ty, Type::Var(v) if v.matches_ident(wildcard_sym)) {
                                            *ty = rep_type.clone();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if inst_ok {
                    registered_instances.push((*span, ClassName::new(class_name.name_symbol()), inst_types.clone()));
                    // Populate instance_registry for codegen dict resolution (same as Decl::Instance)
                    if let Some(iname) = derive_inst_name {
                        for head in extract_all_head_type_cons(&inst_types) {
                            instance_registry_entries
                                .entry((ClassName::new(class_name.name_symbol()), TypeName::new(head)))
                                .or_insert(iname.value);
                        }
                        let module_parts: Vec<Symbol> = module.name.value.parts.clone();
                        instance_module_entries.insert(iname.value, module_parts);
                    } else {
                        // Anonymous derive instances: generate a name for codegen dict resolution.
                        // Mirrors the logic for anonymous Decl::Instance (above).
                        let all_heads = extract_all_head_type_cons(&inst_types);
                        if !all_heads.is_empty() {
                            let class_str = class_name.name.resolve().unwrap_or_default();
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
                                    .entry((ClassName::new(class_name.name_symbol()), TypeName::new(*h)))
                                    .or_insert(gen_sym);
                            }
                            let module_parts: Vec<Symbol> = module.name.value.parts.clone();
                            instance_module_entries.insert(gen_sym, module_parts);
                        }
                    }
                    let inst_name_sym = derive_inst_name.as_ref().map(|n| n.value);
                    instances
                        .entry(qi_class(class_name.name_symbol()))
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
            KindSigSource::Class => has_class_def.contains(&ClassName::new(name.symbol())),
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
                                name: TypeName::new(role_name),
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
                                    name: TypeName::new(role_name),
                                });
                            } else if role_count != arity {
                                errors.push(TypeError::RoleDeclarationArityMismatch {
                                    span: role_span,
                                    name: TypeName::new(role_name),
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
                                ctx.type_roles.insert(TypeName::new(role_name), roles);
                            }
                        }
                        _ => {
                            errors.push(TypeError::OrphanRoleDeclaration {
                                span: role_span,
                                name: TypeName::new(role_name),
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
                    if arity > 0 && !ctx.type_roles.contains_key(&TypeName::new(name.value)) {
                        ctx.type_roles
                            .insert(TypeName::new(name.value), vec![Role::Nominal; arity]);
                    }
                }
                _ => {}
            }
        }

        // Track which types have explicitly declared roles (from `type role` declarations)
        let declared_role_types: HashSet<TypeName> = ctx.type_roles.keys().copied().collect();

        // Pre-initialize all non-declared types with Phantom roles.
        // This is essential for mutually recursive types: without it, looking up
        // a not-yet-computed type defaults to Representational, which propagates
        // incorrectly. Starting from Phantom and iterating upward gives the correct
        // least-restrictive fixed point.
        for (type_name, (type_vars, _)) in &type_ctor_fields {
            if !declared_role_types.contains(&TypeName::new(*type_name)) {
                ctx.type_roles
                    .insert(TypeName::new(*type_name), vec![Role::Phantom; type_vars.len()]);
            }
        }

        // Iterate to a fixed point for mutually recursive types (limited iterations)
        for _ in 0..10 {
            let mut changed = false;
            for (type_name, (type_vars, ctor_fields)) in &type_ctor_fields {
                if declared_role_types.contains(&TypeName::new(*type_name)) {
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
                let existing = ctx.type_roles.get(&TypeName::new(*type_name));
                if existing.map_or(true, |e| e != &inferred) {
                    ctx.type_roles.insert(TypeName::new(*type_name), inferred);
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
            let declared = match ctx.type_roles.get(&TypeName::new(*type_name)) {
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
                                    name: TypeName::new(*type_name),
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
    {
        let type_alias_defs_sym: HashMap<Symbol, (Span, &crate::ast::TypeExpr)> =
            type_alias_defs.iter().map(|(k, v)| (k.symbol(), *v)).collect();
        check_type_synonym_cycles(&type_alias_defs_sym, &mut errors);
    }

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
                            name: TypeName::new(name),
                            span,
                            names_in_cycle: cycle.iter().map(|n| TypeName::new(*n)).collect(),
                            spans: cycle_spans,
                        });
                    }
                }
            }
        }
    }

    // Check for cycles in type class superclass declarations
    {
        let class_defs_sym: HashMap<Symbol, (Span, Vec<Symbol>)> = class_defs
            .iter()
            .map(|(k, (span, supers))| {
                (k.symbol(), (*span, supers.iter().map(|s| s.symbol()).collect()))
            })
            .collect();
        check_type_class_cycles(&class_defs_sym, &mut errors);
    }

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
                name: name.symbol(),
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
            if let Some(scheme) = local_values.get(&ValueName::new(target.name)).cloned() {
                env.insert_scheme(ValueName::new(operator.value), scheme.clone());
                local_values.insert(ValueName::new(operator.value), scheme);
            } else if let Some(scheme) = env.lookup(ValueName::new(target.name)).cloned() {
                // Only use env fallback if scheme has no unresolved unif vars
                // (imported schemes are fully resolved; local failures have raw unif vars)
                if ctx.state.free_unif_vars(&scheme.ty).is_empty() {
                    env.insert_scheme(ValueName::new(operator.value), scheme.clone());
                    local_values.insert(ValueName::new(operator.value), scheme);
                }
            } else if let Some(m) = target.module {
                // Try qualified name (e.g. `infixl 9 S.compose as <.` where
                // compose is imported as `import Control.Semigroupoid as S`)
                let qualified = qualified_symbol(m, target.name);
                if let Some(scheme) = env.lookup(ValueName::new(qualified)).cloned() {
                    if ctx.state.free_unif_vars(&scheme.ty).is_empty() {
                        env.insert_scheme(ValueName::new(operator.value), scheme.clone());
                        local_values.insert(ValueName::new(operator.value), scheme);
                    }
                }
            }
            // If the target is a data constructor, register the operator→constructor mapping
            // so exhaustiveness checking recognizes operator patterns (e.g. `:` for `Cons`).
            if ctx.ctor_details.contains_key(&Qualified::<ConstructorName>::from_qi(target)) {
                ctx.ctor_details
                    .insert(qi_ctor(operator.value), ctx.ctor_details[&Qualified::<ConstructorName>::from_qi(target)].clone());
            }
        }
    }

    // Pass 1.6: Typecheck deferred instance method bodies
    // Pre-insert all values with type signatures so they're available during
    // instance method checking (e.g. stateL used in Functor (StateL s) instance)
    for decl in &module.decls {
        if let Decl::Value { name, .. } = decl {
            if let Some((_, sig_ty)) = signatures.get(&ValueName::new(name.value)) {
                env.insert_scheme(ValueName::new(name.value), Scheme::mono(ctx.state.zonk(sig_ty.clone())));
            } else if !env.lookup(ValueName::new(name.value)).is_some() {
                // Pre-insert fresh unification variables for unsignatured values
                // so instance methods can reference them (e.g. runState)
                let fresh = Type::Unif(ctx.state.fresh_var());
                env.insert_mono(ValueName::new(name.value), fresh);
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
            if let Some((_, sig_ty)) = signatures.get(&ValueName::new(target.name)) {
                env.insert_scheme(ValueName::new(operator.value), Scheme::mono(sig_ty.clone()));
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
            if ctx.ctor_details.contains_key(&Qualified::<ConstructorName>::from_qi(target))
                || ctx.ctor_details.contains_key(&qi_ctor(target.name))
            {
                // Constructor target: remove any inherited function alias flag
                ctx.function_op_aliases.remove(&qi_op(operator.value));
            } else {
                ctx.function_op_aliases.insert(qi_op(operator.value));
            }
            // Track operator → class method target for deferred constraint tracking.
            // Local fixity overrides imported mapping, so remove if new target isn't a class method.
            if ctx.class_methods.contains_key(&Qualified::<ValueName>::from_qi(target)) {
                ctx.operator_class_targets
                    .insert(qi_op(operator.value), Qualified::<ValueName>::from_qi(target));
            } else {
                ctx.operator_class_targets.remove(&qi_op(operator.value));
                // Local fixity redefines the operator to a non-class-method target.
                // Remove any imported constraints so the typechecker doesn't try to
                // resolve constraints (e.g. Semigroupoid) for the new target.
                ctx.signature_constraints.remove(&qi_op(operator.value).map(names::op_as_value));
                ctx.codegen_signature_constraints.remove(&qi_op(operator.value).map(names::op_as_value));
                // Re-register constraints from the local target function (if it has any).
                // E.g., `infixl 4 applySecond as *>` where applySecond has `Apply f =>`.
                let target_val = qi_value(target.name);
                let op_val = qi_value(operator.value);
                if let Some(sig_c) = ctx.signature_constraints.get(&target_val).cloned() {
                    ctx.signature_constraints.insert(op_val.clone(), sig_c);
                }
                if let Some(codegen_c) = ctx.codegen_signature_constraints.get(&target_val).cloned() {
                    ctx.codegen_signature_constraints.insert(op_val, codegen_c);
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
                            set.insert(name.name_symbol());
                        }
                    }
                }
                Some(ImportList::Explicit(items)) => {
                    for item in items {
                        if let Import::Value(sym) = item {
                            // Explicitly imported value — check it's not a class method
                            // in the source module (e.g. `import Prelude (f)` where f
                            // is a class method should not count).
                            let qi_sym = qi_value(sym.value.symbol());
                            if !module_exports.class_methods.contains_key(&qi_sym) {
                                set.insert(sym.value.symbol());
                            }
                        }
                    }
                }
                Some(ImportList::Hiding(_)) => {
                    // Hiding import: all non-class-method, non-hidden values
                    for name in module_exports.values.keys() {
                        if !module_exports.class_methods.contains_key(name) {
                            set.insert(name.name_symbol());
                        }
                    }
                }
            }
        }
        set
    };
    let mut cycle_methods: HashSet<ValueName> = HashSet::new();
    for group in &instance_method_groups {
        let sibling_set: HashSet<ValueName> = group.iter().copied().collect();
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
                    sibling_set.contains(&ValueName::new(head))
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
    let mut inst_methods_with_total_eq: HashSet<(usize, ValueName)> = HashSet::new();
    for (name, _span, binders, _guarded, _where, _expected, _scoped, _given, inst_id, _inst_constraints2) in
        &deferred_instance_methods
    {
        if !binders.iter().any(|b| contains_inherently_partial_binder(b)) {
            inst_methods_with_total_eq.insert((*inst_id, *name));
        }
    }

    let mut prev_constraint_method: Option<(usize, ValueName)> = None;
    for (name, span, binders, guarded, where_clause, expected_ty, inst_scoped, inst_given, inst_id, inst_constraints_for_method) in
        &deferred_instance_methods
    {
        let prev_scoped = ctx.scoped_type_vars.clone();
        let prev_given = ctx.given_class_names.clone();
        ctx.scoped_type_vars.extend(inst_scoped);
        ctx.given_class_names.extend(inst_given.iter().copied());
        // Set current_binding_name for this instance method so deferred constraints
        // are associated with the right binding for constraint parameter resolution.
        ctx.current_binding_name = Some(*name);
        ctx.current_binding_span = Some(*span);
        ctx.current_instance_id = Some(*inst_id);
        // Store instance + method constraints for this method (for ConstraintArg resolution)
        {
            let mut all_constraints: Vec<(Qualified<ClassName>, Vec<Type>)> = inst_constraints_for_method.clone();
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
                if let Some((_, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(cls)) {
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
            for cls_name in constraint_classes {
                ctx.current_given_expanded.insert(*cls_name);
                let mut stack = vec![*cls_name];
                while let Some(cls) = stack.pop() {
                    if let Some((_, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(cls)) {
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
            name.symbol(),
            *span,
            binders,
            guarded,
            where_clause,
            expected_ty.as_ref(),
            false,
        ) {
            errors.push(e);
        }
        // After method body inference, resolve ConstraintArg positions for
        // multi-same-class constraints by matching zonked type args.
        if !inst_constraints_for_method.is_empty() {
            let new_entries = &ctx.codegen_deferred_constraints[pre_deferred_len..];
            // Find class names that appear multiple times in instance constraints
            let mut class_counts: HashMap<ClassName, usize> = HashMap::new();
            for (c, _) in inst_constraints_for_method {
                *class_counts.entry(c.name).or_insert(0) += 1;
            }
            // Structural matching helper: checks if `actual` (with Unif vars) matches
            // `pattern` (with Var type vars), building a consistent var→type mapping.
            fn types_match_structurally(
                actual: &Type,
                pattern: &Type,
                var_map: &mut HashMap<TypeVarName, Type>,
            ) -> bool {
                match (actual, pattern) {
                    (_, Type::Var(tv)) => {
                        if let Some(existing) = var_map.get(tv) {
                            *existing == *actual
                        } else {
                            var_map.insert(*tv, actual.clone());
                            true
                        }
                    }
                    (Type::App(a1, a2), Type::App(p1, p2)) => {
                        types_match_structurally(a1, p1, var_map)
                            && types_match_structurally(a2, p2, var_map)
                    }
                    (Type::Fun(a1, a2), Type::Fun(p1, p2)) => {
                        types_match_structurally(a1, p1, var_map)
                            && types_match_structurally(a2, p2, var_map)
                    }
                    (Type::Con(a), Type::Con(b)) => a == b,
                    (Type::Record(a_fields, a_tail), Type::Record(p_fields, p_tail)) => {
                        if a_fields.len() != p_fields.len() { return false; }
                        for ((an, at), (pn, pt)) in a_fields.iter().zip(p_fields.iter()) {
                            if an != pn { return false; }
                            if !types_match_structurally(at, pt, var_map) { return false; }
                        }
                        match (a_tail, p_tail) {
                            (Some(a), Some(p)) => types_match_structurally(a, p, var_map),
                            (None, None) => true,
                            _ => false,
                        }
                    }
                    (a, b) => a == b,
                }
            }
            /// Count type depth (number of App/Fun/Record layers) for specificity ordering.
            fn type_depth(ty: &Type) -> usize {
                match ty {
                    Type::App(a, b) | Type::Fun(a, b) => 1 + type_depth(a).max(type_depth(b)),
                    Type::Record(fields, tail) => {
                        let max_field = fields.iter().map(|(_, t)| type_depth(t)).max().unwrap_or(0);
                        let tail_d = tail.as_ref().map_or(0, |t| type_depth(t));
                        1 + max_field.max(tail_d)
                    }
                    _ => 0,
                }
            }
            // Multi-same-class constraint resolution is deferred to the post-hoc
            // resolution block (after all equations are processed) which has access to
            // all constraints and can use unif-var partitioning to correctly assign positions.
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
            errors.push(TypeError::NoInstanceFound {
                span: *span,
                class_name: names::unqualified_class("Partial"),
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
        if !seen_values.contains_key(&sig_name.symbol()) {
            errors.push(TypeError::OrphanTypeSignature {
                span: *span,
                name: *sig_name,
            });
        }
    }

    // Pre-insert all values with type signatures so forward references work
    // (e.g. `crash = crashWith "..."` where crashWith is defined later)
    for (name, _) in &value_groups {
        if let Some((_, sig_ty)) = signatures.get(&ValueName::new(*name)) {
            env.insert_scheme(ValueName::new(*name), Scheme::mono(sig_ty.clone()));
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
            if let Some((_, sig_ty)) = signatures.get(&ValueName::new(target.name)) {
                env.insert_scheme(ValueName::new(operator.value), Scheme::mono(sig_ty.clone()));
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
                        if signatures.contains_key(&ValueName::new(name)) {
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
                    let others: Vec<(ValueName, crate::span::Span)> =
                        non_func_members[1..].iter().map(|(n, s)| (ValueName::new(*n), *s)).collect();
                    errors.push(TypeError::CycleInDeclaration {
                        name: ValueName::new(name),
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
                if !signatures.contains_key(&ValueName::new(name)) {
                    let var = Type::Unif(ctx.state.fresh_var());
                    env.insert_mono(ValueName::new(name), var.clone());
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
            let qualified = qi_value(*name);
            let sig = signatures.get(&ValueName::new(*name)).map(|(_, ty)| ty);

            // Expand type aliases in sig to expose hidden Foralls and their constraints.
            // E.g. `three :: Expr Number` where `type Expr a = forall e. E e => e a`
            // expands to `forall e. E e => e Number`, so the body is checked against
            // the inner type with rigid Var(e), producing deferrable constraints.
            let expanded_sig_storage;
            let mut sig_alias_expanded_to_forall = false;
            let mut sig_alias_name: Option<Symbol> = None;
            let sig = if let Some(sig_ty) = sig {
                if !matches!(sig_ty, Type::Forall(..)) {
                    let expanded = expand_type_aliases_limited(sig_ty, &ctx.state.type_aliases, 0);
                    if matches!(&expanded, Type::Forall(..)) {
                        sig_alias_expanded_to_forall = true;
                        // Extract alias name from head of original sig type
                        sig_alias_name = extract_type_head_name(sig_ty);
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
            ctx.current_binding_name = Some(ValueName::new(*name));

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
                        name: ValueName::new(*name),
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
                    env.insert_scheme(ValueName::new(*name), scheme);
                    var
                } else {
                    let var = Type::Unif(ctx.state.fresh_var());
                    env.insert_mono(ValueName::new(*name), var.clone());
                    var
                }
            } else {
                let var = Type::Unif(ctx.state.fresh_var());
                env.insert_mono(ValueName::new(*name), var.clone());
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
                        if let Some((_, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(cls)) {
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
                    if let Some((_, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(cls)) {
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
            let codegen_deferred_start = ctx.codegen_deferred_constraints.len();

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
                            ctx.instance_method_constraints.insert(sp, fn_constraints.clone());
                            ctx.standalone_fn_constraint_spans.insert(sp);
                            ctx.given_constraint_positions.clear();
                            ctx.given_constraint_counters.clear();
                            for (pos, (c, c_args)) in fn_constraints.iter().enumerate() {
                                ctx.given_constraint_positions.push((c.name, c_args.clone(), pos));
                            }
                        } else {
                            ctx.given_constraint_positions.clear();
                            ctx.given_constraint_counters.clear();
                        }
                    } else {
                        ctx.given_constraint_positions.clear();
                        ctx.given_constraint_counters.clear();
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
                        sig_alias_expanded_to_forall,
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
                                                crate::interner::resolve(ordering.name_symbol())
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
                                let lacks_sym = names::unqualified_class("Lacks");
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
                                    // Skip constraints that originated from external functions'
                                    // codegen constraints (propagated for dict resolution only).
                                    // These are not the current function's own Lacks requirements.
                                    if ctx.codegen_only_deferred_spans.contains(&(c_span, c_class.name)) {
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
                                                    f.eq_str(label_str.as_str())
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
                                let coercible_ident =
                                    names::unqualified_class("Coercible");
                                let newtype_ident = names::unqualified_class("Newtype");
                                let type_equals_ident = names::unqualified_class("TypeEquals");
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
                                // Snapshot codegen_deferred_constraints before generalization.
                                // After generalization, unif vars become type variables, making
                                // instance resolution impossible. By zonking now while vars
                                // are still bound to concrete types, we preserve resolvable args.
                                for i in codegen_deferred_start..ctx.codegen_deferred_constraints.len() {
                                    let zonked_args: Vec<Type> = ctx.codegen_deferred_constraints[i].2.iter()
                                        .map(|t| ctx.state.zonk(t.clone()))
                                        .collect();
                                    ctx.codegen_deferred_pre_generalized.insert(i, zonked_args);
                                }
                                // Track whether the explicit signature hides constraints
                                // in type aliases (e.g. `three :: Expr Number` where
                                // `type Expr a = forall e. E e => e a`). Only alias-hidden
                                // constraints need body extraction; for regular explicit
                                // signatures, body constraints should NOT propagate.
                                let has_alias_hidden_forall = sig_alias_expanded_to_forall;
                                let scheme = if let Some(sig_ty) = sig {
                                    if sig_alias_expanded_to_forall {
                                        // The sig was alias-expanded earlier to reveal a hidden Forall.
                                        // Extract forall vars properly for the scheme.
                                        if let Type::Forall(vars, body) = sig_ty {
                                            Scheme {
                                                forall_vars: vars.iter().map(|&(v, _)| v).collect(),
                                                ty: (**body).clone(),
                                            }
                                        } else {
                                            Scheme::mono(ctx.state.zonk(sig_ty.clone()))
                                        }
                                    } else if !matches!(sig_ty, Type::Forall(..)) {
                                        let expanded = expand_type_aliases_limited(sig_ty, &ctx.state.type_aliases, 0);
                                        if let Type::Forall(vars, body) = expanded {
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
                                            let c_str = c_class.name.resolve().unwrap_or_default();
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
                                    env.generalize_excluding(&mut ctx.state, zonked, ValueName::new(*name))
                                };
                                let zonked = ctx.state.zonk(ty.clone());
                                env.insert_scheme(ValueName::new(*name), scheme.clone());
                                local_values.insert(ValueName::new(*name), scheme.clone());

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
                                // For alias-expanded sigs, look up constraints from the
                                // type alias definition (stored in type_alias_constraints).
                                // These constraints are stripped during convert_type_expr
                                // so they're not in the Type representation.
                                if has_alias_hidden_forall && !ctx.signature_constraints.contains_key(&qualified) {
                                    if let Some(alias_name) = sig_alias_name {
                                        if let Some(alias_constraints) = type_alias_constraints.get(&alias_name) {
                                            ctx.signature_constraints.insert(qualified.clone(), alias_constraints.clone());
                                            // Register for ConstraintArg resolution in Pass 3 so that
                                            // pattern-bound vars from newtype constructor patterns
                                            // (e.g. `\(Mailboxed nt) -> nt`) get their dict applied.
                                            if let Some(sp) = ctx.current_binding_span {
                                                ctx.instance_method_constraints.entry(sp).or_insert_with(|| alias_constraints.clone());
                                                ctx.standalone_fn_constraint_spans.insert(sp);
                                            }
                                        }
                                    }
                                }
                                let skip_body_constraint_extraction = sig.is_some() && (
                                    !has_alias_hidden_forall || {
                                        // The alias expanded to reveal a forall but with no
                                        // hidden constraints (e.g., `~>` = `forall a. f a -> g a`).
                                        // Treat as an explicit signature: skip body extraction.
                                        sig_alias_name
                                            .and_then(|name| type_alias_constraints.get(&name))
                                            .map_or(true, |c| c.is_empty())
                                    }
                                );
                                if !skip_body_constraint_extraction && !ctx.signature_constraints.contains_key(&qualified) {
                                    // Build a mapping from generalized unif vars to the scheme's Forall vars.
                                    // This lets us store constraints in terms of the scheme's type vars,
                                    // so they can be properly substituted when the scheme is instantiated.
                                    let unif_to_var: HashMap<crate::typechecker::types::TyVarId, TypeVarName> = {
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
                                    let scheme_var_set: std::collections::HashSet<TypeVarName> =
                                        scheme.forall_vars.iter().copied().collect();
                                    let mut inferred_constraints: Vec<(Qualified<ClassName>, Vec<Type>)> = Vec::new();
                                    let mut seen_class_args: Vec<(ClassName, Vec<Type>)> = Vec::new();
                                    // Skip Coercible constraints — they are resolved at the
                                    // definition site and should never propagate to callers.
                                    let coercible_ident_for_filter = names::unqualified_class("Coercible");
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
                                        if constraint_has_overlap {
                                            // Deduplicate by (class_name, type_args) to avoid true duplicates
                                            // but allow same class with different type args
                                            // (e.g., MyClass a => MyClass (Box a) =>).
                                            let key = (class_name.name, zonked_args.clone());
                                            if !seen_class_args.iter().any(|(cn, args)| *cn == key.0 && args == &key.1) {
                                                seen_class_args.push(key);
                                                inferred_constraints.push((class_name, zonked_args));
                                            }
                                        }
                                    }
                                    if !inferred_constraints.is_empty() {
                                        // Also update instance_method_constraints for codegen
                                        // ConstraintArg resolution (alias-hidden constraints).
                                        let decl_span_for_imc = if let Decl::Value { span, .. } = decls[0] { Some(*span) } else { None };
                                        if let Some(sp) = decl_span_for_imc {
                                            if !ctx.instance_method_constraints.contains_key(&sp) {
                                                ctx.instance_method_constraints.insert(sp, inferred_constraints.clone());
                                                ctx.standalone_fn_constraint_spans.insert(sp);
                                            }
                                        }
                                        ctx.signature_constraints.insert(qualified.clone(), inferred_constraints);
                                    }
                                }

                                // Check for non-exhaustive pattern guards (single equation).
                                // The flag is set during infer_guarded when a pattern guard
                                // doesn't cover all constructors. We also need the overall
                                // function/case to lack an unconditional fallback.
                                if !partial_names.contains(&ValueName::new(*name))
                                    && ctx.has_non_exhaustive_pattern_guards
                                {
                                    if !is_unconditional_for_exhaustiveness(guarded) {
                                        errors.push(TypeError::NoInstanceFound {
                                            span: *span,
                                            class_name: names::unqualified_class("Partial"),
                                            type_args: vec![],
                                        });
                                    }
                                }
                                ctx.has_non_exhaustive_pattern_guards = false;

                                // Check for partial lambdas (refutable binders in lambda expressions).
                                // Unlike guard patterns, partial lambdas always require Partial
                                // regardless of the enclosing function's guard structure.
                                if !partial_names.contains(&ValueName::new(*name)) && ctx.has_partial_lambda {
                                    // Prefer specific NonExhaustivePattern errors from case expressions
                                    if !ctx.non_exhaustive_errors.is_empty() {
                                        errors.extend(ctx.non_exhaustive_errors.drain(..));
                                    } else {
                                        errors.push(TypeError::NoInstanceFound {
                                            span: *span,
                                            class_name: names::unqualified_class("Partial"),
                                            type_args: vec![],
                                        });
                                    }
                                }
                                ctx.has_partial_lambda = false;
                                ctx.non_exhaustive_errors.clear();

                                // Drain any typed holes recorded during inference
                                errors.extend(ctx.drain_pending_holes());

                                result_types.insert(ValueName::new(*name), zonked);
                            }
                        }
                        Err(e) => {
                            errors.push(e);
                            errors.extend(ctx.drain_pending_holes());
                            if let Some(sig_ty) = sig {
                                let scheme = Scheme::mono(ctx.state.zonk(sig_ty.clone()));
                                env.insert_scheme(ValueName::new(*name), scheme.clone());
                                local_values.insert(ValueName::new(*name), scheme);
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
                                name: ValueName::new(*name),
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
                    fn collect_sig_vars(ty: &Type, vars: &mut HashSet<TypeVarName>) {
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
                            sig_alias_expanded_to_forall,
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
                        let coercible_ident = names::unqualified_class("Coercible");
                        let newtype_ident = names::unqualified_class("Newtype"); // probably not quite correct
                        let coercible_givens: Vec<(Type, Type)> = ctx
                            .signature_constraints
                            .get(&qi_value(*name))
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
                        // Snapshot codegen_deferred_constraints before generalization (multi-eq path).
                        for i in codegen_deferred_start..ctx.codegen_deferred_constraints.len() {
                            let zonked_args: Vec<Type> = ctx.codegen_deferred_constraints[i].2.iter()
                                .map(|t| ctx.state.zonk(t.clone()))
                                .collect();
                            ctx.codegen_deferred_pre_generalized.insert(i, zonked_args);
                        }
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
                            env.generalize_excluding(&mut ctx.state, zonked.clone(), ValueName::new(*name))
                        };
                        env.insert_scheme(ValueName::new(*name), scheme.clone());
                        local_values.insert(ValueName::new(*name), scheme.clone());

                        // Extract constraints from deferred_constraints to populate
                        // signature_constraints (needed for codegen dict wrapping).
                        // Skip when function has explicit signature (body constraints
                        // should not propagate — see single-equation block for details).
                        if !has_sig_without_alias_forall && !ctx.signature_constraints.contains_key(&qualified) {
                            let unif_to_var: HashMap<crate::typechecker::types::TyVarId, TypeVarName> = {
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
                            let scheme_var_set: std::collections::HashSet<TypeVarName> =
                                scheme.forall_vars.iter().copied().collect();
                            let mut inferred_constraints: Vec<(Qualified<ClassName>, Vec<Type>)> = Vec::new();
                            let mut seen_class_args: Vec<(ClassName, Vec<Type>)> = Vec::new();
                            // Scan deferred_constraints (skip Coercible — resolved at definition site)
                            let coercible_ident_for_filter = names::unqualified_class("Coercible");
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
                                if constraint_has_overlap {
                                    // Deduplicate by (class_name, type_args) to allow same class
                                    // with different type args (e.g., Show a, Show (f a))
                                    let already_seen = seen_class_args.iter().any(|(cn, args)| *cn == class_name.name && args == &zonked_args);
                                    if !already_seen {
                                        seen_class_args.push((class_name.name, zonked_args.clone()));
                                        inferred_constraints.push((class_name, zonked_args));
                                    }
                                }
                            }
                            if !inferred_constraints.is_empty() {
                                ctx.signature_constraints.insert(qualified.clone(), inferred_constraints);
                            }
                        }

                        if first_arity > 0 && !partial_names.contains(&ValueName::new(*name)) {
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
                        if !partial_names.contains(&ValueName::new(*name)) && ctx.has_non_exhaustive_pattern_guards {
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
                                    class_name: names::unqualified_class("Partial"),
                                    type_args: vec![],
                                });
                            }
                        }
                        ctx.has_non_exhaustive_pattern_guards = false;

                        // Check for partial lambdas (multi-equation).
                        // Skip for multi-equation functions (first_arity > 0) because
                        // individual equation binders are expected to be partial — the
                        // overall exhaustiveness is checked by check_multi_eq_exhaustiveness.
                        if first_arity == 0 && !partial_names.contains(&ValueName::new(*name)) && ctx.has_partial_lambda {
                            if !ctx.non_exhaustive_errors.is_empty() {
                                errors.extend(ctx.non_exhaustive_errors.drain(..));
                            } else {
                                errors.push(TypeError::NoInstanceFound {
                                    span: first_span,
                                    class_name: names::unqualified_class("Partial"),
                                    type_args: vec![],
                                });
                            }
                        }
                        ctx.has_partial_lambda = false;
                        ctx.non_exhaustive_errors.clear();

                        errors.extend(ctx.drain_pending_holes());

                        result_types.insert(ValueName::new(*name), zonked);
                    }
                } else if let Some(sig_ty) = sig {
                    errors.extend(ctx.drain_pending_holes());
                    let scheme = Scheme::mono(ctx.state.zonk(sig_ty.clone()));
                    env.insert_scheme(ValueName::new(*name), scheme.clone());
                    local_values.insert(ValueName::new(*name), scheme);
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
                    env.generalize_excluding(&mut ctx.state, zonked, ValueName::new(cv.name))
                };
                let zonked = ctx.state.zonk(cv.ty.clone());
                env.insert_scheme(ValueName::new(cv.name), scheme.clone());
                local_values.insert(ValueName::new(cv.name), scheme);
                result_types.insert(ValueName::new(cv.name), zonked);
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
            if let Some(scheme) = local_values.get(&ValueName::new(target.name)).cloned() {
                env.insert_scheme(ValueName::new(operator.value), scheme.clone());
                local_values.insert(ValueName::new(operator.value), scheme);
            } else if let Some(scheme) = env.lookup(ValueName::new(target.name)).cloned() {
                if ctx.state.free_unif_vars(&scheme.ty).is_empty() {
                    env.insert_scheme(ValueName::new(operator.value), scheme.clone());
                    local_values.insert(ValueName::new(operator.value), scheme);
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
        if let Some((class_tvs, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(*class_name)) {
            if class_tvs.len() == inst_types.len() {
                let subst: HashMap<TypeVarName, Type> = class_tvs
                    .iter()
                    .map(|tv| TypeVarName::new(*tv))
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
    let mut given_classes_expanded: HashSet<ClassName> = HashSet::new();
    for gcn in &ctx.given_class_names {
        given_classes_expanded.insert(gcn.name);
        let mut stack = vec![gcn.name];
        while let Some(cls) = stack.pop() {
            if let Some((_, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(cls)) {
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
    let mut given_classes_for_zero_instance: HashSet<ClassName> = given_classes_expanded.clone();
    for constraints in ctx.signature_constraints.values() {
        for (class_name, _) in constraints {
            given_classes_for_zero_instance.insert(class_name.name);
            let mut stack = vec![class_name.name];
            while let Some(cls) = stack.pop() {
                if let Some((_, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(cls)) {
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
                let is_magic = ctx.prim_class_names.contains(&class_name.name); // TODO: include class module here
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
        if has_type_vars && chained_classes.contains(&Qualified::unqualified(class_name.name)) {
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
            let (span, class_name_q, _) = ctx.deferred_constraints[i];
            let class_str = class_name_q.name.resolve().unwrap_or_default();
            let zonked_args: Vec<Type> = ctx.deferred_constraints[i]
                .2
                .iter()
                .map(|t| {
                    let z = ctx.state.zonk(t.clone());
                    // Expand type aliases so e.g. Common.NegOne becomes TypeInt(-1)
                    expand_type_aliases_limited(&z, &ctx.state.type_aliases, 0)
                })
                .collect();
            match class_str.as_str() { // TODO: this should include module as well as class name
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
                        let result = Type::Con(qi_type(intern(ordering_str)));
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
    for (_span, class_name_q, type_args) in ctx.deferred_constraints.iter() {
        let class_str = class_name_q.name.resolve().unwrap_or_default();
        if class_str != "Reflectable" { continue; }
        if type_args.len() != 2 { continue; }
        let zonked_0 = ctx.state.zonk(type_args[0].clone());
        let zonked_1 = ctx.state.zonk(type_args[1].clone());
        // Only solve when the second arg is still unsolved (Unif var)
        if !matches!(zonked_1, Type::Unif(_)) { continue; }
        let target_type = match &zonked_0 {
            Type::TypeString(_) => Some(Type::Con(qi_type(crate::interner::intern("String")))),
            Type::TypeInt(_) => Some(Type::Con(qi_type(crate::interner::intern("Int")))),
            Type::Con(c) => {
                let name = crate::interner::resolve(c.name_symbol()).unwrap_or_default().to_string();
                match name.as_str() {
                    "True" | "False" => Some(Type::Con(qi_type(crate::interner::intern("Boolean")))),
                    "LT" | "EQ" | "GT" => Some(Type::Con(qi_type(crate::interner::intern("Ordering")))),
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(target) = target_type {
            let _ = ctx.state.unify(*_span, &zonked_1, &target);
        }
    }

    // Pre-pass: evaluate RowToList constraints in deferred_constraints and bind the list var.
    // RowToList is a Prim solver constraint (like Add/Mul). When the row type is known,
    // we compute the sorted RowList and unify with the list var so the main loop can skip it.
    {
        let nil_sym = crate::interner::intern("Nil");
        let cons_sym = crate::interner::intern("Cons");
        let nil_ty = Type::Con(qi_type(nil_sym));

        let rtl_entries: Vec<(crate::span::Span, Vec<Type>)> = ctx
            .deferred_constraints
            .iter()
            .filter_map(|(span, class_name, args)| {
                if class_name.name.eq_str("RowToList") && args.len() == 2 {
                    Some((*span, args.iter().map(|t| ctx.state.zonk(t.clone())).collect()))
                } else {
                    None
                }
            })
            .collect();

        for (span, args) in rtl_entries {
            let row_ty = &args[0];
            let list_arg = ctx.state.zonk(args[1].clone());
            // Only bind when the list arg is an in-bounds, unsolved unif var
            if let Type::Unif(id) = &list_arg {
                if id.0 < ctx.state.var_count() && ctx.state.probe(*id).is_none() {
                    if let Type::Record(fields, None) = row_ty {
                        let mut sorted_fields = fields.clone();
                        sorted_fields.sort_by(|(a, _), (b, _)| a.to_string().cmp(&b.to_string()));
                        let mut list_ty = nil_ty.clone();
                        for (label, field_ty) in sorted_fields.iter().rev() {
                            let label_sym = crate::interner::intern(&label.to_string());
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
                        let _ = ctx.state.unify(span, &list_arg, &list_ty);
                    }
                }
            }
        }
    }

    /// Recursively resolve functional dependencies through instance sub-constraints.
    /// For `MonadState ?s (WriterT w (ReaderT r (StateT TestState m)))`, this follows:
    ///   WriterT → MonadState s m (sub-constraint) → ReaderT → StateT → determines s=TestState
    /// Returns any type errors from trial unification.
    fn resolve_fundep_transitively(
        class_name: &Qualified<ClassName>,
        args: &[Type],
        instances: &HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
        class_fundeps: &HashMap<Qualified<ClassName>, (Vec<TypeVarName>, Vec<(Vec<usize>, Vec<usize>)>)>,
        state: &mut crate::typechecker::unify::UnifyState,
        span: crate::span::Span,
        depth: u32,
    ) -> Vec<TypeError> {
        if depth > 10 {
            return Vec::new();
        }
        let (_, fundeps) = match class_fundeps.get(class_name) {
            Some(cf) if !cf.1.is_empty() && cf.0.len() == args.len() => cf,
            _ => return Vec::new(),
        };
        let known = match lookup_instances(instances, class_name) {
            Some(k) => k,
            None => return Vec::new(),
        };

        for (lhs_indices, rhs_indices) in fundeps {
            // Only apply when rhs args have unsolved parts
            let rhs_has_unsolved = rhs_indices.iter().any(|&i| {
                i < args.len() && !state.free_unif_vars(&args[i]).is_empty()
            });
            if !rhs_has_unsolved {
                continue;
            }
            // Skip if any lhs arg is a bare unsolved unif var
            let lhs_has_bare_unif = lhs_indices.iter().any(|&i| {
                i < args.len() && matches!(&args[i], Type::Unif(_))
            });
            if lhs_has_bare_unif {
                continue;
            }

            for (inst_types, inst_constraints, _) in known {
                if inst_types.len() != args.len() {
                    continue;
                }
                let mut subst = std::collections::HashMap::new();
                let lhs_match = lhs_indices.iter().all(|&i| {
                    i < args.len()
                        && instances::match_instance_type(&inst_types[i], &args[i], &mut subst)
                });
                if !lhs_match {
                    continue;
                }

                // Check if rhs types are determined by this instance
                let mut all_rhs_determined = true;
                let mut fundep_errors = Vec::new();
                let snapshot = state.snapshot_entries();

                for &ri in rhs_indices {
                    if ri >= args.len() { continue; }
                    let inst_ty = type_utils::apply_var_subst(&subst, &inst_types[ri]);
                    if contains_type_var(&inst_ty) {
                        all_rhs_determined = false;
                        continue;
                    }
                    // Check if the substituted type is just the same unif var (delegation)
                    if inst_ty == args[ri] {
                        all_rhs_determined = false;
                        continue;
                    }
                    // Don't unify rigid type vars — they can't be constrained
                    if matches!(&args[ri], Type::Var(_)) {
                        all_rhs_determined = false;
                        continue;
                    }
                    if let Err(e) = state.unify(span, &args[ri], &inst_ty) {
                        fundep_errors.push(e);
                    }
                }
                state.restore_entries(snapshot);

                if !fundep_errors.is_empty() {
                    return fundep_errors;
                }

                // If rhs wasn't determined, try following sub-constraints recursively.
                // Build a full substitution that maps ALL instance type vars to actual args.
                if !all_rhs_determined && !inst_constraints.is_empty() {
                    let mut full_subst = subst.clone();
                    // Map rhs type vars to their actual arg types (e.g., s → ?s)
                    for &ri in rhs_indices {
                        if ri < inst_types.len() && ri < args.len() {
                            if let Type::Var(v) = &inst_types[ri] {
                                full_subst.entry(*v).or_insert_with(|| args[ri].clone());
                            }
                        }
                    }
                    for (sub_class, sub_args) in inst_constraints {
                        // Only recurse through same-class delegation (e.g., MonadState → MonadState
                        // through WriterT/ReaderT/etc). Cross-class sub-constraints don't help.
                        if sub_class.name != class_name.name {
                            continue;
                        }
                        let sub_concrete: Vec<Type> = sub_args.iter()
                            .map(|t| type_utils::apply_var_subst(&full_subst, t))
                            .collect();
                        // Skip if sub-constraint has type vars that weren't in the original args
                        let has_new_type_vars = sub_concrete.iter().any(|t| {
                            fn has_unsubstituted_var(t: &Type, original_args: &[Type]) -> bool {
                                match t {
                                    Type::Var(v) => !original_args.iter().any(|a| contains_type_var_named(a, *v)),
                                    Type::App(f, a) => has_unsubstituted_var(f, original_args) || has_unsubstituted_var(a, original_args),
                                    Type::Fun(a, b) => has_unsubstituted_var(a, original_args) || has_unsubstituted_var(b, original_args),
                                    Type::Record(fields, tail) => {
                                        fields.iter().any(|(_, ft)| has_unsubstituted_var(ft, original_args))
                                            || tail.as_ref().map_or(false, |t| has_unsubstituted_var(t, original_args))
                                    }
                                    Type::Forall(_, body) => has_unsubstituted_var(body, original_args),
                                    _ => false,
                                }
                            }
                            fn contains_type_var_named(t: &Type, name: TypeVarName) -> bool {
                                match t {
                                    Type::Var(v) => *v == name,
                                    Type::App(f, a) => contains_type_var_named(f, name) || contains_type_var_named(a, name),
                                    Type::Fun(a, b) => contains_type_var_named(a, name) || contains_type_var_named(b, name),
                                    Type::Record(fields, tail) => {
                                        fields.iter().any(|(_, ft)| contains_type_var_named(ft, name))
                                            || tail.as_ref().map_or(false, |t| contains_type_var_named(t, name))
                                    }
                                    Type::Forall(_, body) => contains_type_var_named(body, name),
                                    _ => false,
                                }
                            }
                            has_unsubstituted_var(t, args)
                        });
                        if has_new_type_vars {
                            continue;
                        }
                        let sub_errors = resolve_fundep_transitively(
                            sub_class, &sub_concrete, instances, class_fundeps, state, span, depth + 1,
                        );
                        if !sub_errors.is_empty() {
                            return sub_errors;
                        }
                    }
                }
                break;
            }
        }
        Vec::new()
    }

    // Pass 3: Check deferred type class constraints
    for (span, class_name_typed, type_args) in ctx.deferred_constraints.iter() {
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
            if all_bare_vars && chained_classes.contains(class_name_typed) {
                // Skip if the class is "given" by an enclosing instance context
                // (including transitive superclasses) OR by an explicit type signature.
                // Instance context constraints are satisfied by callers.
                // Explicit signature constraints (e.g. `Axes n a => ...`) are declared
                // requirements — the constraint is intentionally polymorphic.
                // Inferred signature constraints (from body usage without explicit
                // declaration) are NOT skipped — those represent actual ambiguity.
                let is_given = given_classes_expanded.contains(&class_name_typed.name)
                    || explicit_sig_classes.contains(&class_name_typed.name);
                if !is_given {
                    if let Some(known) = lookup_instances(&instances, class_name_typed) {
                        let has_concrete_instance = known.iter().any(|(inst_types, _, _)| {
                            inst_types.iter().any(|t| !matches!(t, Type::Var(_)))
                        });
                        if has_concrete_instance {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name_typed,
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
            if chained_classes.contains(class_name_typed)
                && !all_bare_vars
                && !all_pure_unif
                && has_structured_arg
            {
                // Skip if the class is "given" by an enclosing function's type signature
                // (including transitive superclasses).
                let is_given = given_classes_expanded.contains(&class_name_typed.name);
                if is_given {
                    continue;
                }

                // When args contain type variables, use chain-aware ambiguity checking.
                let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
                // Also check for unif vars inside App args (e.g., C (X ?a Int)) when the
                // instance chain contains a Fail guard — the unif var makes the chain
                // ambiguous and the Fail means it can never succeed.
                let has_unif_in_app = !has_type_vars && zonked_args.iter().any(|t| {
                    if let Type::App(_, _) = t {
                        !ctx.state.free_unif_vars(t).is_empty()
                    } else {
                        false
                    }
                }) && {
                    // Only apply when the chain contains a Fail constraint
                    if let Some(known) = lookup_instances(&instances, class_name_typed) {
                        known.iter().any(|(_, constraints, _)| {
                            constraints.iter().any(|(c, _)| c.name.to_string() == "Fail")
                        })
                    } else {
                        false
                    }
                };
                if has_type_vars || has_unif_in_app {
                    if has_type_vars {
                        // If there are also unsolved unification variables, skip —
                        // can't determine chain ambiguity with partially-known types.
                        let has_unif_vars = zonked_args
                            .iter()
                            .any(|t| !ctx.state.free_unif_vars(t).is_empty());
                        if has_unif_vars {
                            continue;
                        }
                    }
                    if let Some(known) = lookup_instances(&instances, class_name_typed) {
                        match check_chain_ambiguity(known, &zonked_args) {
                            ChainResult::Resolved => {}
                            ChainResult::Ambiguous | ChainResult::NoMatch => {
                                errors.push(TypeError::NoInstanceFound {
                                    span: *span,
                                    class_name: *class_name_typed,
                                    type_args: zonked_args,
                                });
                            }
                        }
                    }
                } else {
                    let has_bare_unif = zonked_args.iter().any(|t| matches!(t, Type::Unif(_)));
                    if has_bare_unif {
                        continue;
                    }
                    match check_instance_depth(
                        &instances,
                        &ctx.state.type_aliases,
                        class_name_typed,
                        &zonked_args,
                        0,
                        Some(&known_classes),
                        Some(&ctx.type_con_arities),
                    ) {
                        InstanceResult::Match => {}
                        InstanceResult::NoMatch => {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name_typed,
                                type_args: zonked_args,
                            });
                        }
                        InstanceResult::DepthExceeded => {
                            errors.push(TypeError::PossiblyInfiniteInstance {
                                span: *span,
                                class_name: *class_name_typed,
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
                let class_str = class_name_typed.name.resolve().unwrap_or_default();
                let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
                if class_str == "Coercible" && zonked_args.len() == 2 && !has_type_vars { // TODO: this should include module as well as class name
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
                                .push((class_name_typed.name, crate::typechecker::registry::DictExpr::ZeroCost));
                        }
                        CoercibleResult::NotCoercible => {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name_typed,
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
                                class_name: *class_name_typed,
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
            let class_has_instances = lookup_instances(&instances, class_name_typed)
                .map_or(false, |insts| !insts.is_empty());
            let all_pure_unif = zonked_args.iter().all(|t| matches!(t, Type::Unif(_)));
            let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
            // Check if any arg contains unsolved unif vars (mixed with concrete types).
            // When mixed unif vars are present, the constraint may be satisfiable through
            // superclass constraints not yet tracked in signature_constraints.
            // But reject pure-unif constraints (all args unknown) with zero instances.
            let has_mixed_unif = !all_pure_unif && zonked_args.iter().any(|t| !ctx.state.free_unif_vars(t).is_empty());
            let is_given = given_classes_for_zero_instance.contains(&class_name_typed.name);
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
                let is_magic = ctx.prim_class_names.contains(&class_name_typed.name);  // TODO: include class module here
                // Skip zero-arg zero-method zero-instance classes: these are "constraint tokens"
                // (e.g. `class GqlSOAA`, `class Partial`) discharged by runner functions like
                // `runGqlSOAA :: (GqlSOAA => a) -> a`. The constraint arises when calling
                // functions that require GqlSOAA (via codegen_signature_constraints), but is
                // consumed by the runner at the call site — NOT by instance resolution.
                // We detect this by: zero args + no class methods registered = constraint token.
                let is_constraint_token = zonked_args.is_empty()
                    && !ctx.class_methods.values().any(|(cn, _)| cn.name == class_name_typed.name);
                if !is_magic && !is_constraint_token {
                    errors.push(TypeError::NoInstanceFound {
                        span: *span,
                        class_name: *class_name_typed,
                        type_args: zonked_args.clone(),
                    });
                }
            }

            // Apply functional dependencies for classes where the determining args are
            // fully solved. E.g. `MonadState ?s MyM | m -> s` with `instance MonadState State MyM`:
            // since `m = MyM` is solved, the fundep determines `s = State`, which we unify
            // with the current `?s`. This catches type mismatches that would otherwise be
            // silently accepted because `?s` absorbed the wrong type from a record update.
            // Apply functional dependencies: for each fundep, try to match the
            // determining (lhs) args against instance types. If matched, the determined
            // (rhs) args are known — trial-unify them with the constraint's rhs args
            // to catch type mismatches. E.g. `MonadState ?s (StateT TestState ?m)` with
            // `instance MonadState s (StateT s m)`: matching lhs arg `StateT TestState ?m`
            // against instance pattern `StateT s m` builds subst {s→TestState, m→?m}.
            // Applying subst to rhs instance type `s` gives `TestState`. Trial-unifying
            // `?s` with `TestState` catches the mismatch.
            {
                let fundep_errors = resolve_fundep_transitively(
                    class_name_typed,
                    &zonked_args,
                    &instances,
                    &ctx.class_fundeps,
                    &mut ctx.state,
                    *span,
                    0,
                );
                errors.extend(fundep_errors);
            }
            continue;
        }

        // Skip type-level solver classes that are resolved by Pass 2.75 solving,
        // not by explicit instances. Without this, fully-resolved Add/Mul/ToString
        // constraints would fail instance resolution since they have no instances.
        // Note: Lacks is NOT skipped here — it's handled by check_instance_depth
        // which correctly rejects Lacks "x" (x :: Int, ...) for concrete rows.
        {
            let class_str = class_name_typed.name.resolve().unwrap_or_default();
            if matches!(
                class_str.as_str(), // TODO: this should include module as well as class name
                "Add" | "Mul" | "ToString" | "Compare" | "Nub" | "Union" | "RowToList"
            ) {
                continue;
            }
        }

        // Coercible solver: handle Coercible constraints with role-based decomposition.
        // Only solve when no type variables remain (polymorphic constraints are deferred).
        if !has_unsolved {
             // TODO: check module
            let class_str = class_name_typed.name.resolve().unwrap_or_default();
            if class_str == "Coercible" && zonked_args.len() == 2 { // TODO: this should include module as well as class name
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
                            .push((class_name_typed.name, crate::typechecker::registry::DictExpr::ZeroCost));
                    }
                    CoercibleResult::NotCoercible => {
                        errors.push(TypeError::NoInstanceFound {
                            span: *span,
                            class_name: *class_name_typed,
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
                            class_name: *class_name_typed,
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
        let class_is_known = lookup_instances(&instances, class_name_typed).is_some()
            || ctx.class_methods.values().any(|(cn, _)| cn == class_name_typed || cn.name == class_name_typed.name)
            || known_classes.contains(class_name_typed)
            || ctx.prim_class_names.contains(&class_name_typed.name) // compiler-magic Prim classes seen in imports
            || {
                // Also recognize compiler-solved classes by name even if they haven't been
                // seen in this module's import chain. This covers cases like `Reflectable`
                // appearing as a transitive sub-constraint of an imported class instance,
                // without being explicitly imported into the current module.
                let cname_str = crate::interner::resolve(class_name_typed.name_symbol()).unwrap_or_default();
                matches!(
                    cname_str.as_str(),
                    "IsSymbol" | "Reflectable" | "Reifiable"
                    | "Partial" | "Warn" | "Fail"
                    | "Coercible"
                    | "Lacks" | "Cons" | "Nub" | "Union" | "RowToList"
                    | "CompareSymbol" | "Append" | "Compare"
                    | "Add" | "Mul" | "ToString"
                )
            };
        if !class_is_known {
            errors.push(TypeError::UnknownClass {
                span: *span,
                name: *class_name_typed,
            });
        } else if zonked_args.is_empty() && given_classes_for_zero_instance.contains(&class_name_typed.name) {
            // Zero-arg marker constraint (e.g. `AttendeeAuth =>`) that is declared
            // in a function signature — discharged by callers, not instance resolution.
        } else if zonked_args.is_empty()
            && !ctx.class_methods.values().any(|(cn, _)| cn.name == class_name_typed.name)
        {
            // Zero-arg zero-method class: "constraint token" pattern (e.g. `class GqlSOAA`).
            // Such classes have no instances and are discharged by explicit runner functions
            // like `runGqlSOAA :: (GqlSOAA => a) -> a`. The constraint arises from calling
            // functions that require GqlSOAA (via codegen_signature_constraints), but the
            // discharge mechanism is at the call site, not via instance resolution.
            // We can safely skip: if the class IS required by the caller but not provided,
            // it would have been caught by the class-is-given check above (given_classes_for_zero_instance).
        } else {
            // For chained classes with type variables in args, use chain-aware
            // ambiguity checking. A chain like `C String else C a` is ambiguous
            // when queried with `C a` (rigid type var) — the first instance
            // "could match" (a might be String) but doesn't "definitely match".
            let has_type_vars = zonked_args.iter().any(|t| contains_type_var(t));
            if has_type_vars && chained_classes.contains(class_name_typed) {
                if let Some(known) = lookup_instances(&instances, class_name_typed) {
                    match check_chain_ambiguity(known, &zonked_args) {
                        ChainResult::Resolved => {}
                        ChainResult::Ambiguous | ChainResult::NoMatch => {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name_typed,
                                type_args: zonked_args,
                            });
                        }
                    }
                }
            } else {
                match check_instance_depth(
                    &instances,
                    &ctx.state.type_aliases,
                    class_name_typed,
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
                                        *class_name_typed,
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
                        // Skip error for codegen-only constraints (from codegen_signature_constraints).
                        // These are transparent calls where the dict comes from the callee, not the caller.
                        if ctx.codegen_only_deferred_spans.contains(&(*span, class_name_typed.name)) {
                            // codegen-only — skip
                        } else {
                            errors.push(TypeError::NoInstanceFound {
                                span: *span,
                                class_name: *class_name_typed,
                                type_args: zonked_args,
                            });
                        }
                    }
                    InstanceResult::DepthExceeded => {
                        errors.push(TypeError::PossiblyInfiniteInstance {
                            span: *span,
                            class_name: *class_name_typed,
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
    for (span, class_name_op, type_args) in &ctx.op_deferred_constraints {
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
            class_name_op,
            &zonked_args,
            0,
            None,
            Some(&ctx.type_con_arities),
        ) {
            errors.push(TypeError::PossiblyInfiniteInstance {
                span: *span,
                class_name: *class_name_op,
                type_args: zonked_args,
            });
        }
    }

    // Dict resolution for codegen: resolve concrete deferred constraints to instance dicts.
    // Build a combined instance registry from local instances + all imported modules.
    {
        // Use pre-computed cache if available, otherwise compute from registry.
        let empty_cache = crate::typechecker::registry::CodegenDictCache::default();
        let cache = dict_cache.unwrap_or(&empty_cache);
        let mut combined_registry: HashMap<(Symbol, Symbol), Vec<(Symbol, Option<Vec<Symbol>>)>> = if dict_cache.is_some() {
            cache.base_registry.clone()
        } else {
            let mut reg: HashMap<(Symbol, Symbol), Vec<(Symbol, Option<Vec<Symbol>>)>> = HashMap::new();
            for (mod_parts, mod_exports) in registry.iter_all() {
                for (&(class, head), &inst_name) in &mod_exports.instance_registry {
                    let defining_mod = mod_exports.instance_modules.get(&inst_name)
                        .cloned()
                        .unwrap_or_else(|| mod_parts.to_vec());
                    let entries = reg.entry((class.symbol(), head.symbol()))
                        .or_default();
                    let entry = (inst_name, Some(defining_mod));
                    if !entries.iter().any(|(n, m)| *n == entry.0 && *m == entry.1) {
                        entries.push(entry);
                    }
                }
            }
            reg
        };
        // Add local instances (override imported — insert at front so they take priority)
        for (&(class, head), &inst_name) in &instance_registry_entries {
            let entries = combined_registry.entry((class.symbol(), head.symbol()))
                .or_default();
            entries.insert(0, (inst_name, None));
        }
        let inst_name_all_modules: &HashMap<(String, usize), Vec<Vec<Symbol>>> = &cache.inst_name_all_modules;

        // Build combined instance_var_kinds from cache + local
        let mut combined_instance_var_kinds: HashMap<Symbol, HashMap<TypeVarName, Symbol>> = if dict_cache.is_some() {
            cache.base_instance_var_kinds.clone()
        } else {
            let mut kinds = HashMap::new();
            for (_, mod_exports) in registry.iter_all() {
                for (inst_name, k) in &mod_exports.instance_var_kinds {
                    kinds.entry(*inst_name).or_insert_with(|| k.clone());
                }
            }
            kinds
        };
        for (inst_name, kinds) in &instance_var_kinds_entries {
            combined_instance_var_kinds.insert(*inst_name, kinds.clone());
        }

        // Build type_head_origins: maps unqualified type name → defining module qualifier.
        // Used to qualify concrete type args before instance matching, so that
        // Foldable List → Foldable (Data.List.Types.List) and the correct instance is found.
        let type_head_origins: HashMap<Symbol, names::ModuleQualifier> = {
            let mut origins: HashMap<Symbol, names::ModuleQualifier> = HashMap::new();
            // Local types: defined in this module (highest priority)
            let current_mq = names::module_qualifier_from_parts(&module.name.value.parts);
            for name in &local_data_type_names {
                origins.insert(name.symbol(), current_mq);
            }
            // Priority 2: Types from directly imported modules where the type is DEFINED
            // in that module (origin matches module). This avoids picking up transitive
            // re-exports that could point to the wrong defining module when type names
            // collide (e.g., Data.List.Types.List vs Data.List.Lazy.Types.List).
            for import_decl in &module.imports {
                let mod_parts: Vec<Symbol> = import_decl.module.parts.clone();
                let mod_str = mod_parts.iter()
                    .filter_map(|s| crate::interner::resolve(*s))
                    .collect::<Vec<_>>()
                    .join(".");
                if let Some(mod_exports) = registry.lookup(&mod_parts) {
                    for (type_name, &origin_sym) in &mod_exports.type_origins {
                        let name_sym = type_name.symbol();
                        let origin_str = crate::interner::resolve(origin_sym).unwrap_or_default().to_string();
                        // Only register if this module DEFINES the type (origin == module)
                        if origin_str == mod_str {
                            origins.entry(name_sym).or_insert_with(|| {
                                names::module_qualifier(&origin_str)
                            });
                        }
                    }
                }
            }
            // Priority 3: Types from directly imported modules (any origin)
            for import_decl in &module.imports {
                let mod_parts: Vec<Symbol> = import_decl.module.parts.clone();
                if let Some(mod_exports) = registry.lookup(&mod_parts) {
                    for (type_name, &origin_sym) in &mod_exports.type_origins {
                        let name_sym = type_name.symbol();
                        origins.entry(name_sym).or_insert_with(|| {
                            let origin_str = crate::interner::resolve(origin_sym).unwrap_or_default();
                            names::module_qualifier(&origin_str)
                        });
                    }
                }
            }
            // Priority 4: All registry modules (fills in any remaining types)
            for (_mod_parts, mod_exports) in registry.iter_all() {
                for (type_name, &origin_sym) in &mod_exports.type_origins {
                    let name_sym = type_name.symbol();
                    origins.entry(name_sym).or_insert_with(|| {
                        let origin_str = crate::interner::resolve(origin_sym).unwrap_or_default();
                        names::module_qualifier(&origin_str)
                    });
                }
            }
            origins
        };

        // Also build combined registry for op_deferred_constraints
        let all_constraints: Vec<(usize, bool)> = (0..ctx.deferred_constraints.len())
            .map(|i| (i, false))
            .chain((0..ctx.op_deferred_constraints.len()).map(|i| (i, true)))
            .collect();

        // Pre-build a map from constraint span → binding span for O(1) lookup
        // (avoids O(n²) when resolving deferred constraints with given_constraints).
        let codegen_span_to_binding: HashMap<crate::span::Span, crate::span::Span> = {
            let mut map = HashMap::new();
            for (ci, (cs, _, _, _)) in ctx.codegen_deferred_constraints.iter().enumerate() {
                if let Some(bs) = ctx.codegen_deferred_constraint_bindings.get(ci).and_then(|b| *b) {
                    map.entry(*cs).or_insert(bs);
                }
            }
            map
        };

        // Precompute which (span, class_name) pairs have multiple deferred constraints
        // with distinct type args. This identifies call sites like `run (Box 99)` that
        // generate e.g. MyClass Int AND MyClass (Box Int) at the same span.
        let multi_class_spans: HashSet<(crate::span::Span, ClassName)> = {
            let mut span_class_args: HashMap<(crate::span::Span, ClassName), Vec<Vec<Type>>> = HashMap::new();
            for (idx, is_op) in &all_constraints {
                let (span, class_name, type_args) = if *is_op {
                    &ctx.op_deferred_constraints[*idx]
                } else {
                    &ctx.deferred_constraints[*idx]
                };
                let zonked: Vec<Type> = type_args.iter().map(|t| ctx.state.zonk(t.clone())).collect();
                let key = (*span, class_name.name);
                let entry = span_class_args.entry(key).or_default();
                if !entry.iter().any(|existing| existing == &zonked) {
                    entry.push(zonked);
                }
            }
            span_class_args.into_iter()
                .filter(|(_, args_list)| args_list.len() > 1)
                .map(|(key, _)| key)
                .collect()
        };

        // Pre-pass: evaluate RowToList constraints and bind the resulting rowlist type variable.
        // This must happen before the main deferred constraint loop so that classes like VBus
        // (which use RowList types derived from RowToList) can be resolved with a concrete rl arg.
        // E.g., `VBus ri p e` where `RowToList (a :: Int, b :: Unit) ri` should bind
        // `ri := RL.Cons "a" Int (RL.Cons "b" Unit RL.Nil)` so instance matching can proceed.
        {
            let nil_sym = crate::interner::intern("Nil");
            let cons_sym = crate::interner::intern("Cons");
            let nil_ty = Type::Con(qi_type(nil_sym));

            let row_to_list_constraints: Vec<(crate::span::Span, Vec<Type>)> = ctx
                .codegen_deferred_constraints
                .iter()
                .filter_map(|(span, class_name, args, _)| {
                    if class_name.name.eq_str("RowToList") && args.len() == 2 {
                        Some((*span, args.iter().map(|t| ctx.state.zonk(t.clone())).collect()))
                    } else {
                        None
                    }
                })
                .collect();

            for (span, args) in row_to_list_constraints {
                if args.len() != 2 { continue; }
                let row_ty = &args[0];
                let list_arg = ctx.state.zonk(args[1].clone());

                // Only evaluate when the row type is a closed Record (no tail var)
                // and the list arg is still unsolved (Unif var or Var).
                let is_unsolved = matches!(list_arg, Type::Unif(_) | Type::Var(_));
                if !is_unsolved { continue; }

                if let Type::Record(fields, None) = row_ty {
                    // Sort fields alphabetically — PureScript RowToList sorts by label
                    let mut sorted_fields = fields.clone();
                    sorted_fields.sort_by(|(a, _), (b, _)| {
                        a.to_string().cmp(&b.to_string())
                    });
                    // Build the RowList type: RL.Cons "label" ty (RL.Cons ...) RL.Nil
                    let mut list_ty = nil_ty.clone();
                    for (label, field_ty) in sorted_fields.iter().rev() {
                        let label_sym = crate::interner::intern(&label.to_string());
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
                    // Unify the list arg (usually a Unif var) with the computed RowList
                    let _ = ctx.state.unify(span, &list_arg, &list_ty);
                }
            }
        }

        // Run multiple passes to handle transitive constraint resolution.
        // E.g., Parallel ?f Aff resolves first and unifies ?f = ParAff,
        // then Alt ?f (now Alt ParAff) can resolve on the next pass.
        for _deferred_pass in 0..2 {
        for (idx, is_op) in &all_constraints {
            let (_constraint_span_dbg, class_name, type_args) = if *is_op {
                &ctx.op_deferred_constraints[*idx]
            } else {
                &ctx.deferred_constraints[*idx]
            };
            // Skip if already resolved.
            // For multi-class spans (same class, different type args at same span),
            // use count-based check to allow all distinct entries through.
            let already_resolved = if multi_class_spans.contains(&(*_constraint_span_dbg, class_name.name)) {
                let resolved_count = ctx.resolved_dicts.get(_constraint_span_dbg)
                    .map_or(0, |v| v.iter().filter(|(c, _)| *c == class_name.name).count());
                let zonked: Vec<Type> = type_args.iter().map(|t| ctx.state.zonk(t.clone())).collect();
                // Count how many distinct type args exist for this (span, class)
                let mut seen: Vec<Vec<Type>> = Vec::new();
                for (i, iop) in &all_constraints {
                    let (sp, cn, ta) = if *iop { &ctx.op_deferred_constraints[*i] } else { &ctx.deferred_constraints[*i] };
                    if *sp == *_constraint_span_dbg && cn.name == class_name.name {
                        let z: Vec<Type> = ta.iter().map(|t| ctx.state.zonk(t.clone())).collect();
                        if !seen.iter().any(|e| e == &z) { seen.push(z); }
                    }
                }
                resolved_count >= seen.len()
            } else {
                ctx.resolved_dicts.get(_constraint_span_dbg).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name))
            };
            if already_resolved { continue; }

            let zonked_args: Vec<Type> = type_args
                .iter()
                .map(|t| ctx.state.zonk(t.clone()))
                .collect();
            // Qualify unqualified type constructors in zonked args using type_head_origins.
            // This ensures that Foldable List becomes Foldable (Data.List.Types.List) so
            // instance matching can distinguish between List from different modules.
            let qualified_args: Vec<Type> = zonked_args.iter().map(|t| {
                qualify_type_head(t, &type_head_origins)
            }).collect();
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
                // Pass given_constraints from enclosing function for parameterized instances.
                let unsolved_method_constraints = codegen_span_to_binding.get(_constraint_span_dbg)
                    .and_then(|bs| ctx.instance_method_constraints.get(bs));
                let dict_expr_result = resolve_dict_expr_from_registry_inner(
                    &combined_registry,
                    &instances,
                    &ctx.state.type_aliases,
                    class_name,
                    &qualified_args,
                    Some(&ctx.type_con_arities),
                    unsolved_method_constraints.map(|v| v.as_slice()),
                    None,
                    false,
                    0,
                    &combined_instance_var_kinds,
                    &inst_name_all_modules,
                    Some(&class_superclasses),
                );
                if let Some(ref dict_expr) = dict_expr_result {
                    let (constraint_span, _, _) = if *is_op {
                        &ctx.op_deferred_constraints[*idx]
                    } else {
                        &ctx.deferred_constraints[*idx]
                    };
                    ctx.resolved_dicts
                        .entry(*constraint_span)
                        .or_insert_with(Vec::new)
                        .push((class_name.name, dict_expr.clone()));

                    // When a constraint with unsolved vars is successfully resolved,
                    // try to unify the unsolved vars with the matched instance's type args.
                    // This enables transitive resolution: e.g., Parallel ?f Aff → ?f = ParAff,
                    // which then allows Alt ?f to be resolved on a subsequent pass.
                    {
                        let type_aliases = ctx.state.type_aliases.clone();
                        try_unify_from_instance(
                            &mut ctx.state,
                            class_name,
                            &zonked_args,
                            &instances,
                            &type_aliases,
                            Some(&ctx.type_con_arities),
                            &combined_instance_var_kinds,
                        );
                    }
                    // Special case for VBus: try_unify_from_instance can't unify ?p and ?e
                    // because VBus instance types have row-tail type vars. Compute concrete
                    // push/event record types directly from the concrete RowList and unify.
                    if class_name.name.eq_str("VBus") && zonked_args.len() == 3 {
                        let ri = ctx.state.zonk(zonked_args[0].clone());
                        let p_arg = ctx.state.zonk(zonked_args[1].clone());
                        let e_arg = ctx.state.zonk(zonked_args[2].clone());
                        let p_has_unif = !ctx.state.free_unif_vars(&p_arg).is_empty();
                        let e_has_unif = !ctx.state.free_unif_vars(&e_arg).is_empty();
                        if p_has_unif || e_has_unif {
                            if let Some((push_ty, event_ty)) = compute_vbus_push_event_types(&ri) {
                                let dummy = crate::span::Span { start: 0, end: 0 };
                                if p_has_unif {
                                    let _ = ctx.state.unify(dummy, &p_arg, &push_ty);
                                }
                                if e_has_unif {
                                    let _ = ctx.state.unify(dummy, &e_arg, &event_ty);
                                }
                            }
                        }
                    }
                }
                continue;
            }

            // Try to resolve the dict — pass given_constraints from the enclosing
            // function's signature so parameterized instances can resolve their
            // sub-constraints via ConstraintArg (e.g., Monad m => MyBind (MyProxy m)).
            let deferred_method_constraints = codegen_span_to_binding.get(_constraint_span_dbg)
                .and_then(|bs| ctx.instance_method_constraints.get(bs));
            let dict_expr_result = resolve_dict_expr_from_registry_inner(
                &combined_registry,
                &instances,
                &ctx.state.type_aliases,
                class_name,
                &qualified_args,
                Some(&ctx.type_con_arities),
                deferred_method_constraints.map(|v| v.as_slice()),
                None,
                false,
                0,
                &combined_instance_var_kinds,
                &inst_name_all_modules,
                Some(&class_superclasses),
            );
            if let Some(ref dict_expr) = dict_expr_result {
                let (constraint_span, _, _) = if *is_op {
                    &ctx.op_deferred_constraints[*idx]
                } else {
                    &ctx.deferred_constraints[*idx]
                };
                ctx.resolved_dicts
                    .entry(*constraint_span)
                    .or_insert_with(Vec::new)
                    .push((class_name.name, dict_expr.clone()));
            }
        }
        } // end deferred_pass loop

        // Note: ConstraintArg resolution for instance method constraints is done in the
        // codegen_deferred_constraints block below, since "given" constraints go there.

        // Constraint parameter resolution for codegen_deferred_constraints (given/instance constraints).
        // Same logic as above, but for constraints that were resolved as "given" in instance scope.
        {
            use crate::typechecker::registry::DictExpr;
            use crate::typechecker::types::TyVarId;

            // Group entries by (instance_id, class_name) — this correctly merges entries from
            // multi-equation methods (which have different binding spans but the same instance ID).
            // Storage: (entry_idx, first_type_arg_after_zonk, binding_span)
            let mut unresolved_groups: HashMap<(usize, Symbol), Vec<(usize, Type, crate::span::Span)>> = HashMap::new();
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
                // Include if any arg contains a variable (Unif or TypeVar) — both bare unif vars
                // and schematic type variables like `App(TypeVar(f), TypeVar(a))` need to be
                // resolved to the correct constraint position.
                let has_vars = zonked_args.iter().any(|a| contains_type_var_or_unif(a));
                if !has_vars { continue; }
                let first_arg = match zonked_args.into_iter().next() {
                    Some(a) => a,
                    None => continue,
                };
                // Use instance ID for grouping (falls back to binding-based grouping if no instance ID)
                let instance_id = if idx < ctx.codegen_deferred_constraint_instance_ids.len() {
                    ctx.codegen_deferred_constraint_instance_ids[idx]
                } else {
                    None
                };
                let group_key = if let Some(iid) = instance_id {
                    (iid, class_name.name.symbol())
                } else {
                    // Fallback: use binding span start as pseudo-instance-id
                    (binding.start as usize, class_name.name.symbol())
                };
                unresolved_groups.entry(group_key)
                    .or_default()
                    .push((idx, first_arg, binding));
            }

            for ((_, class_name_sym), entries) in unresolved_groups {
                let binding_span = entries[0].2;
                let inst_constraints = match ctx.instance_method_constraints.get(&binding_span) {
                    Some(c) => c,
                    None => continue,
                };
                let class_positions: Vec<usize> = inst_constraints.iter().enumerate()
                    .filter(|(_, (c, _))| c.name.symbol() == class_name_sym)
                    .map(|(i, _)| i)
                    .collect();

                // Partition entries by zonked type — entries whose type args zonk to the
                // same type correspond to the same constraint position. This correctly
                // groups entries from different methods that reference the same type param.
                let mut partitions: HashMap<String, (Vec<usize>, Type)> = HashMap::new();
                for (idx, first_arg, _) in &entries {
                    // Re-zonk the stored type arg (in case earlier passes resolved more vars)
                    let zonked = ctx.state.zonk(first_arg.clone());
                    let key = format!("{zonked:?}");
                    let entry = partitions.entry(key).or_insert_with(|| (Vec::new(), zonked.clone()));
                    entry.0.push(*idx);
                }

                // Sort partitions by earliest span (for stable fallback ordering).
                let mut partition_list: Vec<(Vec<usize>, Type)> = partitions.into_values().collect();
                partition_list.sort_by_key(|(indices, _)| {
                    indices.iter().map(|idx| {
                        let (span, _, _, _) = &ctx.codegen_deferred_constraints[*idx];
                        span.start
                    }).min().unwrap_or(0)
                });

                // Type-directed assignment: match each partition to the constraint position
                // whose schematic type pattern best matches the partition's concrete type.
                // This correctly handles cases like `(Arbitrary (f a), Arbitrary a)` where
                // the constraint order differs from the call order in the method body.
                let inst_constraint_args: Vec<&Vec<Type>> = class_positions.iter()
                    .map(|&pos| &inst_constraints[pos].1)
                    .collect();

                let mut partition_assigned = vec![false; partition_list.len()];
                let mut position_used = vec![false; class_positions.len()];

                // Greedy assignment: for each constraint position (in declaration order),
                // find the unassigned partition with the best match score.
                for (ci, &constraint_position) in class_positions.iter().enumerate() {
                    let pattern_args = inst_constraint_args[ci];
                    let mut best_pi: Option<usize> = None;
                    let mut best_score = -1i32;
                    for (pi, (_, part_type)) in partition_list.iter().enumerate() {
                        if partition_assigned[pi] { continue; }
                        // Compare only the first arg: partitions are built from first_arg,
                        // and pattern_args may have more elements (length mismatch → None).
                        let score = if let Some(first_pattern) = pattern_args.first() {
                            crate::typechecker::check::type_utils::constraint_type_match_score(
                                first_pattern,
                                part_type,
                            ).unwrap_or(-1)
                        } else {
                            -1
                        };
                        if score > best_score {
                            best_score = score;
                            best_pi = Some(pi);
                        }
                    }
                    if let Some(pi) = best_pi {
                        partition_assigned[pi] = true;
                        position_used[ci] = true;
                        let indices = &partition_list[pi].0;
                        for idx in indices {
                            let (constraint_span, _, _, _) = &ctx.codegen_deferred_constraints[*idx];
                            ctx.resolved_dicts
                                .entry(*constraint_span)
                                .or_insert_with(Vec::new)
                                .push((ClassName::new(class_name_sym), DictExpr::ConstraintArg(constraint_position)));
                        }
                    }
                }
                // Assign any remaining unmatched partitions sequentially (fallback).
                let mut unused_positions: Vec<usize> = class_positions.iter().enumerate()
                    .filter(|(ci, _)| !position_used[*ci])
                    .map(|(_, &pos)| pos)
                    .collect();
                for (pi, (indices, _)) in partition_list.iter().enumerate() {
                    if partition_assigned[pi] { continue; }
                    if let Some(constraint_position) = unused_positions.first().copied() {
                        unused_positions.remove(0);
                        for idx in indices {
                            let (constraint_span, _, _, _) = &ctx.codegen_deferred_constraints[*idx];
                            ctx.resolved_dicts
                                .entry(*constraint_span)
                                .or_insert_with(Vec::new)
                                .push((ClassName::new(class_name_sym), DictExpr::ConstraintArg(constraint_position)));
                        }
                    }
                }
            }
        }

        // Multi-same-class constraint correction for standalone functions.
        // The counter-based approach in infer.rs assigns ConstraintArg positions
        // based on call order, which may be wrong when the function body doesn't
        // call them in constraint declaration order. Now that types are zonked,
        // we can match type args to determine the correct constraint position
        // and override wrong assignments.
        {
            use crate::typechecker::registry::DictExpr;
            for (idx, (constraint_span, class_name, type_args, _is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
                let binding_span = if idx < ctx.codegen_deferred_constraint_bindings.len() {
                    ctx.codegen_deferred_constraint_bindings[idx]
                } else {
                    None
                };
                let Some(binding) = binding_span else { continue };
                // Only process for standalone functions (not instance methods).
                // Instance method multi-same-class constraints are resolved correctly
                // by the unif-var partition block above (lines 6938+).
                if !ctx.standalone_fn_constraint_spans.contains(&binding) { continue; }
                let inst_constraints = match ctx.instance_method_constraints.get(&binding) {
                    Some(c) => c,
                    None => continue,
                };
                let same_class_positions: Vec<(usize, &Vec<Type>)> = inst_constraints.iter().enumerate()
                    .filter(|(_, (c, _))| c.name == class_name.name)
                    .map(|(i, (_, args))| (i, args))
                    .collect();
                if same_class_positions.len() <= 1 { continue; }

                let zonked_args: Vec<Type> = type_args.iter()
                    .map(|t| ctx.state.zonk(t.clone()))
                    .collect();

                // Try exact structural match first (reference compiler style: binary match/apart)
                let mut exact_match: Option<usize> = None;
                for &(pos, given_args) in &same_class_positions {
                    if given_args.len() != zonked_args.len() { continue; }
                    let all_match = given_args.iter().zip(zonked_args.iter()).all(|(g, a)| {
                        let zonked_g = ctx.state.zonk(g.clone());
                        zonked_g == *a
                    });
                    if all_match {
                        exact_match = Some(pos);
                        break;
                    }
                }

                // If no exact match, try structural matching (type constructors match concrete args)
                let best_pos = exact_match.or_else(|| {
                    let mut best: Option<usize> = None;
                    let mut best_specificity: i32 = -1;
                    for &(pos, given_args) in &same_class_positions {
                        if given_args.len() != zonked_args.len() { continue; }
                        let mut spec = 0i32;
                        let mut compatible = true;
                        for (g, a) in given_args.iter().zip(zonked_args.iter()) {
                            match type_match_specificity_check(g, a) {
                                Some(s) => spec += s,
                                None => { compatible = false; break; }
                            }
                        }
                        if compatible && spec > best_specificity {
                            best_specificity = spec;
                            best = Some(pos);
                        }
                    }
                    best
                });

                if let Some(pos) = best_pos {
                    // Check if there's already a ConstraintArg for this class at this span
                    let existing = ctx.resolved_dicts.get(constraint_span)
                        .and_then(|v| v.iter().find_map(|(c, d)| {
                            if *c == class_name.name {
                                if let DictExpr::ConstraintArg(existing_pos) = d {
                                    Some(*existing_pos)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }));
                    match existing {
                        Some(existing_pos) if existing_pos == pos => {
                            // Already correct, nothing to do
                        }
                        Some(existing_pos) => {
                            // Wrong position from counter — override it
                            if let Some(v) = ctx.resolved_dicts.get_mut(constraint_span) {
                                for (c, d) in v.iter_mut() {
                                    if *c == class_name.name {
                                        if let DictExpr::ConstraintArg(_) = d {
                                            *d = DictExpr::ConstraintArg(pos);
                                        }
                                    }
                                }
                            }
                        }
                        None => {
                            // Not yet resolved — add it
                            ctx.resolved_dicts
                                .entry(*constraint_span)
                                .or_insert_with(Vec::new)
                                .push((class_name.name, DictExpr::ConstraintArg(pos)));
                        }
                    }
                }
            }
        }

        // Fix eagerly-assigned ConstraintArg for instance method constraints.
        // In infer.rs, when a class is "given" (e.g., Ord k, Ord v in scope), the
        // counter-based approach eagerly assigns ConstraintArg(0) to any Ord constraint.
        // But Ord (Iter k v) should resolve via the instance registry (ordIter(dictOrd)(dictOrd1)),
        // not as ConstraintArg(0) (dictOrd). After zonking, we can detect this: if the
        // zonked args have a concrete head type that differs from the given constraint's
        // type args, replace the ConstraintArg with an instance registry lookup.
        {
            use crate::typechecker::registry::DictExpr;
            use crate::typechecker::check::type_utils::extract_head_from_type_tc;
            for (idx, (constraint_span, class_name, type_args, _is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
                // Only look at entries that have a ConstraintArg already
                let existing_pos = match ctx.resolved_dicts.get(constraint_span)
                    .and_then(|v| v.iter().find_map(|(c, d)| {
                        if *c == class_name.name {
                            if let DictExpr::ConstraintArg(pos) = d { Some(*pos) } else { None }
                        } else { None }
                    })) {
                    Some(pos) => pos,
                    None => continue,
                };
                // Only for instance methods (not standalone functions — those are handled above)
                let binding_span = if idx < ctx.codegen_deferred_constraint_bindings.len() {
                    ctx.codegen_deferred_constraint_bindings[idx]
                } else {
                    None
                };
                let Some(binding) = binding_span else { continue };
                if ctx.standalone_fn_constraint_spans.contains(&binding) { continue; }
                let inst_constraints = match ctx.instance_method_constraints.get(&binding) {
                    Some(c) => c,
                    None => continue,
                };

                let zonked_args: Vec<Type> = type_args.iter()
                    .map(|t| ctx.state.zonk(t.clone()))
                    .collect();

                // Check if the zonked args have a concrete head type
                let zonked_head = zonked_args.first().and_then(|t| extract_head_from_type_tc(t));
                let Some(head) = zonked_head else { continue };

                // Check if the given constraint at existing_pos has a matching head
                if let Some((_, given_args)) = inst_constraints.get(existing_pos) {
                    let given_head = given_args.first().and_then(|t| {
                        let zonked_g = ctx.state.zonk(t.clone());
                        extract_head_from_type_tc(&zonked_g)
                    });
                    if given_head == Some(head) {
                        continue; // Heads match — ConstraintArg is correct
                    }
                }

                // Head doesn't match — try instance registry
                let qualified_args2: Vec<Type> = zonked_args.iter().map(|t| {
                    qualify_type_head(t, &type_head_origins)
                }).collect();
                let deferred_method_constraints = ctx.instance_method_constraints.get(&binding);
                let dict_expr_result = resolve_dict_expr_from_registry_inner(
                    &combined_registry,
                    &instances,
                    &ctx.state.type_aliases,
                    class_name,
                    &qualified_args2,
                    Some(&ctx.type_con_arities),
                    deferred_method_constraints.map(|v| v.as_slice()),
                    None,
                    false,
                    0,
                    &combined_instance_var_kinds,
                    &inst_name_all_modules,
                    Some(&class_superclasses),
                );
                if let Some(dict_expr) = dict_expr_result {
                    // Replace the ConstraintArg with the correct dict from registry
                    if let Some(v) = ctx.resolved_dicts.get_mut(constraint_span) {
                        for (c, d) in v.iter_mut() {
                            if *c == class_name.name {
                                if let DictExpr::ConstraintArg(_) = d {
                                    *d = dict_expr.clone();
                                }
                            }
                        }
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

            // Handle Reflectable specially: Reflectable t v => bind v based on t's kind.
            // Reflectable instances are compiler-magic and not in the instance registry.
            let class_str_pre = class_name.name.resolve().unwrap_or_default();
            if class_str_pre == "Reflectable" && zonked_args.len() == 2 {
                if let Type::Unif(id) = &zonked_args[1] {
                    let dummy_span = crate::span::Span { start: 0, end: 0 };
                    let value_type = match &zonked_args[0] {
                        Type::TypeString(_) => {
                            let string_sym = crate::interner::intern("String");
                            Some(Type::Con(qi_type(string_sym)))
                        }
                        Type::TypeInt(_) => {
                            let int_sym = crate::interner::intern("Int");
                            Some(Type::Con(qi_type(int_sym)))
                        }
                        Type::Con(c) => {
                            let name = crate::interner::resolve(c.name_symbol()).unwrap_or_default().to_string();
                            match name.as_str() {
                                "True" | "False" => {
                                    let bool_sym = crate::interner::intern("Boolean");
                                    Some(Type::Con(qi_type(bool_sym)))
                                }
                                "LT" | "EQ" | "GT" => {
                                    let ord_sym = crate::interner::intern("Ordering");
                                    Some(Type::Con(qi_type(ord_sym)))
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    };
                    if let Some(vt) = value_type {
                        let _ = ctx.state.unify(dummy_span, &Type::Unif(*id), &vt);
                    }
                }
                continue;
            }

            let head = zonked_args.first().and_then(|t| extract_head_from_type_tc(t));
            let Some(_head) = head else { continue };
            // Look up matching instance to determine output types.
            // Only unify when exactly one instance matches to avoid ambiguous
            // resolutions (e.g., MonadThrow Error ?m matching both Either and Aff).
            if let Some(known) = lookup_instances(&instances, &class_name) {
                let mut expanding2 = HashSet::new();
                let expanded_args: Vec<Type> = zonked_args
                    .iter()
                    .map(|t| expand_type_aliases_limited_inner(t, &ctx.state.type_aliases, Some(&ctx.type_con_arities), 0, &mut expanding2, None))
                    .collect();
                let mut match_count = 0usize;
                let mut matched_inst: Option<(Vec<Type>, HashMap<TypeVarName, Type>)> = None;
                for (inst_types, _, _) in known {
                    let mut expanding = HashSet::new();
                    let expanded_inst: Vec<Type> = inst_types
                        .iter()
                        .map(|t| expand_type_aliases_limited_inner(t, &ctx.state.type_aliases, Some(&ctx.type_con_arities), 0, &mut expanding, None))
                        .collect();
                    if expanded_inst.len() != expanded_args.len() { continue; }
                    let mut subst: HashMap<TypeVarName, Type> = HashMap::new();
                    let matched = expanded_inst
                        .iter()
                        .zip(expanded_args.iter())
                        .all(|(inst_ty, arg)| match_instance_type(inst_ty, arg, &mut subst));
                    if matched {
                        match_count += 1;
                        if match_count == 1 {
                            matched_inst = Some((expanded_inst, subst));
                        } else {
                            // Multiple matches — ambiguous
                            break;
                        }
                    }
                }
                if match_count == 1 {
                    if let Some((expanded_inst, subst)) = matched_inst {
                        let dummy_span = crate::span::Span { start: 0, end: 0 };
                        for (inst_ty, concrete_arg) in expanded_inst.iter().zip(zonked_args.iter()) {
                            if let Type::Unif(id) = concrete_arg {
                                let resolved_ty = apply_var_subst(&subst, inst_ty);
                                let _ = ctx.state.unify(dummy_span, &Type::Unif(*id), &resolved_ty);
                            }
                        }
                    }
                }
            }
        }

        // Process codegen_deferred_constraints (imported function constraints, codegen-only).
        // Run two passes: first pass resolves what it can, second pass picks up constraints
        // whose type args are now resolved due to bindings from the pre-pass or first pass.
        // After initial passes, do additional zonk+resolve passes for any remaining
        // unresolved constraints with unif vars that may have been solved transitively.
        for _pass in 0..2 {
        for (idx, (constraint_span, class_name, type_args, is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
            // Only skip if THIS specific class was already resolved for this span
            let already_resolved = ctx.resolved_dicts.get(constraint_span).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name));
            if already_resolved { continue; }
            // Use pre-generalization args if available (captured before generalize_excluding
            // replaces unif vars with type variables). Always zonk through current state
            // to resolve any unif vars that have been solved since the snapshot was taken.
            let zonked_args: Vec<Type> = if let Some(pre_gen) = ctx.codegen_deferred_pre_generalized.get(&idx) {
                pre_gen.iter().map(|t| ctx.state.zonk(t.clone())).collect()
            } else {
                type_args
                    .iter()
                    .map(|t| ctx.state.zonk(t.clone()))
                    .collect()
            };


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

            // If the deferred constraint's args contain unsolved vars (type vars or
            // unif vars) and one of the enclosing function's own constraints matches
            // (same class, same concrete positions, variable positions aligned),
            // resolve to ConstraintArg directly.  This handles cases like
            // `shouldContain` (constrained `MonadThrow Error m`) calling `fail`
            // (also needs `MonadThrow Error m`) — the dict must come from the
            // function parameter, not a concrete instance like monadThrowEffect.
            let is_standalone_fn = binding_span
                .map_or(false, |bs| ctx.standalone_fn_constraint_spans.contains(&bs));
            let has_unsolved = zonked_args.iter().any(|t| contains_type_var_or_unif(t));
            if has_unsolved && is_standalone_fn {
                if let Some(mc) = method_constraints {
                    let mut matched = None;
                    for (pos, (gc_class, gc_args)) in mc.iter().enumerate() {
                        if gc_class.name != class_name.name { continue; }
                        if gc_args.len() != zonked_args.len() { continue; }
                        // Strict position-wise compatibility: variable positions must
                        // align (both variable-like) and concrete positions must be equal.
                        // Crucially, a type with a concrete head (e.g., Tuple r) must NOT
                        // match a bare type variable (e.g., m) — the concrete head means
                        // there's a specific instance to use, not the parametric constraint.
                        let args_compatible = gc_args.iter().zip(zonked_args.iter()).all(|(gc, za)| {
                            let za_unsolved = contains_type_var_or_unif(za);
                            let gc_has_var = contains_type_var_or_unif(gc);
                            if za_unsolved && gc_has_var {
                                // Both contain variables, but check structural compatibility:
                                // if za has a concrete type constructor head (like Tuple r),
                                // it should NOT match a bare type variable (like m).
                                let za_head = extract_head_from_type_tc(za);
                                let gc_head = extract_head_from_type_tc(gc);
                                match (za_head, gc_head) {
                                    (Some(zh), Some(gh)) => zh == gh, // same concrete head → compatible
                                    (None, None) => {
                                        // Both are bare variables — if both are TypeVar, they must be
                                        // the same variable. (E.g., Monad m vs Monad g: different vars
                                        // for the same class must not match each other.)
                                        // Unif vars are treated as compatible since they resolve later.
                                        match (za, gc) {
                                            (Type::Var(v1), Type::Var(v2)) => v1 == v2,
                                            _ => true,
                                        }
                                    }
                                    _ => false, // one has concrete head, other doesn't → incompatible
                                }
                            } else if !za_unsolved && !gc_has_var {
                                gc == za // both concrete → must be equal
                            } else {
                                false // mismatch: one variable, one concrete
                            }
                        });
                        if args_compatible {
                            matched = Some(pos);
                            break;
                        }
                    }
                    if let Some(pos) = matched {
                        let dict_expr = DictExpr::ConstraintArg(pos);
                        ctx.resolved_dicts
                            .entry(*constraint_span)
                            .or_insert_with(Vec::new)
                            .push((class_name.name, dict_expr));
                        continue;
                    }
                    // No direct class match — try superclass derivation (transitive).
                    // If class_name is a (transitive) superclass of one of the given constraints,
                    // we can derive the needed dict via a chain of superclass accessor methods.
                    let mut superclass_matched: Option<(usize, Vec<String>)> = None;
                    'sc_outer: for (pos, (gc_class, gc_args)) in mc.iter().enumerate() {
                        if let Some(chain) = instances::find_superclass_chain(
                            &class_superclasses, gc_class, gc_args, class_name, &zonked_args, 0,
                        ) {
                            superclass_matched = Some((pos, chain));
                            break 'sc_outer;
                        }
                    }
                    if let Some((pos, chain)) = superclass_matched {
                        let dict_expr = DictExpr::SuperClassAccess(pos, chain);
                        ctx.resolved_dicts
                            .entry(*constraint_span)
                            .or_insert_with(Vec::new)
                            .push((class_name.name, dict_expr));
                        continue;
                    }
                }
            }

            let qualified_args3: Vec<Type> = zonked_args.iter().map(|t| {
                qualify_type_head(t, &type_head_origins)
            }).collect();
            let dict_expr_result = resolve_dict_expr_from_registry_inner(
                &combined_registry,
                &instances,
                &ctx.state.type_aliases,
                class_name,
                &qualified_args3,
                Some(&ctx.type_con_arities),
                method_constraints.map(|v| v.as_slice()),
                None,
                false,
                0,
                &combined_instance_var_kinds,
                &inst_name_all_modules,
                Some(&class_superclasses),
            );
            // If the resolver returned a fallback Var for a parameterized instance
            // (sub-constraints couldn't be resolved, e.g., from generalized let-bindings),
            // search already-resolved dicts for a properly resolved App with the same
            // instance name. This handles cases where the outer context resolved the
            // same instance correctly at a different call site.
            let dict_expr_result = if let Some(DictExpr::Var(inst_name, ref inst_module)) = dict_expr_result {
                // Check if this instance has constraints (parameterized)
                let has_constraints = instances.values().any(|inst_list| {
                    inst_list.iter().any(|(_, constraints, name_opt)| {
                        name_opt.as_ref() == Some(&inst_name) && !constraints.is_empty()
                    })
                });
                if has_constraints {
                    // Search for a matching App in already-resolved dicts
                    let mut app_match: Option<DictExpr> = None;
                    for (_span, dict_list) in ctx.resolved_dicts.iter() {
                        for (cn, de) in dict_list {
                            if *cn == class_name.name {
                                if let DictExpr::App(app_name, _, _) = de {
                                    if *app_name == inst_name && app_match.is_none() {
                                        app_match = Some(de.clone());
                                    }
                                }
                            }
                        }
                    }
                    if let Some(app_de) = app_match {
                        Some(app_de)
                    } else {
                        Some(DictExpr::Var(inst_name, inst_module.clone()))
                    }
                } else {
                    Some(DictExpr::Var(inst_name, inst_module.clone()))
                }
            } else {
                dict_expr_result
            };
            if let Some(ref dict_expr) = dict_expr_result {
                ctx.resolved_dicts
                    .entry(*constraint_span)
                    .or_insert_with(Vec::new)
                    .push((class_name.name, dict_expr.clone()));

                // When a codegen constraint with unsolved vars is resolved,
                // find the specific resolved instance by name and unify constraint args
                // with its concrete type args. This enables transitive resolution:
                // e.g., Example (m Unit) Unit g resolved to exampleMUnit (instance types
                // [Aff Unit, Unit, Aff]) → unify m = Aff, then Applicative m can resolve.
                {
                    let has_unif = zonked_args.iter().any(|t| {
                        !ctx.state.free_unif_vars(t).is_empty()
                    });
                    if has_unif {
                        // Extract instance name from the resolved dict expr
                        let inst_name_sym = match dict_expr {
                            DictExpr::Var(sym, _) => Some(*sym),
                            DictExpr::App(sym, _, _) => Some(*sym),
                            _ => None,
                        };
                        if let Some(inst_sym) = inst_name_sym {
                            // Find the instance by name in the registry
                            if let Some(known) = lookup_instances(&instances, class_name) {
                                for (inst_types, _, inst_name_opt) in known {
                                    if inst_name_opt.as_ref() == Some(&inst_sym) && inst_types.len() == zonked_args.len() {
                                        // Found the specific instance. Build a substitution
                                        // from positions where the constraint arg is concrete,
                                        // then apply it to resolve instance type vars at
                                        // positions where the constraint arg has unif vars.
                                        let type_aliases = ctx.state.type_aliases.clone();
                                        let mut inst_subst: HashMap<TypeVarName, Type> = HashMap::new();
                                        // Phase 1: bind instance type vars from concrete arg positions
                                        for (inst_ty, arg) in inst_types.iter().zip(zonked_args.iter()) {
                                            if ctx.state.free_unif_vars(arg).is_empty() {
                                                // Concrete arg — use to bind instance type vars
                                                let mut exp = HashSet::new();
                                                let expanded = expand_type_aliases_limited_inner(
                                                    inst_ty, &type_aliases,
                                                    Some(&ctx.type_con_arities), 0, &mut exp, None,
                                                );
                                                match_instance_type(&expanded, arg, &mut inst_subst);
                                            }
                                        }
                                        // Phase 2: for positions with unif vars, apply subst
                                        // and unify
                                        let dummy_span = crate::span::Span { start: 0, end: 0 };
                                        for (inst_ty, arg) in inst_types.iter().zip(zonked_args.iter()) {
                                            if ctx.state.free_unif_vars(arg).is_empty() { continue; }
                                            let mut exp = HashSet::new();
                                            let expanded = expand_type_aliases_limited_inner(
                                                inst_ty, &type_aliases,
                                                Some(&ctx.type_con_arities), 0, &mut exp, None,
                                            );
                                            let resolved = apply_var_subst(&inst_subst, &expanded);
                                            if !contains_type_var(&resolved) {
                                                let _ = ctx.state.unify(dummy_span, arg, &resolved);
                                            }
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        }

        // Extra pass: for unresolved codegen constraints with unsolved unif vars,
        // look at resolved constraints from the same binding span to find the monad type.
        // This handles let-bindings in do-blocks where the monad var was never unified
        // (e.g., `let f = pure x` where the monad is determined by the enclosing context).
        {
            // Build map: binding_span → resolved (class_name, dict_expr, type_args) for resolved constraints
            let mut binding_resolved: HashMap<crate::span::Span, Vec<(ClassName, Vec<Type>)>> = HashMap::new();
            for (idx, (constraint_span, class_name, type_args, _is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
                let already_resolved = ctx.resolved_dicts.get(constraint_span).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name));
                if already_resolved {
                    let binding_span = if idx < ctx.codegen_deferred_constraint_bindings.len() {
                        ctx.codegen_deferred_constraint_bindings[idx]
                    } else {
                        None
                    };
                    if let Some(bs) = binding_span {
                        let zonked_args: Vec<Type> = type_args.iter().map(|t| ctx.state.zonk(t.clone())).collect();
                        binding_resolved.entry(bs).or_default().push((class_name.name, zonked_args));
                    }
                }
            }

            // For each unresolved constraint with unsolved unif vars, check if any resolved
            // constraint from the same binding has the same class (or a superclass) with a concrete type.
            for (idx, (constraint_span, class_name, type_args, _is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
                let already_resolved = ctx.resolved_dicts.get(constraint_span).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name));
                if already_resolved { continue; }

                let zonked_args: Vec<Type> = if let Some(pre_gen) = ctx.codegen_deferred_pre_generalized.get(&idx) {
                    pre_gen.iter().map(|t| ctx.state.zonk(t.clone())).collect()
                } else {
                    type_args.iter().map(|t| ctx.state.zonk(t.clone())).collect()
                };

                let has_unsolved_unif = zonked_args.iter().any(|t| !ctx.state.free_unif_vars(t).is_empty());
                if !has_unsolved_unif { continue; }

                let binding_span = if idx < ctx.codegen_deferred_constraint_bindings.len() {
                    ctx.codegen_deferred_constraint_bindings[idx]
                } else {
                    None
                };
                let bs = match binding_span {
                    Some(bs) => bs,
                    None => continue,
                };

                // Look for resolved constraints in the same binding that have the SAME class
                // with a concrete first arg (the monad type).
                if let Some(resolved_list) = binding_resolved.get(&bs) {
                    let cn = class_name.name;
                    for (resolved_cn, resolved_args) in resolved_list {
                        if *resolved_cn == cn && resolved_args.len() == zonked_args.len() {
                            // Check if the resolved constraint has a concrete first arg
                            // while our unresolved one has an unsolved unif var in the same position
                            let mut can_unify = false;
                            for (za, ra) in zonked_args.iter().zip(resolved_args.iter()) {
                                if !ctx.state.free_unif_vars(za).is_empty() && ctx.state.free_unif_vars(ra).is_empty() {
                                    can_unify = true;
                                }
                            }
                            if can_unify {
                                // Unify the unsolved args with the resolved args
                                let dummy_span = crate::span::Span { start: 0, end: 0 };
                                for (za, ra) in zonked_args.iter().zip(resolved_args.iter()) {
                                    if !ctx.state.free_unif_vars(za).is_empty() && ctx.state.free_unif_vars(ra).is_empty() {
                                        let _ = ctx.state.unify(dummy_span, za, ra);
                                    }
                                }
                                break;
                            }
                        }
                    }
                }
            }

            // After unifying, re-attempt resolution for still-unresolved constraints
            for (idx, (constraint_span, class_name, type_args, is_do_ado)) in ctx.codegen_deferred_constraints.iter().enumerate() {
                let already_resolved = ctx.resolved_dicts.get(constraint_span).map_or(false, |v| v.iter().any(|(c, _)| *c == class_name.name));
                if already_resolved { continue; }

                let zonked_args: Vec<Type> = if let Some(pre_gen) = ctx.codegen_deferred_pre_generalized.get(&idx) {
                    pre_gen.iter().map(|t| ctx.state.zonk(t.clone())).collect()
                } else {
                    type_args.iter().map(|t| ctx.state.zonk(t.clone())).collect()
                };

                if *is_do_ado {
                    let head_extractable = zonked_args.first()
                        .and_then(|t| extract_head_from_type_tc(t))
                        .is_some();
                    if !head_extractable { continue; }
                }

                let binding_span = if idx < ctx.codegen_deferred_constraint_bindings.len() {
                    ctx.codegen_deferred_constraint_bindings[idx]
                } else {
                    None
                };
                let method_constraints = binding_span
                    .and_then(|bs| ctx.instance_method_constraints.get(&bs));

                let qualified_args3: Vec<Type> = zonked_args.iter().map(|t| {
                    qualify_type_head(t, &type_head_origins)
                }).collect();
                let dict_expr_result = resolve_dict_expr_from_registry_inner(
                    &combined_registry,
                    &instances,
                    &ctx.state.type_aliases,
                    class_name,
                    &qualified_args3,
                    Some(&ctx.type_con_arities),
                    method_constraints.map(|v| v.as_slice()),
                    None,
                    false,
                    0,
                    &combined_instance_var_kinds,
                    &inst_name_all_modules,
                    Some(&class_superclasses),
                );
                if let Some(ref dict_expr) = dict_expr_result {
                    ctx.resolved_dicts
                        .entry(*constraint_span)
                        .or_insert_with(Vec::new)
                        .push((class_name.name, dict_expr.clone()));
                }
            }
        }
    }

    // Pass 4: Validate module exports and build export info
    // Collect locally declared type/class names
    let mut declared_types: Vec<TypeName> = Vec::new();
    let mut declared_classes: Vec<ClassName> = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::Data { name, .. } | Decl::Newtype { name, .. } => {
                declared_types.push(TypeName::new(name.value));
            }
            Decl::TypeAlias { name, .. } => {
                declared_types.push(TypeName::new(name.value));
            }
            Decl::Class { name, .. } => {
                declared_classes.push(ClassName::new(name.value));
            }
            Decl::ForeignData { name, .. } => {
                declared_types.push(TypeName::new(name.value));
            }
            _ => {}
        }
    }

    if let Some(ref export_list) = module.exports {
        for export in &export_list.value.exports {
            match export {
                Export::Value(name) => {
                    let sym = name.symbol();
                    if !result_types.contains_key(&ValueName::new(sym)) && env.lookup(ValueName::new(sym)).is_none() {
                        errors.push(TypeError::UnkownExport {
                            span: export_list.span,
                            name: *name,
                        });
                    }
                }
                Export::Type(name, members) => {
                    if !declared_types.contains(name) {
                        errors.push(TypeError::UnkownExport {
                            span: export_list.span,
                            name: ValueName::new(name.symbol()),
                        });
                    } else if let Some(crate::cst::DataMembers::Explicit(ctors)) = members {
                        // Check that each listed constructor actually belongs to this type
                        let valid_ctors = ctx.data_constructors.get(&qi_type(name.symbol()));
                        for ctor in ctors {
                            let is_valid = valid_ctors.map_or(false, |cs| cs.contains(&qi_ctor(ctor.value.symbol())));
                            if !is_valid {
                                errors.push(TypeError::UnkownExport {
                                    span: export_list.span,
                                    name: ValueName::new(ctor.value.symbol()),
                                });
                            }
                        }
                        // Check that ALL constructors are listed — partial constructor
                        // exports are not allowed in PureScript.
                        // T() (empty list) is valid — opaque type export.
                        if !ctors.is_empty() {
                            if let Some(all_ctors) = valid_ctors {
                                let exported_set: std::collections::HashSet<Qualified<ConstructorName>> =
                                    ctors.iter().map(|c| qi_ctor(c.value.symbol())).collect();
                                for ctor in all_ctors {
                                    if !exported_set.contains(ctor) {
                                        errors.push(TypeError::TransitiveExportError {
                                            span: export_list.span,
                                            exported: qi(name.symbol()),
                                            dependency: ctor.to_qi(),
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
                            name: ValueName::new(name.symbol()),
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
        let exported_values: HashSet<ValueName> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Value(n) => Some(*n),
                _ => None,
            })
            .collect();
        let exported_classes: HashSet<ClassName> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Class(n) => Some(*n),
                _ => None,
            })
            .collect();

        // Check: exporting a class member without its class
        for val in &exported_values {
            if let Some((class_name, _)) = ctx.class_methods.get(&Qualified::unqualified(*val)) {
                // Only check locally-defined classes (not imported ones)
                if declared_classes.contains(&class_name.name) && !exported_classes.contains(&class_name.name) {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: qi(val.symbol()),
                        dependency: class_name.to_qi(),
                    });
                }
            }
        }

        // Check: exporting a class without its members
        for cls in &exported_classes {
            for (method, (class_name, _)) in &ctx.class_methods {
                if *class_name == Qualified::unqualified(*cls) && !exported_values.contains(&method.name) {
                    // Only check locally-defined class methods
                    if local_values.contains_key(&method.name) {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(cls.symbol()),
                            dependency: method.to_qi(),
                        });
                        break; // One error per class is enough
                    }
                }
            }
        }

        // Check: exporting a class without its superclasses (transitive)
        let declared_class_set: HashSet<ClassName> = declared_classes.iter().copied().collect();
        for cls in &exported_classes {
            if let Some((_, sc_constraints)) = class_superclasses.get(&Qualified::unqualified(*cls)) {
                for (sc_class, _) in sc_constraints {
                    // Only check locally-defined superclasses
                    if sc_class.module.is_none() && declared_class_set.contains(&sc_class.name) && !exported_classes.contains(&sc_class.name)
                    {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(cls.symbol()),
                            dependency: sc_class.to_qi(),
                        });
                    }
                }
            }
        }

        // Check: exporting a value operator without its target function (local defs only)
        for val in &exported_values {
            if let Some(&target) = value_op_targets.get(&val.symbol()) {
                // Only check locally-defined constructors, not imported ones
                let is_local_ctor = ctx.ctor_details.contains_key(&qi_ctor(target))
                    && local_values.contains_key(&ValueName::new(target));
                if is_local_ctor {
                    // Operator aliases a data constructor — check that the constructor
                    // is exported through its parent type's constructor list.
                    let target_ctor_q = qi_ctor(target);
                    let ctor_exported = export_list.value.exports.iter().any(|e| {
                        if let Export::Type(ty_name, Some(members)) = e {
                            let type_ctors = ctx.data_constructors.get(&qi_type(ty_name.symbol()));
                            let has_this_ctor = type_ctors.map_or(false, |cs| cs.contains(&target_ctor_q));
                            has_this_ctor
                                && match members {
                                    crate::cst::DataMembers::All => true,
                                    crate::cst::DataMembers::Explicit(cs) => cs.iter().any(|c| c.value.symbol() == target),
                                }
                        } else {
                            false
                        }
                    });
                    if !ctor_exported {
                        errors.push(TypeError::TransitiveExportError {
                            span: export_list.span,
                            exported: qi(val.symbol()),
                            dependency: qi(target),
                        });
                    }
                } else if local_values.contains_key(&ValueName::new(target)) && !exported_values.contains(&ValueName::new(target)) {
                    errors.push(TypeError::TransitiveExportError {
                        span: export_list.span,
                        exported: qi(val.symbol()),
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
                Export::Type(n, _) => Some(n.symbol()),
                _ => None,
            })
            .collect();
        let exported_type_ops: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::TypeOp(n) => Some(n.symbol()),
                _ => None,
            })
            .collect();
        let declared_type_set: HashSet<Symbol> = declared_types.iter().map(|t| t.symbol()).collect();
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
            if let Some((_, body)) = ctx.state.type_aliases.get(&Qualified::unqualified(TypeName::new(ty_name))) {
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
                if let Some(ctors) = ctx.data_constructors.get(&qi_type(ty_name.symbol())) {
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
                                            exported: qi(ty_name.symbol()),
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
                        if name.value == ty_name.symbol() {
                            for kind_ann in type_var_kind_anns.iter().flatten() {
                                let mut kind_refs = HashSet::new();
                                collect_type_refs(kind_ann, &mut kind_refs);
                                for dep in &kind_refs {
                                    if declared_type_set.contains(dep)
                                        && !exported_types.contains(dep)
                                    {
                                        errors.push(TypeError::TransitiveExportError {
                                            span: export_list.span,
                                            exported: qi(ty_name.symbol()),
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
                Export::Value(n) => Some(n.symbol()),
                _ => None,
            })
            .collect();
        let exp_types: HashSet<Symbol> = export_list
            .value
            .exports
            .iter()
            .filter_map(|e| match e {
                Export::Type(n, _) => Some(n.symbol()),
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
            if let Some(scheme) = local_values.get(&ValueName::new(val)) {
                let zonked = ctx.state.zonk(scheme.ty.clone());
                let mut referenced_types = Vec::new();
                collect_type_constructors(&zonked, &mut referenced_types);
                for ty_name in &referenced_types {
                    // Only flag local non-alias types that are not exported
                    if declared_types.contains(&TypeName::new(*ty_name))
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
    let local_type_set: HashSet<Symbol> = declared_types.iter().map(|t| t.symbol()).collect();
    let local_class_set: HashSet<ClassName> = declared_classes.iter().copied().collect();

    // Build a filtered alias map for export expansion that excludes aliases from
    // qualified imports that collide with data types. This prevents wrong expansion
    // when e.g. `type GqlError = { ... }` alias (from a qualified import) would
    let mut export_data_constructors: HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>> = HashMap::new();
    let mut export_ctor_details: HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<Type>)> = HashMap::new();
    for type_name in &declared_types {
        if let Some(ctors) = ctx.data_constructors.get(&qi_type(type_name.symbol())) {
            export_data_constructors.insert(qi_type(type_name.symbol()), ctors.clone());
            for ctor in ctors {
                if let Some((parent, tvs, fields)) = ctx.ctor_details.get(ctor) {
                    // Expand type aliases in field types so downstream modules
                    // can resolve them even without importing the alias names
                    // (e.g. NutF wraps Nut' which is a local alias for Entity Int (Node payload)).
                    let expanded_fields: Vec<Type> = fields.iter()
                        .map(|f| expand_type_aliases(f, &ctx.state.type_aliases))
                        .collect();
                    export_ctor_details.insert(*ctor, (*parent, tvs.clone(), expanded_fields));
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
            export_ctor_details.insert(*name, (*parent, tvs.clone(), expanded_fields));
        }
    }

    let mut export_class_methods: HashMap<Qualified<ValueName>, (Qualified<ClassName>, Vec<TypeVarName>)> = HashMap::new();
    for (method, (class_name, tvs)) in &ctx.class_methods {
        if local_class_set.contains(&class_name.name) {
            export_class_methods.insert(*method, (*class_name, tvs.clone()));
        }
    }
    // Register locally-defined class names as types in data_constructors so they
    // participate in ExportConflict detection (classes are types in PureScript).
    for class_name in &declared_classes {
        export_data_constructors
            .entry(qi_type(class_name.symbol()))
            .or_insert_with(Vec::new);
    }

    let mut export_instances: HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>> =
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

    let mut export_type_operators: HashMap<Qualified<TypeOpName>, Qualified<TypeName>> = HashMap::new();
    let mut export_type_fixities: HashMap<Qualified<TypeOpName>, (Associativity, u8)> = HashMap::new();
    let mut export_value_fixities: HashMap<Qualified<OpName>, (Associativity, u8)> = HashMap::new();
    let mut export_function_op_aliases: HashSet<Qualified<OpName>> = HashSet::new();
    let mut export_value_operator_targets: HashMap<Qualified<OpName>, Qualified<ValueName>> = HashMap::new();
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
                export_type_operators.insert(qi_type_op(operator.value), qi_type(target.name));
                export_type_fixities.insert(qi_type_op(operator.value), (*associativity, *precedence));
            } else {
                export_value_fixities.insert(qi_op(operator.value), (*associativity, *precedence));
                export_value_operator_targets.insert(qi_op(operator.value), qi_value(target.name));
                // Track operators that alias functions (not constructors)
                if !ctx.ctor_details.contains_key(&qi_ctor(target.name)) {
                    export_function_op_aliases.insert(qi_op(operator.value));
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
    let self_ref_qis: HashSet<Qualified<TypeName>> = ctx.state.self_referential_aliases
        .iter()
        .filter(|&&name| {
            let name_sym = name.symbol();
            // Check if the DIRECT body contains the self-reference
            if let Some((params, body)) = ctx.state.type_aliases.get(&Qualified::unqualified(name)) {
                let param_count = params.len();
                if contains_self_referential_usage_in_type(body, name_sym, param_count) {
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
        .map(|s| qi_type(s.symbol()))
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
            .map(|name| name.symbol())
            .collect();
        // Collect type constructor names from imported (non-locally-defined) alias bodies
        // that are GENUINELY data types in some registry module.
        let mut imported_body_cons: HashSet<Symbol> = HashSet::new();
        for (name, (_params, body)) in &ctx.state.type_aliases {
            if has_type_alias_def.contains(&name.name) {
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
            if let Some((params, _)) = ctx.state.type_aliases.get(&Qualified::unqualified(TypeName::new(*con_name))) {
                if params.is_empty()
                    && ctx.type_con_arities.contains_key(&qi_type(*con_name))
                    && !has_type_alias_def.contains(&TypeName::new(*con_name))
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
    let export_type_aliases: HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)> = ctx
        .state
        .type_aliases
        .iter()
        .filter(|(name, _)| {
            // Keep locally-defined aliases, but ONLY under unqualified keys.
            // Qualified keys like `H.ComponentHTML` share the same .name as the
            // local alias `ComponentHTML` but come from imports and have different
            // arity/body — exporting them would cause downstream import collisions.
            if name.module.is_none() && has_type_alias_def.contains(&name.name) {
                return true;
            }
            // Exclude aliases with a module qualifier — these came from qualified
            // imports (e.g. `import M as Q`) and are import-specific, not part of
            // this module's public API.
            if name.module.is_some() {
                return false;
            }
            // Exclude aliases that came only from qualified imports
            !ctx.qualified_import_unqual_aliases.contains(&name.name)
        })
        .map(|(name, (params, body))| {
            let expanded_body = if has_type_alias_def.contains(&name.name) {
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
            (*name, (params.clone(), expanded_body))
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
    ctx.state.zonk_con_blockers = con_zero_blockers.iter().map(|s| TypeName::new(*s)).collect();
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
        let mut unif_to_var: HashMap<TyVarId, TypeVarName> = HashMap::new();
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
        value_origins.insert(name.symbol(), current_mod_sym);
    }
    for name in export_data_constructors.keys() {
        type_origins.insert(name.name.symbol(), current_mod_sym);
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
                type_origins.entry(name.symbol()).or_insert(origin);
            }
            // Also propagate value_origins and class_origins from imports.
            // Without this, re-exported values (like Tuple constructor from Prelude)
            // default to source_mod_sym, incorrectly marking them as locally defined
            // and causing false export conflicts.
            // For explicit imports, only propagate origins for names in the import list.
            // Without this filter, wildcard imports inside the imported module pollute
            // origins (e.g., Class has `import Decoders` wildcard, so Class's
            // value_origins[getField] = Decoders. If Facade imports both Class and
            // Combinators, the first-wins or_insert picks Decoders over Combinators).
            match &import_decl.imports {
                Some(ImportList::Explicit(items)) => {
                    let imported_names: HashSet<Symbol> = items.iter().map(|i| i.name()).collect();
                    // Also include class method names for imported classes
                    let mut all_imported = imported_names.clone();
                    for item in items {
                        if let Import::Class(cn) = item {
                            for (method_qi, (class_qi, _)) in &mod_exports.class_methods {
                                if class_qi.name_symbol() == cn.value.symbol() {
                                    all_imported.insert(method_qi.name_symbol());
                                }
                            }
                        }
                    }
                    for (&name, &origin) in &mod_exports.value_origins {
                        if all_imported.contains(&name.symbol()) {
                            value_origins.entry(name.symbol()).or_insert(origin);
                        }
                    }
                }
                _ => {
                    // Wildcard or hiding import: propagate all origins
                    for (&name, &origin) in &mod_exports.value_origins {
                        value_origins.entry(name.symbol()).or_insert(origin);
                    }
                }
            }
            for (&name, &origin) in &mod_exports.class_origins {
                class_origins.entry(name.symbol()).or_insert(origin);
            }
        }
    }
    for class_name in &declared_classes {
        class_origins.insert(class_name.symbol(), current_mod_sym);
    }
    for (_, (class_name, _)) in &export_class_methods {
        class_origins.insert(class_name.name.symbol(), current_mod_sym);
    }
    // Type aliases in local_values were already expanded at lines 7148-7158 using
    // expand_type_aliases_limited_inner (which handles qualified names correctly).
    // Do NOT re-expand here: expand_type_aliases uses unqualified lookup which would
    // incorrectly expand data type references (e.g. HATS.Easing) as aliases.
    // Re-zonk record update types now that all deferred constraints are resolved.
    // During inference, record types may have unsolved row-tail unif vars.
    // Re-zonk record update types now that all deferred constraints are resolved.
    // During inference, record types may have unsolved row-tail unif vars that
    // prevent knowing all fields. After full unification, these may be resolved.
    for (span, record_ty) in &ctx.record_update_types {
        let zonked = ctx.state.zonk(record_ty.clone());
        if let Type::Record(fields, tail) = &zonked {
            let has_open_tail = tail.as_ref().map_or(false, |t| {
                matches!(**t, Type::Unif(_))
            });
            if has_open_tail {
                // Still has open row tail — remove any partial entry so codegen
                // uses the for-in copy fallback
                ctx.record_update_fields.remove(span);
                continue;
            }
            let field_names: Vec<LabelName> = fields.iter().map(|(name, _)| *name).collect();
            // Insert or update if we now have more fields
            let should_update = ctx.record_update_fields.get(span)
                .map_or(true, |existing| field_names.len() > existing.len());
            if should_update {
                ctx.record_update_fields.insert(*span, field_names);
            }
        }
    }

    let mut module_exports = ModuleExports {
        values: local_values.iter().map(|(&k, v)| {
            (Qualified::unqualified(k), Scheme { forall_vars: v.forall_vars.clone(), ty: v.ty.clone() })
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
        constrained_class_methods: ctx.constrained_class_methods.iter().map(|v| Qualified::unqualified(*v)).collect(),
        type_aliases: export_type_aliases,
        class_param_counts: class_param_counts,
        value_origins: value_origins.into_iter().map(|(k, v)| (ValueName::new(k), v)).collect(),
        type_origins: type_origins.into_iter().map(|(k, v)| (TypeName::new(k), v)).collect(),
        class_origins: class_origins.into_iter().map(|(k, v)| (ClassName::new(k), v)).collect(),
        operator_class_targets: ctx.operator_class_targets.iter().map(|(k, v)| (k.name, v.name)).collect(),
        class_fundeps: ctx.class_fundeps.iter().map(|(k, v)| {
            let (tvs, fds) = v;
            (k.name, (tvs.clone(), fds.clone()))
        }).collect(),
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
                if entry.is_empty() {
                    entry.extend(constraints.iter().cloned());
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
        self_referential_aliases: ctx.state.self_referential_aliases.iter().copied().collect(),
        type_kinds: saved_type_kinds
            .iter()
            .filter(|(name, _)| local_type_names.contains(&TypeName::new(name.name.symbol())))
            .map(|(name, kind)| {
                let generalized = generalize_kind_for_export(kind);
                // Strip import-alias module qualifiers from exported kinds so downstream
                // modules can add their own qualifiers via qualify_kind_refs.
                (TypeName::new(name.name.symbol()), strip_kind_qualifiers(&generalized))
            })
            .collect(),
        class_type_kinds: saved_class_kinds
            .iter()
            .map(|(name, kind)| {
                let generalized = generalize_kind_for_export(kind);
                (name.name, strip_kind_qualifiers(&generalized))
            })
            .collect(),
        class_superclasses: class_superclasses.iter().map(|(k, v)| {
            let (tvs, constraints) = v;
            (*k, (tvs.iter().map(|s| TypeVarName::new(*s)).collect(), constraints.clone()))
        }).collect(),
        method_own_constraints: ctx.method_own_constraints.iter().map(|(k, v)| (Qualified::unqualified(*k), v.clone())).collect(),
        method_own_constraint_details: ctx.method_own_constraint_details.clone(),
        module_doc: Vec::new(), // filled in by the outer CST-level wrapper
        instance_registry: instance_registry_entries,
        instance_modules: instance_module_entries,
        resolved_dicts: ctx.resolved_dicts.iter().map(|(span, dicts)| (*span, dicts.iter().map(|(c, d)| (c.symbol(), d.clone())).collect())).collect(),
        let_binding_constraints: ctx.let_binding_constraints.clone(),
        record_update_fields: ctx.record_update_fields.clone(),
        class_method_order: ctx.class_method_order.iter().map(|(k, v)| (*k, v.clone())).collect(),
        return_type_constraints: ctx.return_type_constraints.clone(),
        return_type_arrow_depth: ctx.return_type_arrow_depth.clone(),
        instance_var_kinds: instance_var_kinds_entries,
        resolved_constructors: ctx.resolved_constructors.clone(),
    };
    // Populate partial_value_names from AST type signatures
    for decl in &module.decls {
        if let Decl::TypeSignature { name, ty, .. } = decl {
            if has_partial_constraint(ty) {
                module_exports.partial_value_names.insert(ValueName::new(name.value));
            }
        }
    }
    // Ensure operator targets (e.g. Tuple for /\) are included in exported values and
    // ctor_details, even when the target was imported rather than locally defined.
    for (_op, target) in &module_exports.value_operator_targets.clone() {
        if !module_exports.values.contains_key(target) {
            if let Some(scheme) = env.lookup(ValueName::new(target.name_symbol())) {
                let mut scheme = scheme.clone();
                scheme.ty = ctx.state.zonk(scheme.ty);
                // Replace any remaining Unif vars
                let mut unif_to_var: HashMap<TyVarId, TypeVarName> = HashMap::new();
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
        let target_as_ctor = target.map(names::value_as_constructor);
        if !module_exports.ctor_details.contains_key(&target_as_ctor) {
            if let Some(details) = ctx.ctor_details.get(&target_as_ctor) {
                module_exports.ctor_details.insert(target_as_ctor, (details.0.clone(), details.1.clone(), details.2.clone()));
            }
        }
    }

    // Add constructor schemes to exported values so that `Type(..)` exports and
    // downstream `import M (Type(..))` can find constructor type schemes.
    // Constructors are registered in `env` during type checking but not in `local_values`.
    for (_type_name, ctors) in &module_exports.data_constructors.clone() {
        for ctor in ctors {
            let ctor_as_value = ctor.map(names::constructor_as_value);
            if !module_exports.values.contains_key(&ctor_as_value) {
                if let Some(scheme) = env.lookup(ValueName::new(ctor.name_symbol())) {
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
                    let mut unif_to_var: HashMap<TyVarId, TypeVarName> = HashMap::new();
                    collect_unif_var_ids(&scheme.ty, &mut unif_to_var);
                    if !unif_to_var.is_empty() {
                        scheme.ty = replace_unif_with_vars(&scheme.ty, &unif_to_var);
                        for var_name in unif_to_var.values() {
                            if !scheme.forall_vars.contains(var_name) {
                                scheme.forall_vars.push(*var_name);
                            }
                        }
                    }
                    module_exports.values.insert(ctor_as_value, scheme);
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
    let saved_type_kinds_tn: HashMap<TypeName, Type> = saved_type_kinds.iter().map(|(k, v)| (TypeName::new(k.name.symbol()), v.clone())).collect();
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
                    Decl::Value { name: n, span, .. } if ValueName::new(n.value) == _name => Some(*span),
                    _ => None,
                })
                .unwrap_or(Span::new(0, 0));
            if let Err(e) =
                crate::typechecker::kind::check_inferred_type_kind(ty, &saved_type_kinds_tn, decl_span)
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
                &saved_type_kinds_tn,
                *span,
            ) {
                errors.push(e);
            }
        }
    }

    // Save ctor_details/data_constructors for locally-declared types before export filtering.
    // Codegen needs these for ALL local types (including unexported ones) for instanceof
    // checks and derive newtype instances. Only include locally-declared types to avoid
    // leaking imported constructors into re-export lists.
    let local_type_names: HashSet<Qualified<TypeName>> = declared_types.iter()
        .map(|t| Qualified::unqualified(*t))
        .collect();
    let all_data_constructors: HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>> =
        module_exports.data_constructors.iter()
            .filter(|(name, _)| local_type_names.contains(name))
            .map(|(k, v)| (*k, v.clone()))
            .collect();
    let local_ctor_names: HashSet<Qualified<ConstructorName>> = all_data_constructors.values()
        .flat_map(|ctors| ctors.iter().copied())
        .collect();
    let all_ctor_details = module_exports.ctor_details.iter()
        .filter(|(name, _)| local_ctor_names.contains(name))
        .map(|(k, v)| (*k, v.clone()))
        .collect();

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
        all_ctor_details,
        all_data_constructors,
    }
}

/// Create a qualified symbol by combining a module alias with a name.
fn qualified_symbol(module: Symbol, name: Symbol) -> Symbol {
    crate::interner::intern_qualified(module, name)
}

/// Compute the push-record and event-record types from a resolved VBus RowList.
/// VBus has functional dependency ri -> p e, so given a concrete ri, p and e are fully determined.
/// This is used to unify the unsolved ?p and ?e type vars after VBus is resolved in the
/// deferred constraint loop, enabling downstream Show constraints to be resolved.
///
/// RowList structure: App(App(App(Con(Cons), TypeString(key)), field_ty), rest) | Con(Nil)
/// For each entry:
///   - V(inner_row): push field = push_record(inner_rl), event field = event_record(inner_rl)
///   - z: push field = z -> Effect Unit, event field = Event z
fn compute_vbus_push_event_types(rl: &Type) -> Option<(Type, Type)> {
    let cons_sym = crate::interner::intern("Cons");
    let nil_sym = crate::interner::intern("Nil");
    let v_sym = crate::interner::intern("V");
    let effect_sym = crate::interner::intern("Effect");
    let event_sym = crate::interner::intern("Event");
    let unit_sym = crate::interner::intern("Unit");

    fn go(rl: &Type, cons_sym: Symbol, nil_sym: Symbol, v_sym: Symbol, effect_sym: Symbol, event_sym: Symbol, unit_sym: Symbol) -> Option<(Vec<(LabelName, Type)>, Vec<(LabelName, Type)>)> {
        match rl {
            // Nil → empty records
            Type::Con(qi) if qi.name.symbol() == nil_sym => Some((vec![], vec![])),
            // Cons key field_ty rest
            Type::App(f3_key_ft, rest) => {
                let (key_ty, field_ty) = match f3_key_ft.as_ref() {
                    Type::App(f3_key, ft) => (f3_key.as_ref(), ft.as_ref()),
                    _ => return None,
                };
                // f3_key is App(App(Con(Cons), TypeString(key)))
                // Actually the structure is App(App(App(Con(Cons), key), field_ty), rest)
                // So f3_key_ft = App(App(Con(Cons), key), field_ty) — no, let me re-check.
                // Structure: App( App( App(Con(Cons), TypeString(key)), field_ty ), rest )
                // So: f3_key_ft = App(App(Con(Cons), TypeString(key)), field_ty) — this is matched above as
                // App(f3_key, ft) where f3_key = App(Con(Cons), TypeString(key)) and ft = field_ty
                let label_sym = match key_ty {
                    Type::App(cons_ty, key_str) => {
                        // cons_ty should be Con(Cons), key_str should be TypeString(label)
                        let is_cons = matches!(cons_ty.as_ref(), Type::Con(qi) if qi.name.symbol() == cons_sym);
                        if !is_cons { return None; }
                        match key_str.as_ref() {
                            Type::TypeString(sym) => *sym,
                            _ => return None,
                        }
                    }
                    _ => return None,
                };
                let label = LabelName::new(label_sym);
                let (mut push_fields, mut event_fields) = go(rest, cons_sym, nil_sym, v_sym, effect_sym, event_sym, unit_sym)?;

                // Check if field_ty is V(inner_row)
                match field_ty {
                    Type::App(inner_f, inner_row) if matches!(inner_f.as_ref(), Type::Con(qi) if qi.name.symbol() == v_sym) => {
                        // V case: inner_row is a Record — build RowList from it, recurse
                        let inner_rl = match inner_row.as_ref() {
                            Type::Record(fields, _) => {
                                let mut sorted = fields.clone();
                                sorted.sort_by(|(a, _), (b, _)| a.to_string().cmp(&b.to_string()));
                                let nil_ty = Type::Con(qi_type(nil_sym));
                                let mut rl_ty = nil_ty;
                                for (lbl, ty) in sorted.iter().rev() {
                                    let lbl_sym = crate::interner::intern(&lbl.to_string());
                                    rl_ty = Type::App(
                                        Box::new(Type::App(
                                            Box::new(Type::App(
                                                Box::new(Type::Con(qi_type(cons_sym))),
                                                Box::new(Type::TypeString(lbl_sym)),
                                            )),
                                            Box::new(ty.clone()),
                                        )),
                                        Box::new(rl_ty),
                                    );
                                }
                                rl_ty
                            }
                            _ => return None,
                        };
                        let (inner_push, inner_event) = go(&inner_rl, cons_sym, nil_sym, v_sym, effect_sym, event_sym, unit_sym)?;
                        push_fields.insert(0, (label, Type::Record(inner_push, None)));
                        event_fields.insert(0, (label, Type::Record(inner_event, None)));
                    }
                    z => {
                        // Non-V: push = z -> Effect Unit, event = Event z
                        let effect_unit = Type::App(
                            Box::new(Type::Con(qi_type(effect_sym))),
                            Box::new(Type::Con(qi_type(unit_sym))),
                        );
                        let push_fn = Type::Fun(Box::new(z.clone()), Box::new(effect_unit));
                        let event_ty = Type::App(
                            Box::new(Type::Con(qi_type(event_sym))),
                            Box::new(z.clone()),
                        );
                        push_fields.insert(0, (label, push_fn));
                        event_fields.insert(0, (label, event_ty));
                    }
                }
                Some((push_fields, event_fields))
            }
            _ => None,
        }
    }

    let (push_fields, event_fields) = go(rl, cons_sym, nil_sym, v_sym, effect_sym, event_sym, unit_sym)?;
    Some((
        Type::Record(push_fields, None),
        Type::Record(event_fields, None),
    ))
}

/// Compute how specifically a "given" constraint type matches an "actual" constraint type.
/// Returns Some(specificity_score) if compatible, None if incompatible.
/// Type variables in the given position match anything (score 0), matching
/// constructors score higher. Used for multi-same-class constraint resolution.
fn type_match_specificity_check(given: &Type, actual: &Type) -> Option<i32> {
    match (given, actual) {
        // Type variable in given position — matches anything but low specificity
        (Type::Var(_), _) | (Type::Unif(_), _) => Some(0),
        // Matching constructors — high specificity
        (Type::Con(c1), Type::Con(c2)) => {
            if c1.name == c2.name { Some(10) } else { None }
        }
        // Both applications — structural match gives bonus specificity
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            let fs = type_match_specificity_check(f1, f2)?;
            let as_ = type_match_specificity_check(a1, a2)?;
            // Bonus for matching App structure (even if inner types are wildcards)
            Some(fs + as_ + 1)
        }
        (Type::App(_, _), Type::Con(_)) | (Type::Con(_), Type::App(_, _)) => None,
        (Type::Fun(a1, r1), Type::Fun(a2, r2)) => {
            let as_ = type_match_specificity_check(a1, a2)?;
            let rs = type_match_specificity_check(r1, r2)?;
            Some(as_ + rs + 1)
        }
        (_, Type::Var(_)) | (_, Type::Unif(_)) => Some(0),
        _ => None,
    }
}

