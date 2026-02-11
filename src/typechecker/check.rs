use std::collections::{HashMap, HashSet};

use crate::cst::{Binder, DataMembers, Decl, Export, Import, ImportList, Module};
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::{check_exhaustiveness, extract_type_con, is_unconditional_for_exhaustiveness, InferCtx};
use crate::typechecker::types::{Scheme, Type};

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
}

/// Registry of compiled modules, used to resolve imports.
#[derive(Debug, Clone, Default)]
pub struct ModuleRegistry {
    modules: HashMap<Vec<Symbol>, ModuleExports>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, name: &[Symbol], exports: ModuleExports) {
        self.modules.insert(name.to_vec(), exports);
    }

    pub fn lookup(&self, name: &[Symbol]) -> Option<&ModuleExports> {
        self.modules.get(name)
    }
}

/// Result of typechecking a module: partial type map + accumulated errors + exports.
pub struct CheckResult {
    pub types: HashMap<Symbol, Type>,
    pub errors: Vec<TypeError>,
    pub exports: ModuleExports,
}

/// Build the exports for the built-in Prim module.
/// Prim provides core types (Int, Number, String, Char, Boolean, Array, Function, Record)
/// and is implicitly imported unqualified in every module.
fn prim_exports() -> ModuleExports {
    use crate::interner::intern;
    let mut exports = ModuleExports::default();

    // Register Prim types as known types (empty constructor lists since they're opaque).
    // This makes them findable by the import system (import_item looks up data_constructors).
    for name in &["Int", "Number", "String", "Char", "Boolean", "Array", "Function", "Record"] {
        exports.data_constructors.insert(intern(name), Vec::new());
    }

    exports
}

/// Check if a CST ModuleName matches "Prim".
fn is_prim_module(module_name: &crate::cst::ModuleName) -> bool {
    module_name.parts.len() == 1
        && crate::interner::resolve(module_name.parts[0]).unwrap_or_default() == "Prim"
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

    // Implicitly import Prim unqualified, unless the module explicitly imports
    // Prim as qualified (e.g. `import Prim as P`).
    let prim = prim_exports();
    let has_qualified_prim = module.imports.iter().any(|imp| {
        is_prim_module(&imp.module) && imp.qualified.is_some()
    });
    if !has_qualified_prim {
        import_all(&prim, &mut env, &mut ctx, &mut instances, None);
    }

    // Process imports: bring imported names into scope
    process_imports(module, registry, &mut env, &mut ctx, &mut instances, &mut errors);

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
        if let Decl::Fixity { span, target, operator, is_type, .. } = decl {
            if *is_type {
                seen_type_ops.entry(operator.value).or_default().push(*span);
                ctx.type_operators.insert(operator.value, target.name);
            } else {
                seen_value_ops.entry(operator.value).or_default().push(*span);
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
                match convert_type_expr(ty, &type_ops, &ctx.known_types) {
                    Ok(converted) => {
                        signatures.insert(name.value, (*span, converted));
                    }
                    Err(e) => errors.push(e),
                }
            }
            Decl::Data {
                name, type_vars, constructors, ..
            } => {
                let type_var_syms: Vec<Symbol> =
                    type_vars.iter().map(|tv| tv.value).collect();

                // Build the result type: TypeName tv1 tv2 ...
                let mut result_type = Type::Con(name.value);
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(tv));
                }

                // Register constructors for exhaustiveness checking
                let ctor_names: Vec<Symbol> = constructors.iter().map(|c| c.name.value).collect();
                ctx.data_constructors.insert(name.value, ctor_names);

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
                name, type_vars, constructor, ty, ..
            } => {
                // Register constructor for exhaustiveness checking
                ctx.data_constructors.insert(name.value, vec![constructor.value]);

                let type_var_syms: Vec<Symbol> =
                    type_vars.iter().map(|tv| tv.value).collect();

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
                    Err(e) => errors.push(e),
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
            Decl::Class { name, type_vars, members, .. } => {
                // Register class methods in the environment with their declared types
                let type_var_syms: Vec<Symbol> =
                    type_vars.iter().map(|tv| tv.value).collect();
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
                            local_values.insert(member.name.value, scheme);
                            // Track that this method belongs to this class
                            ctx.class_methods.insert(
                                member.name.value,
                                (name.value, type_var_syms.clone()),
                            );
                        }
                        Err(e) => errors.push(e),
                    }
                }
            }
            Decl::Instance { class_name, types, constraints, members, .. } => {
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
                    instances.entry(class_name.name).or_default().push((inst_types, inst_constraints));
                }

                // Typecheck instance method bodies (simplified: just typecheck the value decls)
                for member_decl in members {
                    if let Decl::Value { name, span, binders, guarded, where_clause, .. } = member_decl {
                        let sig = signatures.get(&name.value).map(|(_, ty)| ty);
                        if let Err(e) = check_value_decl(
                            &mut ctx, &env, name.value, *span,
                            binders, guarded, where_clause, sig,
                        ) {
                            errors.push(e);
                        }
                    }
                }
            }
            Decl::Fixity { is_type, .. } => {
                if !*is_type {
                    // Value-level fixity: deferred to after Pass 2 so the target
                    // function's type is available in env.
                }
            }
            Decl::TypeAlias { type_vars, ty, .. } => {
                if type_vars.is_empty() {
                    if let Err(e) = convert_type_expr(ty, &type_ops, &ctx.known_types) {
                        errors.push(e);
                    }
                }
            }
            Decl::ForeignData { .. } => {
                // Foreign data registers a type name but doesn't need typechecker action
                // since Type::Con(name) works without prior declaration.
            }
            Decl::Derive { .. } => {
                // Derived instances are not yet handled.
            }
            Decl::Value { .. } => {
                // Handled in Pass 2
            }
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

    // Check each value group
    for (name, decls) in &value_groups {
        let sig = signatures.get(name).map(|(_, ty)| ty);

        // Check for duplicate value declarations: multiple equations with 0 binders
        if decls.len() > 1 {
            let zero_arity_spans: Vec<crate::ast::span::Span> = decls.iter().filter_map(|d| {
                if let Decl::Value { span, binders, .. } = d {
                    if binders.is_empty() { Some(*span) } else { None }
                } else { None }
            }).collect();
            if zero_arity_spans.len() > 1 {
                errors.push(TypeError::DuplicateValueDeclaration {
                    spans: zero_arity_spans,
                    name: *name,
                });
                continue;
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
                        let zonked = ctx.state.zonk(ty.clone());
                        let scheme = env.generalize_excluding(&mut ctx.state, zonked.clone(), *name);
                        env.insert_scheme(*name, scheme.clone());
                        local_values.insert(*name, scheme);
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
                Some(sig_ty) => {
                    match ctx.instantiate_forall_type(sig_ty.clone()) {
                        Ok(ty) => ty,
                        Err(e) => {
                            errors.push(e);
                            continue;
                        }
                    }
                }
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
                let first_span = if let Decl::Value { span, .. } = decls[0] { *span } else { crate::ast::span::Span::new(0, 0) };
                if let Err(e) = ctx.state.unify(first_span, &self_ty, &func_ty) {
                    errors.push(e);
                }
                let zonked = ctx.state.zonk(func_ty);
                let scheme = env.generalize_excluding(&mut ctx.state, zonked.clone(), *name);
                env.insert_scheme(*name, scheme.clone());
                local_values.insert(*name, scheme);

                // Exhaustiveness check for multi-equation functions.
                // For each binder position, check that all constructors of the
                // scrutinee type are covered across the equations.
                if first_arity > 0 {
                    check_multi_eq_exhaustiveness(
                        &ctx, first_span, &zonked, first_arity, decls, &mut errors,
                    );
                }

                result_types.insert(*name, zonked);
            }
        }
    }

    // Pass 2.5: Process value-level fixity declarations.
    // Must happen after Pass 2 so target functions are in env with their types.
    for decl in &module.decls {
        if let Decl::Fixity { target, operator, is_type: false, .. } = decl {
            if let Some(scheme) = env.lookup(target.name).cloned() {
                env.insert_scheme(operator.value, scheme.clone());
                local_values.insert(operator.value, scheme);
            }
        }
    }

    // Pass 3: Check deferred type class constraints
    for (span, class_name, type_args) in &ctx.deferred_constraints {
        let zonked_args: Vec<Type> = type_args.iter().map(|t| ctx.state.zonk(t.clone())).collect();

        // Skip if any arg is still unsolved (polymorphic usage — no concrete instance needed)
        if zonked_args.iter().any(|t| matches!(t, Type::Unif(_))) {
            continue;
        }

        if !has_matching_instance(&instances, class_name, &zonked_args) {
            errors.push(TypeError::NoClassInstance {
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

    let mut export_class_methods: HashMap<Symbol, (Symbol, Vec<Symbol>)> = HashMap::new();
    for (method, (class_name, tvs)) in &ctx.class_methods {
        if local_class_set.contains(class_name) {
            export_class_methods.insert(*method, (*class_name, tvs.clone()));
        }
    }

    let mut export_instances: HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>> = HashMap::new();
    for (class_name, insts) in &instances {
        // Export all instances (both for local and imported classes) since instances
        // are globally visible in PureScript
        export_instances.insert(*class_name, insts.clone());
    }

    let mut export_type_operators: HashMap<Symbol, Symbol> = HashMap::new();
    for decl in &module.decls {
        if let Decl::Fixity { target, operator, is_type: true, .. } = decl {
            export_type_operators.insert(operator.value, target.name);
        }
    }

    let mut module_exports = ModuleExports {
        values: local_values,
        class_methods: export_class_methods,
        data_constructors: export_data_constructors,
        ctor_details: export_ctor_details,
        instances: export_instances,
        type_operators: export_type_operators,
    };

    // If there's an explicit export list, filter exports accordingly
    if let Some(ref export_list) = module.exports {
        module_exports = filter_exports(
            &module_exports,
            &export_list.value,
            &local_type_set,
            &local_class_set,
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
    let parts: Vec<String> = module_name.parts.iter()
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
        let module_exports = if is_prim_module(&import_decl.module) {
            &prim
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
                    import_item(item, module_exports, env, ctx, instances, qualifier, import_decl.span, errors);
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
    for (name, scheme) in &exports.values {
        env.insert_scheme(maybe_qualify(*name, qualifier), scheme.clone());
    }
    for (name, info) in &exports.class_methods {
        ctx.class_methods.insert(*name, info.clone());
    }
    for (name, ctors) in &exports.data_constructors {
        ctx.data_constructors.insert(*name, ctors.clone());
        ctx.known_types.insert(maybe_qualify(*name, qualifier));
    }
    for (name, details) in &exports.ctor_details {
        ctx.ctor_details.insert(*name, details.clone());
    }
    for (name, insts) in &exports.instances {
        instances.entry(*name).or_default().extend(insts.clone());
    }
    for (op, target) in &exports.type_operators {
        ctx.type_operators.insert(*op, *target);
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
            if let Some(scheme) = exports.values.get(name) {
                env.insert_scheme(maybe_qualify(*name, qualifier), scheme.clone());
            }
            // Also import class method info and instances if this is a class method
            if let Some((class_name, tvs)) = exports.class_methods.get(name) {
                ctx.class_methods.insert(*name, (*class_name, tvs.clone()));
                // Import instances for the method's class so constraints can be resolved
                if let Some(insts) = exports.instances.get(class_name) {
                    instances.entry(*class_name).or_default().extend(insts.clone());
                }
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
                    ctx.class_methods.insert(*method_name, (*class_name, tvs.clone()));
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
    for (name, scheme) in &exports.values {
        if !hidden.contains(name) {
            env.insert_scheme(maybe_qualify(*name, qualifier), scheme.clone());
        }
    }
    for (name, info) in &exports.class_methods {
        if !hidden.contains(name) {
            ctx.class_methods.insert(*name, info.clone());
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
        instances.entry(*name).or_default().extend(insts.clone());
    }
    for (op, target) in &exports.type_operators {
        if !hidden.contains(op) {
            ctx.type_operators.insert(*op, *target);
        }
    }
}

/// Get the primary symbol name from an Import item.
fn import_name(item: &Import) -> Symbol {
    match item {
        Import::Value(name) | Import::Type(name, _) | Import::TypeOp(name) | Import::Class(name) => *name,
    }
}

/// Filter a module's exports according to an explicit export list.
fn filter_exports(
    all: &ModuleExports,
    export_list: &crate::cst::ExportList,
    _local_types: &HashSet<Symbol>,
    _local_classes: &HashSet<Symbol>,
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
            }
            Export::Class(name) => {
                // Export class metadata (for constraint generation) but NOT methods as values.
                // In PureScript, `module M (class C) where` only exports the class —
                // methods must be listed separately: `module M (class C, methodName) where`.
                for (method_name, (class_name, tvs)) in &all.class_methods {
                    if class_name == name {
                        result.class_methods.insert(*method_name, (*class_name, tvs.clone()));
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
            Export::Module(_) => {
                // Module re-exports: not implemented yet
            }
        }
    }

    // Always export all instances (PureScript instances are globally visible)
    for (class_name, insts) in &all.instances {
        result.instances.entry(*class_name).or_default().extend(insts.clone());
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
                        if let Decl::Value { binders, guarded, .. } = decl {
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

    // Process where clause first (available to guarded expr)
    if !where_clause.is_empty() {
        ctx.process_let_bindings(&mut local_env, where_clause)?;
    }

    if binders.is_empty() {
        // No binders — just infer the body
        let body_ty = ctx.infer_guarded(&local_env, guarded)?;

        if let Some(sig_ty) = expected {
            let instantiated = ctx.instantiate_forall_type(sig_ty.clone())?;
            ctx.state.unify(span, &body_ty, &instantiated)?;
        }

        Ok(body_ty)
    } else {
        // Has binders — build function type
        let mut param_types = Vec::new();

        if let Some(sig_ty) = expected {
            // Peel parameter types from the signature
            let mut remaining_sig = ctx.instantiate_forall_type(sig_ty.clone())?;

            for binder in binders {
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

            let body_ty = ctx.infer_guarded(&local_env, guarded)?;

            let mut result = body_ty;
            for param_ty in param_types.into_iter().rev() {
                result = Type::fun(param_ty, result);
            }
            Ok(result)
        }
    }
}

/// Check if a class has a matching instance for the given concrete type args.
/// Handles constrained instances by recursively checking that constraints are satisfied.
fn has_matching_instance(
    instances: &HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>>,
    class_name: &Symbol,
    concrete_args: &[Type],
) -> bool {
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
        let matched = inst_types.iter().zip(concrete_args.iter()).all(|(inst_ty, arg)| {
            match inst_ty {
                Type::Var(v) => {
                    // Type variable in instance position — bind it
                    if let Some(existing) = subst.get(v) {
                        existing == arg
                    } else {
                        subst.insert(*v, arg.clone());
                        true
                    }
                }
                _ => inst_ty == arg,
            }
        });

        if !matched {
            return false;
        }

        // If there are no constraints, we're done
        if inst_constraints.is_empty() {
            return true;
        }

        // Check each constraint with substituted types
        inst_constraints.iter().all(|(c_class, c_args)| {
            let substituted_args: Vec<Type> = c_args
                .iter()
                .map(|t| apply_var_subst(&subst, t))
                .collect();
            has_matching_instance(instances, c_class, &substituted_args)
        })
    })
}

/// Apply a variable substitution (Type::Var → Type) to a type.
fn apply_var_subst(subst: &HashMap<Symbol, Type>, ty: &Type) -> Type {
    match ty {
        Type::Var(v) => subst.get(v).cloned().unwrap_or_else(|| ty.clone()),
        Type::Fun(a, b) => Type::fun(apply_var_subst(subst, a), apply_var_subst(subst, b)),
        Type::App(f, a) => Type::app(apply_var_subst(subst, f), apply_var_subst(subst, a)),
        Type::Forall(vars, body) => Type::Forall(vars.clone(), Box::new(apply_var_subst(subst, body))),
        Type::Record(fields, tail) => {
            let fields = fields.iter().map(|(l, t)| (*l, apply_var_subst(subst, t))).collect();
            let tail = tail.as_ref().map(|t| Box::new(apply_var_subst(subst, t)));
            Type::Record(fields, tail)
        }
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
    }
}
