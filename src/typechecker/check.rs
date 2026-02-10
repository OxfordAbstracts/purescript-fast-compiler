use std::collections::HashMap;

use crate::cst::{Binder, Decl, Export, Module};
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::{check_exhaustiveness, extract_type_con, InferCtx};
use crate::typechecker::types::{Scheme, Type};

/// Result of typechecking a module: partial type map + accumulated errors.
pub struct CheckResult {
    pub types: HashMap<Symbol, Type>,
    pub errors: Vec<TypeError>,
}

/// Typecheck an entire module, returning a map of top-level names to their types
/// and a list of any errors encountered. Checking continues past errors so that
/// partial results are available for tooling (e.g. IDE hover types).
pub fn check_module(module: &Module) -> CheckResult {
    let mut ctx = InferCtx::new();
    let mut env = Env::new();
    let mut signatures: HashMap<Symbol, (crate::ast::span::Span, Type)> = HashMap::new();
    let mut result_types: HashMap<Symbol, Type> = HashMap::new();
    let mut errors: Vec<TypeError> = Vec::new();

    // Track class info for instance checking
    // Each instance stores (type_args, constraints) where constraints are (class_name, constraint_type_args)
    let mut instances: HashMap<Symbol, Vec<(Vec<Type>, Vec<(Symbol, Vec<Type>)>)>> = HashMap::new();

    // Pass 0: Collect type-level operator fixity declarations.
    // These must be available before any type expressions are converted.
    for decl in &module.decls {
        if let Decl::Fixity { target, operator, is_type: true, .. } = decl {
            ctx.type_operators.insert(operator.value, target.name);
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
                match convert_type_expr(ty, &type_ops) {
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

                    env.insert_scheme(ctor.name.value, Scheme::mono(ctor_ty));
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

                match convert_type_expr(ty, &type_ops) {
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

                        env.insert_scheme(constructor.value, Scheme::mono(ctor_ty));
                    }
                    Err(e) => errors.push(e),
                }
            }
            Decl::Foreign { name, ty, .. } => {
                match convert_type_expr(ty, &type_ops) {
                    Ok(converted) => {
                        env.insert_scheme(name.value, Scheme::mono(converted));
                    }
                    Err(e) => errors.push(e),
                }
            }
            Decl::Class { name, type_vars, members, .. } => {
                // Register class methods in the environment with their declared types
                let type_var_syms: Vec<Symbol> =
                    type_vars.iter().map(|tv| tv.value).collect();
                for member in members {
                    match convert_type_expr(&member.ty, &type_ops) {
                        Ok(member_ty) => {
                            let scheme_ty = if !type_var_syms.is_empty() {
                                Type::Forall(type_var_syms.clone(), Box::new(member_ty))
                            } else {
                                member_ty
                            };
                            env.insert_scheme(member.name.value, Scheme::mono(scheme_ty));
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
                    match convert_type_expr(ty_expr, &type_ops) {
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
            Decl::Fixity { target, operator, is_type, .. } => {
                if *is_type {
                    // Type-level fixity already handled in Pass 0
                } else {
                    // Value-level: register operator alias mapping to target function
                    if let Some(scheme) = env.lookup(target.name).cloned() {
                        env.insert_scheme(operator.value, scheme);
                    }
                }
            }
            Decl::TypeAlias { type_vars, ty, .. } => {
                if type_vars.is_empty() {
                    if let Err(e) = convert_type_expr(ty, &type_ops) {
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
                        env.insert_scheme(*name, scheme);
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
                env.insert_scheme(*name, scheme);

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

    // Pass 4: Validate module exports
    if let Some(ref export_list) = module.exports {
        // Collect declared type/class names for validation
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

        for export in &export_list.value.exports {
            match export {
                Export::Value(name) => {
                    let sym = *name;
                    if !result_types.contains_key(&sym) && env.lookup(sym).is_none() {
                        errors.push(TypeError::UndefinedExport {
                            span: export_list.span,
                            name: sym,
                        });
                    }
                }
                Export::Type(name, _) => {
                    if !declared_types.contains(name) {
                        errors.push(TypeError::UndefinedExport {
                            span: export_list.span,
                            name: *name,
                        });
                    }
                }
                Export::Class(name) => {
                    if !declared_classes.contains(name) {
                        errors.push(TypeError::UndefinedExport {
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

    CheckResult {
        types: result_types,
        errors,
    }
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
                let binder_refs: Vec<&Binder> = decls
                    .iter()
                    .filter_map(|decl| {
                        if let Decl::Value { binders, .. } = decl {
                            binders.get(idx)
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
        Type::Con(_) | Type::Unif(_) => ty.clone(),
    }
}
