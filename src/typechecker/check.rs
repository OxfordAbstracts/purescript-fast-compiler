use std::collections::HashMap;

use crate::cst::{Decl, Module};
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::InferCtx;
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
    let mut instances: HashMap<Symbol, Vec<Vec<Type>>> = HashMap::new();

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
                match convert_type_expr(ty) {
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

                for ctor in constructors {
                    // Build constructor type: field1 -> field2 -> ... -> result_type
                    let field_results: Vec<Result<Type, TypeError>> = ctor
                        .fields
                        .iter()
                        .map(|f| convert_type_expr(f))
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
                let type_var_syms: Vec<Symbol> =
                    type_vars.iter().map(|tv| tv.value).collect();

                let mut result_type = Type::Con(name.value);
                for &tv in &type_var_syms {
                    result_type = Type::app(result_type, Type::Var(tv));
                }

                match convert_type_expr(ty) {
                    Ok(field_ty) => {
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
                match convert_type_expr(ty) {
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
                    match convert_type_expr(&member.ty) {
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
            Decl::Instance { class_name, types, members, .. } => {
                // Register this instance's types
                let mut inst_types = Vec::new();
                let mut inst_ok = true;
                for ty_expr in types {
                    match convert_type_expr(ty_expr) {
                        Ok(ty) => inst_types.push(ty),
                        Err(e) => {
                            errors.push(e);
                            inst_ok = false;
                            break;
                        }
                    }
                }
                if inst_ok {
                    instances.entry(class_name.name).or_default().push(inst_types);
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
            Decl::Fixity { target, operator, .. } => {
                // Register operator alias: operator symbol maps to target function
                if let Some(scheme) = env.lookup(target.name).cloned() {
                    env.insert_scheme(operator.value, scheme);
                }
            }
            Decl::TypeAlias { type_vars, ty, .. } => {
                if type_vars.is_empty() {
                    if let Err(e) = convert_type_expr(ty) {
                        errors.push(e);
                    }
                }
            }
            Decl::ForeignData { .. } | Decl::Derive { .. } => {
                // Foreign data and derive declarations are not yet handled
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

        let has_instance = instances
            .get(class_name)
            .map_or(false, |known| {
                known.iter().any(|inst_types| {
                    inst_types.len() == zonked_args.len()
                        && inst_types.iter().zip(zonked_args.iter()).all(|(i, a)| i == a)
                })
            });

        if !has_instance {
            errors.push(TypeError::NoClassInstance {
                span: *span,
                class_name: *class_name,
                type_args: zonked_args,
            });
        }
    }

    CheckResult {
        types: result_types,
        errors,
    }
}

/// Check a single value declaration equation.
fn check_value_decl(
    ctx: &mut InferCtx,
    env: &Env,
    _name: Symbol,
    span: crate::ast::span::Span,
    binders: &[crate::cst::Binder],
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
