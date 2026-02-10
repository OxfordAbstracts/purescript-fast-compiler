use std::collections::HashMap;

use crate::cst::{Decl, Module};
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::InferCtx;
use crate::typechecker::types::{Scheme, Type};

/// Typecheck an entire module, returning a map of top-level names to their types.
pub fn check_module(module: &Module) -> Result<HashMap<Symbol, Type>, TypeError> {
    let mut ctx = InferCtx::new();
    let mut env = Env::new();
    let mut signatures: HashMap<Symbol, (crate::ast::span::Span, Type)> = HashMap::new();
    let mut result_types: HashMap<Symbol, Type> = HashMap::new();

    // Pass 1: Collect type signatures and data constructors
    for decl in &module.decls {
        match decl {
            Decl::TypeSignature { span, name, ty } => {
                if signatures.contains_key(&name.value) {
                    return Err(TypeError::DuplicateTypeSignature {
                        span: *span,
                        name: name.value,
                    });
                }
                let converted = convert_type_expr(ty)?;
                signatures.insert(name.value, (*span, converted));
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
                    let field_types: Vec<Type> = ctor
                        .fields
                        .iter()
                        .map(|f| convert_type_expr(f))
                        .collect::<Result<_, _>>()?;

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

                let field_ty = convert_type_expr(ty)?;
                let mut ctor_ty = Type::fun(field_ty, result_type);

                if !type_var_syms.is_empty() {
                    ctor_ty = Type::Forall(type_var_syms, Box::new(ctor_ty));
                }

                env.insert_scheme(constructor.value, Scheme::mono(ctor_ty));
            }
            Decl::Foreign { name, ty, .. } => {
                let converted = convert_type_expr(ty)?;
                env.insert_scheme(name.value, Scheme::mono(converted));
            }
            _ => {}
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
            return Err(TypeError::OrphanTypeSignature {
                span: *span,
                name: *sig_name,
            });
        }
    }

    // Check each value group
    for (name, decls) in &value_groups {
        let sig = signatures.get(name).map(|(_, ty)| ty);

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
                let ty = check_value_decl(
                    &mut ctx,
                    &env,
                    *name,
                    *span,
                    binders,
                    guarded,
                    where_clause,
                    sig,
                )?;
                let zonked = ctx.state.zonk(ty.clone());
                let scheme = env.generalize(&mut ctx.state, zonked.clone());
                env.insert_scheme(*name, scheme);
                result_types.insert(*name, zonked);
            }
        } else {
            // Multiple equations — check arity consistency
            let first_arity = if let Decl::Value { binders, .. } = decls[0] {
                binders.len()
            } else {
                0
            };

            for decl in &decls[1..] {
                if let Decl::Value { span, binders, .. } = decl {
                    if binders.len() != first_arity {
                        return Err(TypeError::ArityMismatch {
                            span: *span,
                            name: *name,
                            expected: first_arity,
                            found: binders.len(),
                        });
                    }
                }
            }

            // Create a fresh type for the function and check each equation against it
            let func_ty = if let Some(sig_ty) = sig {
                ctx.instantiate_forall_type(sig_ty.clone())?
            } else {
                Type::Unif(ctx.state.fresh_var())
            };

            for decl in decls {
                if let Decl::Value {
                    span,
                    binders,
                    guarded,
                    where_clause,
                    ..
                } = decl
                {
                    let eq_ty = check_value_decl(
                        &mut ctx,
                        &env,
                        *name,
                        *span,
                        binders,
                        guarded,
                        where_clause,
                        None,
                    )?;
                    ctx.state.unify(*span, &func_ty, &eq_ty)?;
                }
            }

            let zonked = ctx.state.zonk(func_ty);
            let scheme = env.generalize(&mut ctx.state, zonked.clone());
            env.insert_scheme(*name, scheme);
            result_types.insert(*name, zonked);
        }
    }

    Ok(result_types)
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
