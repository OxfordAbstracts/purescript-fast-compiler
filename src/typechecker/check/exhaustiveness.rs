
use crate::ast::{Binder, Decl};
use crate::cst::QualifiedIdent;
use crate::interner::Symbol;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::{
    check_exhaustiveness, extract_type_con, is_refutable, is_unconditional_for_exhaustiveness,
    unwrap_binder, InferCtx,
};
use crate::typechecker::types::Type;

use crate::typechecker::env::Env;

use super::{qi, strip_forall};

/// Check exhaustiveness for multi-equation function definitions.
/// Peels `func_ty` to extract parameter types, then for each binder position,
/// checks if all constructors of the corresponding type are covered.
/// Check if a binder contains array patterns which are inherently non-exhaustive
/// (can never be exhaustive because arrays have infinite possible lengths).
/// Literal patterns (Boolean, Int, etc.) are NOT included because Boolean patterns
/// can be exhaustive across multiple equations (true + false).
/// Constructor patterns are NOT included because multiple equations can together
/// cover all constructors of a data type.
pub(crate) fn contains_inherently_partial_binder(binder: &Binder) -> bool {
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
pub(crate) fn is_single_ctor_irrefutable(binder: &Binder, ctx: &InferCtx) -> bool {
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

pub(crate) fn check_multi_eq_exhaustiveness(
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
/// `sig_from_alias` indicates the signature's forall came from alias expansion,
/// so its bound vars should NOT be added to scoped type variables.
pub(crate) fn check_value_decl(
    ctx: &mut InferCtx,
    env: &Env,
    _name: Symbol,
    span: crate::span::Span,
    binders: &[Binder],
    guarded: &crate::ast::GuardedExpr,
    where_clause: &[crate::ast::LetBinding],
    expected: Option<&Type>,
    sig_from_alias: bool,
) -> Result<Type, TypeError> {
    // Set scoped type variables from the expected type.
    // This enables ScopedTypeVariables: where clause signatures can reference
    // type vars from the enclosing function's forall AND from instance heads.
    // When the signature came from alias expansion (e.g., `foo :: T` where
    // `type T = forall a. Array a`), the alias's forall-bound vars are NOT scoped.
    let prev_scoped = ctx.scoped_type_vars.clone();
    if let Some(ty) = expected {
        fn collect_scoped_type_vars(ty: &Type, vars: &mut std::collections::HashSet<Symbol>, exclude: &std::collections::HashSet<Symbol>) {
            match ty {
                Type::Var(v) => {
                    if !exclude.contains(&v.symbol()) {
                        vars.insert(v.symbol());
                    }
                }
                Type::Forall(bound_vars, body) => {
                    for &(v, _) in bound_vars {
                        if !exclude.contains(&v.symbol()) {
                            vars.insert(v.symbol());
                        }
                    }
                    collect_scoped_type_vars(body, vars, exclude);
                }
                Type::Fun(a, b) => {
                    collect_scoped_type_vars(a, vars, exclude);
                    collect_scoped_type_vars(b, vars, exclude);
                }
                Type::App(f, a) => {
                    collect_scoped_type_vars(f, vars, exclude);
                    collect_scoped_type_vars(a, vars, exclude);
                }
                Type::Record(fields, tail) => {
                    for (_, t) in fields {
                        collect_scoped_type_vars(t, vars, exclude);
                    }
                    if let Some(t) = tail {
                        collect_scoped_type_vars(t, vars, exclude);
                    }
                }
                _ => {}
            }
        }
        // When the signature came from alias expansion, the outermost forall's
        // bound vars should be excluded from scoped type variables (they were not
        // explicitly written by the user).
        let mut exclude = std::collections::HashSet::new();
        if sig_from_alias {
            if let Type::Forall(bound_vars, _) = ty {
                for &(v, _) in bound_vars {
                    exclude.insert(v.symbol());
                }
            }
        }
        collect_scoped_type_vars(ty, &mut ctx.scoped_type_vars, &exclude);
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

pub(crate) fn check_value_decl_inner(
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
