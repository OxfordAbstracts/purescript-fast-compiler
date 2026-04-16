//! Bidirectional inference. Current coverage:
//!
//! - M4a: `Var`, `App`, `Lambda`, `Parens`, `TypeAnnotation`, `Hole`,
//!   `Wildcard`, `Literal`, `Constructor`.
//! - M4b: `If`, `Let` (with let-polymorphism).
//! - M4c: `Case` with constructor / `As` / literal / typed patterns, plus
//!   both `Unconditional` and `Guarded` alternative bodies.
//!
//! Later sub-milestones fill in `Do`/`Ado` (M4d) and records (M4e). Each new
//! form is additive — a new match arm plus its helper.
//!
//! The entry point is `infer_value_scc`, which corresponds to the
//! `infer_value_scc` nanopass in the plan: given an SCC of top-level
//! value decls plus the caller-supplied [`Env`] of dependency schemes, it
//! returns a [`Scheme`] per name defined in the SCC.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::cst::{self, Binder, Decl, Expr, LetBinding, Literal};
use crate::typecheck_db::env::{Env, Lookup};
use crate::typecheck_db::generalize::{generalize, instantiate};
use crate::typecheck_db::types::{convert_type_expr, QName, Scheme, Type, TypeOpMap};
use crate::typecheck_db::unify::{UnifyError, UnifyState};

pub const PASS_NAME: &str = "infer_value_scc";
pub const PASS_VERSION: u32 = 1;

#[derive(Debug, Error)]
pub enum InferError {
    #[error("unification: {0}")]
    Unify(#[from] UnifyError),
    #[error("unbound variable: {0}")]
    UnboundVar(String),
    #[error("unbound constructor: {0}")]
    UnboundConstructor(String),
    #[error("unsupported expression form: {0}")]
    Unsupported(&'static str),
    #[error("unsupported binder form: {0}")]
    UnsupportedBinder(&'static str),
}

/// Output of `infer_value_scc` for one SCC of mutually-recursive value decls.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InferredScheme {
    pub name: String,
    pub scheme: Scheme,
}

// ============================================================================
// Entry points
// ============================================================================

/// Infer a single expression against a (possibly empty) [`Env`]. Used both
/// by tests and by `infer_value_scc`.
pub fn infer_expr(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    expr: &Expr,
) -> Result<Type, InferError> {
    match expr {
        Expr::Var { name, .. } => infer_var(state, env, name),
        Expr::Constructor { name, .. } => infer_constructor(state, env, name),
        Expr::Literal { lit, .. } => Ok(type_of_literal(lit)),
        Expr::App { func, arg, .. } => infer_app(state, env, type_ops, func, arg),
        Expr::Lambda { binders, body, .. } => {
            infer_lambda(state, env, type_ops, binders, body)
        }
        Expr::Parens { expr, .. } => infer_expr(state, env, type_ops, expr),
        Expr::TypeAnnotation { expr, ty, .. } => {
            let declared = convert_type_expr(ty, type_ops);
            check_expr(state, env, type_ops, expr, &declared)?;
            Ok(declared)
        }
        Expr::Wildcard { .. } | Expr::Hole { .. } => Ok(state.fresh()),
        Expr::Negate { expr, .. } => infer_expr(state, env, type_ops, expr),

        Expr::If { cond, then_expr, else_expr, .. } => {
            infer_if(state, env, type_ops, cond, then_expr, else_expr)
        }
        Expr::Let { bindings, body, .. } => {
            infer_let(state, env, type_ops, bindings, body)
        }
        Expr::Case { exprs, alts, .. } => infer_case(state, env, type_ops, exprs, alts),

        // Forms reserved for later sub-milestones.
        Expr::Do { .. } | Expr::Ado { .. } => Err(InferError::Unsupported("do/ado")),
        Expr::Record { .. } | Expr::RecordAccess { .. } | Expr::RecordUpdate { .. } => {
            Err(InferError::Unsupported("record"))
        }
        Expr::Op { .. } | Expr::OpParens { .. } | Expr::BacktickApp { .. } => {
            Err(InferError::Unsupported("operator"))
        }
        Expr::VisibleTypeApp { .. } => Err(InferError::Unsupported("visible-type-app")),
        Expr::Array { .. } => Err(InferError::Unsupported("array")),
        Expr::AsPattern { .. } => Err(InferError::Unsupported("as-pattern")),
    }
}

/// Check an expression against an expected [`Type`]. Minimal checking mode
/// for M4a: infer then unify.
pub fn check_expr(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    expr: &Expr,
    expected: &Type,
) -> Result<(), InferError> {
    let actual = infer_expr(state, env, type_ops, expr)?;
    state.unify(&actual, expected)?;
    Ok(())
}

/// Infer an SCC of value declarations. `env` enters pre-populated with
/// dependency schemes; it is returned untouched (conceptually immutable
/// for the caller).
///
/// For M4a the SCC is expected to contain only non-recursive value decls
/// since we haven't added self-reference logic yet. A single-decl SCC with
/// a straight-line body works today.
pub fn infer_value_scc(
    type_ops: &TypeOpMap,
    env: &mut Env,
    decls: &[&Decl],
) -> Result<Vec<InferredScheme>, InferError> {
    // Pre-register each SCC member with a fresh unif var so mutual
    // references within the SCC type-check. After inference, we generalize.
    let mut state = UnifyState::new();

    let mut slot_of: HashMap<String, Type> = HashMap::new();
    let mut decl_refs: Vec<(&Decl, String)> = Vec::new();

    for decl in decls {
        if let Decl::Value { name, .. } = decl {
            let n = crate::interner::resolve(name.value.symbol()).unwrap_or_default();
            let v = state.fresh();
            env.bind_local(n.clone(), v.clone());
            slot_of.insert(n.clone(), v);
            decl_refs.push((*decl, n));
        }
    }

    // Infer each decl's body against its pre-registered slot.
    for (decl, name) in &decl_refs {
        if let Decl::Value { binders, guarded, where_clause: _, .. } = decl {
            let expected = slot_of.get(name).cloned().unwrap();
            let lam_ty = infer_equation(&mut state, env, type_ops, binders, guarded)?;
            state.unify(&expected, &lam_ty)?;
        }
    }

    // Now generalize. Temporarily clear this SCC's slots from the env so
    // they don't count as "free in env" and block quantification.
    let mut slots_backup: Vec<(String, Type)> = Vec::new();
    if let Some(scope) = env.locals.last_mut() {
        for name in slot_of.keys() {
            if let Some(v) = scope.remove(name) {
                slots_backup.push((name.clone(), v));
            }
        }
    }

    let mut out = Vec::new();
    for (_, name) in &decl_refs {
        let ty = slot_of.get(name).cloned().unwrap();
        let scheme = generalize(&state, env, &ty);
        out.push(InferredScheme { name: name.clone(), scheme });
    }

    // Restore env — callers may reuse it.
    for (name, v) in slots_backup {
        env.bind_local(name, v);
    }

    Ok(out)
}

// ============================================================================
// Expression inference
// ============================================================================

fn infer_var(
    state: &mut UnifyState,
    env: &Env,
    name: &crate::names::Qualified<crate::names::ValueName>,
) -> Result<Type, InferError> {
    let qi = name.to_qi();
    let name_str =
        crate::interner::resolve(qi.name).unwrap_or_default();
    let module_str = qi.module.and_then(crate::interner::resolve);

    if let Some(module) = module_str {
        let q = QName { module: Some(module), name: name_str.clone() };
        return match env.lookup_qualified(&q) {
            Some(scheme) => Ok(instantiate(state, scheme)),
            None => Err(InferError::UnboundVar(format!("{}", q))),
        };
    }

    match env.lookup_unqualified(&name_str) {
        Lookup::Local(ty) => Ok(ty.clone()),
        Lookup::Scheme(s) => Ok(instantiate(state, s)),
        Lookup::Missing => Err(InferError::UnboundVar(name_str)),
    }
}

fn infer_constructor(
    state: &mut UnifyState,
    env: &Env,
    name: &crate::names::Qualified<crate::names::ConstructorName>,
) -> Result<Type, InferError> {
    let qi = name.to_qi();
    let name_str =
        crate::interner::resolve(qi.name).unwrap_or_default();
    let module_str = qi.module.and_then(crate::interner::resolve);

    let q = QName { module: module_str, name: name_str.clone() };
    let scheme = env
        .lookup_qualified(&q)
        .or_else(|| match &q.module {
            // Try unqualified too for the common case where the caller
            // seeded constructors without a module prefix.
            Some(_) => None,
            None => env.top_level.get(&QName::unqualified(name_str.clone())),
        })
        .ok_or_else(|| InferError::UnboundConstructor(format!("{}", q)))?;
    Ok(instantiate(state, scheme))
}

fn infer_app(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    func: &Expr,
    arg: &Expr,
) -> Result<Type, InferError> {
    let func_ty = infer_expr(state, env, type_ops, func)?;
    let arg_ty = infer_expr(state, env, type_ops, arg)?;
    let result = state.fresh();
    state.unify(&func_ty, &Type::fun(arg_ty, result.clone()))?;
    Ok(result)
}

fn infer_lambda(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    binders: &[Binder],
    body: &Expr,
) -> Result<Type, InferError> {
    env.push_scope();
    let mut param_tys = Vec::with_capacity(binders.len());
    for b in binders {
        let ty = bind_pattern(state, env, type_ops, b)?;
        param_tys.push(ty);
    }
    let body_ty = infer_expr(state, env, type_ops, body)?;
    env.pop_scope();

    // Build right-associated arrow: p1 -> p2 -> ... -> body.
    let mut out = body_ty;
    for pt in param_tys.into_iter().rev() {
        out = Type::fun(pt, out);
    }
    Ok(out)
}

/// Process one lambda / value-equation binder, introducing each variable
/// it names into the env. Returns the binder's inferred type.
fn bind_pattern(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    binder: &Binder,
) -> Result<Type, InferError> {
    match binder {
        Binder::Wildcard { .. } => Ok(state.fresh()),
        Binder::Var { name, .. } => {
            let v = state.fresh();
            let n = crate::interner::resolve(name.value.symbol()).unwrap_or_default();
            env.bind_local(n, v.clone());
            Ok(v)
        }
        Binder::Typed { binder, ty, .. } => {
            let declared = convert_type_expr(ty, type_ops);
            let inferred = bind_pattern(state, env, type_ops, binder)?;
            state.unify(&inferred, &declared)?;
            Ok(declared)
        }
        Binder::Parens { binder, .. } => bind_pattern(state, env, type_ops, binder),
        Binder::Literal { lit, .. } => Ok(type_of_literal(lit)),
        Binder::Constructor { name, args, .. } => {
            bind_constructor_pattern(state, env, type_ops, name, args)
        }
        Binder::As { name, binder, .. } => {
            let inner = bind_pattern(state, env, type_ops, binder)?;
            let n = crate::interner::resolve(name.value.symbol()).unwrap_or_default();
            env.bind_local(n, inner.clone());
            Ok(inner)
        }
        // Record / Array / Op patterns: later sub-milestones (M4e and
        // beyond).
        Binder::Record { .. } => Err(InferError::UnsupportedBinder("record")),
        Binder::Array { .. } => Err(InferError::UnsupportedBinder("array")),
        Binder::Op { .. } => Err(InferError::UnsupportedBinder("op")),
    }
}

/// Match a constructor pattern against its constructor's scheme.
///
/// A constructor scheme looks like `forall a. Arg1 -> Arg2 -> ... -> T a`.
/// We instantiate it with fresh unif vars, then peel off `args.len()`
/// function arrows. Each sub-binder is inferred and unified with the
/// corresponding argument type. The remainder (the "return type" of the
/// constructor) is the type of the overall pattern.
fn bind_constructor_pattern(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    name: &crate::names::Qualified<crate::names::ConstructorName>,
    args: &[Binder],
) -> Result<Type, InferError> {
    let qi = name.to_qi();
    let name_str = crate::interner::resolve(qi.name).unwrap_or_default();
    let module_str = qi.module.and_then(crate::interner::resolve);
    let q = QName { module: module_str, name: name_str.clone() };
    let scheme = env
        .lookup_qualified(&q)
        .or_else(|| match &q.module {
            Some(_) => None,
            None => env.top_level.get(&QName::unqualified(name_str.clone())),
        })
        .ok_or_else(|| InferError::UnboundConstructor(format!("{}", q)))?;

    let mut cur = instantiate(state, scheme);
    let mut arg_tys: Vec<Type> = Vec::with_capacity(args.len());
    for _ in 0..args.len() {
        let arg = state.fresh();
        let result = state.fresh();
        state.unify(&cur, &Type::fun(arg.clone(), result.clone()))?;
        arg_tys.push(arg);
        cur = result;
    }
    for (sub, arg_ty) in args.iter().zip(arg_tys.iter()) {
        let sub_ty = bind_pattern(state, env, type_ops, sub)?;
        state.unify(&sub_ty, arg_ty)?;
    }
    Ok(cur)
}

fn infer_if(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    cond: &Expr,
    then_expr: &Expr,
    else_expr: &Expr,
) -> Result<Type, InferError> {
    check_expr(state, env, type_ops, cond, &Type::Con(QName::unqualified("Boolean")))?;
    let then_ty = infer_expr(state, env, type_ops, then_expr)?;
    let else_ty = infer_expr(state, env, type_ops, else_expr)?;
    state.unify(&then_ty, &else_ty)?;
    Ok(then_ty)
}

/// One named value binding lifted out of a `let`.
struct LetValueBinding<'a> {
    name: String,
    /// If a `Signature` binding preceded this one with the same name, its
    /// converted [`Type`] lives here. Used both as the pre-inserted slot and
    /// as the declared type to check the body against.
    sig: Option<Type>,
    expr: &'a Expr,
}

fn infer_let(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    bindings: &[LetBinding],
    body: &Expr,
) -> Result<Type, InferError> {
    env.push_scope();

    // Pass 1: collect signatures keyed by name.
    let mut sigs: HashMap<String, Type> = HashMap::new();
    for b in bindings {
        if let LetBinding::Signature { name, ty, .. } = b {
            let n = crate::interner::resolve(name.value.symbol()).unwrap_or_default();
            sigs.insert(n, convert_type_expr(ty, type_ops));
        }
    }

    // Pass 2: materialize value bindings and pre-insert slots into locals so
    // mutually-recursive `let`s typecheck.
    let mut value_bindings: Vec<LetValueBinding<'_>> = Vec::new();
    for b in bindings {
        match b {
            LetBinding::Value { binder: Binder::Var { name, .. }, expr, .. } => {
                let n = crate::interner::resolve(name.value.symbol()).unwrap_or_default();
                let sig = sigs.get(&n).cloned();
                let slot = sig.clone().unwrap_or_else(|| state.fresh());
                env.bind_local(n.clone(), slot);
                value_bindings.push(LetValueBinding { name: n, sig, expr });
            }
            LetBinding::Value { .. } => {
                return Err(InferError::UnsupportedBinder("let-pattern"));
            }
            LetBinding::Signature { .. } => {}
        }
    }

    // Pass 3: infer each body, unify with its pre-inserted slot (or check
    // against the signature directly if one was supplied).
    for vb in &value_bindings {
        let slot_ty = env
            .lookup_unqualified(&vb.name)
            .local_ty()
            .expect("slot pre-inserted above")
            .clone();
        if vb.sig.is_some() {
            check_expr(state, env, type_ops, vb.expr, &slot_ty)?;
        } else {
            let actual = infer_expr(state, env, type_ops, vb.expr)?;
            state.unify(&slot_ty, &actual)?;
        }
    }

    // Pass 4: replace each monomorphic slot with a generalized scheme so the
    // body benefits from let-polymorphism. We remove the slot from `locals`
    // *before* generalizing so its own unif var isn't considered free in the
    // surrounding env.
    let mut finished: Vec<(String, Scheme)> = Vec::new();
    for vb in &value_bindings {
        let slot_ty = env
            .locals
            .last_mut()
            .and_then(|s| s.remove(&vb.name))
            .expect("slot present");
        let scheme = generalize(state, env, &slot_ty);
        finished.push((vb.name.clone(), scheme));
    }
    for (n, scheme) in finished {
        env.bind_local_scheme(n, scheme);
    }

    let body_ty = infer_expr(state, env, type_ops, body)?;
    env.pop_scope();
    Ok(body_ty)
}

fn infer_case(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    scrutinees: &[Expr],
    alts: &[cst::CaseAlternative],
) -> Result<Type, InferError> {
    // Infer each scrutinee's type up front. These are what every alt's
    // binders must match against, column-wise.
    let scrut_tys: Vec<Type> = scrutinees
        .iter()
        .map(|e| infer_expr(state, env, type_ops, e))
        .collect::<Result<_, _>>()?;

    // All branches must unify with a single fresh result type.
    let result_ty = state.fresh();

    for alt in alts {
        if alt.binders.len() != scrut_tys.len() {
            return Err(InferError::Unsupported("case alt arity mismatch"));
        }
        env.push_scope();
        for (binder, scrut_ty) in alt.binders.iter().zip(scrut_tys.iter()) {
            let bt = bind_pattern(state, env, type_ops, binder)?;
            state.unify(&bt, scrut_ty)?;
        }
        let branch_ty = infer_guarded(state, env, type_ops, &alt.result)?;
        state.unify(&branch_ty, &result_ty)?;
        env.pop_scope();
    }

    Ok(result_ty)
}

/// Infer the result type of a `GuardedExpr`. `Unconditional` defers to
/// `infer_expr`; `Guarded` threads each guard's patterns (Boolean guards
/// must be Boolean; pattern guards bind locals in a sub-scope) then infers
/// the guard's result expression.
fn infer_guarded(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    guarded: &cst::GuardedExpr,
) -> Result<Type, InferError> {
    match guarded {
        cst::GuardedExpr::Unconditional(e) => infer_expr(state, env, type_ops, e),
        cst::GuardedExpr::Guarded(guards) => {
            if guards.is_empty() {
                return Err(InferError::Unsupported("empty guarded body"));
            }
            let result_ty = state.fresh();
            for g in guards {
                env.push_scope();
                for p in &g.patterns {
                    match p {
                        cst::GuardPattern::Boolean(e) => {
                            check_expr(
                                state,
                                env,
                                type_ops,
                                e,
                                &Type::Con(QName::unqualified("Boolean")),
                            )?;
                        }
                        cst::GuardPattern::Pattern(binder, expr) => {
                            let scrut_ty = infer_expr(state, env, type_ops, expr)?;
                            let bt = bind_pattern(state, env, type_ops, binder)?;
                            state.unify(&bt, &scrut_ty)?;
                        }
                    }
                }
                let g_ty = infer_expr(state, env, type_ops, &g.expr)?;
                state.unify(&g_ty, &result_ty)?;
                env.pop_scope();
            }
            Ok(result_ty)
        }
    }
}

fn infer_equation(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    binders: &[Binder],
    guarded: &cst::GuardedExpr,
) -> Result<Type, InferError> {
    // `foo x y = body` acts as `\x y -> body` at the top level. The body
    // may be guarded (M4c); `infer_guarded` handles both shapes.
    if binders.is_empty() {
        return infer_guarded(state, env, type_ops, guarded);
    }

    env.push_scope();
    let mut param_tys = Vec::with_capacity(binders.len());
    for b in binders {
        let ty = bind_pattern(state, env, type_ops, b)?;
        param_tys.push(ty);
    }
    let body_ty = infer_guarded(state, env, type_ops, guarded)?;
    env.pop_scope();

    let mut out = body_ty;
    for pt in param_tys.into_iter().rev() {
        out = Type::fun(pt, out);
    }
    Ok(out)
}

fn type_of_literal(lit: &Literal) -> Type {
    match lit {
        Literal::Int(_) => Type::Con(QName::unqualified("Int")),
        Literal::Float(_) => Type::Con(QName::unqualified("Number")),
        Literal::String(_) => Type::Con(QName::unqualified("String")),
        Literal::Char(_) => Type::Con(QName::unqualified("Char")),
        Literal::Boolean(_) => Type::Con(QName::unqualified("Boolean")),
        Literal::Array(_) => Type::Con(QName::unqualified("_Array_M4a")),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn int() -> Type {
        Type::Con(QName::unqualified("Int"))
    }

    fn bool_ty() -> Type {
        Type::Con(QName::unqualified("Boolean"))
    }

    fn parse_expr_from_val(src: &str) -> Expr {
        let m = parse(src).unwrap();
        for d in m.decls {
            if let Decl::Value { guarded, .. } = d {
                if let cst::GuardedExpr::Unconditional(e) = guarded {
                    return *e;
                }
            }
        }
        panic!("no value decl");
    }

    fn scheme_display(s: &Scheme) -> String {
        if s.vars.is_empty() {
            format!("{}", s.ty)
        } else {
            format!("forall {}. {}", s.vars.join(" "), s.ty)
        }
    }

    #[test]
    fn literal_int_infers_int() {
        let mut s = UnifyState::new();
        let mut env = Env::new();
        let ops = TypeOpMap::default();
        let e = parse_expr_from_val("module M where\nx = 42\n");
        assert_eq!(infer_expr(&mut s, &mut env, &ops, &e).unwrap(), int());
    }

    #[test]
    fn var_lookup_instantiates_scheme() {
        let mut s = UnifyState::new();
        let mut env = Env::new();
        env.bind_scheme(
            QName::unqualified("foo"),
            Scheme { vars: vec!["a".into()], ty: Type::Var("a".into()) },
        );
        let ops = TypeOpMap::default();
        let e = parse_expr_from_val("module M where\nx = foo\n");
        let t = infer_expr(&mut s, &mut env, &ops, &e).unwrap();
        assert!(matches!(t, Type::Unif(_)));
    }

    #[test]
    fn identity_lambda_generalizes_to_forall_a_a_to_a() {
        let src = "module M where\nident x = x\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(schemes.len(), 1);
        assert_eq!(scheme_display(&schemes[0].scheme), "forall a. (a -> a)");
    }

    #[test]
    fn const_lambda_generalizes_to_two_vars() {
        let src = "module M where\nkonst x y = x\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(schemes.len(), 1);
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "forall a b. (a -> (b -> a))",
        );
    }

    #[test]
    fn application_unifies_arg_with_domain() {
        // `ident 42` should give back `Int`.
        let mut env = Env::new();
        env.bind_scheme(
            QName::unqualified("ident"),
            Scheme {
                vars: vec!["a".into()],
                ty: Type::fun(Type::Var("a".into()), Type::Var("a".into())),
            },
        );
        let ops = TypeOpMap::default();

        let e = parse_expr_from_val("module M where\nx = ident 42\n");
        let mut s = UnifyState::new();
        let ty = infer_expr(&mut s, &mut env, &ops, &e).unwrap();
        assert_eq!(s.zonk(&ty), int());
    }

    #[test]
    fn application_of_non_function_fails() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("foo"), Scheme::mono(int()));
        let ops = TypeOpMap::default();

        let e = parse_expr_from_val("module M where\nx = foo 42\n");
        let mut s = UnifyState::new();
        let err = infer_expr(&mut s, &mut env, &ops, &e).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn unbound_var_reports_error() {
        let mut env = Env::new();
        let ops = TypeOpMap::default();
        let e = parse_expr_from_val("module M where\nx = missing\n");
        let mut s = UnifyState::new();
        let err = infer_expr(&mut s, &mut env, &ops, &e).unwrap_err();
        match err {
            InferError::UnboundVar(n) => assert_eq!(n, "missing"),
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn typed_binder_constrains_lambda() {
        // `\(x :: Int) -> x` must infer Int -> Int (no generalization).
        let src = "module M where\nfoo = \\(x :: Int) -> x\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "(Int -> Int)");
    }

    #[test]
    fn type_annotation_forces_expected_type() {
        // `(foo :: Boolean)` — fails because foo is Int.
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("foo"), Scheme::mono(int()));
        let ops = TypeOpMap::default();
        let e = parse_expr_from_val("module M where\nx = (foo :: Boolean)\n");
        let mut s = UnifyState::new();
        let err = infer_expr(&mut s, &mut env, &ops, &e).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)));
    }

    #[test]
    fn constructor_looked_up_in_env() {
        // Seed `Just` as `forall a. a -> Maybe a`.
        let mut env = Env::new();
        env.bind_scheme(
            QName::unqualified("Just"),
            Scheme {
                vars: vec!["a".into()],
                ty: Type::fun(
                    Type::Var("a".into()),
                    Type::app(
                        Type::Con(QName::unqualified("Maybe")),
                        Type::Var("a".into()),
                    ),
                ),
            },
        );
        let ops = TypeOpMap::default();

        let e = parse_expr_from_val("module M where\nx = Just 1\n");
        let mut s = UnifyState::new();
        let ty = infer_expr(&mut s, &mut env, &ops, &e).unwrap();
        let zonked = s.zonk(&ty);
        assert_eq!(
            zonked,
            Type::app(Type::Con(QName::unqualified("Maybe")), int()),
        );
    }

    #[test]
    fn mutual_recursion_within_scc_types_consistently() {
        // f calls g, g calls f. Without explicit signatures both must
        // unify through their pre-inserted slots.
        let src = "module M where\nf x = g x\ng x = f x\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        // Both should generalize to `forall a b. a -> b` (or similar).
        assert_eq!(schemes.len(), 2);
        let f = schemes.iter().find(|s| s.name == "f").unwrap();
        let g = schemes.iter().find(|s| s.name == "g").unwrap();
        // Both inferred the same shape a -> b.
        match (&f.scheme.ty, &g.scheme.ty) {
            (Type::Fun(..), Type::Fun(..)) => {}
            other => panic!("{other:?}"),
        }
    }

    // ------------------------------------------------------------------
    // M4b: if / let
    // ------------------------------------------------------------------

    #[test]
    fn if_returns_unified_branch_type() {
        let mut s = UnifyState::new();
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("c"), Scheme::mono(bool_ty()));
        let ops = TypeOpMap::default();
        let e = parse_expr_from_val("module M where\nx = if c then 1 else 2\n");
        let t = infer_expr(&mut s, &mut env, &ops, &e).unwrap();
        assert_eq!(s.zonk(&t), int());
    }

    #[test]
    fn if_cond_must_be_boolean() {
        let mut s = UnifyState::new();
        let mut env = Env::new();
        let ops = TypeOpMap::default();
        // Condition `1` is Int, not Boolean — unification must fail.
        let e = parse_expr_from_val("module M where\nx = if 1 then 1 else 2\n");
        let err = infer_expr(&mut s, &mut env, &ops, &e).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn if_branches_must_unify() {
        let mut s = UnifyState::new();
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("c"), Scheme::mono(bool_ty()));
        let ops = TypeOpMap::default();
        let e = parse_expr_from_val("module M where\nx = if c then 1 else \"hi\"\n");
        let err = infer_expr(&mut s, &mut env, &ops, &e).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn let_binds_simple_value() {
        let src = "module M where\nfoo = let x = 1 in x\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Int");
    }

    #[test]
    fn let_is_polymorphic() {
        // `let id = \y -> y in id 1` must type-check: `id` generalizes to
        // `forall a. a -> a`, then instantiates with `Int` at the call site.
        let src = "module M where\nfoo = let id = \\y -> y in id 1\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Int");
    }

    #[test]
    fn let_polymorphic_binding_used_at_two_types() {
        // Same `id` applied to an Int in `then`, a Boolean in `else`.
        // Branches must unify, so the *expression* is Int-or-Boolean, which
        // won't match: we expect a Unify error.
        let src = "module M where\nc = true\nfoo = let id = \\y -> y in if c then id 1 else id true\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        // Seed `true` since our literal handling doesn't know Boolean ctors.
        env.bind_scheme(QName::unqualified("true"), Scheme::mono(bool_ty()));
        let err = infer_value_scc(&ops, &mut env, &decls).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn let_signature_constrains_binding() {
        // Signature forces Int; body is fine. Subsequent use must match.
        let src = "\
module M where
foo =
  let
    x :: Int
    x = 1
  in x
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Int");
    }

    #[test]
    fn let_binding_shadows_outer_scheme() {
        // Outer `foo = 1` is Int. Inner `let foo = "str" in foo` rebinds it
        // to String locally. The overall expression is String.
        let src = "module M where\nbar = let foo = \"str\" in foo\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("foo"), Scheme::mono(int()));
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "String");
    }

    #[test]
    fn let_mutually_recursive() {
        // Both names are pre-inserted, so `f` can refer to `g` and vice
        // versa while they're being inferred. Both should generalize.
        let src = "\
module M where
foo =
  let
    f x = g x
    g x = f x
  in f
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        // The outer `foo` is whatever `f` is — a -> b shape.
        match &schemes[0].scheme.ty {
            Type::Fun(..) => {}
            other => panic!("expected fun, got {other:?}"),
        }
    }

    // ------------------------------------------------------------------
    // M4c: case / patterns
    // ------------------------------------------------------------------

    fn seed_maybe(env: &mut Env) {
        let a = Type::Var("a".into());
        let maybe_a = Type::app(Type::Con(QName::unqualified("Maybe")), a.clone());
        env.bind_scheme(
            QName::unqualified("Just"),
            Scheme { vars: vec!["a".into()], ty: Type::fun(a.clone(), maybe_a.clone()) },
        );
        env.bind_scheme(
            QName::unqualified("Nothing"),
            Scheme { vars: vec!["a".into()], ty: maybe_a },
        );
    }

    #[test]
    fn case_with_literal_patterns_returns_branch_type() {
        let src = "\
module M where
foo x = case x of
  0 -> \"zero\"
  _ -> \"other\"
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "(Int -> String)");
    }

    #[test]
    fn case_constructor_pattern_unwraps_data_type() {
        // `case m of Just x -> x; Nothing -> 0` requires m :: Maybe Int,
        // branches unify to Int.
        let src = "\
module M where
foo m = case m of
  Just x -> x
  Nothing -> 0
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        seed_maybe(&mut env);
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "((Maybe Int) -> Int)");
    }

    #[test]
    fn case_nested_constructor_pattern() {
        // `Just (Just x)` binds x to the inner type.
        let src = "\
module M where
foo m = case m of
  Just (Just x) -> x
  Just Nothing -> 0
  Nothing -> 1
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        seed_maybe(&mut env);
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "((Maybe (Maybe Int)) -> Int)",
        );
    }

    #[test]
    fn case_branches_must_unify() {
        // One branch returns Int, the other a String — must fail because
        // `Just _ -> 1` forces result = Int, `Nothing -> "oops"` forces
        // result = String, and Int vs String doesn't unify.
        let src = "\
module M where
foo m = case m of
  Just _ -> 1
  Nothing -> \"oops\"
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        seed_maybe(&mut env);
        let err = infer_value_scc(&ops, &mut env, &decls).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn case_as_pattern_binds_whole_and_parts() {
        // `all@(Just _)` binds `all` to `Maybe a` and still enforces the
        // constructor match.
        let src = "\
module M where
foo m = case m of
  all@(Just _) -> all
  Nothing -> Nothing
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        seed_maybe(&mut env);
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        // Argument and result must both be `Maybe a` for the same a.
        assert!(
            scheme_display(&schemes[0].scheme).contains("Maybe"),
            "expected Maybe in {}",
            scheme_display(&schemes[0].scheme),
        );
    }

    #[test]
    fn case_multi_scrutinee_pair() {
        // PureScript case supports multi-scrutinee: `case x, y of p, q -> ...`.
        let src = "\
module M where
foo m n = case m, n of
  Just x, Just y -> x
  _, _ -> 0
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        seed_maybe(&mut env);
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        // The second scrutinee's `y` is unused in the first branch — its
        // element type stays polymorphic and gets generalized. The first
        // scrutinee's `x` is returned, so it's forced to Int by the
        // fallthrough branch.
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "forall a. ((Maybe Int) -> ((Maybe a) -> Int))",
        );
    }

    #[test]
    fn guarded_equation_boolean_guard() {
        // `foo x | x == x = 1` — for M4c we accept any Boolean-typed guard
        // expression. Seed `eq` so the guard expression has a way to type.
        let src = "\
module M where
foo x | isOk x = 1
      | true = 0
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        env.bind_scheme(
            QName::unqualified("isOk"),
            Scheme {
                vars: vec!["a".into()],
                ty: Type::fun(Type::Var("a".into()), bool_ty()),
            },
        );
        env.bind_scheme(QName::unqualified("true"), Scheme::mono(bool_ty()));
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        // foo :: forall a. a -> Int (first guard ignores result of isOk,
        // returns Int; second guard returns Int).
        let disp = scheme_display(&schemes[0].scheme);
        assert!(disp.ends_with("Int)"), "got: {disp}");
    }

    #[test]
    fn guard_cond_must_be_boolean() {
        let src = "\
module M where
foo x | x = 1
";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        // Bind x's inferred type loosely; expect the guard to force it to
        // Boolean. That in itself is fine; the failure here comes if we seed
        // x :: Int.
        // Instead, test by requiring the scheme to end with "Boolean -> Int".
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "(Boolean -> Int)");
    }

    #[test]
    fn boolean_literal_infers_boolean() {
        let mut s = UnifyState::new();
        let mut env = Env::new();
        let ops = TypeOpMap::default();
        let e = parse_expr_from_val("module M where\nx = true\n");
        // `true` is parsed as Constructor or Var depending on the parser.
        // Fall through: if it resolves as an unbound Var, seed it.
        let res = infer_expr(&mut s, &mut env, &ops, &e);
        if let Err(InferError::UnboundVar(_)) = res {
            env.bind_scheme(QName::unqualified("true"), Scheme::mono(bool_ty()));
            let t = infer_expr(&mut s, &mut env, &ops, &e).unwrap();
            assert_eq!(s.zonk(&t), bool_ty());
        } else {
            assert_eq!(s.zonk(&res.unwrap()), bool_ty());
        }
    }
}
