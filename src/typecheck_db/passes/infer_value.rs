//! Bidirectional inference. Current coverage:
//!
//! - M4a: `Var`, `App`, `Lambda`, `Parens`, `TypeAnnotation`, `Hole`,
//!   `Wildcard`, `Literal`, `Constructor`.
//! - M4b: `If`, `Let` (with let-polymorphism).
//! - M4c: `Case` with constructor / `As` / literal / typed patterns, plus
//!   both `Unconditional` and `Guarded` alternative bodies.
//! - M4d: records — literals (including puns), field access, field
//!   update; `Binder::Record` patterns.
//! - M4e: arrays — `Expr::Array` literals and `Binder::Array` patterns
//!   (elements unify to a single `Array α`).
//!
//! The entry point is `infer_value_scc`, which corresponds to the
//! `infer_value_scc` nanopass in the plan: given an SCC of top-level
//! value decls plus the caller-supplied [`Env`] of dependency schemes, it
//! returns a [`Scheme`] per name defined in the SCC.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::typecheck_db::driver::{DriverError, TypecheckDb};
use crate::typecheck_db::ir::{self as ir, Binder, Decl, Expr, LetBinding, Literal};
use crate::typecheck_db::env::{Env, Lookup};
use crate::typecheck_db::generalize::{generalize, instantiate};
use crate::typecheck_db::key::{hash_bytes, InputHasher, OutputHash, PassKey};
use crate::typecheck_db::store::DepEdge;
use crate::typecheck_db::types::{convert_type_expr, Constraint, QName, Scheme, Type, TypeOpMap};
use crate::typecheck_db::unify::{UnifyError, UnifyState};

pub const PASS_NAME: &str = "infer_value_scc";
pub const PASS_VERSION: u32 = 1;

#[derive(Debug, Clone, Error)]
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
    #[error("do-block may not end with `let`")]
    InvalidDoLet,
    #[error("do-block may not end with `<-` bind")]
    InvalidDoBind,
    #[error("empty do-block")]
    EmptyDoBlock,
    #[error("anonymous function argument in invalid context")]
    IncorrectAnonymousArgument,
}

/// Output of `infer_value_scc` for one SCC of mutually-recursive value decls.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InferredScheme {
    pub name: String,
    pub scheme: Scheme,
    /// Exhaustiveness findings from case expressions and multi-equation
    /// groups inside this decl's body. Empty when either nothing needed
    /// checking or no registries were supplied (see
    /// `infer_value_scc` vs `infer_value_scc_with_registries`).
    #[serde(default)]
    pub exhaustiveness_errors:
        Vec<crate::typecheck_db::passes::exhaustiveness::NonExhaustive>,
    /// Constraints collected from this decl's body but not yet
    /// discharged. Populated by the M5 Phase A collector; Phase B's
    /// solver consumes this and writes to `resolved_dicts` /
    /// `constraint_errors` below.
    #[serde(default)]
    pub pending_constraints:
        Vec<crate::typecheck_db::passes::constraints::PendingConstraint>,
    /// Phase B: one entry per constraint the solver successfully
    /// matched to an instance. Shallow dicts for now — Phase E
    /// nests context resolutions.
    #[serde(default)]
    pub resolved_dicts:
        Vec<crate::typecheck_db::passes::constraints::ResolvedDict>,
    /// Phase B: unresolvable constraints (no matching instance in
    /// scope, for now).
    #[serde(default)]
    pub constraint_errors:
        Vec<crate::typecheck_db::passes::constraints::ConstraintError>,
    /// Phase E: per-call-site lookup. Keyed by the `Var`
    /// reference's span (the site the constraint was born at, not
    /// the instance's span), mapped to the `ResolvedDict` that
    /// satisfies it. Codegen consults this to emit the right dict
    /// reference at each use.
    ///
    /// Context-induced sub-constraints pushed by the recursive
    /// solver inherit their parent's span — they land in this map
    /// too, but the caller stores only the last resolution per
    /// span (outer over context) since codegen only emits a
    /// reference once per site and recovers the sub-dicts from
    /// `ResolvedDict::context` on demand.
    #[serde(default)]
    pub constraint_dicts: std::collections::HashMap<
        crate::span::Span,
        crate::typecheck_db::passes::constraints::ResolvedDict,
    >,
    /// Typed-hole diagnostics recorded during this decl's body. Each
    /// entry captures the hole's source name, inferred type (zonked),
    /// constraints born downstream of the hole that reference its
    /// unification variables, and a snapshot of the local bindings
    /// visible at the hole site.
    #[serde(default)]
    pub hole_diagnostics: Vec<HoleDiagnostic>,
}

/// A typed-hole diagnostic surfaced from inference. Mirrors the
/// old `TypeError::HoleInferredType` variant's shape, adapted to the
/// typecheck_db type world.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HoleDiagnostic {
    pub decl_name: Option<String>,
    pub span: crate::span::Span,
    pub hole_name: String,
    pub inferred_type: Type,
    pub constraints: Vec<Constraint>,
    pub local_bindings: Vec<(String, Type)>,
    /// Internal bookkeeping: how many `pending_constraints` had been
    /// recorded on `UnifyState` when this hole was seen. At drain time,
    /// constraints with index >= this value are the candidates for
    /// "constraints related to this hole". Zeroed out in serialized
    /// form; callers should treat it as opaque.
    #[serde(skip)]
    pub constraint_start: usize,
}

/// Case / multi-equation pattern match recorded during inference so
/// the exhaustiveness check can run against fully-zonked scrutinee
/// types at the end of the SCC.
#[derive(Debug, Clone)]
pub struct PendingExhaust {
    /// Name of the value decl whose body the case sits inside. The
    /// draining caller uses this to route findings to the right
    /// `InferredScheme`.
    pub decl_name: Option<String>,
    pub span: crate::span::Span,
    pub scrutinee_tys: Vec<Type>,
    pub alts: Vec<PendingAlt>,
}

#[derive(Debug, Clone)]
pub struct PendingAlt {
    pub binders: Vec<Binder>,
    pub guarded: ir::GuardedExpr,
}

/// Snapshot the monomorphic + scheme-typed local bindings visible at a
/// point inside a decl body, walking inner-to-outer and dropping outer
/// bindings shadowed by inner ones. Used by typed-hole reporting to
/// capture the `CONTEXT:` set for the emitted diagnostic.
fn snapshot_env_locals(env: &Env, state: &UnifyState) -> Vec<(String, Type)> {
    use std::collections::HashSet;
    let mut seen: HashSet<String> = HashSet::new();
    let mut out: Vec<(String, Type)> = Vec::new();
    for scope in env.locals.iter().rev() {
        for (name, ty) in scope {
            if seen.insert(name.clone()) {
                out.push((name.clone(), state.zonk(&ty.clone())));
            }
        }
    }
    for scope in env.local_schemes.iter().rev() {
        for (name, scheme) in scope {
            if seen.insert(name.clone()) {
                out.push((name.clone(), state.zonk(&scheme.ty.clone())));
            }
        }
    }
    out
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
        Expr::Var { span, name } => infer_var(state, env, *span, name),
        Expr::Constructor { name, .. } => infer_constructor(state, env, name),
        Expr::Literal { lit, .. } => Ok(type_of_literal(lit)),
        Expr::App { func, arg, .. } => infer_app(state, env, type_ops, func, arg),
        Expr::Lambda { binders, body, .. } => {
            infer_lambda(state, env, type_ops, binders, body)
        }
        Expr::Parens { expr, .. } => infer_expr(state, env, type_ops, expr),
        Expr::TypeAnnotation { expr, ty, .. } => {
            // The declared type may be polymorphic (outer `Forall`
            // and/or a `Constrained` layer). Deep-instantiate into
            // every positive position so inner foralls on `Fun.ret`
            // also collapse to unifs — keeping the result
            // structurally compatible with a caller-side sig that
            // was produced the same way. See
            // `deep_instantiate_positive` for the PJ §5 rationale.
            let mut declared = crate::typecheck_db::types::expand_aliases(
                convert_type_expr(ty, type_ops),
                &env.aliases,
            );
            if !env.scoped_tys.is_empty() {
                declared = crate::typecheck_db::generalize::apply_var_subst(
                    &declared,
                    &env.scoped_tys,
                );
            }
            // Scoped type variables for the inner expression: if the
            // annotation has an outer `Forall`, register each
            // forall-bound name in `env.scoped_tys` (mapping to the
            // fresh unif `deep_instantiate_positive` is about to
            // produce) so a nested annotation like
            // `(\b -> b :: b) :: forall b. b -> b` resolves the
            // inner `b` to the same unif as the outer one.
            let mut scoped_added: Vec<String> = Vec::new();
            if let Type::Forall(vs, _) = &declared {
                for (n, _, _) in vs {
                    if !env.scoped_tys.contains_key(n) {
                        let u = state.fresh();
                        env.scoped_tys.insert(n.clone(), u);
                        scoped_added.push(n.clone());
                    }
                }
            }
            // Now apply scoped_tys substitution again so the outer
            // forall vars map to those same unifs throughout.
            if !env.scoped_tys.is_empty() {
                declared = crate::typecheck_db::generalize::apply_var_subst(
                    &declared,
                    &env.scoped_tys,
                );
            }
            let monotype =
                deep_instantiate_positive(state, declared, true);
            let outcome = check_expr(state, env, type_ops, expr, &monotype);
            for n in scoped_added {
                env.scoped_tys.remove(&n);
            }
            outcome?;
            Ok(monotype)
        }
        // A bare `_` in expression position is only valid if the
        // desugar pipeline has already lifted it into a lambda
        // param (operator sections, record-update sections, ...).
        // Any residual `Expr::Wildcard` at inference time means the
        // user wrote `_` outside a section context, which is the
        // `IncorrectAnonymousArgument` case in the reference
        // compiler.
        Expr::Wildcard { .. } => Err(InferError::IncorrectAnonymousArgument),
        Expr::Hole { span, name } => {
            let ty = state.fresh();
            let hole_name = name.resolve().unwrap_or_default();
            let local_bindings = snapshot_env_locals(env, state);
            let constraint_start = state.pending_constraints_len();
            state.record_pending_hole(HoleDiagnostic {
                decl_name: None,
                span: *span,
                hole_name,
                inferred_type: ty.clone(),
                constraints: Vec::new(),
                local_bindings,
                constraint_start,
            });
            Ok(ty)
        }
        Expr::Negate { expr, .. } => infer_expr(state, env, type_ops, expr),

        Expr::If { cond, then_expr, else_expr, .. } => {
            infer_if(state, env, type_ops, cond, then_expr, else_expr)
        }
        Expr::Let { bindings, body, .. } => {
            infer_let(state, env, type_ops, bindings, body)
        }
        Expr::Case { span, exprs, alts } => {
            infer_case(state, env, type_ops, *span, exprs, alts)
        }
        Expr::Record { fields, .. } => infer_record(state, env, type_ops, fields),
        Expr::RecordAccess { expr, field, .. } => {
            infer_record_access(state, env, type_ops, expr, field)
        }
        Expr::RecordUpdate { expr, updates, .. } => {
            infer_record_update(state, env, type_ops, expr, updates)
        }
        Expr::Array { elements, .. } => infer_array(state, env, type_ops, elements),

        // Forms reserved for later sub-milestones.
        // Operators (`Expr::Op`, `OpParens`, `BacktickApp`) don't
        // exist in `ir::Expr` — they're eliminated at lowering
        // time, which is why this match doesn't need an arm for
        // them any more.
        Expr::Do { statements, .. } => infer_do(state, env, type_ops, statements),
        Expr::Ado { statements, result, .. } => {
            infer_ado(state, env, type_ops, statements, result)
        }
        Expr::VisibleTypeApp { func, .. } => {
            // Visible type applications (`f @Int x`) pin the next
            // quantified type variable of `f` to the annotated
            // type. A precise implementation would instantiate
            // `f`'s scheme with the explicit type in place of the
            // first fresh unif; we don't track quantifier order
            // through instantiation yet, so fall back to ignoring
            // the annotation and inferring `f` normally. Wrong for
            // pathological cases that only work with the
            // annotation, but correct for the majority where the
            // annotation just echoes inference's result.
            infer_expr(state, env, type_ops, func)
        }
        Expr::AsPattern { name, .. } => {
            // At expression level, `name@pattern` survives from parsing
            // only when the rhs is a VTA annotation (`f@Type`). The
            // pattern slot carries the annotation. We don't yet
            // specialise f's scheme with the annotation — fall back to
            // inferring the base expression, matching the
            // VisibleTypeApp treatment above.
            infer_expr(state, env, type_ops, name)
        }
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
    // Zonk first in case `expected` is a unif bound to a Forall.
    let zonked = state.zonk(expected);
    // Deep-skolemisation: push fresh skolems through every
    // outer `Forall`, `Constrained.body`, and `Fun.ret` layer.
    // A later attempt to bind an OUTER unification variable to
    // anything containing these skolems fails via `bind_var`'s
    // escape check — exactly how rank-2 violations surface
    // (see Peyton-Jones et al., "Practical type inference for
    // arbitrary-rank types" §5). A1 discards the peeled
    // constraint-givens; A2 will push them onto a given stack so
    // the solver can discharge matching pending constraints.
    let needs_skolemise = matches!(
        &zonked,
        Type::Forall(_, _) | Type::Constrained(_, _)
    );
    if needs_skolemise {
        let (skolemised, givens) = deep_skolemise_positive(state, zonked);
        let snapshot = state.push_givens(givens);
        let outcome = check_expr(state, env, type_ops, expr, &skolemised);
        state.pop_givens_to(snapshot);
        return outcome;
    }

    // Bidirectional shortcut: `Lambda` checked against an arrow
    // type peels arrows and binds each `Var` binder directly to
    // the arg type. Without this, `bind_pattern` creates fresh
    // unifs and any polymorphic structure in the expected is
    // lost to a fresh unif.
    if let Expr::Lambda { binders, body, .. } = expr {
        if matches!(zonked, Type::Fun(_, _)) {
            return check_lambda(state, env, type_ops, binders, body, &zonked);
        }
    }

    // Subsumption (sigma-vs-rho per Peyton-Jones §5): the
    // expected has already been deep-skolemised above, so when
    // the inferred actual zonks to a `Forall` or a `Constrained`
    // we deep-instantiate it before unifying. Without this a
    // polymorphic local — e.g. a check-mode binder that
    // preserved its rank-2 sig — wouldn't unify against the
    // skolemised expected because `forall_head_matches` rejects
    // non-`Con`-headed foralls.
    let actual = infer_expr(state, env, type_ops, expr)?;
    let actual_zonked = state.zonk(&actual);
    let actual_inst = if matches!(
        &actual_zonked,
        Type::Forall(_, _) | Type::Constrained(_, _)
    ) {
        deep_instantiate_positive(state, actual_zonked, true)
    } else {
        actual
    };
    state.unify(&actual_inst, expected)?;
    Ok(())
}

/// True when the scheme's body contains a top-level `Constrained`
/// layer — either directly or inside a `Forall`. Used to gate
/// check-mode: constrained sigs need a given-tracking solver that
/// we don't have yet; without it, stripping the constraint would
/// leave body-level class-method uses unsolvable.
fn scheme_has_constraint(scheme: &Scheme) -> bool {
    fn walk(ty: &Type) -> bool {
        match ty {
            Type::Constrained(_, _) => true,
            Type::Forall(_, body) => walk(body),
            _ => false,
        }
    }
    walk(&scheme.ty)
}

/// True when the scheme's body contains a `Forall` below the
/// outer layer — i.e. the scheme describes a rank-2+ type. Used
/// to gate check-mode: only rank-2 decls need the skolem-based
/// bidirectional path; rank-1 decls stay on the existing
/// infer-then-unify path.
/// True when `ty` contains a `Forall` anywhere — including
/// inside `Fun.arg` positions. Used to gate the lambda-arg
/// routing in `infer_app`: even a `Fun(Forall(..), Int)` arg
/// type needs check-mode so the binder gets the Forall.
fn type_contains_forall(ty: &Type) -> bool {
    match ty {
        Type::Forall(_, _) => true,
        Type::App(f, a) | Type::Fun(f, a) | Type::Kinded(f, a) => {
            type_contains_forall(f) || type_contains_forall(a)
        }
        Type::Constrained(cs, b) => {
            cs.iter().any(|c| c.args.iter().any(type_contains_forall))
                || type_contains_forall(b)
        }
        Type::Record(fs, t) | Type::Row(fs, t) => {
            fs.iter().any(|(_, v)| type_contains_forall(v))
                || t.as_ref().map_or(false, |t| type_contains_forall(t))
        }
        _ => false,
    }
}

fn scheme_has_inner_forall(scheme: &Scheme) -> bool {
    fn walk_below_top(ty: &Type) -> bool {
        match ty {
            Type::Forall(_, _) => true,
            Type::App(f, a) | Type::Fun(f, a) | Type::Kinded(f, a) => {
                walk_below_top(f) || walk_below_top(a)
            }
            Type::Constrained(cs, b) => {
                cs.iter().any(|c| c.args.iter().any(walk_below_top))
                    || walk_below_top(b)
            }
            Type::Record(fs, t) | Type::Row(fs, t) => {
                fs.iter().any(|(_, v)| walk_below_top(v))
                    || t.as_ref().map_or(false, |t| walk_below_top(t))
            }
            _ => false,
        }
    }
    walk_below_top(&scheme.ty)
}

/// Check a decl's binders + guarded body against an expected
/// type. Peels the expected (skolemising foralls, stripping
/// constraints) down to a `Fun` chain matching the decl's
/// binders, then checks the body against the return type.
///
/// Mirrors `check_lambda` but works over decl-level binders +
/// `GuardedExpr` rather than `Lambda` binders + `Expr`.
fn check_equation(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    binders: &[Binder],
    guarded: &ir::GuardedExpr,
    expected: &Type,
) -> Result<(), InferError> {
    // Peel outer `Forall` (introducing skolems) and any
    // `Constrained` layer once, so the arrow-peeling loop below
    // sees a `Fun`-chain. Record each Forall-var → skolem
    // mapping in `env.scoped_tys` so body-level typed binders
    // (`\(x :: a) -> …`) and type annotations refer to the
    // same skolem. Peeled constraints become givens: the solver
    // treats them as known-true while checking the body, which
    // is what lets a sig like `Semigroupoid a => …` call
    // `compose` (itself `Semigroupoid a =>`) without tripping
    // `NoInstanceFound` against a skolem.
    let mut scoped_added: Vec<String> = Vec::new();
    let givens_snapshot = state.push_givens(Vec::new());
    let peeled = {
        let mut cur = state.zonk(expected);
        loop {
            match cur {
                Type::Forall(vs, body) => {
                    let mut subst: HashMap<String, Type> = HashMap::new();
                    for (n, _, _) in &vs {
                        let sk = Type::Skolem(state.fresh_named_skolem(n));
                        subst.insert(n.clone(), sk.clone());
                        env.scoped_tys.insert(n.clone(), sk);
                        scoped_added.push(n.clone());
                    }
                    cur = crate::typecheck_db::generalize::apply_var_subst(
                        &body, &subst,
                    );
                }
                Type::Constrained(cs, body) => {
                    state.push_givens(cs);
                    cur = *body;
                }
                other => break other,
            }
        }
    };

    env.push_scope();
    let mut rest = peeled;
    let mut consumed: usize = 0;
    for b in binders {
        // Before each arrow peel, also peel any `Forall` /
        // `Constrained` layer that sits in the return position.
        // Sigs like
        // `forall s i o. s -> (s -> i -> o) -> forall r. (...) -> r`
        // (after alias expansion of `SomeAuto`) need their inner
        // `forall r` skolemised once we're past the first two
        // arrows so the third binder can see the now-skolemised
        // arrow chain.
        loop {
            let zonked = state.zonk(&rest);
            match zonked {
                Type::Forall(vs, body) => {
                    let mut subst: HashMap<String, Type> = HashMap::new();
                    for (n, _, _) in &vs {
                        let sk = Type::Skolem(state.fresh_named_skolem(n));
                        subst.insert(n.clone(), sk.clone());
                        env.scoped_tys.insert(n.clone(), sk);
                        scoped_added.push(n.clone());
                    }
                    rest = crate::typecheck_db::generalize::apply_var_subst(
                        &body, &subst,
                    );
                }
                Type::Constrained(cs, body) => {
                    state.push_givens(cs);
                    rest = *body;
                }
                _ => break,
            }
        }
        let zonked = state.zonk(&rest);
        let (arg, new_rest) = match zonked {
            Type::Fun(a, r) => (*a, *r),
            _ => break,
        };
        match b {
            Binder::Var { name, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                env.bind_local(n, arg);
            }
            _ => {
                let pat_ty = bind_pattern(state, env, type_ops, b)?;
                state.unify(&pat_ty, &arg)?;
            }
        }
        rest = new_rest;
        consumed += 1;
    }
    if consumed < binders.len() {
        // Ran out of arrows before binders — fall back to
        // inference for the tail.
        let tail_ty = infer_equation(
            state,
            env,
            type_ops,
            &binders[consumed..],
            guarded,
        )?;
        state.unify(&tail_ty, &rest)?;
    } else {
        check_guarded(state, env, type_ops, guarded, &rest)?;
    }
    env.pop_scope();
    // Remove the scoped-ty entries we added — they belong to
    // THIS decl's scope, not siblings.
    for n in scoped_added {
        env.scoped_tys.remove(&n);
    }
    state.pop_givens_to(givens_snapshot);
    Ok(())
}

/// Check a `GuardedExpr` body against an expected type. Only
/// `Unconditional` uses true check-mode; guarded alternatives
/// fall back to inferring and unifying.
fn check_guarded(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    g: &ir::GuardedExpr,
    expected: &Type,
) -> Result<(), InferError> {
    match g {
        ir::GuardedExpr::Unconditional(e) => {
            check_expr(state, env, type_ops, e, expected)
        }
        ir::GuardedExpr::Guarded(_) => {
            let actual = infer_guarded(state, env, type_ops, g)?;
            state.unify(&actual, expected)?;
            Ok(())
        }
    }
}

/// Check a lambda expression against an expected arrow type by
/// peeling `Fun(arg, rest)` per binder. `Binder::Var` is bound
/// directly to `arg` — preserves any `Forall` inside; others go
/// through `bind_pattern` + unify.
fn check_lambda(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    binders: &[Binder],
    body: &Expr,
    expected: &Type,
) -> Result<(), InferError> {
    env.push_scope();
    let mut rest = expected.clone();
    let mut consumed: usize = 0;
    for b in binders {
        // Pre-peel any `Forall` / `Constrained` that sits in
        // return position before the next arrow — same trick as
        // `check_equation`. Without this a sig like
        // `... -> forall r. (...) -> r` (after alias expansion of
        // `SomeAuto`) breaks the binder chain at the inner
        // forall instead of skolemising it.
        loop {
            let zonked = state.zonk(&rest);
            match zonked {
                Type::Forall(vs, body) => {
                    let mut subst: HashMap<String, Type> = HashMap::new();
                    for (n, _, _) in &vs {
                        subst.insert(
                            n.clone(),
                            Type::Skolem(state.fresh_named_skolem(n)),
                        );
                    }
                    rest = crate::typecheck_db::generalize::apply_var_subst(
                        &body, &subst,
                    );
                }
                Type::Constrained(cs, body) => {
                    state.push_givens(cs);
                    rest = *body;
                }
                _ => break,
            }
        }
        let zonked = state.zonk(&rest);
        let (arg, new_rest) = match zonked {
            Type::Fun(a, r) => (*a, *r),
            _ => break,
        };
        match b {
            Binder::Var { name, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                env.bind_local(n, arg);
            }
            _ => {
                let pat_ty = bind_pattern(state, env, type_ops, b)?;
                state.unify(&pat_ty, &arg)?;
            }
        }
        rest = new_rest;
        consumed += 1;
    }
    if consumed < binders.len() {
        let tail_ty =
            infer_lambda(state, env, type_ops, &binders[consumed..], body)?;
        state.unify(&tail_ty, &rest)?;
    } else {
        check_expr(state, env, type_ops, body, &rest)?;
    }
    env.pop_scope();
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
    let data = crate::typecheck_db::passes::exhaustiveness::DataConstructors::new();
    let ctors = crate::typecheck_db::passes::exhaustiveness::CtorRegistry::new();
    infer_value_scc_with_registries(type_ops, env, decls, &data, &ctors)
}

/// Like `infer_value_scc`, but also checks exhaustiveness of every
/// case expression encountered while inferring the SCC's bodies.
///
/// Thin wrapper around [`infer_value_scc_with_all`] with an empty
/// instance index — no constraint solving runs. Kept so the older
/// tests that predate Phase B can stay on this entry point.
pub fn infer_value_scc_with_registries(
    type_ops: &TypeOpMap,
    env: &mut Env,
    decls: &[&Decl],
    data_constructors: &crate::typecheck_db::passes::exhaustiveness::DataConstructors,
    ctor_details: &crate::typecheck_db::passes::exhaustiveness::CtorRegistry,
) -> Result<Vec<InferredScheme>, InferError> {
    let instances = crate::typecheck_db::passes::instance_index::InstanceIndex::new();
    infer_value_scc_with_all(type_ops, env, decls, data_constructors, ctor_details, &instances)
}

/// The real entry point: runs inference, exhaustiveness, *and*
/// constraint solving for one SCC.
///
/// `instances` is the set of instances visible when solving. An
/// empty index is well-defined — every pending constraint will
/// either defer (polymorphic) or produce a `NoInstanceFound` error.
pub fn infer_value_scc_with_all(
    type_ops: &TypeOpMap,
    env: &mut Env,
    decls: &[&Decl],
    data_constructors: &crate::typecheck_db::passes::exhaustiveness::DataConstructors,
    ctor_details: &crate::typecheck_db::passes::exhaustiveness::CtorRegistry,
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
) -> Result<Vec<InferredScheme>, InferError> {
    // Pre-register each SCC member with a fresh unif var so mutual
    // references within the SCC type-check. After inference, we generalize.
    let mut state = UnifyState::new();

    let mut slot_of: HashMap<String, Type> = HashMap::new();
    let mut decl_refs: Vec<(&Decl, String)> = Vec::new();
    // Track decls whose declared signature carries a `Partial`
    // constraint. Those decls are allowed to be non-exhaustive:
    // the caller has promised via the constraint that the
    // uncovered cases never arise at runtime. Skipping
    // exhaustiveness for them is how `fromJust (Just x) = x`
    // stays clean.
    let mut partial_decls: std::collections::HashSet<String> =
        std::collections::HashSet::new();

    for decl in decls {
        if let Decl::Value { name, .. } = decl {
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            if has_partial_constraint(env, &n) {
                partial_decls.insert(n.clone());
            }
            let v = state.fresh();
            // For rank-2+ user-signed decls — those that will go
            // through check-mode below — skip the local-slot
            // shadow. The slot's unif is allocated BEFORE
            // `check_equation` introduces skolems, so any later
            // self-reference that tries to bind the slot to a
            // skolem-containing type would fail the escape
            // check. Leaving the name in `env.top_level` only
            // means self-ref goes through scheme instantiation
            // each time — fresh unifs at each call site.
            let is_signed_for_check_mode = env
                .local_signed
                .contains(&n)
                && env
                    .top_level
                    .get(&QName { module: None, name: n.clone() })
                    .map(|s| scheme_has_inner_forall(s))
                    .unwrap_or(false);
            if !is_signed_for_check_mode {
                env.bind_local(n.clone(), v.clone());
            }
            slot_of.insert(n.clone(), v);
            decl_refs.push((*decl, n));
        }
    }

    // Infer each decl's body against its pre-registered slot. The
    // "current decl" marker on state lets `infer_case` stamp each
    // pending exhaustiveness record with its owning decl.
    for (decl, name) in &decl_refs {
        if let Decl::Value { binders, guarded, where_clause, .. } = decl {
            let expected = slot_of.get(name).cloned().unwrap();
            state.set_current_decl(Some(name.clone()));
            let _ = sig_param_types; // retained for future sig-aware work
            let guarded_with_where =
                wrap_guarded_with_where(guarded.clone(), where_clause.clone());

            // Bidirectional check-mode: enabled for rank-2+
            // user-signed decls only (those whose body has a
            // `Forall` below the outer layer). Rank-1 sigs stay
            // on the infer path because turning check-mode on
            // for them is currently noisy (module-qualifier
            // mismatches, constraint-discharge edge cases).
            let sig_scheme: Option<Scheme> = if env.local_signed.contains(name) {
                let candidate = env
                    .top_level
                    .get(&QName { module: None, name: name.clone() })
                    .cloned();
                match candidate {
                    Some(s) if scheme_has_inner_forall(&s) => Some(s),
                    _ => None,
                }
            } else {
                None
            };
            let _ = decl;
            let _ = scheme_has_constraint;

            if let Some(scheme) = sig_scheme {
                // Reconstruct the full declared type:
                // `Forall(vars, body)`. `check_expr` will
                // skolemise the outer forall and peel the
                // `Constrained` layer before descending into
                // the body with check-mode active.
                let full_sig = if scheme.vars.is_empty() {
                    scheme.ty.clone()
                } else {
                    Type::Forall(
                        scheme
                            .vars
                            .iter()
                            .cloned()
                            .map(|n| (n, false, None))
                            .collect(),
                        Box::new(scheme.ty.clone()),
                    )
                };
                check_equation(
                    &mut state,
                    env,
                    type_ops,
                    binders,
                    &guarded_with_where,
                    &full_sig,
                )?;
                // Pin the slot to a deep-instantiated monotype of
                // the sig so the final generalize step
                // reconstructs the same scheme. `deep_instantiate_
                // positive` replaces every positive-position
                // `Forall` var with a fresh unif (so generalize
                // can quantify them back) and registers any
                // `Constrained` layer's constraints as pending
                // (so the inferred scheme carries them).
                // `instantiate_scheme_no_constraints` was wrong
                // here because it stripped inner `Forall`s
                // without substituting their vars — leaving rigid
                // `Var` ids leaking into the final scheme.
                let slot_shape =
                    deep_instantiate_positive(&mut state, full_sig.clone(), true);
                let _ = state.unify(&expected, &slot_shape);
            } else {
                // Scoped type variables (rank-1 path): when the
                // decl is user-signed, populate `env.scoped_tys`
                // with the sig's outer forall vars mapped to
                // fresh unifs so any let-binding sig (in
                // `where` / `let`) that references them resolves
                // to the same unif. This is the standard
                // PureScript ScopedTypeVariables behaviour for
                // sig-bound names like `f` and `a` referenced in
                // a `where`-clause helper's own sig.
                let mut scoped_added: Vec<String> = Vec::new();
                if env.local_signed.contains(name) {
                    if let Some(scheme) = env
                        .top_level
                        .get(&QName { module: None, name: name.clone() })
                    {
                        for v in &scheme.vars {
                            if !env.scoped_tys.contains_key(v) {
                                let u = state.fresh();
                                env.scoped_tys.insert(v.clone(), u);
                                scoped_added.push(v.clone());
                            }
                        }
                    }
                }
                let lam_ty = infer_equation(
                    &mut state,
                    env,
                    type_ops,
                    binders,
                    &guarded_with_where,
                )?;
                state.unify(&expected, &lam_ty)?;
                for n in scoped_added {
                    env.scoped_tys.remove(&n);
                }
            }
        }
    }
    state.set_current_decl(None);

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

    // Drain pending exhaustiveness entries once, then partition by
    // owning decl. Running the check here (after unification has
    // settled) means scrutinee types zonk to their final form.
    let pending = state.take_pending_exhaust();
    // Same treatment for pending constraints: group by owning decl
    // and zonk each constraint's type arguments so the solver sees
    // final forms (Phase A collects only; Phase B adds the solver).
    let pending_constraints_raw = state.take_pending_constraints();

    // Drain typed-hole records. For each hole, zonk its inferred type
    // and local-binding types, then scan the constraints born after
    // the hole for any whose args reference the hole's free unif vars
    // — those are the constraints we surface as "relevant to this
    // hole" in the diagnostic. This mirrors the old typechecker's
    // drain_pending_holes.
    //
    // Build a map from decl name → instantiated declared return type
    // (no constraints recorded). For a decl with `k` binders, we strip
    // the first `k` argument types from the sig so we get the return
    // type — what the hole in the body is expected to produce.
    let decl_binder_count: HashMap<String, usize> = decl_refs
        .iter()
        .filter_map(|(decl, name)| {
            if let Decl::Value { binders, .. } = decl {
                Some((name.clone(), binders.len()))
            } else {
                None
            }
        })
        .collect();
    // Full sig map (not binder-stripped): used for slot-sig unification so
    // that free unif vars inside partially-inferred types (e.g. `String -> u0`)
    // get resolved via the declared sig (e.g. `String -> Effect Unit`).
    let full_sig_map: HashMap<String, Type> = slot_of
        .keys()
        .filter_map(|n| {
            let scheme = env
                .top_level
                .get(&crate::typecheck_db::types::QName {
                    module: None,
                    name: n.clone(),
                })?
                .clone();
            let ty = instantiate_scheme_no_constraints(&mut state, &scheme);
            Some((n.clone(), ty))
        })
        .collect();
    // Unify each slot with its full declared sig — but only for decls that
    // actually contain a typed hole. Without the guard every decl's slot gets
    // unified with its sig, which corrupts state for `Partial`-constrained or
    // wildcard-typed decls that don't have holes.
    let hole_decls = state.decls_with_holes();
    for (n, sig_ty) in &full_sig_map {
        if !hole_decls.contains(n) {
            continue;
        }
        if let Some(slot) = slot_of.get(n) {
            let _ = state.unify(slot, sig_ty);
        }
    }
    // Binder-stripped sig map: used for direct hole-type annotation when the
    // hole is still a bare unif var (fallback path after slot-sig unification).
    let decl_sig_map: HashMap<String, Type> = slot_of
        .keys()
        .filter_map(|n| {
            let scheme = env
                .top_level
                .get(&crate::typecheck_db::types::QName {
                    module: None,
                    name: n.clone(),
                })?
                .clone();
            let mut ty = instantiate_scheme_no_constraints(&mut state, &scheme);
            // Strip argument types for each binder so the remaining
            // type is the return type (what the hole body must be).
            let binders = decl_binder_count.get(n).copied().unwrap_or(0);
            for _ in 0..binders {
                match ty {
                    Type::Fun(_, ret) => ty = *ret,
                    other => { ty = other; break; }
                }
            }
            Some((n.clone(), ty))
        })
        .collect();

    let pending_holes_raw = state.take_pending_holes();
    let mut holes_by_decl: HashMap<String, Vec<HoleDiagnostic>> = HashMap::new();
    for mut hole in pending_holes_raw {
        hole.inferred_type = state.zonk(&hole.inferred_type);
        // If the hole type is still a fully-free unif var (no
        // structural info), try to annotate it from the declared sig
        // of the owning decl.
        if let (Type::Unif(_), Some(owner)) =
            (&hole.inferred_type, &hole.decl_name)
        {
            if let Some(sig_ty) = decl_sig_map.get(owner) {
                // Unify the hole var with the declared sig type —
                // purely for diagnostic annotation, errors silently
                // ignored (body-inferred type takes precedence).
                let _ = state.unify(&hole.inferred_type, sig_ty);
                hole.inferred_type = state.zonk(&hole.inferred_type);
            }
        }
        // Deskolemise so hole diagnostics report types in the
        // reference compiler's `Var(name)` shape rather than our
        // internal `!sN`. Only applies when check-mode has
        // captured a name for the skolem via `fresh_named_skolem`.
        hole.inferred_type = state.deskolemise(&hole.inferred_type);
        for (_, ty) in hole.local_bindings.iter_mut() {
            *ty = state.deskolemise(&state.zonk(ty));
        }
        let hole_vars = state.free_unif_vars(&hole.inferred_type);
        if !hole_vars.is_empty() && hole.constraint_start <= pending_constraints_raw.len() {
            for pc in &pending_constraints_raw[hole.constraint_start..] {
                let zonked_args: Vec<Type> = pc
                    .constraint
                    .args
                    .iter()
                    .map(|a| state.zonk(a))
                    .collect();
                let arg_vars: std::collections::HashSet<u32> = zonked_args
                    .iter()
                    .flat_map(|a| state.free_unif_vars(a))
                    .collect();
                if hole_vars.iter().any(|v| arg_vars.contains(v)) {
                    hole.constraints.push(Constraint {
                        class: pc.constraint.class.clone(),
                        args: zonked_args,
                    });
                }
            }
        }
        if let Some(owner) = hole.decl_name.clone() {
            holes_by_decl.entry(owner).or_default().push(hole);
        }
    }

    let mut constraints_by_decl: HashMap<
        String,
        Vec<crate::typecheck_db::passes::constraints::PendingConstraint>,
    > = HashMap::new();
    for mut pc in pending_constraints_raw {
        let owner = match pc.decl_name.clone() {
            Some(n) => n,
            None => continue,
        };
        pc.constraint.args = pc
            .constraint
            .args
            .iter()
            .map(|a| state.zonk(a))
            .collect();
        constraints_by_decl.entry(owner).or_default().push(pc);
    }
    let mut errors_by_decl: HashMap<String, Vec<
        crate::typecheck_db::passes::exhaustiveness::NonExhaustive,
    >> = HashMap::new();
    for p in pending {
        let owner = match &p.decl_name {
            Some(n) => n.clone(),
            None => continue,
        };
        // Decls whose signature carries `Partial =>` opt out of
        // exhaustiveness — the user is asserting the missing
        // cases never arise at runtime.
        if partial_decls.contains(&owner) {
            continue;
        }
        // For each scrutinee column: gather the column's binders from
        // each unconditional-enough alt, zonk the scrutinee, run the
        // check.
        for (col, raw_scrut) in p.scrutinee_tys.iter().enumerate() {
            let scrut = state.zonk(raw_scrut);
            let mut column: Vec<&Binder> = Vec::new();
            for a in &p.alts {
                if !crate::typecheck_db::passes::exhaustiveness
                    ::is_unconditional_for_exhaustiveness(&a.guarded)
                {
                    continue;
                }
                if let Some(b) = a.binders.get(col) {
                    column.push(b);
                }
            }
            if let Some(missing) =
                crate::typecheck_db::passes::exhaustiveness::check_exhaustiveness(
                    &column,
                    &scrut,
                    data_constructors,
                    ctor_details,
                )
            {
                // Recover the type name from the zonked scrutinee so
                // the error message knows which ADT is short.
                let type_name = extract_head_name(&scrut).unwrap_or_default();
                errors_by_decl
                    .entry(owner.clone())
                    .or_default()
                    .push(crate::typecheck_db::passes::exhaustiveness::NonExhaustive {
                        span: p.span,
                        type_name,
                        missing,
                    });
            }
        }
    }

    // Run the Phase B solver over every pending constraint now that
    // inference has settled. The solver reads bindings out of `state`
    // (via zonk), so it must see the final solved unif table. After
    // solving, each constraint is either: resolved (dict attached to
    // its owning decl), no-instance (error attached), or deferred
    // (re-surfaced as a pending constraint — Phase D's improvement
    // loop picks these back up).
    let all_pending: Vec<_> = constraints_by_decl
        .values()
        .flatten()
        .cloned()
        .collect();
    let report = crate::typecheck_db::passes::constraints::solve_all(
        &mut state,
        instances,
        &all_pending,
    );
    let crate::typecheck_db::passes::constraints::SolveReport {
        mut dicts,
        mut dicts_by_span,
        mut errors,
        deferred,
    } = report;
    // Deferred constraints get rewritten back onto their owners so a
    // follow-up pass can revisit them.
    let mut deferred_by_decl: HashMap<
        String,
        Vec<crate::typecheck_db::passes::constraints::PendingConstraint>,
    > = HashMap::new();
    for pc in deferred {
        if let Some(n) = pc.decl_name.clone() {
            deferred_by_decl.entry(n).or_default().push(pc);
        }
    }

    let mut out = Vec::new();
    for (_, name) in &decl_refs {
        let ty = slot_of.get(name).cloned().unwrap();
        let exhaustiveness_errors = errors_by_decl.remove(name).unwrap_or_default();
        let resolved_dicts = dicts.remove(name).unwrap_or_default();
        let constraint_errors = errors.remove(name).unwrap_or_default();
        let pending_constraints = deferred_by_decl.remove(name).unwrap_or_default();
        let constraint_dicts = dicts_by_span.remove(name).unwrap_or_default();
        let hole_diagnostics = holes_by_decl.remove(name).unwrap_or_default();
        // Fold deferred constraints into the scheme using a single
        // shared unif→typevar substitution. Importers see the
        // constraints in the bound scheme and re-instantiate them at
        // each use-site; without this they'd see `forall a. a -> ..`
        // and miss the `Eq a => Semiring a =>` requirements.
        let constraint_args: Vec<crate::typecheck_db::types::Constraint> =
            pending_constraints
                .iter()
                .map(|pc| pc.constraint.clone())
                .collect();
        let scheme = crate::typecheck_db::generalize::generalize_with_constraints(
            &state,
            env,
            &ty,
            &constraint_args,
        );
        out.push(InferredScheme {
            name: name.clone(),
            scheme,
            exhaustiveness_errors,
            pending_constraints,
            resolved_dicts,
            constraint_errors,
            constraint_dicts,
            hole_diagnostics,
        });
    }

    // Restore env — callers may reuse it.
    for (name, v) in slots_backup {
        env.bind_local(name, v);
    }

    Ok(out)
}

/// Compute the `input_hash` for one SCC-inference cache entry.
///
/// Folds in the SCC's source hash, a module-context hash (covering local
/// class / instance / data state the module contributes to inference),
/// and every direct dep's scheme-only `output_hash`.
fn scc_input_hash(
    scc_source_hash: [u8; 32],
    dep_output_hashes: &[(String, String, OutputHash)],
    module_context_hash: [u8; 32],
) -> crate::typecheck_db::key::InputHash {
    let mut hasher = InputHasher::new(PASS_NAME, PASS_VERSION)
        .with_source_hash(scc_source_hash)
        .with_module_context(module_context_hash);
    for (dep_mod, dep_decl, oh) in dep_output_hashes {
        hasher.add_dep(dep_mod.clone(), dep_decl.clone(), PASS_NAME, *oh);
    }
    hasher.finish()
}

/// Look up a cached SCC inference result. On hit, binds each cached
/// scheme into `env` so later SCCs that reference them resolve.
///
/// Returns `Some((schemes, scheme_only_output_hash))` on hit, `None` on
/// miss.
pub fn try_get_cached(
    db: &mut TypecheckDb,
    module: &str,
    scc_key: &str,
    scc_source_hash: [u8; 32],
    dep_output_hashes: &[(String, String, OutputHash)],
    module_context_hash: [u8; 32],
    env: &mut Env,
) -> Result<Option<(Vec<InferredScheme>, OutputHash)>, DriverError> {
    let key = PassKey::new(module, scc_key, PASS_NAME);
    let input_hash =
        scc_input_hash(scc_source_hash, dep_output_hashes, module_context_hash);
    if let Some((schemes, _blob_oh)) = db.get_cached::<Vec<InferredScheme>>(&key, input_hash)? {
        for s in &schemes {
            env.bind_scheme(QName::unqualified(&s.name), s.scheme.clone());
        }
        let scheme_oh = scheme_only_output_hash(&schemes);
        return Ok(Some((schemes, scheme_oh)));
    }
    Ok(None)
}

/// Persist a fresh SCC inference result and record its direct deps.
/// Returns the scheme-only output hash (what downstream SCCs key on).
pub fn put_cached(
    db: &mut TypecheckDb,
    module: &str,
    scc_key: &str,
    scc_source_hash: [u8; 32],
    dep_output_hashes: &[(String, String, OutputHash)],
    module_context_hash: [u8; 32],
    schemes: &[InferredScheme],
) -> Result<OutputHash, DriverError> {
    let key = PassKey::new(module, scc_key, PASS_NAME);
    let input_hash =
        scc_input_hash(scc_source_hash, dep_output_hashes, module_context_hash);

    let schemes_vec: Vec<InferredScheme> = schemes.to_vec();
    db.put(&key, input_hash, &schemes_vec)?;
    let dep_edges: Vec<DepEdge> = dep_output_hashes
        .iter()
        .map(|(m, d, _)| DepEdge {
            dep_module: m.clone(),
            dep_decl: d.clone(),
            dep_pass: PASS_NAME.to_string(),
        })
        .collect();
    db.put_deps(&key, &dep_edges)?;
    Ok(scheme_only_output_hash(schemes))
}

/// Hash the SCC's schemes only, ignoring body-derived diagnostics
/// (exhaustiveness errors, dict resolutions, etc.). Downstream passes
/// key off this hash, so body edits that preserve the inferred schemes
/// don't ripple.
pub fn scheme_only_output_hash(schemes: &[InferredScheme]) -> OutputHash {
    let mut pairs: Vec<(String, Scheme)> = schemes
        .iter()
        .map(|s| (s.name.clone(), s.scheme.clone()))
        .collect();
    pairs.sort_by(|a, b| a.0.cmp(&b.0));
    let bytes = bincode::serialize(&pairs).expect("scheme serialization");
    hash_bytes(&bytes)
}

/// Walk an `App` chain down to its head `Con` and return the
/// constructor's simple name. Used to stamp
/// `NonExhaustive::type_name` from a zonked scrutinee type.
fn extract_head_name(ty: &Type) -> Option<String> {
    let mut cur = ty;
    loop {
        match cur {
            Type::App(f, _) => cur = f,
            Type::Con(q) => return Some(q.name.clone()),
            _ => return None,
        }
    }
}

// ============================================================================
// Expression inference
// ============================================================================

fn infer_var(
    state: &mut UnifyState,
    env: &Env,
    span: crate::span::Span,
    name: &crate::names::Qualified<crate::names::ValueName>,
) -> Result<Type, InferError> {
    let qi = name.to_qi();
    let name_str =
        crate::typecheck_db::util::resolve_symbol(qi.name);
    let module_str = qi.module.map(crate::typecheck_db::util::resolve_symbol);

    if let Some(module) = module_str {
        let q = QName { module: Some(module), name: name_str.clone() };
        return match env.lookup_qualified(&q) {
            Some(scheme) => Ok(instantiate_and_record_constraints(state, scheme, span)),
            None => Err(InferError::UnboundVar(format!("{}", q))),
        };
    }

    match env.lookup_unqualified(&name_str) {
        Lookup::Local(ty) => Ok(ty.clone()),
        Lookup::Scheme(s) => Ok(instantiate_and_record_constraints(state, s, span)),
        Lookup::Missing => Err(InferError::UnboundVar(name_str)),
    }
}

/// Instantiate a scheme fresh, then peel any outer `Type::Constrained`
/// layer and record each constraint on `state` for Phase B's solver.
/// Returns the monotype body.
fn instantiate_and_record_constraints(
    state: &mut UnifyState,
    scheme: &Scheme,
    span: crate::span::Span,
) -> Type {
    use crate::typecheck_db::passes::constraints::{
        peel_constraints, ConstraintOrigin, PendingConstraint,
    };
    let ty = instantiate(state, scheme);
    let (cs, body) = peel_constraints(ty);
    for c in cs {
        state.record_pending_constraint(PendingConstraint {
            decl_name: None, // stamped by `record_pending_constraint`
            span,
            constraint: c,
            origin: ConstraintOrigin::Signature,
            givens: Vec::new(), // filled from stack by record_pending_constraint
        });
    }
    body
}

fn infer_constructor(
    state: &mut UnifyState,
    env: &Env,
    name: &crate::names::Qualified<crate::names::ConstructorName>,
) -> Result<Type, InferError> {
    let qi = name.to_qi();
    let name_str =
        crate::typecheck_db::util::resolve_symbol(qi.name);
    let module_str = qi.module.map(crate::typecheck_db::util::resolve_symbol);

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
    // The parser emits record updates (`r { x = 1 }`) as
    // `App(r, Record { fields: [RecordField{..., is_update: true}] })`,
    // not as `Expr::RecordUpdate`. Recognize that shape here so the
    // record-update inference path gets the same treatment as the
    // direct CST variant.
    if let Expr::Record { fields, .. } = arg {
        if !fields.is_empty() && fields.iter().all(|f| f.is_update) {
            return infer_record_update_from_fields(state, env, type_ops, func, fields);
        }
    }
    let raw_func_ty = infer_expr(state, env, type_ops, func)?;
    // If the function's type zonks to a `Forall` — typically
    // because it was pulled from a `Local` binding whose pattern
    // match extracted a rank-2 constructor field — deep-
    // instantiate fresh at THIS call site so any inner foralls
    // on `Fun.ret` also get fresh unifs.
    let func_ty_zonked = state.zonk(&raw_func_ty);
    let func_ty = if matches!(func_ty_zonked, Type::Forall(_, _)) {
        deep_instantiate_positive(state, func_ty_zonked, true)
    } else {
        raw_func_ty
    };
    // Subsumption on the arg: when the function's expected arg
    // type is a `Forall` (rank-2 arg), we need PJ §5
    // subsumption.
    //
    // Two sub-cases:
    //
    // 1. The arg is a `Lambda` whose first binder is a plain
    //    `Var` — bind that binder DIRECTLY to the polymorphic
    //    arg type so body-level uses of the binder retain the
    //    Forall. This is what `g (\\f -> if f true then f 0
    //    else f 1)` requires when `g :: (forall a. a -> a) ->
    //    Int`: f must be polymorphic in the body.
    //
    // 2. Anything else: route through `check_expr` so
    //    `deep_skolemise_positive` peels the Forall and rejects
    //    rank-2 violations via skolem escape. This is what
    //    catches `test (\\n -> n + 1)` against
    //    `(forall a. a -> a) -> Number`.
    let zonked_func = state.zonk(&func_ty);
    if let Type::Fun(expected_arg, ret) = zonked_func {
        let expected_arg_zonked = state.zonk(&expected_arg);
        // Lambda + Forall-anywhere expected_arg: route through
        // check_expr so check_lambda peels arrows and binds
        // each binder to its expected type — preserving any
        // inner `Forall`s as polymorphic binder types. Without
        // this `g (\\f -> if f true then f 0 else f 1)` against
        // `((forall a. a -> a) -> Int) -> Int` infers f as a
        // monomorphic unif and the second use at a different
        // type is rejected.
        if matches!(arg, Expr::Lambda { .. })
            && type_contains_forall(&expected_arg_zonked)
        {
            check_expr(state, env, type_ops, arg, &expected_arg_zonked)?;
            return Ok(*ret);
        }
        if matches!(&expected_arg_zonked, Type::Forall(_, _)) {
            check_expr(state, env, type_ops, arg, &expected_arg_zonked)?;
            return Ok(*ret);
        }
        // Constrained-in-arg-position: a ctor field like
        // `data X a = X (Y a => Proxy a)` produces a func type
        // `Fun(Constrained([Y ?u], Proxy ?u), X ?u)`. Push the
        // constraints as givens for the duration of the arg's
        // inference so any sub-expression that needs `Y ?u`
        // discharges from the given. The givens are popped on
        // exit; constraints that couldn't be discharged stay
        // pending and bubble up into the surrounding scheme,
        // which is how `test1 = X (Proxy :: _ Int)` typechecks
        // even without an `instance Y Int` in scope.
        if let Type::Constrained(cs, body) = &expected_arg_zonked {
            let snapshot = state.push_givens(cs.clone());
            let arg_ty_res = infer_expr(state, env, type_ops, arg);
            state.pop_givens_to(snapshot);
            let arg_ty = arg_ty_res?;
            state.unify(body, &arg_ty)?;
            return Ok(*ret);
        }
    }
    let arg_ty = infer_expr(state, env, type_ops, arg)?;
    let result = state.fresh();
    state.unify(&func_ty, &Type::fun(arg_ty, result.clone()))?;
    Ok(result)
}

/// Shared helper: given an "expression being updated" and a list of
/// `RecordField`s representing the updates, unify against an open record
/// and return the updated record's type. Used both from `infer_app`
/// (where the parser emits `App(expr, Record{is_update})`) and from
/// `infer_record_update` (where a later desugar pass emits the
/// dedicated `Expr::RecordUpdate` form).
fn infer_record_update_from_fields(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    expr: &Expr,
    fields: &[ir::RecordField],
) -> Result<Type, InferError> {
    let expr_ty = infer_expr(state, env, type_ops, expr)?;
    let mut update_fields: Vec<(String, Type)> = Vec::with_capacity(fields.len());
    for f in fields {
        let label = crate::typecheck_db::util::resolve_symbol(f.label.value.symbol());
        // A record update field always has a `value` (it's `x = expr`,
        // not a pun).
        let val = f.value.as_ref().expect("parser: update field must carry a value");
        let new_val_ty = infer_expr(state, env, type_ops, val)?;
        update_fields.push((label, new_val_ty));
    }
    let tail = state.fresh();
    let expected = Type::Record(update_fields, Some(Box::new(tail)));
    state.unify(&expr_ty, &expected)?;
    Ok(expr_ty)
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
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            env.bind_local(n, v.clone());
            Ok(v)
        }
        Binder::Typed { binder, ty, .. } => {
            let mut declared = crate::typecheck_db::types::expand_aliases(
                convert_type_expr(ty, type_ops),
                &env.aliases,
            );
            // Scoped type variables: if the outer decl's
            // signature put `a → skolem_0` into `env.scoped_tys`
            // via check-mode, replace any `Var("a")` in this
            // annotation with the skolem so `\(x :: a) -> x` at a
            // rank-1 sig site correctly matches the skolemised
            // param type.
            if !env.scoped_tys.is_empty() {
                declared = crate::typecheck_db::generalize::apply_var_subst(
                    &declared,
                    &env.scoped_tys,
                );
            }
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
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            env.bind_local(n, inner.clone());
            Ok(inner)
        }
        Binder::Record { fields, .. } => bind_record_pattern(state, env, type_ops, fields),
        Binder::Array { elements, .. } => bind_array_pattern(state, env, type_ops, elements),
        // `Binder::Op` doesn't exist in `ir::Binder` — the lowering
        // pass rebrackets operator patterns to `Binder::Constructor`
        // before they reach inference.
    }
}

/// Match `{ l1, l2: sub2, ... }` against an open record type. Pun
/// fields (`{ l }`) bind `l` to a fresh unification var; explicit
/// fields (`{ l: sub }`) recurse into the sub-binder.
fn bind_record_pattern(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    fields: &[ir::RecordBinderField],
) -> Result<Type, InferError> {
    let mut field_tys: Vec<(String, Type)> = Vec::with_capacity(fields.len());
    for f in fields {
        let label = crate::typecheck_db::util::resolve_symbol(f.label.value.symbol());
        let ty = match &f.binder {
            Some(b) => bind_pattern(state, env, type_ops, b)?,
            None => {
                // Pun: `{ x }` binds `x` with a fresh type.
                let ty = state.fresh();
                env.bind_local(label.clone(), ty.clone());
                ty
            }
        };
        field_tys.push((label, ty));
    }
    let tail = state.fresh();
    Ok(Type::Record(field_tys, Some(Box::new(tail))))
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
    let name_str = crate::typecheck_db::util::resolve_symbol(qi.name);
    let module_str = qi.module.map(crate::typecheck_db::util::resolve_symbol);
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

// ============================================================================
// M4d: records
// ============================================================================

fn infer_record(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    fields: &[ir::RecordField],
) -> Result<Type, InferError> {
    // A bare `Expr::Record` with `is_update` fields is the nested
    // record-update position: in `init { bar { baz = 1 } }`, the
    // inner `{ baz = 1 }` arrives here with is_update=true on `baz`.
    // We treat these fields as value fields — the field's contribution
    // to the row is the inferred value type. The surrounding
    // `infer_record_update` already models the "must contain at least
    // these labels" shape via an open record, so structural soundness
    // is preserved at the outer level.
    let is_update_section = fields.iter().any(|f| f.is_update);
    let mut inferred: Vec<(String, Type)> = Vec::with_capacity(fields.len());
    for f in fields {
        let label = crate::typecheck_db::util::resolve_symbol(f.label.value.symbol());
        let field_ty = match &f.value {
            Some(e) => infer_expr(state, env, type_ops, e)?,
            None => {
                // Pun: `{ x }` ≡ `{ x: x }`. Look up `x` in the env.
                match env.lookup_unqualified(&label) {
                    Lookup::Local(ty) => ty.clone(),
                    Lookup::Scheme(s) => instantiate(state, s),
                    Lookup::Missing => return Err(InferError::UnboundVar(label.clone())),
                }
            }
        };
        inferred.push((label, field_ty));
    }
    // Update sections produce an OPEN row so nested updates
    // (`init { bar { baz = 1 } }`) can unify with whatever extra
    // fields the surrounding record already has.
    let tail = if is_update_section {
        Some(Box::new(state.fresh()))
    } else {
        None
    };
    Ok(Type::Record(inferred, tail))
}

fn infer_record_access(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    expr: &Expr,
    field: &crate::cst::Spanned<crate::names::LabelName>,
) -> Result<Type, InferError> {
    let expr_ty = infer_expr(state, env, type_ops, expr)?;
    let label = crate::typecheck_db::util::resolve_symbol(field.value.symbol());
    let field_ty = state.fresh();
    let tail = state.fresh();
    let expected = Type::Record(
        vec![(label, field_ty.clone())],
        Some(Box::new(tail)),
    );
    state.unify(&expr_ty, &expected)?;
    // If the field's declared type is polymorphic (a nested
    // `Forall` — e.g. `{ return :: forall a. a -> m a }`), each
    // access site should see a fresh instantiation, not the
    // `Forall` itself, so repeated uses (`m.return 1`, then
    // `m.return "x"`) don't accidentally unify their result
    // types. Zonk the slot and deep-instantiate any surfaced
    // Forall so inner foralls in `Fun.ret` are also fresh.
    let zonked = state.zonk(&field_ty);
    if matches!(&zonked, Type::Forall(_, _)) {
        return Ok(deep_instantiate_positive(state, zonked, true));
    }
    Ok(field_ty)
}

fn infer_record_update(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    expr: &Expr,
    updates: &[ir::RecordUpdate],
) -> Result<Type, InferError> {
    let expr_ty = infer_expr(state, env, type_ops, expr)?;
    // Infer the new value's type for each update field; the updated
    // record must contain at least those labels with those types.
    let mut update_fields: Vec<(String, Type)> = Vec::with_capacity(updates.len());
    for u in updates {
        let label = crate::typecheck_db::util::resolve_symbol(u.label.value.symbol());
        let new_val_ty = infer_expr(state, env, type_ops, &u.value)?;
        update_fields.push((label, new_val_ty));
    }
    let tail = state.fresh();
    let expected = Type::Record(update_fields, Some(Box::new(tail)));
    state.unify(&expr_ty, &expected)?;
    // Record update preserves the record's shape.
    Ok(expr_ty)
}

// ============================================================================
// M4e: arrays
// ============================================================================

/// Build `Array α` for the current element type.
fn array_of(elem: Type) -> Type {
    Type::app(Type::Con(QName::unqualified("Array")), elem)
}

fn infer_array(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    elements: &[Expr],
) -> Result<Type, InferError> {
    // A single fresh element type links every item in the literal.
    // Empty arrays leave the element type polymorphic; generalization
    // picks it up later.
    let elem = state.fresh();
    for e in elements {
        let t = infer_expr(state, env, type_ops, e)?;
        state.unify(&t, &elem)?;
    }
    Ok(array_of(elem))
}

fn bind_array_pattern(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    elements: &[Binder],
) -> Result<Type, InferError> {
    // Length isn't constrained by the type — an `[a, b]` pattern
    // matches any `Array α`; exhaustiveness over arrays is a later
    // milestone. Element types are pairwise unified through one fresh
    // `α`, same as a literal.
    let elem = state.fresh();
    for b in elements {
        let t = bind_pattern(state, env, type_ops, b)?;
        state.unify(&t, &elem)?;
    }
    Ok(array_of(elem))
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

    // Pass 1: collect signatures keyed by name. Aliases are
    // expanded here so downstream `check_expr` calls unify
    // against the canonical form (see `Env::aliases`).
    let mut sigs: HashMap<String, Type> = HashMap::new();
    for b in bindings {
        if let LetBinding::Signature { name, ty, .. } = b {
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            let mut converted = convert_type_expr(ty, type_ops);
            // Scoped type variables: replace any `Var("r")` here
            // that matches an outer-decl skolem (via check_equation
            // seeding `env.scoped_tys`). Without this a where-clause
            // sig that mentions the outer sig's forall vars would
            // carry a rigid `Var` that can't unify with the outer
            // sig's skolem — breaking patterns like
            // `reifySymbol :: forall r. ... -> r` using a helper
            // `coerce :: ... -> r` in its `where`.
            if !env.scoped_tys.is_empty() {
                converted = crate::typecheck_db::generalize::apply_var_subst(
                    &converted,
                    &env.scoped_tys,
                );
            }
            sigs.insert(n, crate::typecheck_db::types::expand_aliases(converted, &env.aliases));
        }
    }

    // Pass 2: materialize value bindings.
    //
    // * `LetBinding::Value` with a bare `Binder::Var` is the
    //   standard case: pre-insert a slot so mutual recursion
    //   resolves, then (Pass 3) infer the body.
    // * `LetBinding::Value` with a *pattern* binder (e.g.
    //   `let X a = e`, `let {x, y} = r`) deconstructs the RHS
    //   into its sub-binders. We infer the RHS, bind the
    //   pattern against it, and skip slot/generalize logic —
    //   pattern bindings aren't let-polymorphic (each binder
    //   gets a monomorphic type).
    let mut value_bindings: Vec<LetValueBinding<'_>> = Vec::new();
    let mut pattern_bindings: Vec<(&Binder, &Expr)> = Vec::new();
    for b in bindings {
        match b {
            LetBinding::Value { binder: Binder::Var { name, .. }, expr, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let sig = sigs.get(&n).cloned();
                if let Some(sig_ty) = sig.clone() {
                    let scheme = sig_to_scheme(sig_ty.clone());
                    env.bind_local_scheme(n.clone(), scheme);
                } else {
                    let slot = state.fresh();
                    env.bind_local(n.clone(), slot);
                }
                value_bindings.push(LetValueBinding { name: n, sig, expr });
            }
            LetBinding::Value { binder, expr, .. } => {
                pattern_bindings.push((binder, expr));
            }
            LetBinding::Signature { .. } => {}
        }
    }

    // Pass 3: infer each body. For signed bindings, check against
    // a freshly-instantiated monotype of the sig (so constraints
    // surface as pending and match the body's types correctly).
    // For unsigned bindings, infer + unify with the pre-inserted
    // monomorphic slot as before.
    for vb in &value_bindings {
        if let Some(sig_ty) = vb.sig.clone() {
            let monotype = instantiate_sig_as_monotype(state, sig_ty);
            check_expr(state, env, type_ops, vb.expr, &monotype)?;
        } else {
            let slot_ty = env
                .lookup_unqualified(&vb.name)
                .local_ty()
                .expect("slot pre-inserted above")
                .clone();
            let actual = infer_expr(state, env, type_ops, vb.expr)?;
            state.unify(&slot_ty, &actual)?;
        }
    }

    // Pass 3b: pattern bindings. Infer the RHS, bind the pattern
    // against it. Each name introduced by the pattern becomes a
    // local monotype — pattern bindings don't participate in
    // let-polymorphism the way bare-name bindings do.
    for (binder, expr) in &pattern_bindings {
        let rhs_ty = infer_expr(state, env, type_ops, expr)?;
        let pat_ty = bind_pattern(state, env, type_ops, binder)?;
        state.unify(&pat_ty, &rhs_ty)?;
    }

    // Pass 4: replace each monomorphic slot with a generalized scheme so the
    // body benefits from let-polymorphism. We remove the slot from `locals`
    // *before* generalizing so its own unif var isn't considered free in the
    // surrounding env.
    //
    // Duplicate names in `value_bindings` (multi-equation let, e.g.
    // `let f Nothing = 0; f (Just x) = x in …`) map to a single slot —
    // the second `bind_local` in Pass 2 overwrote the first and only one
    // entry remains to remove. We dedupe by name here so the second
    // pass-4 iteration doesn't trip on an already-empty slot.
    let mut finished: Vec<(String, Scheme)> = Vec::new();
    let mut generalized: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for vb in &value_bindings {
        if !generalized.insert(vb.name.clone()) {
            continue;
        }
        // Signed bindings already have their scheme in
        // `local_schemes` from Pass 2; skip generalization for
        // them. Unsigned bindings need their fresh unif-slot
        // plucked out and generalized.
        if vb.sig.is_some() {
            continue;
        }
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

/// Do-notation. Desugars semantically to `bind` / `discard` chaining
/// without going through an actual desugar — we just unify each
/// `<-` statement's RHS against `m a`, pull out the `a`, bind it,
/// and require the last statement to be an expression whose type
/// is `m r` for some result `r`.
fn infer_do(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    statements: &[ir::DoStatement],
) -> Result<Type, InferError> {
    if statements.is_empty() {
        return Err(InferError::EmptyDoBlock);
    }
    env.push_scope();

    // A single monad constructor threads through the entire block.
    let m = state.fresh();
    let last_idx = statements.len() - 1;

    let mut result_ty: Option<Type> = None;
    for (i, stmt) in statements.iter().enumerate() {
        let is_last = i == last_idx;
        match stmt {
            ir::DoStatement::Bind { binder, expr, .. } => {
                if is_last {
                    env.pop_scope();
                    return Err(InferError::InvalidDoBind);
                }
                let expr_ty = infer_expr(state, env, type_ops, expr)?;
                let a = state.fresh();
                let expected = Type::App(Box::new(m.clone()), Box::new(a.clone()));
                state.unify(&expr_ty, &expected)?;
                let pat_ty = bind_pattern(state, env, type_ops, binder)?;
                state.unify(&pat_ty, &a)?;
            }
            ir::DoStatement::Let { bindings, .. } => {
                if is_last {
                    env.pop_scope();
                    return Err(InferError::InvalidDoLet);
                }
                process_do_let_bindings(state, env, type_ops, bindings)?;
            }
            ir::DoStatement::Discard { expr, .. } => {
                let expr_ty = infer_expr(state, env, type_ops, expr)?;
                if is_last {
                    // Last statement is the block's result. Its type
                    // must be `m r` for some r — force-unify to pin the
                    // shape and feed the surrounding context.
                    let r = state.fresh();
                    let expected = Type::App(Box::new(m.clone()), Box::new(r.clone()));
                    state.unify(&expr_ty, &expected)?;
                    result_ty = Some(expr_ty);
                } else {
                    let any = state.fresh();
                    let expected = Type::App(Box::new(m.clone()), Box::new(any));
                    state.unify(&expr_ty, &expected)?;
                }
            }
        }
    }

    env.pop_scope();
    result_ty.ok_or(InferError::EmptyDoBlock)
}

/// Ado-notation. Applicative variant of do: each `<-` statement's RHS
/// has type `m a`, bindings introduced by `<-` are applicative-
/// independent (can't see each other), and the `in <expr>` at the
/// end runs in an environment that DOES see the binds.
fn infer_ado(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    statements: &[ir::DoStatement],
    result: &Expr,
) -> Result<Type, InferError> {
    // Two envs: `expr_env` is what each `<-` expression sees; it only
    // accumulates `let` bindings. `result_env` sees everything (binds
    // + lets) and is what the final `in <expr>` runs under. This
    // matches PureScript semantics for applicative scoping.
    let m = state.fresh();

    // Clone env so we have a "frozen at entry" version for expressions.
    env.push_scope();
    let mut expr_env = env.clone();

    for stmt in statements {
        match stmt {
            ir::DoStatement::Bind { binder, expr, .. } => {
                let expr_ty = infer_expr(state, &mut expr_env, type_ops, expr)?;
                let a = state.fresh();
                let expected = Type::App(Box::new(m.clone()), Box::new(a.clone()));
                state.unify(&expr_ty, &expected)?;
                let pat_ty = bind_pattern(state, env, type_ops, binder)?;
                state.unify(&pat_ty, &a)?;
            }
            ir::DoStatement::Let { bindings, .. } => {
                process_do_let_bindings(state, env, type_ops, bindings)?;
                // Let bindings ARE visible to subsequent <- expressions,
                // so also replay them into expr_env.
                process_do_let_bindings(state, &mut expr_env, type_ops, bindings)?;
            }
            ir::DoStatement::Discard { expr, .. } => {
                // In ado, bare expressions have the shape `m _` but
                // don't contribute to the result; they behave like
                // `_ <- expr`.
                let expr_ty = infer_expr(state, &mut expr_env, type_ops, expr)?;
                let a = state.fresh();
                let expected = Type::App(Box::new(m.clone()), Box::new(a));
                state.unify(&expr_ty, &expected)?;
            }
        }
    }

    let result_a = infer_expr(state, env, type_ops, result)?;
    env.pop_scope();
    // ado yields `m <result>`.
    Ok(Type::App(Box::new(m), Box::new(result_a)))
}

/// Shared helper: add `LetBinding`s from a do/ado `let` statement into
/// `env`. Monomorphic — no generalization. Signatures are honored for
/// the bound scheme via `sig_to_scheme`, matching `infer_let`'s signed-
/// binding path (which also doesn't re-generalize signatures).
fn process_do_let_bindings(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    bindings: &[LetBinding],
) -> Result<(), InferError> {
    let mut sigs: HashMap<String, Type> = HashMap::new();
    for b in bindings {
        if let LetBinding::Signature { name, ty, .. } = b {
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            let converted = convert_type_expr(ty, type_ops);
            sigs.insert(
                n,
                crate::typecheck_db::types::expand_aliases(converted, &env.aliases),
            );
        }
    }
    for b in bindings {
        match b {
            LetBinding::Value { binder: Binder::Var { name, .. }, expr, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                if let Some(sig_ty) = sigs.get(&n).cloned() {
                    let scheme = sig_to_scheme(sig_ty.clone());
                    env.bind_local_scheme(n.clone(), scheme);
                    let monotype = instantiate_sig_as_monotype(state, sig_ty);
                    check_expr(state, env, type_ops, expr, &monotype)?;
                } else {
                    let slot = state.fresh();
                    env.bind_local(n.clone(), slot.clone());
                    let actual = infer_expr(state, env, type_ops, expr)?;
                    state.unify(&slot, &actual)?;
                }
            }
            LetBinding::Value { binder, expr, .. } => {
                let rhs = infer_expr(state, env, type_ops, expr)?;
                let pat_ty = bind_pattern(state, env, type_ops, binder)?;
                state.unify(&pat_ty, &rhs)?;
            }
            LetBinding::Signature { .. } => {}
        }
    }
    Ok(())
}

fn infer_case(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    span: crate::span::Span,
    scrutinees: &[Expr],
    alts: &[ir::CaseAlternative],
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

    // Record the case for post-inference exhaustiveness analysis. The
    // scrutinee types stored here may still be unification variables;
    // the caller zonks before running the check.
    state.record_pending_exhaust(PendingExhaust {
        decl_name: None, // stamped by `record_pending_exhaust`
        span,
        scrutinee_tys: scrut_tys.clone(),
        alts: alts
            .iter()
            .map(|a| PendingAlt {
                binders: a.binders.clone(),
                guarded: a.result.clone(),
            })
            .collect(),
    });

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
    guarded: &ir::GuardedExpr,
) -> Result<Type, InferError> {
    match guarded {
        ir::GuardedExpr::Unconditional(e) => infer_expr(state, env, type_ops, e),
        ir::GuardedExpr::Guarded(guards) => {
            if guards.is_empty() {
                return Err(InferError::Unsupported("empty guarded body"));
            }
            let result_ty = state.fresh();
            for g in guards {
                env.push_scope();
                for p in &g.patterns {
                    match p {
                        ir::GuardPattern::Boolean(e) => {
                            check_expr(
                                state,
                                env,
                                type_ops,
                                e,
                                &Type::Con(QName::unqualified("Boolean")),
                            )?;
                        }
                        ir::GuardPattern::Pattern(binder, expr) => {
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
    guarded: &ir::GuardedExpr,
) -> Result<Type, InferError> {
    infer_equation_with_hints(state, env, type_ops, binders, guarded, None)
}

/// Like `infer_equation` but also unifies each binder's slot
/// against an optional signature-hinted type. The hints come
/// from `sig_param_types`, which instantiates the decl's
/// signature once per SCC and splits out the arrow arguments.
/// Threading the signature in here is what lets a parameter
/// like `m :: { return :: forall a. a -> m a }` carry its
/// polymorphic field types into the body.
fn infer_equation_with_hints(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    binders: &[Binder],
    guarded: &ir::GuardedExpr,
    hints: Option<&[Type]>,
) -> Result<Type, InferError> {
    if binders.is_empty() {
        return infer_guarded(state, env, type_ops, guarded);
    }

    env.push_scope();
    let mut param_tys = Vec::with_capacity(binders.len());
    for (i, b) in binders.iter().enumerate() {
        let ty = bind_pattern(state, env, type_ops, b)?;
        if let Some(h) = hints.and_then(|hs| hs.get(i)) {
            state.unify(&ty, h)?;
        }
        param_tys.push(ty);
    }
    let body_ty = infer_guarded(state, env, type_ops, guarded)?;
    env.pop_scope();

    // A single-equation decl with refutable top-level binders (like
    // `f (Just y) = y`) doesn't go through `infer_case`, so we
    // synthesize a pending exhaustiveness record here as if it were a
    // one-alternative case. Multi-equation decls with the same name
    // have already been collapsed into a `case` by MDd's multi_eq
    // merger and flow through `infer_case` instead.
    if binders
        .iter()
        .any(crate::typecheck_db::passes::exhaustiveness::is_refutable)
    {
        state.record_pending_exhaust(PendingExhaust {
            decl_name: None, // stamped by `record_pending_exhaust`
            span: binders
                .first()
                .map(|b| b.span())
                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            scrutinee_tys: param_tys.clone(),
            alts: vec![PendingAlt {
                binders: binders.to_vec(),
                guarded: guarded.clone(),
            }],
        });
    }

    let mut out = body_ty;
    for pt in param_tys.into_iter().rev() {
        out = Type::fun(pt, out);
    }
    Ok(out)
}

/// Lower a value decl's `where` clause into a synthetic `let`
/// wrapping each guard's body. Mirrors multi_eq's helper so a
/// `foo … | g = e where h = …` program behaves the same through
/// both paths (merged via multi_eq or direct).
fn wrap_guarded_with_where(
    g: ir::GuardedExpr,
    where_clause: Vec<LetBinding>,
) -> ir::GuardedExpr {
    if where_clause.is_empty() {
        return g;
    }
    match g {
        ir::GuardedExpr::Unconditional(e) => {
            let span = e.span();
            ir::GuardedExpr::Unconditional(Box::new(Expr::Let {
                span,
                bindings: where_clause,
                body: e,
            }))
        }
        ir::GuardedExpr::Guarded(guards) => ir::GuardedExpr::Guarded(
            guards
                .into_iter()
                .map(|grd| ir::Guard {
                    span: grd.span,
                    patterns: grd.patterns,
                    expr: Box::new(Expr::Let {
                        span: grd.expr.span(),
                        bindings: where_clause.clone(),
                        body: grd.expr,
                    }),
                })
                .collect(),
        ),
    }
}

/// Convert a user-written signature type (as `Type`, coming from
/// `convert_type_expr`) into a `Scheme`. Peels any outer
/// `Type::Forall` into the scheme's `vars`; the body keeps any
/// `Type::Constrained` layer so `infer_var`'s
/// `instantiate_and_record_constraints` can peel it at each use
/// site.
fn sig_to_scheme(sig_ty: Type) -> Scheme {
    match sig_ty {
        Type::Forall(qs, body) => {
            let vars = qs.into_iter().map(|(n, _, _)| n).collect();
            Scheme { vars, ty: *body }
        }
        other => Scheme { vars: Vec::new(), ty: other },
    }
}

/// Instantiate a let-binding signature into a fresh monotype
/// suitable for `check_expr`. Any top-level `Forall` introduces
/// fresh unif vars; any `Constrained` layer is peeled and each
/// constraint is recorded as a pending constraint on the
/// surrounding SCC state — mirrors what
/// `instantiate_and_record_constraints` does at reference sites
/// so the body's constraints and the signature's constraints
/// share the same unif identities.
/// Instantiate a scheme with fresh unif vars for its forall-bound vars,
/// stripping any `Constrained` or nested `Forall` wrappers. Does NOT
/// record pending constraints — safe to call for diagnostic annotation
/// without affecting inference.
fn instantiate_scheme_no_constraints(
    state: &mut UnifyState,
    scheme: &crate::typecheck_db::types::Scheme,
) -> Type {
    use crate::typecheck_db::generalize::apply_var_subst;
    let fresh: Vec<Type> = scheme.vars.iter().map(|_| state.fresh()).collect();
    let subst: std::collections::HashMap<String, Type> = scheme
        .vars
        .iter()
        .cloned()
        .zip(fresh.into_iter())
        .collect();
    let mut ty = apply_var_subst(&scheme.ty, &subst);
    loop {
        match ty {
            Type::Constrained(_, body) => ty = *body,
            Type::Forall(_, body) => ty = *body,
            other => break other,
        }
    }
}

fn instantiate_sig_as_monotype(state: &mut UnifyState, sig_ty: Type) -> Type {
    use crate::typecheck_db::generalize::instantiate;
    use crate::typecheck_db::passes::constraints::{
        peel_constraints, ConstraintOrigin, PendingConstraint,
    };
    let scheme = sig_to_scheme(sig_ty);
    let instantiated = instantiate(state, &scheme);
    let (cs, body) = peel_constraints(instantiated);
    for c in cs {
        state.record_pending_constraint(PendingConstraint {
            decl_name: None,
            span: crate::span::Span { start: 0, end: 0 },
            constraint: c,
            origin: ConstraintOrigin::Signature,
            givens: Vec::new(),
        });
    }
    body
}

/// Deep-instantiate positive positions: replace outer `Forall` with
/// fresh unif vars and recurse under every `Fun.ret` and
/// `Constrained.body`. Negative positions (`Fun.arg`) keep their
/// foralls intact so a sig like
/// `forall x. Array x -> (forall a. Array a) -> Array x`
/// round-trips against the same shape on the caller side.
/// See Peyton-Jones et al. §5.
///
/// `record_constraints=true` registers `Constrained` layers as
/// pending constraints on `state` (matches
/// `instantiate_sig_as_monotype`'s existing behaviour); `false`
/// drops them (safe for diagnostic-only uses).
fn deep_instantiate_positive(
    state: &mut UnifyState,
    ty: Type,
    record_constraints: bool,
) -> Type {
    use crate::typecheck_db::generalize::apply_var_subst;
    use crate::typecheck_db::passes::constraints::{
        ConstraintOrigin, PendingConstraint,
    };
    let mut cur = ty;
    loop {
        cur = match cur {
            Type::Forall(vs, body) => {
                let mut subst: HashMap<String, Type> = HashMap::new();
                for (n, _, _) in &vs {
                    subst.insert(n.clone(), state.fresh());
                }
                apply_var_subst(&body, &subst)
            }
            Type::Constrained(cs, body) => {
                if record_constraints {
                    for c in cs {
                        state.record_pending_constraint(PendingConstraint {
                            decl_name: None,
                            span: crate::span::Span { start: 0, end: 0 },
                            constraint: c,
                            origin: ConstraintOrigin::Signature,
                            givens: Vec::new(),
                        });
                    }
                }
                *body
            }
            Type::Fun(arg, ret) => {
                let ret_inst = deep_instantiate_positive(
                    state,
                    *ret,
                    record_constraints,
                );
                return Type::fun(*arg, ret_inst);
            }
            other => return other,
        };
    }
}

/// Deep-skolemise positive positions: replace outer `Forall` with
/// fresh skolems, recurse under every `Fun.ret` and peel
/// `Constrained` layers. Returns the skolemised type plus the
/// flattened list of constraint-givens peeled along the way — A2
/// will push those onto the solver's given stack; A1 callers just
/// discard them (same as the pre-existing surface-only `Constrained`
/// peeling in `check_expr`).
fn deep_skolemise_positive(
    state: &mut UnifyState,
    ty: Type,
) -> (Type, Vec<Constraint>) {
    use crate::typecheck_db::generalize::apply_var_subst;
    let mut cur = ty;
    let mut givens: Vec<Constraint> = Vec::new();
    loop {
        cur = match cur {
            Type::Forall(vs, body) => {
                let mut subst: HashMap<String, Type> = HashMap::new();
                for (n, _, _) in &vs {
                    subst.insert(n.clone(), Type::Skolem(state.fresh_named_skolem(n)));
                }
                apply_var_subst(&body, &subst)
            }
            Type::Constrained(cs, body) => {
                givens.extend(cs);
                *body
            }
            Type::Fun(arg, ret) => {
                let (ret_s, ret_g) = deep_skolemise_positive(state, *ret);
                givens.extend(ret_g);
                return (Type::fun(*arg, ret_s), givens);
            }
            other => return (other, givens),
        };
    }
}

/// If `name` has a declared signature in the env, instantiate it
/// as a monotype (recording constraints) and return the first
/// `arity` argument types of the resulting arrow chain. Used to
/// pre-seed parameter types during equation inference, so
/// polymorphic fields in the sig (`{ return :: forall a. a -> m a }`)
/// actually reach the body instead of being lost to a bare unif
/// on the parameter.
///
/// Returns `None` when the decl has no sig, when it isn't a
/// function type, or when the arrow has fewer segments than the
/// body's binder count (the caller falls back to fresh unifs).
fn sig_param_types(
    env: &Env,
    name: &str,
    state: &mut UnifyState,
    arity: usize,
) -> Option<Vec<Type>> {
    if arity == 0 {
        return None;
    }
    // The SCC's pre-bind has already shadowed `name` with a
    // fresh unif in `env.locals`, so `lookup_unqualified` would
    // hit that first. Reach into `top_level` directly to find
    // the declared signature (placed there by
    // `bind_local_ctors` for every `Decl::TypeSignature`).
    let scheme = env
        .top_level
        .get(&QName { module: None, name: name.to_string() })
        .cloned()?;
    let mono = instantiate_sig_as_monotype(state, Type::Forall(
        scheme
            .vars
            .iter()
            .cloned()
            .map(|n| (n, false, None))
            .collect(),
        Box::new(scheme.ty),
    ));
    let mut args: Vec<Type> = Vec::new();
    let mut cur = mono;
    for _ in 0..arity {
        match cur {
            Type::Fun(a, b) => {
                args.push(*a);
                cur = *b;
            }
            _ => return None,
        }
    }
    Some(args)
}

/// Does the env's scheme for `name` carry a `Partial` constraint?
/// A decl whose signature declares `Partial =>` is allowed to be
/// non-exhaustive — the signature is the user's way of saying
/// "I promise uncovered cases can't happen at runtime."
fn has_partial_constraint(env: &Env, name: &str) -> bool {
    let scheme = match env.lookup_unqualified(name) {
        Lookup::Scheme(s) => s,
        _ => return false,
    };
    fn walk(ty: &Type) -> bool {
        match ty {
            Type::Constrained(cs, body) => {
                cs.iter().any(|c| c.class.name == "Partial") || walk(body)
            }
            Type::Forall(_, body) => walk(body),
            _ => false,
        }
    }
    walk(&scheme.ty)
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
    use crate::parser::parse as parse_cst;

    /// Parse + desugar + lower — every test in this module works in
    /// `ir::*` land since that's what the infer pipeline consumes.
    /// Desugar is mandatory: the IR lowering rejects any surviving
    /// `Op` / `OpParens` / `BacktickApp` / `Binder::Op` as
    /// `LoweringError::Residual*`, so test sources that use
    /// operators need the full pipeline.
    fn parse(src: &str) -> crate::typecheck_db::ir::Module {
        use crate::typecheck_db::desugar::{
            desugar_module, fixity_table_from_decls, DesugarContext,
        };
        let cst_mod = parse_cst(src).unwrap();
        let (fixity_table, module_fixity_hash) = fixity_table_from_decls(&cst_mod.decls);
        let ctx = DesugarContext { module_fixity_hash, fixity_table };
        let decls = desugar_module(cst_mod.decls.clone(), &ctx);
        let desugared = crate::cst::Module { decls, ..cst_mod };
        crate::typecheck_db::ir::lower_module(desugared).expect("cst → ir lowering")
    }

    fn int() -> Type {
        Type::Con(QName::unqualified("Int"))
    }

    fn bool_ty() -> Type {
        Type::Con(QName::unqualified("Boolean"))
    }

    fn parse_expr_from_val(src: &str) -> Expr {
        let m = parse(src);
        for d in m.decls {
            if let Decl::Value { guarded, .. } = d {
                if let ir::GuardedExpr::Unconditional(e) = guarded {
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
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(schemes.len(), 1);
        assert_eq!(scheme_display(&schemes[0].scheme), "forall a. a -> a");
    }

    #[test]
    fn const_lambda_generalizes_to_two_vars() {
        let src = "module M where\nkonst x y = x\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(schemes.len(), 1);
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "forall a b. a -> b -> a",
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
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Int -> Int");
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
        let m = parse(src);
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
        let m = parse(src);
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
        let m = parse(src);
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
        let m = parse(src);
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
        let m = parse(src);
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
        let m = parse(src);
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
        let m = parse(src);
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
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Int -> String");
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
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        seed_maybe(&mut env);
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Maybe Int -> Int");
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
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        seed_maybe(&mut env);
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "Maybe (Maybe Int) -> Int",
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
        let m = parse(src);
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
        let m = parse(src);
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
        let m = parse(src);
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
            "forall a. Maybe Int -> Maybe a -> Int",
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
        let m = parse(src);
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
        assert!(disp.ends_with("Int"), "got: {disp}");
    }

    #[test]
    fn guard_cond_must_be_boolean() {
        let src = "\
module M where
foo x | x = 1
";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        // Bind x's inferred type loosely; expect the guard to force it to
        // Boolean. That in itself is fine; the failure here comes if we seed
        // x :: Int.
        // Instead, test by requiring the scheme to end with "Boolean -> Int".
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Boolean -> Int");
    }

    // ------------------------------------------------------------------
    // M4d: records
    // ------------------------------------------------------------------

    fn string_ty() -> Type {
        Type::Con(QName::unqualified("String"))
    }

    #[test]
    fn record_literal_infers_closed_record() {
        let src = "module M where\nr = { x: 1, y: \"hi\" }\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        if let Type::Record(fields, tail) = &schemes[0].scheme.ty {
            assert!(tail.is_none(), "literal record should be closed");
            let labels: Vec<_> = fields.iter().map(|(l, _)| l.as_str()).collect();
            assert!(labels.contains(&"x"));
            assert!(labels.contains(&"y"));
        } else {
            panic!("expected Record, got {:?}", schemes[0].scheme.ty);
        }
    }

    #[test]
    fn record_pun_looks_up_outer_binding() {
        // `r = { x }` resolves `x` from the surrounding env.
        let src = "module M where\nx = 1\nr = { x }\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        let r = schemes.iter().find(|s| s.name == "r").unwrap();
        assert_eq!(scheme_display(&r.scheme), "{ x :: Int }");
    }

    #[test]
    fn record_pun_unbound_is_error() {
        let src = "module M where\nr = { y }\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let err = infer_value_scc(&ops, &mut env, &decls).unwrap_err();
        assert!(matches!(&err, InferError::UnboundVar(n) if n == "y"), "got: {err:?}");
    }

    #[test]
    fn record_access_constrains_record_via_open_row() {
        // `f r = r.x` should infer `forall a t. { x :: a | t } -> a`.
        let src = "module M where\nf r = r.x\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        // The type should be a function from an open-record (with an `x`
        // field) to that x's type.
        if let Type::Fun(arg, ret) = &schemes[0].scheme.ty {
            if let Type::Record(fields, tail) = arg.as_ref() {
                assert!(tail.is_some(), "access constrains only the x field");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0, "x");
                // Field type should match the return.
                assert_eq!(&fields[0].1, ret.as_ref());
            } else {
                panic!("expected Record arg, got {arg:?}");
            }
        } else {
            panic!("expected Fun, got {:?}", schemes[0].scheme.ty);
        }
    }

    #[test]
    fn record_access_on_record_with_extra_fields_works() {
        // `r :: { x :: Int, y :: String }`, `r.x` must yield Int.
        let src = "module M where\nv = (r :: { x :: Int, y :: String }).x\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        env.bind_scheme(
            QName::unqualified("r"),
            Scheme::mono(Type::Record(
                vec![("x".into(), int()), ("y".into(), string_ty())],
                None,
            )),
        );
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "Int");
    }

    #[test]
    fn record_update_preserves_record_type() {
        // `f r = r { x = 1 }` has the same type as `f :: { x :: Int | t } -> { x :: Int | t }`.
        let src = "module M where\nf r = r { x = 1 }\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        if let Type::Fun(arg, ret) = &schemes[0].scheme.ty {
            assert_eq!(arg, ret, "update preserves record shape");
        } else {
            panic!("expected Fun, got {:?}", schemes[0].scheme.ty);
        }
    }

    #[test]
    fn record_update_on_wrong_field_type_errors() {
        // `r :: { x :: Int }`; `r { x = "hi" }` must fail — String doesn't
        // unify with the existing Int field type.
        let src = "module M where\nv = r { x = \"hi\" }\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        env.bind_scheme(
            QName::unqualified("r"),
            Scheme::mono(Type::Record(vec![("x".into(), int())], None)),
        );
        let err = infer_value_scc(&ops, &mut env, &decls).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn record_pattern_pun_binds_fresh_vars() {
        // `\{x, y} -> x` should infer `forall a b t. { x :: a, y :: b | t } -> a`.
        let src = "module M where\nf = \\{x, y} -> x\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        if let Type::Fun(arg, _) = &schemes[0].scheme.ty {
            if let Type::Record(fields, tail) = arg.as_ref() {
                assert!(tail.is_some());
                let labels: Vec<_> = fields.iter().map(|(l, _)| l.as_str()).collect();
                assert!(labels.contains(&"x"));
                assert!(labels.contains(&"y"));
            } else {
                panic!("expected Record, got {arg:?}");
            }
        } else {
            panic!("expected Fun, got {:?}", schemes[0].scheme.ty);
        }
    }

    #[test]
    fn record_pattern_explicit_field_recurses() {
        // `\{x: y} -> y` — x must be bound but locally named `y`.
        let src = "module M where\nf = \\{x: y} -> y\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        // Just check the shape compiles; the scheme is
        // `forall a t. { x :: a | t } -> a`.
        match &schemes[0].scheme.ty {
            Type::Fun(arg, _) => {
                assert!(matches!(arg.as_ref(), Type::Record(fs, Some(_)) if fs.len() == 1));
            }
            other => panic!("expected Fun, got {other:?}"),
        }
    }

    // ------------------------------------------------------------------
    // M4e: arrays
    // ------------------------------------------------------------------

    fn array_ty(elem: Type) -> Type {
        Type::app(Type::Con(QName::unqualified("Array")), elem)
    }

    #[test]
    fn array_literal_infers_array_of_elem() {
        let src = "module M where\nxs = [1, 2, 3]\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(schemes[0].scheme.ty, array_ty(int()));
    }

    #[test]
    fn array_elements_must_unify() {
        // Mixed element types: Int and String must unify → fails.
        let src = "module M where\nxs = [1, \"hi\"]\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let err = infer_value_scc(&ops, &mut env, &decls).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn empty_array_generalizes_element_type() {
        let src = "module M where\nxs = []\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "forall a. Array a");
    }

    #[test]
    fn array_pattern_unifies_elements_with_fresh_var() {
        // `\[x, y] -> x` infers `forall a. Array a -> a`.
        let src = "module M where\nfst2 = \\[x, y] -> x\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "forall a. Array a -> a",
        );
    }

    #[test]
    fn array_pattern_with_typed_outer_constrains_element() {
        // `f (xs :: Array Int) = ...` constrains the element via the
        // annotation; an array pattern inside unifies each position with
        // the same Int.
        let src = "module M where\ng (xs :: Array Int) = xs\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "Array Int -> Array Int",
        );
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

    // ------------------------------------------------------------------
    // M5 part 2: exhaustiveness integration into infer_value_scc
    //
    // These tests drive the `infer_value_scc_with_registries` entry
    // point that accepts a `DataConstructors` + `CtorRegistry` pair and
    // returns `InferredScheme`s with `exhaustiveness_errors` filled in.
    // They fail until the wiring lands.
    // ------------------------------------------------------------------

    use crate::typecheck_db::passes::exhaustiveness::{
        CtorInfo, CtorRegistry, DataConstructors,
    };

    /// Build a standard Maybe registry for integration tests.
    fn maybe_registry() -> (DataConstructors, CtorRegistry) {
        let mut data = DataConstructors::new();
        let mut ctors = CtorRegistry::new();
        data.insert("Maybe".into(), vec!["Nothing".into(), "Just".into()]);
        ctors.insert(
            "Nothing".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                type_vars: vec!["a".into()],
                fields: vec![],
            },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        (data, ctors)
    }

    /// Same for Boolean (as an ADT with True/False).
    fn boolean_registry() -> (DataConstructors, CtorRegistry) {
        let mut data = DataConstructors::new();
        let mut ctors = CtorRegistry::new();
        data.insert("Boolean".into(), vec!["True".into(), "False".into()]);
        ctors.insert(
            "True".into(),
            CtorInfo { parent_type: "Boolean".into(), type_vars: vec![], fields: vec![] },
        );
        ctors.insert(
            "False".into(),
            CtorInfo { parent_type: "Boolean".into(), type_vars: vec![], fields: vec![] },
        );
        (data, ctors)
    }

    /// Wire the Just/Nothing constructors into `env` so bodies can
    /// typecheck.
    fn seed_maybe_env(env: &mut Env) {
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

    fn infer_with(
        src: &str,
        env: &mut Env,
        data: &DataConstructors,
        ctors: &CtorRegistry,
    ) -> Vec<InferredScheme> {
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        infer_value_scc_with_registries(&ops, env, &decls, data, ctors).unwrap()
    }

    #[test]
    fn integration_exhaustive_case_produces_no_errors() {
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  Nothing -> 0
  Just y -> y
",
            &mut env,
            &data,
            &ctors,
        );
        assert_eq!(schemes.len(), 1);
        assert!(
            schemes[0].exhaustiveness_errors.is_empty(),
            "got: {:?}",
            schemes[0].exhaustiveness_errors,
        );
    }

    #[test]
    fn integration_missing_nothing_reports_error() {
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  Just y -> y
",
            &mut env,
            &data,
            &ctors,
        );
        assert_eq!(schemes[0].exhaustiveness_errors.len(), 1);
        let err = &schemes[0].exhaustiveness_errors[0];
        assert_eq!(err.type_name, "Maybe");
        assert_eq!(err.missing, vec!["Nothing".to_string()]);
    }

    #[test]
    fn integration_missing_just_reports_error() {
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  Nothing -> 0
",
            &mut env,
            &data,
            &ctors,
        );
        assert_eq!(schemes[0].exhaustiveness_errors.len(), 1);
        assert_eq!(
            schemes[0].exhaustiveness_errors[0].missing,
            vec!["Just".to_string()],
        );
    }

    #[test]
    fn integration_nested_missing_reported_with_prefix() {
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  Nothing -> 0
  Just (Just y) -> y
",
            &mut env,
            &data,
            &ctors,
        );
        // Inner `Just` binder covers Just; the Nothing inside Just
        // is uncovered, so we should see "Just Nothing".
        let errs = &schemes[0].exhaustiveness_errors;
        assert_eq!(errs.len(), 1, "got: {errs:?}");
        assert_eq!(errs[0].missing, vec!["Just Nothing".to_string()]);
    }

    #[test]
    fn integration_wildcard_fallback_clears_errors() {
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  Just y -> y
  _ -> 0
",
            &mut env,
            &data,
            &ctors,
        );
        assert!(schemes[0].exhaustiveness_errors.is_empty());
    }

    #[test]
    fn integration_multi_equation_missing_ctor_reports_error() {
        // Post-MDd, multi-equation f is merged into a single
        // case-bodied decl. Exhaustiveness should still catch the
        // missing Nothing.
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        let (data, ctors) = maybe_registry();
        // Pre-merge decls first (the desugar is currently only used by
        // the cached pass; for this direct test we invoke the merger
        // manually).
        let cst_m = parse_cst(
            "\
module M where
f (Just y) = y
",
        )
        .unwrap();
        let merged_cst = crate::typecheck_db::desugar::multi_eq::merge(cst_m.decls);
        let merged: Vec<Decl> = merged_cst
            .into_iter()
            .map(|d| crate::typecheck_db::ir::lower_decl(d).expect("lower"))
            .collect();
        let decls: Vec<&Decl> = merged.iter().collect();
        let ops = TypeOpMap::default();
        let schemes =
            infer_value_scc_with_registries(&ops, &mut env, &decls, &data, &ctors).unwrap();
        let errs = &schemes[0].exhaustiveness_errors;
        // Single-equation without wildcard → missing Nothing.
        assert_eq!(errs.len(), 1, "got: {errs:?}");
        assert_eq!(errs[0].missing, vec!["Nothing".to_string()]);
    }

    #[test]
    fn integration_guarded_without_fallback_contributes_nothing() {
        // `Nothing | someCond` has no true/otherwise fallback, so
        // that alt shouldn't count for coverage and Nothing must
        // still be reported as missing.
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        env.bind_scheme(QName::unqualified("someCond"), Scheme::mono(bool_ty()));
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  Nothing
    | someCond -> 1
  Just y -> y
",
            &mut env,
            &data,
            &ctors,
        );
        let errs = &schemes[0].exhaustiveness_errors;
        assert_eq!(errs.len(), 1, "got: {errs:?}");
        assert_eq!(errs[0].missing, vec!["Nothing".to_string()]);
    }

    #[test]
    fn integration_otherwise_guard_counts_as_fallback() {
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        env.bind_scheme(QName::unqualified("someCond"), Scheme::mono(bool_ty()));
        env.bind_scheme(QName::unqualified("otherwise"), Scheme::mono(bool_ty()));
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  Nothing
    | someCond -> 1
    | otherwise -> 2
  Just y -> y
",
            &mut env,
            &data,
            &ctors,
        );
        assert!(schemes[0].exhaustiveness_errors.is_empty(), "{:?}", schemes[0].exhaustiveness_errors);
    }

    #[test]
    fn integration_non_adt_scrutinee_no_errors() {
        // Case on an Int has no ADT constructor list — exhaustiveness
        // doesn't apply here.
        let mut env = Env::new();
        let (data, ctors) = maybe_registry();
        let schemes = infer_with(
            "\
module M where
f x = case x of
  0 -> \"zero\"
  _ -> \"other\"
",
            &mut env,
            &data,
            &ctors,
        );
        assert!(schemes[0].exhaustiveness_errors.is_empty());
    }

    #[test]
    fn integration_multi_scrutinee_column_checked_independently() {
        // `case m, n of Just _, True -> 1` — missing Nothing on column 0
        // and missing False on column 1. Both must be reported.
        let mut env = Env::new();
        seed_maybe_env(&mut env);
        env.bind_scheme(QName::unqualified("True"), Scheme::mono(bool_ty()));
        env.bind_scheme(QName::unqualified("False"), Scheme::mono(bool_ty()));
        let mut data = DataConstructors::new();
        let mut ctors = CtorRegistry::new();
        data.insert("Maybe".into(), vec!["Nothing".into(), "Just".into()]);
        ctors.insert(
            "Nothing".into(),
            CtorInfo { parent_type: "Maybe".into(), type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let (bdata, bctors) = boolean_registry();
        for (k, v) in bdata {
            data.insert(k, v);
        }
        for (k, v) in bctors {
            ctors.insert(k, v);
        }
        let schemes = infer_with(
            "\
module M where
f m n = case m, n of
  Just _, True -> 1
",
            &mut env,
            &data,
            &ctors,
        );
        let errs = &schemes[0].exhaustiveness_errors;
        // Two column errors expected — order may vary.
        assert_eq!(errs.len(), 2, "got: {errs:?}");
        let type_names: Vec<&str> =
            errs.iter().map(|e| e.type_name.as_str()).collect();
        assert!(type_names.contains(&"Maybe"));
        assert!(type_names.contains(&"Boolean"));
    }

    #[test]
    fn integration_wrapper_infer_value_scc_defaults_to_empty_errors() {
        // The no-registry wrapper exists so the vast majority of
        // existing tests don't have to care about exhaustiveness.
        // It must still return InferredSchemes with an empty error
        // list.
        let src = "module M where\nx = 1\n";
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert!(schemes[0].exhaustiveness_errors.is_empty());
    }
}
