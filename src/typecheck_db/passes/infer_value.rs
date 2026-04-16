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
        Expr::Record { fields, .. } => infer_record(state, env, type_ops, fields),
        Expr::RecordAccess { expr, field, .. } => {
            infer_record_access(state, env, type_ops, expr, field)
        }
        Expr::RecordUpdate { expr, updates, .. } => {
            infer_record_update(state, env, type_ops, expr, updates)
        }
        Expr::Array { elements, .. } => infer_array(state, env, type_ops, elements),

        // Forms reserved for later sub-milestones.
        Expr::Do { .. } | Expr::Ado { .. } => Err(InferError::Unsupported("do/ado")),
        Expr::Op { .. } | Expr::OpParens { .. } | Expr::BacktickApp { .. } => {
            Err(InferError::Unsupported("operator"))
        }
        Expr::VisibleTypeApp { .. } => Err(InferError::Unsupported("visible-type-app")),
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
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
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
        crate::typecheck_db::util::resolve_symbol(qi.name);
    let module_str = qi.module.map(crate::typecheck_db::util::resolve_symbol);

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
    let func_ty = infer_expr(state, env, type_ops, func)?;
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
    fields: &[cst::RecordField],
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
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            env.bind_local(n, inner.clone());
            Ok(inner)
        }
        Binder::Record { fields, .. } => bind_record_pattern(state, env, type_ops, fields),
        Binder::Array { elements, .. } => bind_array_pattern(state, env, type_ops, elements),
        // Op patterns (`x :| xs`) — deferred; they need fixity + data-ctor
        // resolution, a job for a later milestone.
        Binder::Op { .. } => Err(InferError::UnsupportedBinder("op")),
    }
}

/// Match `{ l1, l2: sub2, ... }` against an open record type. Pun
/// fields (`{ l }`) bind `l` to a fresh unification var; explicit
/// fields (`{ l: sub }`) recurse into the sub-binder.
fn bind_record_pattern(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    fields: &[cst::RecordBinderField],
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
    fields: &[cst::RecordField],
) -> Result<Type, InferError> {
    // A bare `Expr::Record` should only appear as a literal — fields
    // with `is_update = true` are emitted by the parser exclusively
    // under an `App` (record update) and are handled in `infer_app`.
    // A standalone all-update record is a parser invariant violation.
    assert!(
        fields.iter().all(|f| !f.is_update),
        "parser invariant: bare Expr::Record with update fields should appear under App",
    );
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
    Ok(Type::Record(inferred, None))
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
    Ok(field_ty)
}

fn infer_record_update(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    expr: &Expr,
    updates: &[cst::RecordUpdate],
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

    // Pass 1: collect signatures keyed by name.
    let mut sigs: HashMap<String, Type> = HashMap::new();
    for b in bindings {
        if let LetBinding::Signature { name, ty, .. } = b {
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            sigs.insert(n, convert_type_expr(ty, type_ops));
        }
    }

    // Pass 2: materialize value bindings and pre-insert slots into locals so
    // mutually-recursive `let`s typecheck.
    let mut value_bindings: Vec<LetValueBinding<'_>> = Vec::new();
    for b in bindings {
        match b {
            LetBinding::Value { binder: Binder::Var { name, .. }, expr, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
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

    // ------------------------------------------------------------------
    // M4d: records
    // ------------------------------------------------------------------

    fn string_ty() -> Type {
        Type::Con(QName::unqualified("String"))
    }

    #[test]
    fn record_literal_infers_closed_record() {
        let src = "module M where\nr = { x: 1, y: \"hi\" }\n";
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
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
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let err = infer_value_scc(&ops, &mut env, &decls).unwrap_err();
        assert!(matches!(err, InferError::Unify(_)), "got: {err:?}");
    }

    #[test]
    fn empty_array_generalizes_element_type() {
        let src = "module M where\nxs = []\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(scheme_display(&schemes[0].scheme), "forall a. (Array a)");
    }

    #[test]
    fn array_pattern_unifies_elements_with_fresh_var() {
        // `\[x, y] -> x` infers `forall a. Array a -> a`.
        let src = "module M where\nfst2 = \\[x, y] -> x\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "forall a. ((Array a) -> a)",
        );
    }

    #[test]
    fn array_pattern_with_typed_outer_constrains_element() {
        // `f (xs :: Array Int) = ...` constrains the element via the
        // annotation; an array pattern inside unifies each position with
        // the same Int.
        let src = "module M where\ng (xs :: Array Int) = xs\n";
        let m = parse(src).unwrap();
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let mut env = Env::new();
        let schemes = infer_value_scc(&ops, &mut env, &decls).unwrap();
        assert_eq!(
            scheme_display(&schemes[0].scheme),
            "((Array Int) -> (Array Int))",
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
}
