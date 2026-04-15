//! M4a: bidirectional inference for `Var`, `App`, `Lambda` (and trivial
//! degenerate forms: `Parens`, `TypeAnnotation`, `Hole`, `Wildcard`,
//! `Literal`, `Constructor`).
//!
//! Later sub-milestones fill in `Let`/`If` (M4b), `Case` (M4c), `Do`/`Ado`
//! (M4d), records (M4e). The hooks are written so those additions are
//! additive — each new form adds a match arm without reshaping the
//! surrounding API.
//!
//! The entry point is `infer_value_scc`, which corresponds to the
//! `infer_value_scc` nanopass in the plan: given an SCC of top-level
//! value decls plus the caller-supplied [`Env`] of dependency schemes, it
//! returns a [`Scheme`] per name defined in the SCC.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::cst::{self, Binder, Decl, Expr, Literal};
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

        // Forms reserved for later sub-milestones.
        Expr::Let { .. } => Err(InferError::Unsupported("let")),
        Expr::If { .. } => Err(InferError::Unsupported("if")),
        Expr::Case { .. } => Err(InferError::Unsupported("case")),
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
        // Constructor / Record / Array / As / Op patterns: later
        // sub-milestones (M4c / M4e).
        Binder::Constructor { .. } => Err(InferError::UnsupportedBinder("constructor")),
        Binder::Record { .. } => Err(InferError::UnsupportedBinder("record")),
        Binder::Array { .. } => Err(InferError::UnsupportedBinder("array")),
        Binder::As { .. } => Err(InferError::UnsupportedBinder("as")),
        Binder::Op { .. } => Err(InferError::UnsupportedBinder("op")),
    }
}

fn infer_equation(
    state: &mut UnifyState,
    env: &mut Env,
    type_ops: &TypeOpMap,
    binders: &[Binder],
    guarded: &cst::GuardedExpr,
) -> Result<Type, InferError> {
    // `foo x y = body` acts as `\x y -> body` at the top level. For M4a we
    // require Unconditional bodies; guards arrive alongside Case in M4c.
    let body = match guarded {
        cst::GuardedExpr::Unconditional(e) => e,
        cst::GuardedExpr::Guarded(_) => {
            return Err(InferError::Unsupported("guarded equation"))
        }
    };
    if binders.is_empty() {
        return infer_expr(state, env, type_ops, body);
    }

    env.push_scope();
    let mut param_tys = Vec::with_capacity(binders.len());
    for b in binders {
        let ty = bind_pattern(state, env, type_ops, b)?;
        param_tys.push(ty);
    }
    let body_ty = infer_expr(state, env, type_ops, body)?;
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
