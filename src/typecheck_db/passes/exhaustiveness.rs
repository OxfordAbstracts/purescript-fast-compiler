//! M5 exhaustiveness pass.
//!
//! Column-based pattern-match coverage check over constructor data
//! types. Modeled on the legacy checker in
//! [src/typechecker/check/exhaustiveness.rs] and
//! [src/typechecker/infer.rs::check_exhaustiveness], but refactored so
//! the core algorithm is a pure function over `cst::Binder` + a
//! constructor registry, with no dependency on the inference pipeline.
//!
//! Scope:
//! * Decide if a set of top-level `Binder`s at one scrutinee position
//!   covers every constructor of the scrutinee's data type.
//! * Recurse into single-field constructors' sub-patterns (`Just x`,
//!   `Cons a as`, newtype wrappers). Multi-field constructors are not
//!   recursed into: column-based cross-product analysis is unsound for
//!   them, and the legacy checker takes the same conservative stance.
//! * Report missing patterns as human-readable strings (e.g.
//!   `"Just Nothing"`) so diagnostics can be printed directly.
//!
//! Out of scope for this pass:
//! * Array-length partiality (flagged as a `Partial` class need, not an
//!   exhaustiveness miss). That's a separate diagnostic category.
//! * Arbitrary literals (Int / String / Char) — there's no finite
//!   constructor set so the only way to cover them is a wildcard or
//!   variable binder. The check reflects that.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::typecheck_db::ir::{Binder, Expr, GuardPattern, GuardedExpr, Literal};
use crate::typecheck_db::types::Type;

// ---------------------------------------------------------------------------
// Registry types
// ---------------------------------------------------------------------------

/// Everything the exhaustiveness checker needs to know about one
/// constructor. Populated from [`crate::typecheck_db::passes::ctor_details`]
/// outputs across every data type in scope.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CtorInfo {
    /// Name of the parent `data`/`newtype`.
    pub parent_type: String,
    /// The parent type's declared type vars — used when instantiating
    /// constructor field types against the scrutinee's actual type
    /// arguments.
    pub type_vars: Vec<String>,
    /// Ordered list of field types, in source order.
    pub fields: Vec<Type>,
}

/// Lookup: data type → every constructor name that belongs to it.
pub type DataConstructors = HashMap<String, Vec<String>>;

/// Lookup: constructor name → its metadata.
pub type CtorRegistry = HashMap<String, CtorInfo>;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// One exhaustiveness finding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonExhaustive {
    /// Span of the case expression (or multi-equation group) that's
    /// missing coverage.
    pub span: crate::span::Span,
    /// Scrutinee / parameter type's constructor name.
    pub type_name: String,
    /// Human-readable list of missing patterns, each a standalone
    /// snippet like `"Nothing"` or `"Just (Just _)"`.
    pub missing: Vec<String>,
}

// ---------------------------------------------------------------------------
// Core check
// ---------------------------------------------------------------------------

/// Does `binders` exhaust every constructor of `scrutinee_ty`?
///
/// Returns `None` when exhaustive *or* when the type isn't a known ADT
/// (in which case the coverage question is out of scope — a bare `Int`
/// scrutinee, for instance, can only be covered by a wildcard, and we
/// report that only if the caller asks for it via the "non-ADT needs
/// catchall" path).
///
/// Returns `Some(missing)` otherwise, where each element is a
/// human-readable pattern description.
pub fn check_exhaustiveness(
    binders: &[&Binder],
    scrutinee_ty: &Type,
    data_constructors: &DataConstructors,
    ctor_details: &CtorRegistry,
) -> Option<Vec<String>> {
    let (type_name, type_args) = extract_type_con_and_args(scrutinee_ty)?;
    let all_ctors = data_constructors.get(&type_name)?;

    // Classify every binder.
    let mut has_catchall = false;
    let mut covered_names: Vec<String> = Vec::new();
    // For each ctor: the arg lists of every pattern that matched it.
    // Preserved so single-field recursion sees every sub-pattern.
    let mut covered_args: HashMap<String, Vec<Vec<Binder>>> = HashMap::new();

    for b in binders {
        classify(b, &mut has_catchall, &mut covered_names, &mut covered_args);
    }

    if has_catchall {
        return None;
    }

    // Name-collision tolerance (legacy): if any covered ctor isn't
    // listed in `all_ctors`, we've likely hit a cross-module name
    // collision and can't safely decide coverage. Bail with None
    // rather than report every real ctor as missing.
    if !covered_names.is_empty() && !covered_names.iter().all(|n| all_ctors.contains(n)) {
        return None;
    }

    // Missing at *this* level.
    let missing_here: Vec<String> = all_ctors
        .iter()
        .filter(|c| !covered_names.contains(c))
        .cloned()
        .collect();
    if !missing_here.is_empty() {
        return Some(missing_here);
    }

    // Every ctor at this level is covered. Recurse into single-field
    // ctors — their unique argument position may still be partial.
    // Multi-field ctors are skipped: column-based analysis across
    // multiple sub-positions is cross-product-unsound, and the legacy
    // checker takes the same conservative stance.
    let mut nested: Vec<String> = Vec::new();
    for ctor_name in all_ctors {
        let info = match ctor_details.get(ctor_name) {
            Some(i) => i,
            None => continue,
        };
        if info.fields.len() != 1 {
            continue;
        }
        let arg_groups = match covered_args.get(ctor_name) {
            Some(g) if !g.is_empty() => g,
            _ => continue,
        };
        // Gather the single sub-binder from each pattern that matched
        // this ctor.
        let sub_binders: Vec<&Binder> =
            arg_groups.iter().filter_map(|args| args.first()).collect();
        if sub_binders.is_empty() {
            continue;
        }
        let field_ty = substitute_type_vars(&info.fields[0], &info.type_vars, &type_args);
        if let Some(inner_missing) =
            check_exhaustiveness(&sub_binders, &field_ty, data_constructors, ctor_details)
        {
            for desc in inner_missing {
                nested.push(wrap_with_ctor(ctor_name, &desc));
            }
        }
    }
    if nested.is_empty() {
        None
    } else {
        Some(nested)
    }
}

/// Does a `GuardedExpr` count as "unconditional" for exhaustiveness
/// accounting? An `Unconditional` body always does; a `Guarded` body
/// counts only if it has a fallback case — either a literal `true` or
/// a reference to `otherwise` (from `Prelude`/`Data.Boolean`, or
/// unqualified), or a pattern guard on an irrefutable binder.
///
/// When a guarded alternative does **not** count, the caller must
/// ignore its pattern for coverage purposes: even if the pattern
/// matched, the guard might not.
pub fn is_unconditional_for_exhaustiveness(g: &GuardedExpr) -> bool {
    match g {
        GuardedExpr::Unconditional(_) => true,
        GuardedExpr::Guarded(guards) => guards.iter().any(guard_is_fallback),
    }
}

fn guard_is_fallback(guard: &crate::typecheck_db::ir::Guard) -> bool {
    // Only single-pattern guards qualify — multi-pattern guards can
    // always fail on any of their sub-patterns.
    if guard.patterns.len() != 1 {
        return false;
    }
    match &guard.patterns[0] {
        GuardPattern::Boolean(expr) => is_guard_true_literal(expr),
        GuardPattern::Pattern(binder, _) => !is_refutable(binder),
    }
}

fn is_guard_true_literal(e: &Expr) -> bool {
    match e {
        Expr::Literal { lit: Literal::Boolean(true), .. } => true,
        Expr::Var { name, .. } => {
            let n = crate::typecheck_db::util::resolve_symbol(name.name.symbol());
            if n != "otherwise" {
                return false;
            }
            match name.module {
                None => true,
                Some(m) => {
                    let ms = crate::typecheck_db::util::resolve_symbol(m.symbol());
                    ms == "Prelude" || ms == "Data.Boolean"
                }
            }
        }
        _ => false,
    }
}

pub fn is_refutable(b: &Binder) -> bool {
    !matches!(peel(b), Binder::Wildcard { .. } | Binder::Var { .. })
}

// ---------------------------------------------------------------------------
// Small helpers (stubbed for now; real impls in the follow-up commit)
// ---------------------------------------------------------------------------

/// "Catchall" binders (`_`, `x`) defeat further coverage analysis —
/// once one appears, the column is automatically exhaustive.
pub fn is_catchall(b: &Binder) -> bool {
    matches!(peel(b), Binder::Wildcard { .. } | Binder::Var { .. })
}

/// Strip `Parens` / `Typed` / `As` wrappers so the real shape of the
/// binder is what gets analysed.
fn peel(b: &Binder) -> &Binder {
    match b {
        Binder::Parens { binder, .. }
        | Binder::Typed { binder, .. }
        | Binder::As { binder, .. } => peel(binder),
        other => other,
    }
}

/// Decide what one binder contributes to coverage analysis.
fn classify(
    binder: &Binder,
    has_catchall: &mut bool,
    covered_names: &mut Vec<String>,
    covered_args: &mut HashMap<String, Vec<Vec<Binder>>>,
) {
    match peel(binder) {
        Binder::Wildcard { .. } | Binder::Var { .. } => *has_catchall = true,
        Binder::Constructor { name, args, .. } => {
            let n = crate::typecheck_db::util::resolve_symbol(name.name.symbol());
            if !covered_names.contains(&n) {
                covered_names.push(n.clone());
            }
            covered_args.entry(n).or_default().push(args.clone());
        }
        // Literal / Record / Array / Op patterns don't advance
        // constructor coverage. Literal and Record are matchable but
        // don't exhaust any ADT; Array is inherently length-partial;
        // Op would only be reached if rebracketing didn't desugar it.
        _ => {}
    }
}

/// Peel an `App` chain down to its head `Con` and collect the applied
/// arguments. Returns `None` for anything that isn't a saturated (or
/// partial) type-constructor application — `Unif`, bare `Var`,
/// function arrows, records, etc.
fn extract_type_con_and_args(ty: &Type) -> Option<(String, Vec<Type>)> {
    let mut args: Vec<Type> = Vec::new();
    let mut cur = ty;
    loop {
        match cur {
            Type::App(f, a) => {
                args.push((**a).clone());
                cur = f;
            }
            Type::Con(q) => {
                args.reverse();
                return Some((q.name.clone(), args));
            }
            _ => return None,
        }
    }
}

/// Instantiate `ty` by replacing each `Type::Var(v)` with the
/// corresponding entry from `args`, where `vars[i]` names the var
/// bound at position `i`. Vars the caller hasn't supplied a value
/// for are left unchanged.
fn substitute_type_vars(ty: &Type, vars: &[String], args: &[Type]) -> Type {
    match ty {
        Type::Var(name) => vars
            .iter()
            .position(|v| v == name)
            .and_then(|i| args.get(i).cloned())
            .unwrap_or_else(|| ty.clone()),
        Type::App(f, a) => Type::app(
            substitute_type_vars(f, vars, args),
            substitute_type_vars(a, vars, args),
        ),
        Type::Fun(f, t) => Type::fun(
            substitute_type_vars(f, vars, args),
            substitute_type_vars(t, vars, args),
        ),
        Type::Record(fields, tail) => Type::Record(
            fields
                .iter()
                .map(|(l, t)| (l.clone(), substitute_type_vars(t, vars, args)))
                .collect(),
            tail.as_ref()
                .map(|t| Box::new(substitute_type_vars(t, vars, args))),
        ),
        Type::Row(fields, tail) => Type::Row(
            fields
                .iter()
                .map(|(l, t)| (l.clone(), substitute_type_vars(t, vars, args)))
                .collect(),
            tail.as_ref()
                .map(|t| Box::new(substitute_type_vars(t, vars, args))),
        ),
        _ => ty.clone(),
    }
}

/// Prefix a nested missing-pattern description with the parent
/// constructor. Single-token descriptions (`"Nothing"`) get a bare
/// space (`"Just Nothing"`); multi-token descriptions get parenthesized
/// so precedence stays unambiguous (`"Just (Just _)"`).
fn wrap_with_ctor(ctor: &str, inner: &str) -> String {
    if inner.contains(' ') {
        format!("{} ({})", ctor, inner)
    } else {
        format!("{} {}", ctor, inner)
    }
}

// ---------------------------------------------------------------------------
// Tests
//
// These are intentionally written *before* the implementation. They
// exercise:
//
// * `is_unconditional_for_exhaustiveness`: what counts as a body we
//   trust to actually execute when a pattern matches.
// * `check_exhaustiveness`: the coverage algorithm itself — wildcards,
//   constructors, nested single-field ctors, newtypes, literals,
//   non-ADT scrutinees, and edge cases (empty data type, as-patterns,
//   record binders, array binders, operator-alias constructors).
//
// The tests compile today against the stubbed API but *fail* with a
// panic on first call. Once the real implementation lands they go
// green one by one.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::ir::{self, Decl};
    use crate::typecheck_db::types::QName;

    // -- helpers ------------------------------------------------------

    fn type_con(name: &str) -> Type {
        Type::Con(QName::unqualified(name))
    }

    fn app(f: Type, a: Type) -> Type {
        Type::app(f, a)
    }

    fn lower(src: &str) -> ir::Module {
        let cst_mod = parse(src).unwrap();
        ir::lower_module(cst_mod).expect("lowering")
    }

    /// Parse a single `f _ = case SCRUTINEE of <alts>` and return the
    /// first binder from each alt. The dummy `_` parameter side-steps
    /// parser requirements for top-level bodies.
    fn case_binders(src: &str) -> Vec<Binder> {
        let m = lower(src);
        let body = m
            .decls
            .into_iter()
            .find_map(|d| match d {
                Decl::Value { guarded: GuardedExpr::Unconditional(e), .. } => Some(*e),
                _ => None,
            })
            .expect("need a Value decl with an unconditional body");
        let alts = match body {
            Expr::Case { alts, .. } => alts,
            other => panic!("expected Expr::Case, got {other:?}"),
        };
        alts.into_iter()
            .map(|a| a.binders.into_iter().next().expect("one binder per alt"))
            .collect()
    }

    fn first_guarded(src: &str) -> GuardedExpr {
        let m = lower(src);
        for d in m.decls {
            if let Decl::Value { guarded, .. } = d {
                return guarded;
            }
        }
        panic!("no Value decl");
    }

    /// Built-in registry: `Maybe`, `Either`, `Bool`, `List`, a newtype
    /// `Age`, plus an empty `Void`. Enough to cover all tests below
    /// without hand-building binders for constructor details.
    fn registry() -> (DataConstructors, CtorRegistry) {
        let mut data: DataConstructors = HashMap::new();
        let mut ctors: CtorRegistry = HashMap::new();

        // data Maybe a = Nothing | Just a
        data.insert(
            "Maybe".into(),
            vec!["Nothing".into(), "Just".into()],
        );
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

        // data Either a b = Left a | Right b
        data.insert(
            "Either".into(),
            vec!["Left".into(), "Right".into()],
        );
        ctors.insert(
            "Left".into(),
            CtorInfo {
                parent_type: "Either".into(),
                type_vars: vec!["a".into(), "b".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        ctors.insert(
            "Right".into(),
            CtorInfo {
                parent_type: "Either".into(),
                type_vars: vec!["a".into(), "b".into()],
                fields: vec![Type::Var("b".into())],
            },
        );

        // data Boolean = True | False  (PureScript uses True/False as ctors)
        data.insert("Boolean".into(), vec!["True".into(), "False".into()]);
        ctors.insert(
            "True".into(),
            CtorInfo { parent_type: "Boolean".into(), type_vars: vec![], fields: vec![] },
        );
        ctors.insert(
            "False".into(),
            CtorInfo { parent_type: "Boolean".into(), type_vars: vec![], fields: vec![] },
        );

        // data List a = Nil | Cons a (List a)  (two-field, no recursion)
        data.insert("List".into(), vec!["Nil".into(), "Cons".into()]);
        ctors.insert(
            "Nil".into(),
            CtorInfo { parent_type: "List".into(), type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Cons".into(),
            CtorInfo {
                parent_type: "List".into(),
                type_vars: vec!["a".into()],
                fields: vec![
                    Type::Var("a".into()),
                    app(type_con("List"), Type::Var("a".into())),
                ],
            },
        );

        // newtype Age = Age Int
        data.insert("Age".into(), vec!["Age".into()]);
        ctors.insert(
            "Age".into(),
            CtorInfo {
                parent_type: "Age".into(),
                type_vars: vec![],
                fields: vec![type_con("Int")],
            },
        );

        // data Void  (no constructors)
        data.insert("Void".into(), vec![]);

        (data, ctors)
    }

    // =================================================================
    // is_unconditional_for_exhaustiveness
    // =================================================================

    #[test]
    fn unconditional_body_counts() {
        let g = first_guarded("module M where\nf _ = 1\n");
        assert!(is_unconditional_for_exhaustiveness(&g));
    }

    #[test]
    fn guarded_with_true_fallback_counts() {
        let g = first_guarded(
            "module M where\nf _\n  | someCond = 1\n  | true = 0\n",
        );
        assert!(is_unconditional_for_exhaustiveness(&g));
    }

    #[test]
    fn guarded_with_otherwise_counts() {
        let g = first_guarded(
            "module M where\nf _\n  | someCond = 1\n  | otherwise = 0\n",
        );
        assert!(is_unconditional_for_exhaustiveness(&g));
    }

    #[test]
    fn guarded_without_fallback_does_not_count() {
        let g = first_guarded("module M where\nf _\n  | someCond = 1\n");
        assert!(!is_unconditional_for_exhaustiveness(&g));
    }

    #[test]
    fn guarded_pattern_guard_only_does_not_count() {
        // `| Just x <- e = …` is still refutable — no coverage credit.
        let g = first_guarded("module M where\nf _\n  | Just x <- foo = x\n");
        assert!(!is_unconditional_for_exhaustiveness(&g));
    }

    // =================================================================
    // Catchall / peel helpers
    // =================================================================

    #[test]
    fn wildcard_is_catchall() {
        let bs = case_binders("module M where\nf _ = case x of\n  _ -> 0\n");
        assert!(is_catchall(&bs[0]));
    }

    #[test]
    fn var_is_catchall() {
        let bs = case_binders("module M where\nf _ = case x of\n  y -> 0\n");
        assert!(is_catchall(&bs[0]));
    }

    #[test]
    fn as_pattern_inherits_catchall_ness() {
        // `y@_` — catchall because it wraps a wildcard.
        let bs = case_binders("module M where\nf _ = case x of\n  y@_ -> 0\n");
        assert!(is_catchall(&bs[0]));
    }

    #[test]
    fn constructor_is_not_catchall() {
        let bs = case_binders("module M where\nf _ = case x of\n  Just _ -> 0\n");
        assert!(!is_catchall(&bs[0]));
    }

    // =================================================================
    // check_exhaustiveness — simple constructor coverage
    // =================================================================

    #[test]
    fn exhaustive_maybe_by_ctors() {
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Nothing -> 0\n  Just y -> y\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn missing_nothing_reports_nothing() {
        let bs = case_binders("module M where\nf _ = case x of\n  Just y -> y\n");
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(
            check_exhaustiveness(&refs, &scrutinee, &d, &c),
            Some(vec!["Nothing".into()]),
        );
    }

    #[test]
    fn missing_just_reports_just() {
        let bs = case_binders("module M where\nf _ = case x of\n  Nothing -> 0\n");
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(
            check_exhaustiveness(&refs, &scrutinee, &d, &c),
            Some(vec!["Just".into()]),
        );
    }

    #[test]
    fn both_ctors_missing_reports_both() {
        let bs = case_binders("module M where\nf _ = case x of\n  Left y -> y\n");
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(app(type_con("Either"), type_con("Int")), type_con("String"));
        let result = check_exhaustiveness(&refs, &scrutinee, &d, &c);
        match result {
            Some(ms) => assert_eq!(ms, vec!["Right".to_string()]),
            None => panic!("expected missing Right"),
        }
    }

    #[test]
    fn wildcard_makes_exhaustive() {
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Just _ -> 1\n  _ -> 0\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn var_makes_exhaustive() {
        let bs = case_binders("module M where\nf _ = case x of\n  y -> y\n");
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // check_exhaustiveness — nested (single-field recursion)
    // =================================================================

    #[test]
    fn nested_just_maybe_exhaustive() {
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Nothing -> 0\n  Just Nothing -> 1\n  Just (Just y) -> y\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), app(type_con("Maybe"), type_con("Int")));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn nested_just_missing_inner_nothing() {
        // Covers Just (Just _) and Nothing, but not Just Nothing.
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Nothing -> 0\n  Just (Just y) -> y\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), app(type_con("Maybe"), type_con("Int")));
        // Expect a single missing pattern: "Just Nothing".
        match check_exhaustiveness(&refs, &scrutinee, &d, &c) {
            Some(ms) => assert_eq!(ms, vec!["Just Nothing".to_string()]),
            None => panic!("expected missing 'Just Nothing'"),
        }
    }

    #[test]
    fn multi_field_ctor_does_not_recurse() {
        // `Cons` has two fields — legacy explicitly bails on recursion
        // for multi-field ctors. So `Cons 1 Nil` alone + `Nil` is
        // exhaustive *at this level* because both Nil and Cons are
        // named; the fact that `Cons 1 _` doesn't cover `Cons 2 _` is
        // not our problem here (would need constraint refinement).
        let bs = case_binders(
            "module M where\nf _ = case xs of\n  Nil -> 0\n  Cons h t -> 1\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("List"), type_con("Int"));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // check_exhaustiveness — newtype, empty, non-ADT
    // =================================================================

    #[test]
    fn newtype_single_ctor_pattern_exhaustive() {
        let bs = case_binders("module M where\nf _ = case a of\n  Age n -> n\n");
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = type_con("Age");
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn empty_data_type_is_vacuously_exhaustive() {
        let bs: Vec<Binder> = vec![];
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = type_con("Void");
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn non_adt_scrutinee_returns_none() {
        // A bare `Int` scrutinee has no constructor list — the check
        // doesn't apply. Reporting "Int literal patterns are partial"
        // is the caller's job, not this pass's.
        let bs = case_binders("module M where\nf _ = case x of\n  1 -> \"one\"\n");
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = type_con("Int");
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // check_exhaustiveness — Boolean-as-ADT
    // =================================================================

    #[test]
    fn boolean_both_ctors_exhaustive() {
        let bs = case_binders(
            "module M where\nf _ = case b of\n  True -> 1\n  False -> 0\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = type_con("Boolean");
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn boolean_only_true_missing_false() {
        let bs = case_binders("module M where\nf _ = case b of\n  True -> 1\n");
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = type_con("Boolean");
        assert_eq!(
            check_exhaustiveness(&refs, &scrutinee, &d, &c),
            Some(vec!["False".into()]),
        );
    }

    // =================================================================
    // check_exhaustiveness — wrapper peels (Parens / Typed / As)
    // =================================================================

    #[test]
    fn parens_around_ctor_still_covers() {
        let bs = case_binders(
            "module M where\nf _ = case x of\n  (Nothing) -> 0\n  (Just y) -> y\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn as_pattern_around_ctor_still_covers() {
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Nothing -> 0\n  all@(Just y) -> y\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn typed_binder_is_peeled() {
        // `(y :: Int)` in a position where Int isn't an ADT still
        // counts as catchall because the inner `y` is a var.
        let bs = case_binders(
            "module M where\nf _ = case x of\n  (y :: Int) -> y\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        assert!(is_catchall(&bs[0]), "typed binder wrapping a var should be catchall: {:?}", bs[0]);
        let (d, c) = registry();
        let scrutinee = type_con("Int");
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // check_exhaustiveness — redundant / duplicate coverage
    // =================================================================

    #[test]
    fn duplicate_constructor_still_exhaustive() {
        // `Just x; Just y; Nothing` — the second `Just y` is redundant
        // (first one already covers), but the check only cares that
        // every ctor is covered *at least* once. Redundancy is a
        // separate concern and not tested here.
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Just a -> a\n  Just b -> b\n  Nothing -> 0\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // check_exhaustiveness — literal patterns never exhaust
    // =================================================================

    #[test]
    fn int_literals_without_wildcard_non_adt_returns_none() {
        // Scrutinee is Int — not an ADT. Same rule as
        // `non_adt_scrutinee_returns_none`: exhaustiveness isn't this
        // pass's responsibility for primitive types.
        let bs = case_binders(
            "module M where\nf _ = case x of\n  0 -> 1\n  1 -> 2\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = type_con("Int");
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // check_exhaustiveness — constructor with nested wildcards
    // =================================================================

    #[test]
    fn just_wildcard_covers_just_branch() {
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Nothing -> 0\n  Just _ -> 1\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), app(type_con("Maybe"), type_con("Int")));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    #[test]
    fn nested_wildcard_beats_nested_specific() {
        // `Just _` covers everything nested under Just, so
        // `Just (Just _)` is exhaustive if combined with Nothing.
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Nothing -> 0\n  Just _ -> 1\n",
        );
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), app(type_con("Maybe"), type_con("Int")));
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // check_exhaustiveness — name-collision tolerance
    // =================================================================

    #[test]
    fn unknown_constructor_in_binders_returns_none() {
        // Covered constructor `Zzz` isn't in the registry at all — the
        // check bails rather than reporting every real constructor as
        // missing. Preserves legacy behavior for cross-module name
        // collisions.
        let bs: Vec<Binder> = {
            // Build a single Constructor binder for a nonexistent ctor.
            let _ignored = parse("module M where\nf _ = case x of\n  Zzz -> 0\n")
                .expect("parse OK");
            case_binders("module M where\nf _ = case x of\n  Zzz -> 0\n")
        };
        let refs: Vec<&Binder> = bs.iter().collect();
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        // Either None or Some containing both ctors would be arguable;
        // legacy returns None to avoid false positives.
        assert_eq!(check_exhaustiveness(&refs, &scrutinee, &d, &c), None);
    }

    // =================================================================
    // Integration: guard-aware filtering
    //
    // A guarded alt that doesn't count must be skipped when deciding
    // coverage. Test by combining a guarded-without-fallback alt with
    // an unconditional alt that alone doesn't cover.
    // =================================================================

    #[test]
    fn guarded_without_fallback_does_not_contribute_to_coverage() {
        // `Nothing | someCond = ...` has no true/otherwise fallback, so
        // this branch doesn't count; `Just y -> y` alone leaves
        // `Nothing` uncovered.
        let bs = case_binders(
            "module M where\nf _ = case x of\n  Nothing\n    | someCond -> 1\n  Just y -> y\n",
        );
        // Manually filter: the caller (infer_case) decides which alts
        // count. Here we test the filter directly.
        let g_nothing = first_guarded(
            "module M where\nf _\n  | someCond = 1\n",
        );
        assert!(!is_unconditional_for_exhaustiveness(&g_nothing));
        // And for the second alt (unconditional):
        let g_just = first_guarded("module M where\nf _ = 1\n");
        assert!(is_unconditional_for_exhaustiveness(&g_just));
        // Calling exhaustiveness with only the unconditional binder:
        let only_just = vec![&bs[1]];
        let (d, c) = registry();
        let scrutinee = app(type_con("Maybe"), type_con("Int"));
        assert_eq!(
            check_exhaustiveness(&only_just, &scrutinee, &d, &c),
            Some(vec!["Nothing".into()]),
        );
    }
}
