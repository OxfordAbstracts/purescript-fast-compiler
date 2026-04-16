//! MDd sub-transform: merge multi-equation value declarations into one.
//!
//! The CST stores each function equation as its own `Decl::Value`:
//!
//! ```text
//! f Nothing    = 0
//! f (Just x)   = x
//! ```
//!
//! → two adjacent `Decl::Value` rows, both named `f`. This transform
//! collapses such groups into a single decl whose body is a `case`:
//!
//! ```text
//! f $eq_0 = case $eq_0 of
//!   Nothing  -> 0
//!   Just x   -> x
//! ```
//!
//! Multi-arg equations generalize column-wise:
//!
//! ```text
//! f Nothing  _  = 0
//! f (Just x) y  = x + y
//! ```
//!
//! →
//!
//! ```text
//! f $eq_0 $eq_1 = case $eq_0, $eq_1 of
//!   Nothing,  _ -> 0
//!   Just x,   y -> x + y
//! ```
//!
//! Per-equation `where`-clauses are lowered to a `let` around the
//! equation's result (wrapping both `Unconditional` and `Guarded`
//! bodies), so the merged decl carries no `where_clause` itself.
//!
//! Only *adjacent* `Decl::Value`s with the same name *and same arity*
//! are merged. A mismatch in arity is a user error the typechecker will
//! surface — we leave such groups unmerged.
//!
//! This transform works at the *module* level (it changes the decl
//! count), unlike the per-decl transforms in the MDb/MDc group. Callers
//! must run it before dispatching the pipeline per-decl.

use crate::cst::{
    Binder, CaseAlternative, Decl, Expr, Guard, GuardedExpr, LetBinding, Spanned,
};
use crate::names::{value_name, Qualified, ValueName};
use crate::span::Span;

/// Entry point: collapse adjacent same-name `Decl::Value` runs into
/// single case-bodied decls. Non-value decls pass through unchanged.
pub fn merge(decls: Vec<Decl>) -> Vec<Decl> {
    let mut out: Vec<Decl> = Vec::with_capacity(decls.len());
    let mut group: Vec<Decl> = Vec::new();

    for d in decls {
        if extend_group(&group, &d) {
            group.push(d);
        } else {
            flush(&mut out, std::mem::take(&mut group));
            if matches!(d, Decl::Value { .. }) {
                group.push(d);
            } else {
                out.push(d);
            }
        }
    }
    flush(&mut out, group);
    out
}

/// Would appending `d` to `group` keep a valid same-name / same-arity
/// run going?
fn extend_group(group: &[Decl], d: &Decl) -> bool {
    let (Some(Decl::Value { name: gn, binders: gb, .. }), Decl::Value { name: dn, binders: db, .. }) =
        (group.first(), d)
    else {
        return false;
    };
    gn.value.symbol() == dn.value.symbol() && gb.len() == db.len()
}

fn flush(out: &mut Vec<Decl>, group: Vec<Decl>) {
    match group.len() {
        0 => {}
        1 => out.push(group.into_iter().next().unwrap()),
        _ => out.push(merge_equations(group)),
    }
}

fn merge_equations(equations: Vec<Decl>) -> Decl {
    let arity = match &equations[0] {
        Decl::Value { binders, .. } => binders.len(),
        _ => unreachable!("group only contains Decl::Value"),
    };
    let merged_span = match &equations[0] {
        Decl::Value { span, .. } => *span,
        _ => unreachable!(),
    };

    // Fresh top-level parameters: `$eq_0`, `$eq_1`, ...
    let fresh: Vec<ValueName> = (0..arity)
        .map(|i| value_name(&format!("$eq_{}", i)))
        .collect();

    // Walk the equations to build the case alternatives. Clone out the
    // fields we need; the rest of each equation is discarded.
    let mut alts: Vec<CaseAlternative> = Vec::with_capacity(equations.len());
    // Grab the first equation's name + doc_comments; everything else
    // folds into the case body.
    let mut iter = equations.into_iter();
    let (name, doc_comments) = match iter.next().unwrap() {
        Decl::Value { name, binders, guarded, where_clause, span, doc_comments } => {
            alts.push(CaseAlternative {
                span,
                binders,
                result: wrap_where(guarded, where_clause),
            });
            (name, doc_comments)
        }
        _ => unreachable!(),
    };
    for d in iter {
        if let Decl::Value { binders, guarded, where_clause, span, .. } = d {
            alts.push(CaseAlternative {
                span,
                binders,
                result: wrap_where(guarded, where_clause),
            });
        }
    }

    // Scrutinees: `$eq_0, $eq_1, ...`
    let scrutinees: Vec<Expr> = fresh
        .iter()
        .map(|n| Expr::Var {
            span: merged_span,
            name: Qualified::unqualified(n.clone()),
        })
        .collect();

    let case_expr = Expr::Case {
        span: merged_span,
        exprs: scrutinees,
        alts,
    };

    // Outer binders: `$eq_0 $eq_1 ...`
    let new_binders: Vec<Binder> = fresh
        .iter()
        .map(|n| Binder::Var {
            span: merged_span,
            name: Spanned { span: merged_span, value: n.clone() },
        })
        .collect();

    Decl::Value {
        span: merged_span,
        name,
        binders: new_binders,
        guarded: GuardedExpr::Unconditional(Box::new(case_expr)),
        where_clause: Vec::new(),
        doc_comments,
    }
}

/// Wrap `guarded` with `let where_clause in ...` if non-empty. Both
/// shapes of guarded body are handled: `Unconditional` wraps its
/// expression; `Guarded` wraps *each* guard's result expression (so
/// every guard sees the where bindings in scope).
fn wrap_where(g: GuardedExpr, where_clause: Vec<LetBinding>) -> GuardedExpr {
    if where_clause.is_empty() {
        return g;
    }
    match g {
        GuardedExpr::Unconditional(e) => {
            let span = e.span();
            GuardedExpr::Unconditional(Box::new(Expr::Let {
                span,
                bindings: where_clause,
                body: e,
            }))
        }
        GuardedExpr::Guarded(guards) => GuardedExpr::Guarded(
            guards
                .into_iter()
                .map(|g| wrap_guard(g, where_clause.clone()))
                .collect(),
        ),
    }
}

fn wrap_guard(g: Guard, where_clause: Vec<LetBinding>) -> Guard {
    let span = g.expr.span();
    Guard {
        span: g.span,
        patterns: g.patterns,
        expr: Box::new(Expr::Let {
            span,
            bindings: where_clause,
            body: g.expr,
        }),
    }
}

// Silence unused `Span` import warning in the bare case — reserved for
// future use in this file.
#[allow(dead_code)]
fn _touch_span(_: Span) {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn module_decls(src: &str) -> Vec<Decl> {
        parse(src).unwrap().decls
    }

    fn count_value_named(decls: &[Decl], name: &str) -> usize {
        decls
            .iter()
            .filter(|d| match d {
                Decl::Value { name: n, .. } => {
                    crate::interner::resolve(n.value.symbol()).as_deref() == Some(name)
                }
                _ => false,
            })
            .count()
    }

    fn is_case_body(d: &Decl) -> bool {
        if let Decl::Value { guarded: GuardedExpr::Unconditional(e), .. } = d {
            matches!(e.as_ref(), Expr::Case { .. })
        } else {
            false
        }
    }

    #[test]
    fn single_equation_is_untouched() {
        let decls = module_decls("module M where\nf x = x\n");
        let out = merge(decls.clone());
        assert_eq!(out, decls);
    }

    #[test]
    fn two_equations_same_arity_merge() {
        let decls = module_decls("\
module M where
f Nothing = 0
f (Just x) = x
");
        assert_eq!(count_value_named(&decls, "f"), 2);
        let out = merge(decls);
        assert_eq!(count_value_named(&out, "f"), 1);
        assert!(is_case_body(&out[0]), "merged decl should have a Case body");
        // One new top-level binder per arity slot.
        if let Decl::Value { binders, .. } = &out[0] {
            assert_eq!(binders.len(), 1);
        } else {
            panic!("expected Value");
        }
    }

    #[test]
    fn multi_arg_multi_equation_merges_with_matching_arity() {
        let decls = module_decls("\
module M where
g Nothing _ = 0
g (Just x) y = x
");
        assert_eq!(count_value_named(&decls, "g"), 2);
        let out = merge(decls);
        assert_eq!(count_value_named(&out, "g"), 1);
        assert!(is_case_body(&out[0]));
        if let Decl::Value { binders, .. } = &out[0] {
            assert_eq!(binders.len(), 2, "multi-arg merged decl keeps arity");
        }
    }

    #[test]
    fn differing_arity_prevents_merge() {
        // PureScript normally rejects mixed arity; we leave such groups
        // unmerged so the typechecker can surface the error.
        let decls = module_decls("\
module M where
f 0 = 1
f = 2
");
        assert_eq!(count_value_named(&decls, "f"), 2);
        let out = merge(decls);
        // No merge — still two `f` decls.
        assert_eq!(count_value_named(&out, "f"), 2);
    }

    #[test]
    fn non_adjacent_equations_are_not_merged() {
        let decls = module_decls("\
module M where
f 0 = 1
g x = x
f n = n
");
        let out = merge(decls);
        // Still two `f`s, one `g`.
        assert_eq!(count_value_named(&out, "f"), 2);
        assert_eq!(count_value_named(&out, "g"), 1);
    }

    #[test]
    fn signature_between_sig_and_equations_keeps_merge() {
        // `f :: Int -> Int` sits before the equations — the two
        // equations are still adjacent after the signature.
        let decls = module_decls("\
module M where
f :: Int -> Int
f 0 = 1
f n = n
");
        let out = merge(decls);
        assert_eq!(count_value_named(&out, "f"), 1);
        assert!(is_case_body(out.iter().find(|d| matches!(d, Decl::Value{..})).unwrap()));
    }

    #[test]
    fn where_clause_is_lifted_into_the_alternative() {
        let decls = module_decls("\
module M where
f 0 = helper
  where helper = 0
f n = n
");
        let out = merge(decls);
        assert_eq!(count_value_named(&out, "f"), 1);
        // Verify the merged decl has no outer where_clause (it moved
        // into the case alt).
        if let Decl::Value { where_clause, .. } = &out[0] {
            assert!(where_clause.is_empty());
        }
        // And the first alternative's Unconditional body is now a Let.
        if let Decl::Value { guarded: GuardedExpr::Unconditional(e), .. } = &out[0] {
            if let Expr::Case { alts, .. } = e.as_ref() {
                let first = &alts[0];
                if let GuardedExpr::Unconditional(inner) = &first.result {
                    assert!(
                        matches!(inner.as_ref(), Expr::Let { .. }),
                        "expected Let around where-lifted body"
                    );
                }
            }
        }
    }

    #[test]
    fn merge_is_idempotent() {
        let decls = module_decls("\
module M where
f Nothing = 0
f (Just x) = x
");
        let once = merge(decls);
        let twice = merge(once.clone());
        assert_eq!(once, twice);
    }
}
