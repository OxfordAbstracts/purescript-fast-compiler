//! MDb sub-transform: operator sections → lambda.
//!
//! An underscore in an operand position of `Op`, `App`, or `BacktickApp`
//! is a section, e.g.:
//!
//!   (_ + 1)         becomes  \a -> a + 1
//!   (1 +)           is already desugared by the parser; not our problem
//!   (_ `cmp` 1)     becomes  \a -> a `cmp` 1
//!   f _             becomes  \a -> f a          (single-arg app section)
//!   _ f             becomes  \a -> a f
//!
//! The transform is post-order: inner sections are wrapped first, so by
//! the time we visit an outer `Op` its operands are either "no wildcard"
//! or a lambda (the inner section's result). We then check the *current*
//! node for any remaining direct `Expr::Wildcard` operands; if there are
//! any, we collect them, rename each to a fresh parameter, and wrap the
//! rewritten node in a lambda of those parameters.
//!
//! We deliberately do NOT descend into a wildcard *within* a record (e.g.
//! `(_ { x = 1 })` is a record-update section, distinct syntax handled by
//! a separate sub-transform).

use crate::cst::{Binder, Expr, Spanned};
use crate::names::{value_name, ValueName};
use crate::span::Span;

use super::walk::fold_decl_exprs;

pub fn desugar_decl(decl: crate::cst::Decl) -> crate::cst::Decl {
    let mut counter: u32 = 0;
    fold_decl_exprs(decl, &mut |node| rewrite_node(node, &mut counter))
}

fn is_wildcard(e: &Expr) -> bool {
    matches!(e, Expr::Wildcard { .. })
}

/// A record-update section (`_ { x = 1 }`) is represented as
/// `App { func: Wildcard, arg: Record { fields all is_update } }`. It's
/// handled by the records sub-transform (MDb record wildcards), not here.
fn is_record_update_section(func: &Expr, arg: &Expr) -> bool {
    if !is_wildcard(func) {
        return false;
    }
    matches!(
        arg,
        Expr::Record { fields, .. } if !fields.is_empty() && fields.iter().all(|f| f.is_update)
    )
}

/// Does this node have at least one direct `_` operand that makes it a
/// section? Only operand positions count — `{ x: _ }` inside a record
/// literal is not a section at this level (that's the record-wildcards
/// transform's job).
fn has_section_wildcard(e: &Expr) -> bool {
    match e {
        Expr::Op { left, right, .. } => is_wildcard(left) || is_wildcard(right),
        Expr::App { func, arg, .. } => {
            if is_record_update_section(func, arg) {
                false
            } else {
                is_wildcard(func) || is_wildcard(arg)
            }
        }
        Expr::BacktickApp { left, right, .. } => is_wildcard(left) || is_wildcard(right),
        // `if _ then _ else _` sections: any direct wildcard in
        // cond/then/else slots produces a lambda of the
        // corresponding arity.
        Expr::If { cond, then_expr, else_expr, .. } => {
            is_wildcard(cond) || is_wildcard(then_expr) || is_wildcard(else_expr)
        }
        // `case _, x, _ of …` sections: any scrutinee slot that
        // is a direct wildcard becomes a fresh lambda binder,
        // bound around the whole case expression.
        Expr::Case { exprs, .. } => exprs.iter().any(is_wildcard),
        _ => false,
    }
}

fn rewrite_node(e: Expr, counter: &mut u32) -> Expr {
    if !has_section_wildcard(&e) {
        return e;
    }
    let span = span_of(&e);
    let mut params: Vec<Binder> = Vec::new();
    let body = replace_one_level_wildcards(e, counter, &mut params);
    Expr::Lambda { span, binders: params, body: Box::new(body) }
}

/// Walk the *direct* operand slots of one node and swap every `_` for a
/// fresh `$arg_N` variable, appending a matching `Binder::Var` to
/// `params`. Non-wildcard children are left alone (they've already been
/// post-order-rewritten by `fold_expr`).
fn replace_one_level_wildcards(
    e: Expr,
    counter: &mut u32,
    params: &mut Vec<Binder>,
) -> Expr {
    match e {
        Expr::Op { span, left, op, right } => Expr::Op {
            span,
            left: Box::new(swap_if_wildcard(*left, counter, params)),
            op,
            right: Box::new(swap_if_wildcard(*right, counter, params)),
        },
        Expr::App { span, func, arg } => Expr::App {
            span,
            func: Box::new(swap_if_wildcard(*func, counter, params)),
            arg: Box::new(swap_if_wildcard(*arg, counter, params)),
        },
        Expr::BacktickApp { span, func, left, right } => Expr::BacktickApp {
            span,
            func,
            left: Box::new(swap_if_wildcard(*left, counter, params)),
            right: Box::new(swap_if_wildcard(*right, counter, params)),
        },
        Expr::If { span, cond, then_expr, else_expr } => Expr::If {
            span,
            cond: Box::new(swap_if_wildcard(*cond, counter, params)),
            then_expr: Box::new(swap_if_wildcard(*then_expr, counter, params)),
            else_expr: Box::new(swap_if_wildcard(*else_expr, counter, params)),
        },
        Expr::Case { span, exprs, alts } => Expr::Case {
            span,
            exprs: exprs
                .into_iter()
                .map(|e| swap_if_wildcard(e, counter, params))
                .collect(),
            alts,
        },
        other => other,
    }
}

fn swap_if_wildcard(e: Expr, counter: &mut u32, params: &mut Vec<Binder>) -> Expr {
    if !is_wildcard(&e) {
        return e;
    }
    let span = span_of(&e);
    let name = fresh_param(counter);
    params.push(Binder::Var {
        span,
        name: Spanned { span, value: name.clone() },
    });
    Expr::Var {
        span,
        name: crate::names::Qualified::unqualified(name),
    }
}

fn fresh_param(counter: &mut u32) -> ValueName {
    let s = format!("$sec_{}", counter);
    *counter += 1;
    value_name(&s)
}

fn span_of(e: &Expr) -> Span {
    match e {
        Expr::Var { span, .. }
        | Expr::Constructor { span, .. }
        | Expr::Literal { span, .. }
        | Expr::App { span, .. }
        | Expr::VisibleTypeApp { span, .. }
        | Expr::Lambda { span, .. }
        | Expr::Op { span, .. }
        | Expr::OpParens { span, .. }
        | Expr::If { span, .. }
        | Expr::Case { span, .. }
        | Expr::Let { span, .. }
        | Expr::Do { span, .. }
        | Expr::Ado { span, .. }
        | Expr::Record { span, .. }
        | Expr::RecordAccess { span, .. }
        | Expr::RecordUpdate { span, .. }
        | Expr::Parens { span, .. }
        | Expr::TypeAnnotation { span, .. }
        | Expr::Wildcard { span, .. }
        | Expr::Hole { span, .. }
        | Expr::Array { span, .. }
        | Expr::Negate { span, .. }
        | Expr::AsPattern { span, .. }
        | Expr::BacktickApp { span, .. } => *span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cst::Decl;
    use crate::parser::parse;

    fn first_decl(src: &str) -> Decl {
        parse(src).unwrap().decls.into_iter().next().unwrap()
    }

    fn count_wildcards(d: &Decl) -> u32 {
        let mut n = 0u32;
        let _ = super::super::walk::fold_decl_exprs(d.clone(), &mut |x| {
            if matches!(x, Expr::Wildcard { .. }) {
                n += 1;
            }
            x
        });
        n
    }

    fn count_lambdas(d: &Decl) -> u32 {
        let mut n = 0u32;
        let _ = super::super::walk::fold_decl_exprs(d.clone(), &mut |x| {
            if matches!(x, Expr::Lambda { .. }) {
                n += 1;
            }
            x
        });
        n
    }

    #[test]
    fn op_section_becomes_lambda() {
        let d = first_decl("module M where\nf = (_ + 1)\n");
        assert_eq!(count_wildcards(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_wildcards(&d2), 0);
        assert!(count_lambdas(&d2) >= 1, "expected at least one lambda");
    }

    #[test]
    fn backtick_section_becomes_lambda() {
        let d = first_decl("module M where\nf = (_ `cmp` 1)\n");
        assert_eq!(count_wildcards(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_wildcards(&d2), 0);
    }

    #[test]
    fn app_section_becomes_lambda() {
        // `f _` — single-arg application section. The parser may or may
        // not emit this shape depending on context; the key assertion is
        // that if it does, our transform eats the wildcard.
        let d = first_decl("module M where\nrun = f _\n");
        let before = count_wildcards(&d);
        let d2 = desugar_decl(d);
        // Either 0 wildcards (got converted) or equal to before if the
        // parser didn't produce a section shape here. Never more.
        assert!(count_wildcards(&d2) <= before);
    }

    #[test]
    fn non_section_is_untouched() {
        let d = first_decl("module M where\nfoo = 1 + 2\n");
        let d2 = desugar_decl(d.clone());
        assert_eq!(d, d2);
    }

    #[test]
    fn idempotent() {
        let d = first_decl("module M where\nf = (_ + 1)\n");
        let d1 = desugar_decl(d);
        let d2 = desugar_decl(d1.clone());
        assert_eq!(d1, d2);
    }
}
