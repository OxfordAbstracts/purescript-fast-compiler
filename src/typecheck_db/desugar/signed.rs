//! MDb sub-transform: signed literals → `negate` application.
//!
//! The CST represents `-x` as `Expr::Negate { expr: x }`. We lower that to
//! `Expr::App { func: Var("negate"), arg: x }` so the typechecker only has
//! to know about plain applications — and so that user-shadowed `negate`
//! is picked up through the ordinary resolve / infer path.

use crate::cst::{Decl, Expr};
use crate::names::unqualified_value;

use super::walk::fold_decl_exprs;

pub fn desugar_decl(decl: Decl) -> Decl {
    fold_decl_exprs(decl, &mut rewrite)
}

fn rewrite(e: Expr) -> Expr {
    match e {
        Expr::Negate { span, expr } => Expr::App {
            span,
            func: Box::new(Expr::Var { span, name: unqualified_value("negate") }),
            arg: expr,
        },
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn first_decl(src: &str) -> Decl {
        parse(src).unwrap().decls.into_iter().next().unwrap()
    }

    /// Count remaining `Expr::Negate` nodes anywhere inside a decl.
    fn count_negate(d: &Decl) -> u32 {
        let mut n = 0;
        let _ = fold_decl_exprs(d.clone(), &mut |e| {
            if matches!(e, Expr::Negate { .. }) {
                n += 1;
            }
            e
        });
        n
    }

    #[test]
    fn rewrites_top_level_negate() {
        let d = first_decl("module M where\nfoo = -1\n");
        assert_eq!(count_negate(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_negate(&d2), 0);
    }

    #[test]
    fn rewrites_negate_inside_subexpression() {
        // `foo x = f (-x)` — the `-x` is nested inside an application.
        let d = first_decl("module M where\nfoo x = f (-x)\n");
        assert_eq!(count_negate(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_negate(&d2), 0);
    }

    #[test]
    fn non_negate_is_untouched() {
        let d = first_decl("module M where\nfoo = 1\n");
        let d2 = desugar_decl(d.clone());
        assert_eq!(d, d2);
    }

    #[test]
    fn idempotent() {
        let d = first_decl("module M where\nfoo = -1\n");
        let d1 = desugar_decl(d);
        let d2 = desugar_decl(d1.clone());
        assert_eq!(d1, d2);
    }
}
