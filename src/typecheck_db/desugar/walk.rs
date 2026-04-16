//! Expression-tree traversal helpers shared by every desugar sub-transform.
//!
//! `fold_expr` does a post-order rewrite: every sub-expression is visited
//! bottom-up, and the caller-supplied closure gets to inspect/replace each
//! node. Post-order is what MDb's transforms want (rewrite inner first,
//! then the outer can look at its already-rewritten children).
//!
//! Composition of transforms is "pipeline-by-sequencing": run transform A
//! as one `fold_expr`, then run transform B on the result. This is simpler
//! than interleaving them in one traversal and plenty fast for desugar's
//! decl-sized inputs.

use crate::cst::{
    CaseAlternative, DoStatement, Expr, Guard, GuardPattern, GuardedExpr, LetBinding,
    Literal, RecordField, RecordUpdate,
};

pub fn fold_expr<F: FnMut(Expr) -> Expr>(e: Expr, f: &mut F) -> Expr {
    let e = recurse_children(e, f);
    f(e)
}

fn recurse_children<F: FnMut(Expr) -> Expr>(e: Expr, f: &mut F) -> Expr {
    match e {
        Expr::Var { .. }
        | Expr::Constructor { .. }
        | Expr::Wildcard { .. }
        | Expr::Hole { .. }
        | Expr::OpParens { .. } => e,

        Expr::Literal { span, lit } => match lit {
            Literal::Array(xs) => Expr::Literal {
                span,
                lit: Literal::Array(xs.into_iter().map(|x| fold_expr(x, f)).collect()),
            },
            other => Expr::Literal { span, lit: other },
        },

        Expr::App { span, func, arg } => Expr::App {
            span,
            func: Box::new(fold_expr(*func, f)),
            arg: Box::new(fold_expr(*arg, f)),
        },
        Expr::VisibleTypeApp { span, func, ty } => Expr::VisibleTypeApp {
            span,
            func: Box::new(fold_expr(*func, f)),
            ty,
        },
        Expr::Lambda { span, binders, body } => Expr::Lambda {
            span,
            binders,
            body: Box::new(fold_expr(*body, f)),
        },
        Expr::Op { span, left, op, right } => Expr::Op {
            span,
            left: Box::new(fold_expr(*left, f)),
            op,
            right: Box::new(fold_expr(*right, f)),
        },
        Expr::If { span, cond, then_expr, else_expr } => Expr::If {
            span,
            cond: Box::new(fold_expr(*cond, f)),
            then_expr: Box::new(fold_expr(*then_expr, f)),
            else_expr: Box::new(fold_expr(*else_expr, f)),
        },
        Expr::Case { span, exprs, alts } => Expr::Case {
            span,
            exprs: exprs.into_iter().map(|e| fold_expr(e, f)).collect(),
            alts: alts.into_iter().map(|a| fold_alt(a, f)).collect(),
        },
        Expr::Let { span, bindings, body } => Expr::Let {
            span,
            bindings: bindings.into_iter().map(|b| fold_let_binding(b, f)).collect(),
            body: Box::new(fold_expr(*body, f)),
        },
        Expr::Do { span, module, statements } => Expr::Do {
            span,
            module,
            statements: statements.into_iter().map(|s| fold_do_stmt(s, f)).collect(),
        },
        Expr::Ado { span, module, statements, result } => Expr::Ado {
            span,
            module,
            statements: statements.into_iter().map(|s| fold_do_stmt(s, f)).collect(),
            result: Box::new(fold_expr(*result, f)),
        },
        Expr::Record { span, fields } => Expr::Record {
            span,
            fields: fields.into_iter().map(|r| fold_record_field(r, f)).collect(),
        },
        Expr::RecordAccess { span, expr, field } => Expr::RecordAccess {
            span,
            expr: Box::new(fold_expr(*expr, f)),
            field,
        },
        Expr::RecordUpdate { span, expr, updates } => Expr::RecordUpdate {
            span,
            expr: Box::new(fold_expr(*expr, f)),
            updates: updates
                .into_iter()
                .map(|u| fold_record_update(u, f))
                .collect(),
        },
        Expr::Parens { span, expr } => Expr::Parens {
            span,
            expr: Box::new(fold_expr(*expr, f)),
        },
        Expr::TypeAnnotation { span, expr, ty } => Expr::TypeAnnotation {
            span,
            expr: Box::new(fold_expr(*expr, f)),
            ty,
        },
        Expr::Array { span, elements } => Expr::Array {
            span,
            elements: elements.into_iter().map(|e| fold_expr(e, f)).collect(),
        },
        Expr::Negate { span, expr } => Expr::Negate {
            span,
            expr: Box::new(fold_expr(*expr, f)),
        },
        Expr::AsPattern { span, name, pattern } => Expr::AsPattern {
            span,
            name: Box::new(fold_expr(*name, f)),
            pattern: Box::new(fold_expr(*pattern, f)),
        },
        Expr::BacktickApp { span, func, left, right } => Expr::BacktickApp {
            span,
            func: Box::new(fold_expr(*func, f)),
            left: Box::new(fold_expr(*left, f)),
            right: Box::new(fold_expr(*right, f)),
        },
    }
}

fn fold_alt<F: FnMut(Expr) -> Expr>(a: CaseAlternative, f: &mut F) -> CaseAlternative {
    CaseAlternative {
        span: a.span,
        binders: a.binders,
        result: fold_guarded(a.result, f),
    }
}

fn fold_guarded<F: FnMut(Expr) -> Expr>(g: GuardedExpr, f: &mut F) -> GuardedExpr {
    match g {
        GuardedExpr::Unconditional(e) => GuardedExpr::Unconditional(Box::new(fold_expr(*e, f))),
        GuardedExpr::Guarded(gs) => {
            GuardedExpr::Guarded(gs.into_iter().map(|g| fold_guard(g, f)).collect())
        }
    }
}

fn fold_guard<F: FnMut(Expr) -> Expr>(g: Guard, f: &mut F) -> Guard {
    Guard {
        span: g.span,
        patterns: g.patterns.into_iter().map(|p| fold_guard_pattern(p, f)).collect(),
        expr: Box::new(fold_expr(*g.expr, f)),
    }
}

fn fold_guard_pattern<F: FnMut(Expr) -> Expr>(p: GuardPattern, f: &mut F) -> GuardPattern {
    match p {
        GuardPattern::Boolean(e) => GuardPattern::Boolean(Box::new(fold_expr(*e, f))),
        GuardPattern::Pattern(b, e) => GuardPattern::Pattern(b, Box::new(fold_expr(*e, f))),
    }
}

fn fold_let_binding<F: FnMut(Expr) -> Expr>(b: LetBinding, f: &mut F) -> LetBinding {
    match b {
        LetBinding::Value { span, binder, expr } => LetBinding::Value {
            span,
            binder,
            expr: fold_expr(expr, f),
        },
        sig @ LetBinding::Signature { .. } => sig,
    }
}

fn fold_do_stmt<F: FnMut(Expr) -> Expr>(s: DoStatement, f: &mut F) -> DoStatement {
    match s {
        DoStatement::Bind { span, binder, expr } => DoStatement::Bind {
            span,
            binder,
            expr: fold_expr(expr, f),
        },
        DoStatement::Let { span, bindings } => DoStatement::Let {
            span,
            bindings: bindings.into_iter().map(|b| fold_let_binding(b, f)).collect(),
        },
        DoStatement::Discard { span, expr } => DoStatement::Discard {
            span,
            expr: fold_expr(expr, f),
        },
    }
}

fn fold_record_field<F: FnMut(Expr) -> Expr>(r: RecordField, f: &mut F) -> RecordField {
    RecordField {
        span: r.span,
        label: r.label,
        value: r.value.map(|e| fold_expr(e, f)),
        type_ann: r.type_ann,
        is_update: r.is_update,
        is_nested: r.is_nested,
    }
}

fn fold_record_update<F: FnMut(Expr) -> Expr>(u: RecordUpdate, f: &mut F) -> RecordUpdate {
    RecordUpdate {
        span: u.span,
        label: u.label,
        value: fold_expr(u.value, f),
    }
}

/// Walk every top-level expression position inside a declaration and map it
/// through `f`. Most desugar transforms target expressions, and this saves
/// each one from writing its own decl-shape boilerplate.
pub fn fold_decl_exprs<F: FnMut(Expr) -> Expr>(
    d: crate::cst::Decl,
    f: &mut F,
) -> crate::cst::Decl {
    use crate::cst::Decl;
    match d {
        Decl::Value { name, binders, guarded, where_clause, span, doc_comments } => {
            Decl::Value {
                name,
                binders,
                guarded: fold_guarded(guarded, f),
                where_clause: where_clause
                    .into_iter()
                    .map(|b| fold_let_binding(b, f))
                    .collect(),
                span,
                doc_comments,
            }
        }
        other => other,
    }
}
