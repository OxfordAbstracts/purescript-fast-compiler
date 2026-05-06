//! CST → IR lowering.
//!
//! The input [`crate::cst::Module`] has already been through the
//! desugar pipeline (parser → multi-equation merge → record
//! desugar → do/ado pre-pass → operator rebracketing). After
//! rebracketing, an operator expression `x + y` should exist only
//! as `App(App(Var(add), x), y)`, not as `Op { … }`. This pass
//! enforces that by converting CST nodes into [`super::Expr`] /
//! [`super::Binder`] — IR variants that simply don't include
//! operator shapes. Any residual `Expr::Op` / `Expr::OpParens` /
//! `Expr::BacktickApp` / `Binder::Op` in the input is reported as
//! a [`LoweringError`] instead of silently passed through.

use crate::cst::{self, DataMembers};
use crate::names::{value_name, Qualified};
use crate::span::Span;

use super::binder::{Binder, RecordBinderField};
use super::decl::{
    CaseAlternative, Decl, DoStatement, Guard, GuardPattern, GuardedExpr, LetBinding, Module,
};
use super::expr::{Expr, Literal, RecordField, RecordUpdate};

fn op_name_string(
    op: &crate::cst::Spanned<crate::names::Qualified<crate::names::OpName>>,
) -> String {
    crate::interner::resolve(op.value.name.symbol()).unwrap_or_default()
}

fn lower_literal(lit: cst::Literal) -> Result<Literal, LoweringError> {
    Ok(match lit {
        cst::Literal::Int(i) => Literal::Int(i),
        cst::Literal::Float(f) => Literal::Float(f),
        cst::Literal::String(s) => Literal::String(s),
        cst::Literal::Char(c) => Literal::Char(c),
        cst::Literal::Boolean(b) => Literal::Boolean(b),
        cst::Literal::Array(elements) => Literal::Array(
            elements.into_iter().map(lower_expr).collect::<Result<_, _>>()?,
        ),
    })
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweringError {
    /// An `Expr::Op` / `Expr::OpParens` / `Expr::BacktickApp`
    /// survived desugar. Indicates the upstream rebracketer failed
    /// (missing fixity, unusual shape) — would be
    /// `InferError::Unsupported("operator")` at the call site.
    ResidualOperator { span: Span, op: String },
    /// A `Binder::Op` survived desugar. Same root cause.
    ResidualBinderOperator { span: Span, op: String },
    /// A `DataMembers::Explicit` list was encountered at a position
    /// it shouldn't be — surfaces a parser invariant violation
    /// cleanly instead of panicking downstream.
    MalformedDataMembers { span: Span },
}

pub fn lower_module(module: cst::Module) -> Result<Module, LoweringError> {
    let decls = module
        .decls
        .into_iter()
        .map(lower_decl)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Module {
        span: module.span,
        name: module.name,
        exports: module.exports,
        imports: module.imports,
        decls,
        comments: module.comments,
        doc_comments: module.doc_comments,
    })
}

pub fn lower_decl(decl: cst::Decl) -> Result<Decl, LoweringError> {
    Ok(match decl {
        cst::Decl::Value { span, name, binders, guarded, where_clause, doc_comments } => {
            Decl::Value {
                span,
                name,
                binders: lower_binders(binders)?,
                guarded: lower_guarded(guarded)?,
                where_clause: where_clause
                    .into_iter()
                    .map(lower_let_binding)
                    .collect::<Result<_, _>>()?,
                doc_comments,
            }
        }
        cst::Decl::TypeSignature { span, name, ty, doc_comments } => {
            Decl::TypeSignature { span, name, ty, doc_comments }
        }
        cst::Decl::Data {
            span, name, type_vars, constructors, kind_sig, is_role_decl, kind_type,
            type_var_kind_anns, doc_comments,
        } => Decl::Data {
            span, name, type_vars, constructors, kind_sig, is_role_decl, kind_type,
            type_var_kind_anns, doc_comments,
        },
        cst::Decl::TypeAlias { span, name, type_vars, ty, type_var_kind_anns, doc_comments } => {
            Decl::TypeAlias { span, name, type_vars, ty, type_var_kind_anns, doc_comments }
        }
        cst::Decl::Newtype {
            span, name, type_vars, constructor, ty, type_var_kind_anns, doc_comments,
        } => Decl::Newtype {
            span, name, type_vars, constructor, ty, type_var_kind_anns, doc_comments,
        },
        cst::Decl::Class {
            span, constraints, name, type_vars, fundeps, members, is_kind_sig, kind_type,
            type_var_kind_anns, doc_comments,
        } => Decl::Class {
            span, constraints, name, type_vars, fundeps, members, is_kind_sig, kind_type,
            type_var_kind_anns, doc_comments,
        },
        cst::Decl::Instance {
            span, name, constraints, class_name, types, members, chain, doc_comments,
        } => Decl::Instance {
            span, name, constraints, class_name, types,
            members: members.into_iter().map(lower_decl).collect::<Result<_, _>>()?,
            chain, doc_comments,
        },
        cst::Decl::Fixity {
            span, associativity, precedence, target, operator, is_type, doc_comments,
        } => Decl::Fixity {
            span, associativity, precedence, target, operator, is_type, doc_comments,
        },
        cst::Decl::Foreign { span, name, ty, doc_comments } => {
            Decl::Foreign { span, name, ty, doc_comments }
        }
        cst::Decl::ForeignData { span, name, kind, doc_comments } => {
            Decl::ForeignData { span, name, kind, doc_comments }
        }
        cst::Decl::Derive {
            span, newtype, name, constraints, class_name, types, doc_comments,
        } => Decl::Derive {
            span, newtype, name, constraints, class_name, types, doc_comments,
        },
    })
}

fn lower_guarded(guarded: cst::GuardedExpr) -> Result<GuardedExpr, LoweringError> {
    Ok(match guarded {
        cst::GuardedExpr::Unconditional(e) => {
            GuardedExpr::Unconditional(Box::new(lower_expr(*e)?))
        }
        cst::GuardedExpr::Guarded(gs) => {
            let gs = gs
                .into_iter()
                .map(|g| {
                    let patterns = g
                        .patterns
                        .into_iter()
                        .map(lower_guard_pattern)
                        .collect::<Result<_, _>>()?;
                    let expr = Box::new(lower_expr(*g.expr)?);
                    Ok(Guard { span: g.span, patterns, expr })
                })
                .collect::<Result<_, _>>()?;
            GuardedExpr::Guarded(gs)
        }
    })
}

fn lower_guard_pattern(gp: cst::GuardPattern) -> Result<GuardPattern, LoweringError> {
    Ok(match gp {
        cst::GuardPattern::Boolean(e) => GuardPattern::Boolean(Box::new(lower_expr(*e)?)),
        cst::GuardPattern::Pattern(b, e) => {
            GuardPattern::Pattern(lower_binder(b)?, Box::new(lower_expr(*e)?))
        }
    })
}

fn lower_binders(bs: Vec<cst::Binder>) -> Result<Vec<Binder>, LoweringError> {
    bs.into_iter().map(lower_binder).collect()
}

pub fn lower_binder(binder: cst::Binder) -> Result<Binder, LoweringError> {
    Ok(match binder {
        cst::Binder::Wildcard { span } => Binder::Wildcard { span },
        cst::Binder::Var { span, name } => Binder::Var { span, name },
        cst::Binder::Literal { span, lit } => Binder::Literal { span, lit: lower_literal(lit)? },
        cst::Binder::Constructor { span, name, args } => Binder::Constructor {
            span,
            name,
            args: lower_binders(args)?,
        },
        cst::Binder::Record { span, fields } => {
            let fields = fields
                .into_iter()
                .map(|f| {
                    Ok(RecordBinderField {
                        span: f.span,
                        label: f.label,
                        binder: f.binder.map(lower_binder).transpose()?,
                    })
                })
                .collect::<Result<_, LoweringError>>()?;
            Binder::Record { span, fields }
        }
        cst::Binder::As { span, name, binder } => Binder::As {
            span,
            name,
            binder: Box::new(lower_binder(*binder)?),
        },
        cst::Binder::Parens { span, binder } => Binder::Parens {
            span,
            binder: Box::new(lower_binder(*binder)?),
        },
        cst::Binder::Array { span, elements } => Binder::Array {
            span,
            elements: lower_binders(elements)?,
        },
        cst::Binder::Op { span, op, .. } => {
            // Desugar is responsible for converting every
            // `Binder::Op` into a `Binder::Constructor` via
            // `rebracket::rewrite_binder`. Reaching here means
            // that pass was skipped or the parser emitted a
            // shape it doesn't handle.
            return Err(LoweringError::ResidualBinderOperator {
                span,
                op: crate::interner::resolve(op.value.name.symbol())
                    .unwrap_or_default(),
            });
        }
        cst::Binder::Typed { span, binder, ty } => Binder::Typed {
            span,
            binder: Box::new(lower_binder(*binder)?),
            ty,
        },
    })
}

pub fn lower_expr(expr: cst::Expr) -> Result<Expr, LoweringError> {
    Ok(match expr {
        cst::Expr::Var { span, name } => Expr::Var { span, name },
        cst::Expr::Constructor { span, name } => Expr::Constructor { span, name },
        cst::Expr::Literal { span, lit } => Expr::Literal { span, lit: lower_literal(lit)? },
        cst::Expr::App { span, func, arg } => Expr::App {
            span,
            func: Box::new(lower_expr(*func)?),
            arg: Box::new(lower_expr(*arg)?),
        },
        cst::Expr::VisibleTypeApp { span, func, ty } => Expr::VisibleTypeApp {
            span,
            func: Box::new(lower_expr(*func)?),
            ty,
        },
        cst::Expr::Lambda { span, binders, body } => Expr::Lambda {
            span,
            binders: lower_binders(binders)?,
            body: Box::new(lower_expr(*body)?),
        },
        cst::Expr::Op { span, op, .. } => {
            // Desugar is responsible for rewriting every `Op`
            // chain to `App`s via `rebracket::rewrite_expr`. If
            // one survived, the pipeline is mis-configured —
            // surface a clear error instead of silently synth'ing
            // a `Var` lookup that would shadow the real problem.
            return Err(LoweringError::ResidualOperator { span, op: op_name_string(&op) });
        }
        cst::Expr::OpParens { span, op } => {
            return Err(LoweringError::ResidualOperator { span, op: op_name_string(&op) });
        }
        cst::Expr::BacktickApp { span, func, .. } => {
            // Backticks are also the rebracketer's responsibility
            // — they flatten into the same operator chain as
            // named operators. Seeing one here means we skipped
            // desugar or the rebracket walker missed a branch.
            return Err(LoweringError::ResidualOperator {
                span,
                op: match &*func {
                    cst::Expr::Var { name, .. } => {
                        crate::interner::resolve(name.name.symbol())
                            .unwrap_or_default()
                    }
                    _ => "<backtick>".to_string(),
                },
            });
        }
        cst::Expr::If { span, cond, then_expr, else_expr } => Expr::If {
            span,
            cond: Box::new(lower_expr(*cond)?),
            then_expr: Box::new(lower_expr(*then_expr)?),
            else_expr: Box::new(lower_expr(*else_expr)?),
        },
        cst::Expr::Case { span, exprs, alts } => {
            let exprs = exprs.into_iter().map(lower_expr).collect::<Result<_, _>>()?;
            let alts = alts
                .into_iter()
                .map(|a| {
                    Ok(CaseAlternative {
                        span: a.span,
                        binders: lower_binders(a.binders)?,
                        result: lower_guarded(a.result)?,
                    })
                })
                .collect::<Result<_, LoweringError>>()?;
            Expr::Case { span, exprs, alts }
        }
        cst::Expr::Let { span, bindings, body } => Expr::Let {
            span,
            bindings: bindings.into_iter().map(lower_let_binding).collect::<Result<_, _>>()?,
            body: Box::new(lower_expr(*body)?),
            is_where: false,
        },
        cst::Expr::Do { span, module, statements } => Expr::Do {
            span,
            module,
            statements: statements
                .into_iter()
                .map(lower_do_statement)
                .collect::<Result<_, _>>()?,
        },
        cst::Expr::Ado { span, module, statements, result } => Expr::Ado {
            span,
            module,
            statements: statements
                .into_iter()
                .map(lower_do_statement)
                .collect::<Result<_, _>>()?,
            result: Box::new(lower_expr(*result)?),
        },
        cst::Expr::Record { span, fields } => Expr::Record {
            span,
            fields: fields
                .into_iter()
                .map(|f| {
                    Ok(RecordField {
                        span: f.span,
                        label: f.label,
                        value: f.value.map(lower_expr).transpose()?,
                        type_ann: f.type_ann,
                        is_update: f.is_update,
                        is_nested: f.is_nested,
                    })
                })
                .collect::<Result<_, LoweringError>>()?,
        },
        cst::Expr::RecordAccess { span, expr, field } => Expr::RecordAccess {
            span,
            expr: Box::new(lower_expr(*expr)?),
            field,
        },
        cst::Expr::RecordUpdate { span, expr, updates } => {
            let updates = updates
                .into_iter()
                .map(|u| Ok(RecordUpdate { span: u.span, label: u.label, value: lower_expr(u.value)? }))
                .collect::<Result<_, LoweringError>>()?;
            Expr::RecordUpdate { span, expr: Box::new(lower_expr(*expr)?), updates }
        }
        cst::Expr::Parens { span, expr } => Expr::Parens {
            span,
            expr: Box::new(lower_expr(*expr)?),
        },
        cst::Expr::TypeAnnotation { span, expr, ty } => Expr::TypeAnnotation {
            span,
            expr: Box::new(lower_expr(*expr)?),
            ty,
        },
        cst::Expr::Wildcard { span } => Expr::Wildcard { span },
        cst::Expr::Hole { span, name } => Expr::Hole { span, name },
        cst::Expr::Array { span, elements } => Expr::Array {
            span,
            elements: elements
                .into_iter()
                .map(lower_expr)
                .collect::<Result<_, _>>()?,
        },
        cst::Expr::Negate { span, expr } => Expr::Negate {
            span,
            expr: Box::new(lower_expr(*expr)?),
        },
        cst::Expr::AsPattern { span, name, pattern } => Expr::AsPattern {
            span,
            name: Box::new(lower_expr(*name)?),
            pattern: Box::new(lower_expr(*pattern)?),
        },
    })
}

fn lower_let_binding(lb: cst::LetBinding) -> Result<LetBinding, LoweringError> {
    Ok(match lb {
        cst::LetBinding::Value { span, binder, expr } => LetBinding::Value {
            span,
            binder: lower_binder(binder)?,
            expr: lower_expr(expr)?,
        },
        cst::LetBinding::Signature { span, name, ty } => {
            LetBinding::Signature { span, name, ty }
        }
    })
}

fn lower_do_statement(s: cst::DoStatement) -> Result<DoStatement, LoweringError> {
    Ok(match s {
        cst::DoStatement::Bind { span, binder, expr } => DoStatement::Bind {
            span,
            binder: lower_binder(binder)?,
            expr: lower_expr(expr)?,
        },
        cst::DoStatement::Let { span, bindings } => DoStatement::Let {
            span,
            bindings: bindings
                .into_iter()
                .map(lower_let_binding)
                .collect::<Result<_, _>>()?,
        },
        cst::DoStatement::Discard { span, expr } => DoStatement::Discard {
            span,
            expr: lower_expr(expr)?,
        },
    })
}

// Silence `DataMembers` / `value_name` / `Qualified` "unused" if
// consumers don't touch them yet.
#[allow(dead_code)]
fn _touch(_: DataMembers, _: Qualified<()>) {}

#[allow(dead_code)]
fn _touch_value_name(s: &str) -> crate::names::ValueName {
    value_name(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn first_expr(src: &str) -> cst::Expr {
        let m = parse(src).unwrap();
        let d = m.decls.into_iter().find_map(|d| match d {
            cst::Decl::Value { guarded, .. } => Some(guarded),
            _ => None,
        })
        .expect("value decl");
        match d {
            cst::GuardedExpr::Unconditional(e) => *e,
            _ => panic!("expected unconditional body"),
        }
    }

    #[test]
    fn lower_simple_app_roundtrips() {
        let e = first_expr("module M where\nf = g 1\n");
        let ir = lower_expr(e).unwrap();
        assert!(matches!(ir, Expr::App { .. }));
    }

    #[test]
    fn lower_record_literal() {
        let e = first_expr("module M where\nf = { a: 1, b: 2 }\n");
        let ir = lower_expr(e).unwrap();
        if let Expr::Record { fields, .. } = ir {
            assert_eq!(fields.len(), 2);
            assert!(fields.iter().all(|f| !f.is_update));
        } else {
            panic!("expected record");
        }
    }

    #[test]
    fn lower_case_expression() {
        let e = first_expr(
            "\
module M where
f x = case x of
  0 -> 1
  _ -> 2
",
        );
        let ir = lower_expr(e).unwrap();
        assert!(matches!(ir, Expr::Case { .. }));
    }

    #[test]
    fn residual_op_is_a_hard_error() {
        // Desugar owns operator elimination end-to-end. Reaching
        // the IR lowering with a surviving `Expr::Op` means the
        // pipeline is mis-configured — surface it as
        // `LoweringError::ResidualOperator` so callers can see the
        // exact span and operator name rather than silently
        // fabricating a `Var` lookup.
        use crate::cst::Spanned;
        use crate::interner::intern;
        use crate::names::Qualified;
        let span = crate::span::Span::new(0, 0);
        let op_sym = intern("+");
        let op_name = crate::names::OpName::new(op_sym);
        let op = Spanned::new(Qualified::unqualified(op_name), span);
        let input = cst::Expr::Op {
            span,
            left: Box::new(cst::Expr::Wildcard { span }),
            op,
            right: Box::new(cst::Expr::Wildcard { span }),
        };
        match lower_expr(input) {
            Err(LoweringError::ResidualOperator { op, .. }) => assert_eq!(op, "+"),
            other => panic!("expected ResidualOperator, got {other:?}"),
        }
    }
}
