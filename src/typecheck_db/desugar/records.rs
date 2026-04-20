//! MDb sub-transform: record literals with wildcard fields → lambda.
//!
//! `{ x: _, y: 1 }` becomes `\a -> { x: a, y: 1 }`. Two wildcards in the
//! literal produce a two-arg lambda, filled left-to-right in source order.
//!
//! Fields with `value = None` are puns (`{ x }`) — those resolve to a
//! same-named variable, not a wildcard, and we leave them alone. We also
//! leave record-update literals alone: this transform only rewrites
//! record-*literal* fields (`is_update == false`).

use crate::cst::{Binder, Expr, RecordField, Spanned};
use crate::names::value_name;

use super::walk::fold_decl_exprs;

pub fn desugar_decl(decl: crate::cst::Decl) -> crate::cst::Decl {
    let mut counter: u32 = 0;
    fold_decl_exprs(decl, &mut |node| rewrite_node(node, &mut counter))
}

fn rewrite_node(e: Expr, counter: &mut u32) -> Expr {
    match e {
        // `{ x: _, y: 1 }` → `\a -> { x: a, y: 1 }`. Only applies
        // to record *literals* (no `is_update` fields). Leaving
        // record-update records alone here lets the
        // `App(r, Record{is_update})` case at the outer level
        // wrap the whole thing in a lambda together.
        Expr::Record { span, fields } if fields.iter().all(|f| !f.is_update) => {
            let has_hole = fields.iter().any(|f| {
                matches!(f.value.as_ref(), Some(Expr::Wildcard { .. }))
            });
            if !has_hole {
                return Expr::Record { span, fields };
            }
            let mut params: Vec<Binder> = Vec::new();
            let new_fields: Vec<RecordField> = fields
                .into_iter()
                .map(|f| swap_field_wildcard(f, counter, &mut params))
                .collect();
            Expr::Lambda {
                span,
                binders: params,
                body: Box::new(Expr::Record { span, fields: new_fields }),
            }
        }
        // `record { field = _ }` parses as `App(record, Record
        // { fields: [{is_update: true, value: Wildcard}] })`.
        // Wrap in a lambda that binds each wildcard to a fresh
        // param, keeping the underlying `App(record, Record)`
        // shape so downstream inference still recognises it as
        // a record update.
        //
        // `_ { field = v }` adds the outer wildcard as an extra
        // lambda binder (first position).
        Expr::App { span, func, arg }
            if matches!(
                arg.as_ref(),
                Expr::Record { fields, .. }
                    if !fields.is_empty() && fields.iter().all(|f| f.is_update)
            ) =>
        {
            let (record_expr_fields, record_span) = match *arg {
                Expr::Record { span, fields } => (fields, span),
                _ => unreachable!(),
            };
            let any_field_hole = record_expr_fields.iter().any(|f| {
                matches!(f.value.as_ref(), Some(Expr::Wildcard { .. }))
            });
            let outer_wildcard = matches!(func.as_ref(), Expr::Wildcard { .. });
            if !any_field_hole && !outer_wildcard {
                // Nothing to desugar — rebuild unchanged.
                return Expr::App {
                    span,
                    func,
                    arg: Box::new(Expr::Record {
                        span: record_span,
                        fields: record_expr_fields,
                    }),
                };
            }
            let mut params: Vec<Binder> = Vec::new();
            let new_func: Box<Expr> = if outer_wildcard {
                let wspan = match func.as_ref() {
                    Expr::Wildcard { span } => *span,
                    _ => span,
                };
                let name = value_name(&format!("$rec_{}", counter));
                *counter += 1;
                params.push(Binder::Var {
                    span: wspan,
                    name: Spanned { span: wspan, value: name.clone() },
                });
                Box::new(Expr::Var {
                    span: wspan,
                    name: crate::names::Qualified::unqualified(name),
                })
            } else {
                func
            };
            let new_fields: Vec<RecordField> = record_expr_fields
                .into_iter()
                .map(|f| swap_field_wildcard(f, counter, &mut params))
                .collect();
            let new_record = Expr::Record { span: record_span, fields: new_fields };
            Expr::Lambda {
                span,
                binders: params,
                body: Box::new(Expr::App {
                    span,
                    func: new_func,
                    arg: Box::new(new_record),
                }),
            }
        }
        other => other,
    }
}

fn swap_field_wildcard(
    f: RecordField,
    counter: &mut u32,
    params: &mut Vec<Binder>,
) -> RecordField {
    let RecordField { span, label, value, type_ann, is_update, is_nested } = f;
    let new_value = match value {
        Some(Expr::Wildcard { span: wspan }) => {
            let name = value_name(&format!("$rec_{}", counter));
            *counter += 1;
            params.push(Binder::Var {
                span: wspan,
                name: Spanned { span: wspan, value: name.clone() },
            });
            Some(Expr::Var {
                span: wspan,
                name: crate::names::Qualified::unqualified(name),
            })
        }
        other => other,
    };
    RecordField { span, label, value: new_value, type_ann, is_update, is_nested }
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
    fn single_wildcard_field_becomes_lambda() {
        let d = first_decl("module M where\nr = { x: _, y: 1 }\n");
        assert_eq!(count_wildcards(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_wildcards(&d2), 0);
        assert!(count_lambdas(&d2) >= 1);
    }

    #[test]
    fn two_wildcards_become_two_arg_lambda() {
        let d = first_decl("module M where\nr = { x: _, y: _ }\n");
        assert_eq!(count_wildcards(&d), 2);
        let d2 = desugar_decl(d);
        assert_eq!(count_wildcards(&d2), 0);
        // The resulting Lambda should have 2 binders.
        if let Decl::Value { guarded: crate::cst::GuardedExpr::Unconditional(e), .. } = &d2 {
            if let Expr::Lambda { binders, .. } = e.as_ref() {
                assert_eq!(binders.len(), 2);
                return;
            }
        }
        panic!("expected a Lambda with 2 binders, got {:?}", d2);
    }

    #[test]
    fn literal_without_wildcard_is_untouched() {
        let d = first_decl("module M where\nr = { x: 1, y: 2 }\n");
        let d2 = desugar_decl(d.clone());
        assert_eq!(d, d2);
    }

    #[test]
    fn idempotent() {
        let d = first_decl("module M where\nr = { x: _ }\n");
        let d1 = desugar_decl(d);
        let d2 = desugar_decl(d1.clone());
        assert_eq!(d1, d2);
    }
}
