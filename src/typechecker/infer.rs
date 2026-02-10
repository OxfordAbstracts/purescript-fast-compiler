use std::collections::HashMap;

use crate::cst::{Binder, Expr, LetBinding, Literal};
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::{Scheme, TyVarId, Type};
use crate::typechecker::unify::UnifyState;

/// The inference context, holding mutable unification state.
pub struct InferCtx {
    pub state: UnifyState,
}

impl InferCtx {
    pub fn new() -> Self {
        InferCtx {
            state: UnifyState::new(),
        }
    }

    /// Infer the type of an expression in the given environment.
    pub fn infer(&mut self, env: &Env, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Literal { span, lit } => self.infer_literal(*span, lit),
            Expr::Var { span, name } => self.infer_var(env, *span, name),
            Expr::Lambda { span, binders, body } => {
                self.infer_lambda(env, *span, binders, body)
            }
            Expr::App { span, func, arg } => self.infer_app(env, *span, func, arg),
            Expr::If {
                span,
                cond,
                then_expr,
                else_expr,
            } => self.infer_if(env, *span, cond, then_expr, else_expr),
            Expr::Let {
                span,
                bindings,
                body,
            } => self.infer_let(env, *span, bindings, body),
            Expr::TypeAnnotation { span, expr, ty } => {
                self.infer_annotation(env, *span, expr, ty)
            }
            Expr::Parens { expr, .. } => self.infer(env, expr),
            Expr::Negate { span, expr } => self.infer_negate(env, *span, expr),
            other => Err(TypeError::NotImplemented {
                span: other.span(),
                feature: format!("inference for this expression form"),
            }),
        }
    }

    fn infer_literal(
        &mut self,
        span: crate::ast::span::Span,
        lit: &Literal,
    ) -> Result<Type, TypeError> {
        Ok(match lit {
            Literal::Int(_) => Type::int(),
            Literal::Float(_) => Type::float(),
            Literal::String(_) => Type::string(),
            Literal::Char(_) => Type::char(),
            Literal::Boolean(_) => Type::boolean(),
            Literal::Array(_) => {
                return Err(TypeError::NotImplemented {
                    span,
                    feature: "array literal inference".to_string(),
                })
            }
        })
    }

    fn infer_var(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        name: &crate::cst::QualifiedIdent,
    ) -> Result<Type, TypeError> {
        match env.lookup(name.name) {
            Some(scheme) => Ok(self.instantiate(scheme)),
            None => Err(TypeError::UndefinedVariable {
                span,
                name: name.name,
            }),
        }
    }

    /// Instantiate a type scheme: replace each quantified variable with a fresh unification variable.
    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        if scheme.forall_vars.is_empty() {
            return scheme.ty.clone();
        }
        let subst: HashMap<TyVarId, Type> = scheme
            .forall_vars
            .iter()
            .map(|&v| (v, Type::Unif(self.state.fresh_var())))
            .collect();
        self.apply_subst(&subst, &scheme.ty)
    }

    /// Apply a substitution (mapping old TyVarIds to new Types) to a type.
    fn apply_subst(&self, subst: &HashMap<TyVarId, Type>, ty: &Type) -> Type {
        match ty {
            Type::Unif(v) => match subst.get(v) {
                Some(replacement) => replacement.clone(),
                None => ty.clone(),
            },
            Type::Fun(from, to) => {
                Type::fun(self.apply_subst(subst, from), self.apply_subst(subst, to))
            }
            Type::App(f, a) => {
                Type::app(self.apply_subst(subst, f), self.apply_subst(subst, a))
            }
            Type::Forall(vars, body) => {
                Type::Forall(vars.clone(), Box::new(self.apply_subst(subst, body)))
            }
            Type::Con(_) | Type::Var(_) => ty.clone(),
        }
    }

    fn infer_lambda(
        &mut self,
        env: &Env,
        _span: crate::ast::span::Span,
        binders: &[Binder],
        body: &Expr,
    ) -> Result<Type, TypeError> {
        let mut current_env = env.child();
        let mut param_types = Vec::new();

        for binder in binders {
            match binder {
                Binder::Var { name, .. } => {
                    let param_ty = Type::Unif(self.state.fresh_var());
                    current_env.insert_mono(name.value, param_ty.clone());
                    param_types.push(param_ty);
                }
                Binder::Wildcard { .. } => {
                    let param_ty = Type::Unif(self.state.fresh_var());
                    param_types.push(param_ty);
                }
                other => {
                    return Err(TypeError::NotImplemented {
                        span: other.span(),
                        feature: "complex binder in lambda".to_string(),
                    })
                }
            }
        }

        let body_ty = self.infer(&current_env, body)?;

        // Build the function type right-to-left: t1 -> t2 -> ... -> body_ty
        let mut result = body_ty;
        for param_ty in param_types.into_iter().rev() {
            result = Type::fun(param_ty, result);
        }
        Ok(result)
    }

    fn infer_app(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        func: &Expr,
        arg: &Expr,
    ) -> Result<Type, TypeError> {
        let func_ty = self.infer(env, func)?;
        let arg_ty = self.infer(env, arg)?;
        let result_ty = Type::Unif(self.state.fresh_var());

        let expected_func_ty = Type::fun(arg_ty, result_ty.clone());
        self.state.unify(span, &func_ty, &expected_func_ty)?;

        Ok(result_ty)
    }

    fn infer_if(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        cond: &Expr,
        then_expr: &Expr,
        else_expr: &Expr,
    ) -> Result<Type, TypeError> {
        let cond_ty = self.infer(env, cond)?;
        self.state.unify(cond.span(), &cond_ty, &Type::boolean())?;

        let then_ty = self.infer(env, then_expr)?;
        let else_ty = self.infer(env, else_expr)?;
        self.state.unify(span, &then_ty, &else_ty)?;

        Ok(then_ty)
    }

    fn infer_let(
        &mut self,
        env: &Env,
        _span: crate::ast::span::Span,
        bindings: &[LetBinding],
        body: &Expr,
    ) -> Result<Type, TypeError> {
        let mut current_env = env.child();

        for binding in bindings {
            match binding {
                LetBinding::Value { binder, expr, .. } => match binder {
                    Binder::Var { name, .. } => {
                        let binding_ty = self.infer(&current_env, expr)?;
                        let scheme = current_env.generalize(&mut self.state, binding_ty);
                        current_env.insert_scheme(name.value, scheme);
                    }
                    _ => {
                        // For non-variable binders, just infer without generalizing
                        let _ = self.infer(&current_env, expr)?;
                    }
                },
                LetBinding::Signature { .. } => {
                    // Type signatures in let — skip for scaffolding
                }
            }
        }

        self.infer(&current_env, body)
    }

    fn infer_annotation(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        expr: &Expr,
        ty_expr: &crate::cst::TypeExpr,
    ) -> Result<Type, TypeError> {
        let inferred = self.infer(env, expr)?;
        let annotated = convert_type_expr(ty_expr)?;
        self.state.unify(span, &inferred, &annotated)?;
        Ok(annotated)
    }

    fn infer_negate(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        expr: &Expr,
    ) -> Result<Type, TypeError> {
        let ty = self.infer(env, expr)?;
        self.state.unify(span, &ty, &Type::int())?;
        Ok(ty)
    }
}
