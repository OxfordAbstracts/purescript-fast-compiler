use std::collections::HashMap;

use crate::cst::{Binder, Expr, GuardedExpr, GuardPattern, LetBinding, Literal};
use crate::interner::Symbol;
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
            Expr::Constructor { span, name } => self.infer_var(env, *span, name),
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
            Expr::Op { span, left, op, right } => self.infer_op(env, *span, left, op, right),
            Expr::OpParens { span, op } => self.infer_op_parens(env, *span, op),
            Expr::Case { span, exprs, alts } => self.infer_case(env, *span, exprs, alts),
            Expr::Array { span, elements } => self.infer_array(env, *span, elements),
            Expr::Hole { span, name } => self.infer_hole(*span, *name),
            other => Err(TypeError::NotImplemented {
                span: other.span(),
                feature: format!("inference for this expression form"),
            }),
        }
    }

    fn infer_literal(
        &mut self,
        _span: crate::ast::span::Span,
        lit: &Literal,
    ) -> Result<Type, TypeError> {
        Ok(match lit {
            Literal::Int(_) => Type::int(),
            Literal::Float(_) => Type::float(),
            Literal::String(_) => Type::string(),
            Literal::Char(_) => Type::char(),
            Literal::Boolean(_) => Type::boolean(),
            Literal::Array(elems) => {
                let elem_ty = Type::Unif(self.state.fresh_var());
                // We can't infer element types here since we don't have env access;
                // array literal inference is handled in infer_array instead
                if elems.is_empty() {
                    Type::array(elem_ty)
                } else {
                    Type::array(elem_ty)
                }
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
            Some(scheme) => {
                let ty = self.instantiate(scheme);
                // If the scheme's type is a Forall, also instantiate that
                self.instantiate_forall_type(ty)
            }
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

    /// Instantiate a Type::Forall by replacing named Type::Var with fresh unification variables.
    /// This is used for data constructor types which are stored as Type::Forall(symbols, body).
    pub fn instantiate_forall_type(&mut self, ty: Type) -> Result<Type, TypeError> {
        match ty {
            Type::Forall(vars, body) => {
                let subst: HashMap<Symbol, Type> = vars
                    .iter()
                    .map(|&v| (v, Type::Unif(self.state.fresh_var())))
                    .collect();
                Ok(self.apply_symbol_subst(&subst, &body))
            }
            other => Ok(other),
        }
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

    /// Apply a substitution mapping Symbol names to Types (for forall instantiation).
    fn apply_symbol_subst(&self, subst: &HashMap<Symbol, Type>, ty: &Type) -> Type {
        match ty {
            Type::Var(sym) => match subst.get(sym) {
                Some(replacement) => replacement.clone(),
                None => ty.clone(),
            },
            Type::Fun(from, to) => {
                Type::fun(
                    self.apply_symbol_subst(subst, from),
                    self.apply_symbol_subst(subst, to),
                )
            }
            Type::App(f, a) => {
                Type::app(
                    self.apply_symbol_subst(subst, f),
                    self.apply_symbol_subst(subst, a),
                )
            }
            Type::Forall(vars, body) => {
                // Don't substitute variables that are rebound by this forall
                let mut inner_subst = subst.clone();
                for v in vars {
                    inner_subst.remove(v);
                }
                Type::Forall(vars.clone(), Box::new(self.apply_symbol_subst(&inner_subst, body)))
            }
            Type::Con(_) | Type::Unif(_) => ty.clone(),
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
            let param_ty = Type::Unif(self.state.fresh_var());
            self.infer_binder(&mut current_env, binder, &param_ty)?;
            param_types.push(param_ty);
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
        self.process_let_bindings(&mut current_env, bindings)?;
        self.infer(&current_env, body)
    }

    /// Process let bindings, adding them to the environment.
    /// Shared between let-expressions and where-clauses.
    pub fn process_let_bindings(
        &mut self,
        env: &mut Env,
        bindings: &[LetBinding],
    ) -> Result<(), TypeError> {
        for binding in bindings {
            match binding {
                LetBinding::Value { binder, expr, .. } => match binder {
                    Binder::Var { name, .. } => {
                        let binding_ty = self.infer(env, expr)?;
                        let scheme = env.generalize(&mut self.state, binding_ty);
                        env.insert_scheme(name.value, scheme);
                    }
                    _ => {
                        let _ = self.infer(env, expr)?;
                    }
                },
                LetBinding::Signature { .. } => {
                    // Type signatures in let — skip for now
                }
            }
        }
        Ok(())
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

    fn infer_op(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        left: &Expr,
        op: &crate::cst::Spanned<crate::cst::QualifiedIdent>,
        right: &Expr,
    ) -> Result<Type, TypeError> {
        // Treat `left op right` as `(op left) right`
        let op_ty = match env.lookup(op.value.name) {
            Some(scheme) => {
                let ty = self.instantiate(scheme);
                self.instantiate_forall_type(ty)?
            }
            None => {
                return Err(TypeError::UndefinedVariable {
                    span: op.span,
                    name: op.value.name,
                });
            }
        };

        let left_ty = self.infer(env, left)?;
        let right_ty = self.infer(env, right)?;

        let intermediate_ty = Type::Unif(self.state.fresh_var());
        let result_ty = Type::Unif(self.state.fresh_var());

        // op : left_ty -> intermediate_ty
        self.state
            .unify(span, &op_ty, &Type::fun(left_ty, intermediate_ty.clone()))?;
        // intermediate : right_ty -> result_ty
        self.state
            .unify(span, &intermediate_ty, &Type::fun(right_ty, result_ty.clone()))?;

        Ok(result_ty)
    }

    fn infer_op_parens(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        op: &crate::cst::Spanned<crate::cst::QualifiedIdent>,
    ) -> Result<Type, TypeError> {
        match env.lookup(op.value.name) {
            Some(scheme) => {
                let ty = self.instantiate(scheme);
                self.instantiate_forall_type(ty)
            }
            None => Err(TypeError::UndefinedVariable {
                span,
                name: op.value.name,
            }),
        }
    }

    fn infer_case(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        exprs: &[Expr],
        alts: &[crate::cst::CaseAlternative],
    ) -> Result<Type, TypeError> {
        // Infer types of scrutinees
        let scrutinee_types: Vec<Type> = exprs
            .iter()
            .map(|e| self.infer(env, e))
            .collect::<Result<_, _>>()?;

        let result_ty = Type::Unif(self.state.fresh_var());

        for alt in alts {
            let mut alt_env = env.child();

            // Check binder count matches scrutinee count
            if alt.binders.len() != scrutinee_types.len() {
                return Err(TypeError::NotImplemented {
                    span: alt.span,
                    feature: "case alternative binder count mismatch".to_string(),
                });
            }

            // Infer each binder against corresponding scrutinee type
            for (binder, scrut_ty) in alt.binders.iter().zip(scrutinee_types.iter()) {
                self.infer_binder(&mut alt_env, binder, scrut_ty)?;
            }

            // Infer the body and unify with result type
            let body_ty = self.infer_guarded(&alt_env, &alt.result)?;
            self.state.unify(span, &result_ty, &body_ty)?;
        }

        Ok(result_ty)
    }

    fn infer_array(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        elements: &[Expr],
    ) -> Result<Type, TypeError> {
        let elem_ty = Type::Unif(self.state.fresh_var());

        for elem in elements {
            let t = self.infer(env, elem)?;
            self.state.unify(span, &elem_ty, &t)?;
        }

        Ok(Type::array(elem_ty))
    }

    fn infer_hole(
        &mut self,
        span: crate::ast::span::Span,
        name: Symbol,
    ) -> Result<Type, TypeError> {
        let ty = Type::Unif(self.state.fresh_var());
        Err(TypeError::TypeHole { span, name, ty })
    }

    // ===== Binder inference =====

    /// Infer a binder against an expected type, binding variables in the environment.
    pub fn infer_binder(
        &mut self,
        env: &mut Env,
        binder: &Binder,
        expected: &Type,
    ) -> Result<(), TypeError> {
        match binder {
            Binder::Var { name, .. } => {
                env.insert_mono(name.value, expected.clone());
                Ok(())
            }
            Binder::Wildcard { .. } => Ok(()),
            Binder::Literal { span, lit } => {
                let lit_ty = match lit {
                    Literal::Int(_) => Type::int(),
                    Literal::Float(_) => Type::float(),
                    Literal::String(_) => Type::string(),
                    Literal::Char(_) => Type::char(),
                    Literal::Boolean(_) => Type::boolean(),
                    Literal::Array(_) => {
                        return Err(TypeError::NotImplemented {
                            span: *span,
                            feature: "array literal in binder".to_string(),
                        });
                    }
                };
                self.state.unify(*span, expected, &lit_ty)?;
                Ok(())
            }
            Binder::Constructor { span, name, args } => {
                // Look up constructor type in env
                match env.lookup(name.name) {
                    Some(scheme) => {
                        let mut ctor_ty = self.instantiate(scheme);
                        ctor_ty = self.instantiate_forall_type(ctor_ty)?;

                        // Peel off argument types
                        for arg_binder in args {
                            match ctor_ty {
                                Type::Fun(arg_ty, ret_ty) => {
                                    self.infer_binder(env, arg_binder, &arg_ty)?;
                                    ctor_ty = *ret_ty;
                                }
                                _ => {
                                    return Err(TypeError::NotImplemented {
                                        span: *span,
                                        feature: "constructor applied to too many arguments in pattern".to_string(),
                                    });
                                }
                            }
                        }

                        // The remaining type should unify with expected
                        self.state.unify(*span, expected, &ctor_ty)?;
                        Ok(())
                    }
                    None => Err(TypeError::UndefinedVariable {
                        span: *span,
                        name: name.name,
                    }),
                }
            }
            Binder::Parens { binder, .. } => self.infer_binder(env, binder, expected),
            Binder::As { name, binder, .. } => {
                env.insert_mono(name.value, expected.clone());
                self.infer_binder(env, binder, expected)
            }
            Binder::Typed { span, binder, ty } => {
                let annotated = convert_type_expr(ty)?;
                self.state.unify(*span, expected, &annotated)?;
                self.infer_binder(env, binder, expected)
            }
            other => Err(TypeError::NotImplemented {
                span: other.span(),
                feature: "complex binder pattern".to_string(),
            }),
        }
    }

    // ===== Guarded expression inference =====

    /// Infer the type of a guarded expression.
    pub fn infer_guarded(
        &mut self,
        env: &Env,
        guarded: &GuardedExpr,
    ) -> Result<Type, TypeError> {
        match guarded {
            GuardedExpr::Unconditional(expr) => self.infer(env, expr),
            GuardedExpr::Guarded(guards) => {
                let result_ty = Type::Unif(self.state.fresh_var());
                for guard in guards {
                    // Check each guard pattern
                    for pattern in &guard.patterns {
                        match pattern {
                            GuardPattern::Boolean(expr) => {
                                let ty = self.infer(env, expr)?;
                                self.state.unify(guard.span, &ty, &Type::boolean())?;
                            }
                            GuardPattern::Pattern(_binder, _expr) => {
                                // Pattern guards - not implemented yet
                                return Err(TypeError::NotImplemented {
                                    span: guard.span,
                                    feature: "pattern guard".to_string(),
                                });
                            }
                        }
                    }
                    let body_ty = self.infer(env, &guard.expr)?;
                    self.state.unify(guard.span, &result_ty, &body_ty)?;
                }
                Ok(result_ty)
            }
        }
    }
}
