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
    /// Map from method name → (class_name, class_type_vars).
    /// Set by check_module before typechecking value declarations.
    pub class_methods: HashMap<Symbol, (Symbol, Vec<Symbol>)>,
    /// Deferred type class constraints: (span, class_name, [type_args as unif vars]).
    /// Checked after inference to verify instances exist.
    pub deferred_constraints: Vec<(crate::ast::span::Span, Symbol, Vec<Type>)>,
    /// Map from type constructor name → list of data constructor names.
    /// Used for exhaustiveness checking of case expressions.
    pub data_constructors: HashMap<Symbol, Vec<Symbol>>,
    /// Map from type-level operator symbol → target type constructor name.
    /// Populated from `infixr N type TypeName as op` declarations.
    pub type_operators: HashMap<Symbol, Symbol>,
    /// Map from data constructor name → (parent type name, type var symbols, field types).
    /// Used for nested exhaustiveness checking to know each constructor's field types.
    pub ctor_details: HashMap<Symbol, (Symbol, Vec<Symbol>, Vec<Type>)>,
}

impl InferCtx {
    pub fn new() -> Self {
        InferCtx {
            state: UnifyState::new(),
            class_methods: HashMap::new(),
            deferred_constraints: Vec::new(),
            data_constructors: HashMap::new(),
            type_operators: HashMap::new(),
            ctor_details: HashMap::new(),
        }
    }

    /// Create a qualified symbol by combining a module alias with a name.
    fn qualified_symbol(module: Symbol, name: Symbol) -> Symbol {
        let mod_str = crate::interner::resolve(module).unwrap_or_default();
        let name_str = crate::interner::resolve(name).unwrap_or_default();
        crate::interner::intern(&format!("{}.{}", mod_str, name_str))
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
            Expr::Record { span, fields } => self.infer_record(env, *span, fields),
            Expr::RecordAccess { span, expr, field } => self.infer_record_access(env, *span, expr, field),
            Expr::RecordUpdate { span, expr, updates } => self.infer_record_update(env, *span, expr, updates),
            Expr::Do { span, statements, .. } => self.infer_do(env, *span, statements),
            Expr::Ado { span, statements, result, .. } => self.infer_ado(env, *span, statements, result),
            Expr::VisibleTypeApp { span, func, ty } => self.infer_visible_type_app(env, *span, func, ty),
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
        // For qualified names (e.g. OM.foo), construct qualified symbol and look up
        let lookup_result = if let Some(module) = name.module {
            let qual_sym = Self::qualified_symbol(module, name.name);
            env.lookup(qual_sym)
        } else {
            env.lookup(name.name)
        };
        match lookup_result {
            Some(scheme) => {
                let ty = self.instantiate(scheme);

                // If this is a class method, capture the constraint during instantiation
                if let Some((class_name, class_tvs)) = self.class_methods.get(&name.name).cloned() {
                    if let Type::Forall(vars, body) = ty {
                        let subst: HashMap<Symbol, Type> = vars
                            .iter()
                            .map(|&v| (v, Type::Unif(self.state.fresh_var())))
                            .collect();
                        let result = self.apply_symbol_subst(&subst, &body);

                        // Record constraint with the fresh unif vars for the class type params
                        let constraint_types: Vec<Type> = class_tvs
                            .iter()
                            .filter_map(|tv| subst.get(tv).cloned())
                            .collect();
                        self.deferred_constraints.push((span, class_name, constraint_types));

                        return Ok(result);
                    }
                }

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
            Type::Record(fields, tail) => {
                let fields = fields.iter().map(|(l, t)| (*l, self.apply_subst(subst, t))).collect();
                let tail = tail.as_ref().map(|t| Box::new(self.apply_subst(subst, t)));
                Type::Record(fields, tail)
            }
            Type::Con(_) | Type::Var(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
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
            Type::Record(fields, tail) => {
                let fields = fields.iter().map(|(l, t)| (*l, self.apply_symbol_subst(subst, t))).collect();
                let tail = tail.as_ref().map(|t| Box::new(self.apply_symbol_subst(subst, t)));
                Type::Record(fields, tail)
            }
            Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
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
        // First pass: collect local type signatures
        let mut local_sigs: HashMap<Symbol, Type> = HashMap::new();
        for binding in bindings {
            if let LetBinding::Signature { name, ty, .. } = binding {
                let converted = convert_type_expr(ty, &self.type_operators)?;
                local_sigs.insert(name.value, converted);
            }
        }

        // Second pass: process value bindings
        for binding in bindings {
            match binding {
                LetBinding::Value { span, binder, expr } => match binder {
                    Binder::Var { name, .. } => {
                        let binding_ty = self.infer(env, expr)?;
                        // If there's a local signature, unify with it
                        if let Some(sig_ty) = local_sigs.get(&name.value) {
                            let instantiated = self.instantiate_forall_type(sig_ty.clone())?;
                            self.state.unify(*span, &binding_ty, &instantiated)?;
                        }
                        let scheme = env.generalize(&mut self.state, binding_ty);
                        env.insert_scheme(name.value, scheme);
                    }
                    _ => {
                        // Destructuring let: infer RHS then bind pattern variables
                        let binding_ty = self.infer(env, expr)?;
                        self.infer_binder(env, binder, &binding_ty)?;
                    }
                },
                LetBinding::Signature { .. } => {
                    // Already collected in first pass
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
        let annotated = convert_type_expr(ty_expr, &self.type_operators)?;
        self.state.unify(span, &inferred, &annotated)?;
        Ok(annotated)
    }

    fn infer_visible_type_app(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        func: &Expr,
        ty_expr: &crate::cst::TypeExpr,
    ) -> Result<Type, TypeError> {
        let func_ty = self.infer_preserving_forall(env, func)?;
        let applied_ty = convert_type_expr(ty_expr, &self.type_operators)?;

        match func_ty {
            Type::Forall(vars, body) if !vars.is_empty() => {
                let mut subst = HashMap::new();
                subst.insert(vars[0], applied_ty);
                let result = self.apply_symbol_subst(&subst, &body);
                if vars.len() > 1 {
                    Ok(Type::Forall(vars[1..].to_vec(), Box::new(result)))
                } else {
                    Ok(result)
                }
            }
            _ => Err(TypeError::NotImplemented {
                span,
                feature: format!("visible type application on non-polymorphic type"),
            }),
        }
    }

    /// Infer the type of an expression, preserving Forall for visible type application.
    /// Unlike `infer`, this does NOT instantiate Forall types — VTA peels them explicitly.
    fn infer_preserving_forall(&mut self, env: &Env, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Var { span, name } | Expr::Constructor { span, name } => {
                match env.lookup(name.name) {
                    Some(scheme) => Ok(self.scheme_to_forall(scheme)),
                    None => Err(TypeError::UndefinedVariable { span: *span, name: name.name }),
                }
            }
            Expr::VisibleTypeApp { span, func, ty } => {
                self.infer_visible_type_app(env, *span, func, ty)
            }
            Expr::Parens { expr, .. } => self.infer_preserving_forall(env, expr),
            other => self.infer(env, other),
        }
    }

    /// Convert a scheme to a Type::Forall, preserving quantified variables as named
    /// type vars so VTA can peel them one at a time.
    fn scheme_to_forall(&mut self, scheme: &Scheme) -> Type {
        if scheme.forall_vars.is_empty() {
            // Data constructors/foreign: type may already be Type::Forall
            return scheme.ty.clone();
        }
        // Convert TyVarId-based quantification to Symbol-based Forall
        let mut subst: HashMap<TyVarId, Type> = HashMap::new();
        let mut var_names: Vec<Symbol> = Vec::new();
        for &var_id in &scheme.forall_vars {
            let name = crate::interner::intern(&format!("_t{}", var_id.0));
            subst.insert(var_id, Type::Var(name));
            var_names.push(name);
        }
        let body = self.apply_subst(&subst, &scheme.ty);
        Type::Forall(var_names, Box::new(body))
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
        let op_lookup = if let Some(module) = op.value.module {
            let qual_sym = Self::qualified_symbol(module, op.value.name);
            env.lookup(qual_sym)
        } else {
            env.lookup(op.value.name)
        };
        let op_ty = match op_lookup {
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
        let lookup_result = if let Some(module) = op.value.module {
            let qual_sym = Self::qualified_symbol(module, op.value.name);
            env.lookup(qual_sym)
        } else {
            env.lookup(op.value.name)
        };
        match lookup_result {
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

        // Exhaustiveness check: for each scrutinee, verify all constructors are covered
        for (idx, scrut_ty) in scrutinee_types.iter().enumerate() {
            let zonked = self.state.zonk(scrut_ty.clone());
            if let Some(type_name) = extract_type_con(&zonked) {
                if self.data_constructors.contains_key(&type_name) {
                    // Only count binders from unconditional alternatives (or
                    // guarded alternatives with a trivially-true fallback like `| true ->`).
                    // Guarded alternatives might not match even if the pattern does.
                    let binder_refs: Vec<&Binder> = alts
                        .iter()
                        .filter(|alt| is_unconditional_for_exhaustiveness(&alt.result))
                        .filter_map(|alt| alt.binders.get(idx))
                        .collect();
                    if let Some(missing) = check_exhaustiveness(
                        &binder_refs,
                        &zonked,
                        &self.data_constructors,
                        &self.ctor_details,
                    ) {
                        return Err(TypeError::NonExhaustivePattern {
                            span,
                            type_name,
                            missing,
                        });
                    }
                }
            }
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

    fn infer_record(
        &mut self,
        env: &Env,
        _span: crate::ast::span::Span,
        fields: &[crate::cst::RecordField],
    ) -> Result<Type, TypeError> {
        let mut field_types = Vec::new();
        for field in fields {
            let field_ty = if let Some(ref value) = field.value {
                self.infer(env, value)?
            } else {
                // Punning: { x } means { x: x }
                match env.lookup(field.label.value) {
                    Some(scheme) => {
                        let ty = self.instantiate(scheme);
                        self.instantiate_forall_type(ty)?
                    }
                    None => return Err(TypeError::UndefinedVariable {
                        span: field.span,
                        name: field.label.value,
                    }),
                }
            };
            field_types.push((field.label.value, field_ty));
        }
        Ok(Type::Record(field_types, None))
    }

    fn infer_record_access(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        expr: &Expr,
        field: &crate::cst::Spanned<crate::interner::Symbol>,
    ) -> Result<Type, TypeError> {
        let record_ty = self.infer(env, expr)?;
        let record_ty = self.state.zonk(record_ty);
        match record_ty {
            Type::Record(fields, _) => {
                for (label, ty) in &fields {
                    if *label == field.value {
                        return Ok(ty.clone());
                    }
                }
                Err(TypeError::NotImplemented {
                    span,
                    feature: format!("record does not have field"),
                })
            }
            _ => {
                // Try row-polymorphic approach: create a record with the field + row tail
                let field_ty = Type::Unif(self.state.fresh_var());
                let row_tail = Type::Unif(self.state.fresh_var());
                let expected_record = Type::Record(
                    vec![(field.value, field_ty.clone())],
                    Some(Box::new(row_tail)),
                );
                self.state.unify(span, &record_ty, &expected_record)?;
                Ok(field_ty)
            }
        }
    }

    fn infer_record_update(
        &mut self,
        env: &Env,
        _span: crate::ast::span::Span,
        expr: &Expr,
        updates: &[crate::cst::RecordUpdate],
    ) -> Result<Type, TypeError> {
        let record_ty = self.infer(env, expr)?;
        // Infer all update values
        for update in updates {
            let _update_ty = self.infer(env, &update.value)?;
        }
        // For now, return the same record type (simplified)
        Ok(record_ty)
    }

    fn infer_do(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        statements: &[crate::cst::DoStatement],
    ) -> Result<Type, TypeError> {
        if statements.is_empty() {
            return Err(TypeError::NotImplemented {
                span,
                feature: "empty do block".to_string(),
            });
        }

        let monad_ty = Type::Unif(self.state.fresh_var());
        let mut current_env = env.child();

        for (i, stmt) in statements.iter().enumerate() {
            let is_last = i == statements.len() - 1;
            match stmt {
                crate::cst::DoStatement::Discard { expr, .. } => {
                    let expr_ty = self.infer(&current_env, expr)?;
                    if is_last {
                        // Last statement determines the do-block type: m a
                        let result_inner = Type::Unif(self.state.fresh_var());
                        let expected = Type::app(monad_ty.clone(), result_inner.clone());
                        self.state.unify(span, &expr_ty, &expected)?;
                        return Ok(expr_ty);
                    } else {
                        // Non-last discard: m _
                        let discard_inner = Type::Unif(self.state.fresh_var());
                        let expected = Type::app(monad_ty.clone(), discard_inner);
                        self.state.unify(span, &expr_ty, &expected)?;
                    }
                }
                crate::cst::DoStatement::Bind { binder, expr, .. } => {
                    let expr_ty = self.infer(&current_env, expr)?;
                    // expr : m a, bind binder to a
                    let inner_ty = Type::Unif(self.state.fresh_var());
                    let expected = Type::app(monad_ty.clone(), inner_ty.clone());
                    self.state.unify(span, &expr_ty, &expected)?;
                    self.infer_binder(&mut current_env, binder, &inner_ty)?;
                }
                crate::cst::DoStatement::Let { bindings, .. } => {
                    self.process_let_bindings(&mut current_env, bindings)?;
                }
            }
        }

        // If we get here, the last statement was a Bind or Let (unusual but handle it)
        Err(TypeError::NotImplemented {
            span,
            feature: "do block must end with an expression".to_string(),
        })
    }

    fn infer_ado(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        statements: &[crate::cst::DoStatement],
        result: &Expr,
    ) -> Result<Type, TypeError> {
        let functor_ty = Type::Unif(self.state.fresh_var());
        let mut current_env = env.child();

        for stmt in statements {
            match stmt {
                crate::cst::DoStatement::Bind { binder, expr, .. } => {
                    let expr_ty = self.infer(&current_env, expr)?;
                    let inner_ty = Type::Unif(self.state.fresh_var());
                    let expected = Type::app(functor_ty.clone(), inner_ty.clone());
                    self.state.unify(span, &expr_ty, &expected)?;
                    self.infer_binder(&mut current_env, binder, &inner_ty)?;
                }
                crate::cst::DoStatement::Let { bindings, .. } => {
                    self.process_let_bindings(&mut current_env, bindings)?;
                }
                crate::cst::DoStatement::Discard { expr, .. } => {
                    let expr_ty = self.infer(&current_env, expr)?;
                    let discard_inner = Type::Unif(self.state.fresh_var());
                    let expected = Type::app(functor_ty.clone(), discard_inner);
                    self.state.unify(span, &expr_ty, &expected)?;
                }
            }
        }

        let result_ty = self.infer(&current_env, result)?;
        Ok(Type::app(functor_ty, result_ty))
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
                    Literal::Array(elems) => {
                        let elem_ty = Type::Unif(self.state.fresh_var());
                        self.state.unify(*span, expected, &Type::array(elem_ty.clone()))?;
                        for elem in elems {
                            let t = self.infer(env, elem)?;
                            self.state.unify(*span, &elem_ty, &t)?;
                        }
                        return Ok(());
                    }
                };
                self.state.unify(*span, expected, &lit_ty)?;
                Ok(())
            }
            Binder::Constructor { span, name, args } => {
                // Look up constructor type in env (handle qualified names)
                let lookup_result = if let Some(module) = name.module {
                    let qual_sym = Self::qualified_symbol(module, name.name);
                    env.lookup(qual_sym)
                } else {
                    env.lookup(name.name)
                };
                match lookup_result {
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
                let annotated = convert_type_expr(ty, &self.type_operators)?;
                self.state.unify(*span, expected, &annotated)?;
                self.infer_binder(env, binder, expected)
            }
            Binder::Array { span, elements } => {
                let elem_ty = Type::Unif(self.state.fresh_var());
                self.state.unify(*span, expected, &Type::array(elem_ty.clone()))?;
                for elem_binder in elements {
                    self.infer_binder(env, elem_binder, &elem_ty)?;
                }
                Ok(())
            }
            Binder::Op { span, left, op, right } => {
                // Treat as constructor pattern: op left right
                match env.lookup(op.value) {
                    Some(scheme) => {
                        let mut ctor_ty = self.instantiate(scheme);
                        ctor_ty = self.instantiate_forall_type(ctor_ty)?;

                        // Peel off two argument types (left, right)
                        match ctor_ty {
                            Type::Fun(left_ty, rest) => {
                                self.infer_binder(env, left, &left_ty)?;
                                match *rest {
                                    Type::Fun(right_ty, result_ty) => {
                                        self.infer_binder(env, right, &right_ty)?;
                                        self.state.unify(*span, expected, &result_ty)?;
                                        Ok(())
                                    }
                                    result_ty => {
                                        // Unary operator constructor — right becomes result
                                        self.infer_binder(env, right, &result_ty)?;
                                        // This is unusual but handle gracefully
                                        Ok(())
                                    }
                                }
                            }
                            _ => Err(TypeError::UndefinedVariable {
                                span: *span,
                                name: op.value,
                            }),
                        }
                    }
                    None => Err(TypeError::UndefinedVariable {
                        span: *span,
                        name: op.value,
                    }),
                }
            }
            Binder::Record { span, fields } => {
                let mut field_types = Vec::new();
                for field in fields {
                    let field_ty = Type::Unif(self.state.fresh_var());
                    match &field.binder {
                        Some(binder) => {
                            self.infer_binder(env, binder, &field_ty)?;
                        }
                        None => {
                            // Pun: { x } means bind x to the value of field x
                            env.insert_mono(field.label.value, field_ty.clone());
                        }
                    }
                    field_types.push((field.label.value, field_ty));
                }
                // Open row tail allows matching records with extra fields
                let row_tail = Type::Unif(self.state.fresh_var());
                let record_ty = Type::Record(field_types, Some(Box::new(row_tail)));
                self.state.unify(*span, expected, &record_ty)?;
                Ok(())
            }
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
                            GuardPattern::Pattern(binder, expr) => {
                                // Pattern guard: binder <- expr
                                // Infer the expression, then match binder against its type
                                let expr_ty = self.infer(env, expr)?;
                                let mut guard_env = env.child();
                                self.infer_binder(&mut guard_env, binder, &expr_ty)?;
                                // Note: variables bound here should be available in the body
                                // For simplicity, we don't propagate guard_env further here
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

/// Extract the outermost type constructor name from a type,
/// peeling through type applications. E.g. `Maybe Int` → `Maybe`.
pub fn extract_type_con(ty: &Type) -> Option<Symbol> {
    match ty {
        Type::Con(name) => Some(*name),
        Type::App(f, _) => extract_type_con(f),
        _ => None,
    }
}

/// Classify a binder for exhaustiveness checking.
/// Sets `has_catchall` if the binder matches anything (wildcard, variable, literal).
/// Adds constructor names to `covered` for constructor patterns.
/// Recurses through Parens, As, and Typed wrappers.
pub fn classify_binder(binder: &Binder, has_catchall: &mut bool, covered: &mut Vec<Symbol>) {
    match binder {
        Binder::Wildcard { .. } | Binder::Var { .. } => {
            *has_catchall = true;
        }
        Binder::Literal { .. } => {
            // Literal patterns don't exhaust constructors but act as partial coverage;
            // for constructor exhaustiveness they don't help, so treat as no-op.
        }
        Binder::Constructor { name, .. } => {
            if !covered.contains(&name.name) {
                covered.push(name.name);
            }
        }
        Binder::As { binder: inner, .. } => {
            classify_binder(inner, has_catchall, covered);
        }
        Binder::Parens { binder: inner, .. } => {
            classify_binder(inner, has_catchall, covered);
        }
        Binder::Typed { binder: inner, .. } => {
            classify_binder(inner, has_catchall, covered);
        }
        Binder::Array { .. } | Binder::Record { .. } | Binder::Op { .. } => {
            // These don't contribute to constructor exhaustiveness
        }
    }
}

/// Extract the outermost type constructor name AND its type arguments from a type.
/// E.g. `Maybe Int` → `Some((Maybe, [Int]))`, `Either String Int` → `Some((Either, [String, Int]))`.
pub fn extract_type_con_and_args(ty: &Type) -> Option<(Symbol, Vec<Type>)> {
    match ty {
        Type::Con(name) => Some((*name, Vec::new())),
        Type::App(f, a) => {
            let (name, mut args) = extract_type_con_and_args(f)?;
            args.push((**a).clone());
            Some((name, args))
        }
        _ => None,
    }
}

/// Substitute type variables in a type using a mapping from var symbol → concrete type.
fn substitute_type_vars(ty: &Type, subst: &HashMap<Symbol, Type>) -> Type {
    match ty {
        Type::Var(sym) => {
            if let Some(replacement) = subst.get(sym) {
                replacement.clone()
            } else {
                ty.clone()
            }
        }
        Type::Con(_) | Type::Unif(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
        Type::App(f, a) => Type::App(
            Box::new(substitute_type_vars(f, subst)),
            Box::new(substitute_type_vars(a, subst)),
        ),
        Type::Fun(from, to) => Type::Fun(
            Box::new(substitute_type_vars(from, subst)),
            Box::new(substitute_type_vars(to, subst)),
        ),
        Type::Forall(vars, body) => {
            // Don't substitute bound variables
            let mut inner_subst = subst.clone();
            for v in vars {
                inner_subst.remove(v);
            }
            Type::Forall(vars.clone(), Box::new(substitute_type_vars(body, &inner_subst)))
        }
        Type::Record(fields, tail) => {
            let new_fields = fields
                .iter()
                .map(|(label, t)| (*label, substitute_type_vars(t, subst)))
                .collect();
            let new_tail = tail.as_ref().map(|t| Box::new(substitute_type_vars(t, subst)));
            Type::Record(new_fields, new_tail)
        }
    }
}

/// Unwrap a binder through Parens, As, and Typed wrappers to get the inner binder.
fn unwrap_binder(binder: &Binder) -> &Binder {
    match binder {
        Binder::Parens { binder: inner, .. }
        | Binder::As { binder: inner, .. }
        | Binder::Typed { binder: inner, .. } => unwrap_binder(inner),
        _ => binder,
    }
}

/// Check if a guarded expression should be treated as unconditional for exhaustiveness.
/// Unconditional results always match. Guarded results only count if any guard has
/// a single `| true -> ...` pattern (the common `otherwise` fallback).
pub fn is_unconditional_for_exhaustiveness(guarded: &GuardedExpr) -> bool {
    match guarded {
        GuardedExpr::Unconditional(_) => true,
        GuardedExpr::Guarded(guards) => {
            guards.iter().any(|guard| {
                if guard.patterns.len() != 1 {
                    return false;
                }
                match &guard.patterns[0] {
                    GuardPattern::Boolean(expr) => match expr.as_ref() {
                        Expr::Literal { lit: Literal::Boolean(true), .. } => true,
                        Expr::Var { name, .. } => {
                            let n = crate::interner::resolve(name.name).unwrap_or_default();
                            let module_name = name.module.map(|m| crate::interner::resolve(m).unwrap_or_default());
                            n == "otherwise" && (module_name.as_deref() == Some("Prelude") || module_name.as_deref() == Some("Data.Boolean"))
                        }
                        _ => false,
                    },
                    _ => false,
                }
            })
        }
    }
}

/// Check exhaustiveness of a set of binders against a scrutinee type, recursing into
/// sub-patterns for constructors with exactly one field.
///
/// Returns `Some(missing_patterns)` if the match is non-exhaustive, where each string
/// describes a missing pattern (e.g. "Nothing", "Just Nothing", "Left (Just _)").
/// Returns `None` if exhaustive or if the type is not a known data type.
///
/// `ctor_details` maps constructor name → (parent type, type vars, field types).
/// `data_constructors` maps type name → list of all constructor names.
pub fn check_exhaustiveness(
    binders: &[&Binder],
    scrutinee_ty: &Type,
    data_constructors: &HashMap<Symbol, Vec<Symbol>>,
    ctor_details: &HashMap<Symbol, (Symbol, Vec<Symbol>, Vec<Type>)>,
) -> Option<Vec<String>> {
    let type_name = extract_type_con(scrutinee_ty)?;
    let all_ctors = data_constructors.get(&type_name)?;

    // Classify all binders
    let mut has_catchall = false;
    let mut covered: Vec<Symbol> = Vec::new();
    for binder in binders {
        classify_binder(binder, &mut has_catchall, &mut covered);
    }

    if has_catchall {
        return None; // Exhaustive via wildcard/variable
    }

    // Find missing constructors at this level
    let missing_at_this_level: Vec<Symbol> = all_ctors
        .iter()
        .filter(|c| !covered.contains(c))
        .copied()
        .collect();

    if !missing_at_this_level.is_empty() {
        // Missing constructors — report them
        let missing_strs = missing_at_this_level
            .iter()
            .map(|c| crate::interner::resolve(*c).unwrap_or_default())
            .collect();
        return Some(missing_strs);
    }

    // All constructors are covered at this level.
    // Now recurse into sub-patterns for single-field constructors.
    // For multi-field constructors, column-based analysis is unsound (cross-product issue),
    // so we only recurse into constructors with exactly one field.
    let type_args = extract_type_con_and_args(scrutinee_ty)
        .map(|(_, args)| args)
        .unwrap_or_default();

    for ctor_name in all_ctors {
        let details = match ctor_details.get(ctor_name) {
            Some(d) => d,
            None => continue,
        };
        let (_parent_type, type_var_syms, field_types) = details;

        // Only recurse into single-field constructors
        if field_types.len() != 1 {
            continue;
        }

        // Build substitution from type vars to concrete type args
        let subst: HashMap<Symbol, Type> = type_var_syms
            .iter()
            .zip(type_args.iter())
            .map(|(var, arg)| (*var, arg.clone()))
            .collect();
        let concrete_field_ty = substitute_type_vars(&field_types[0], &subst);

        // Check if the concrete field type is itself a data type we can check
        if extract_type_con(&concrete_field_ty).is_none() {
            continue;
        }

        // Collect sub-binders for this constructor from all alternatives
        let mut sub_binders: Vec<&Binder> = Vec::new();
        let mut has_ctor_catchall = false;
        for binder in binders {
            let inner = unwrap_binder(binder);
            match inner {
                Binder::Constructor { name, args, .. } if name.name == *ctor_name => {
                    if args.len() == 1 {
                        sub_binders.push(&args[0]);
                    }
                    // If args.len() != 1, something is wrong but skip gracefully
                }
                Binder::Wildcard { .. } | Binder::Var { .. } => {
                    has_ctor_catchall = true;
                }
                _ => {}
            }
        }

        if has_ctor_catchall {
            continue; // A wildcard/var at this level covers everything inside
        }

        // Recursively check exhaustiveness of the sub-binders
        if let Some(nested_missing) = check_exhaustiveness(
            &sub_binders,
            &concrete_field_ty,
            data_constructors,
            ctor_details,
        ) {
            let ctor_str = crate::interner::resolve(*ctor_name).unwrap_or_default();
            let missing_strs = nested_missing
                .into_iter()
                .map(|m| format!("{} ({})", ctor_str, m))
                .collect();
            return Some(missing_strs);
        }
    }

    None // Exhaustive
}
