use std::collections::{HashMap, HashSet};

use crate::cst::{Associativity, Binder, Expr, GuardedExpr, GuardPattern, LetBinding, Literal};
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::{Role, Scheme, Type};
use crate::typechecker::unify::UnifyState;

/// Check if a binder introduces reserved do-notation names (`bind` or `discard`).
fn check_do_reserved_names(binder: &Binder) -> Result<(), TypeError> {
    if let Binder::Var { name, .. } = binder {
        let resolved = crate::interner::resolve(name.value).unwrap_or_default();
        if resolved == "bind" || resolved == "discard" {
            return Err(TypeError::CannotUseBindWithDo {
                span: name.span,
                name: name.value,
            });
        }
    }
    Ok(())
}

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
    /// Set of known type constructor names in scope (Int, String, Maybe, etc.).
    /// Used to validate TypeExpr::Constructor references during type conversion.
    pub known_types: HashSet<Symbol>,
    /// Number of type parameters for each known type constructor.
    /// Used to detect over-applied types after type alias expansion.
    pub type_con_arities: HashMap<Symbol, usize>,
    /// Type aliases whose body has kind `Type` (declared with `{ }` record syntax).
    /// Used to detect invalid row tails like `{ | Foo }` where `Foo = { x :: Number }`.
    pub record_type_aliases: HashSet<Symbol>,
    /// Type aliases: name → (type_var_names, expanded_body).
    /// E.g. `type Fn1 a b = a -> b` → ("Fn1", ([a, b], Fun(Var(a), Var(b))))
    pub type_aliases: HashMap<Symbol, (Vec<Symbol>, Type)>,
    /// Value-level operator fixities: operator_symbol → (associativity, precedence).
    /// Used for re-associating operator chains during inference.
    pub value_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// Value-level operators that alias functions (NOT constructors).
    /// Used to detect invalid operator usage in binder patterns.
    pub function_op_aliases: HashSet<Symbol>,
    /// Class methods whose declared type has extra constraints (e.g. `Applicative m =>`).
    /// These get implicit dictionary parameters, making them functions even with 0 explicit binders.
    /// Used to avoid false CycleInDeclaration errors for instance methods.
    pub constrained_class_methods: HashSet<Symbol>,
    /// Whether we're checking a full module (enables scope checks for desugared names)
    pub module_mode: bool,
    /// Names that are ambiguous due to being imported from multiple modules.
    /// Referencing these names produces a ScopeConflict error.
    pub scope_conflicts: HashSet<Symbol>,
    /// Map from operator → class method target name (e.g. `<>` → `append`).
    /// Used for tracking deferred constraints on operator usage.
    pub operator_class_targets: HashMap<Symbol, Symbol>,
    /// Deferred constraints from operator usage (e.g. `<>` → Semigroup constraint).
    /// Only used for CannotGeneralizeRecursiveFunction detection, NOT for instance
    /// resolution (the instance matcher can't handle complex nested types).
    pub op_deferred_constraints: Vec<(crate::ast::span::Span, Symbol, Vec<Type>)>,
    /// Map from class name → (type_vars, fundeps as (lhs_indices, rhs_indices)).
    /// Used for fundep-aware orphan instance checking.
    pub class_fundeps: HashMap<Symbol, (Vec<Symbol>, Vec<(Vec<usize>, Vec<usize>)>)>,
    /// Whether the last infer_guarded found non-exhaustive pattern guards.
    /// Set during inference, consumed by check.rs to emit Partial constraint.
    pub has_non_exhaustive_pattern_guards: bool,
    /// Constraints from type signatures: function name → list of (class_name, type_args).
    /// When a function with signature constraints is called, these are instantiated
    /// with the forall substitution and added as deferred constraints.
    pub signature_constraints: HashMap<Symbol, Vec<(Symbol, Vec<Type>)>>,
    /// Deferred constraints from signature propagation (separate from main deferred_constraints).
    /// These are only checked for zero-instance classes, since our instance resolution
    /// may not handle complex imported instances correctly.
    pub sig_deferred_constraints: Vec<(crate::ast::span::Span, Symbol, Vec<Type>)>,
    /// Classes with instance chains (else keyword). Used to route chained class constraints
    /// to deferred_constraints for proper chain ambiguity checking.
    pub chained_classes: std::collections::HashSet<Symbol>,
    /// Roles for each type constructor: type_name → [Role per type parameter].
    /// Populated from role declarations and inferred from constructor fields.
    pub type_roles: HashMap<Symbol, Vec<Role>>,
    /// Set of type names declared as newtypes (for Coercible solving).
    pub newtype_names: HashSet<Symbol>,
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
            known_types: HashSet::new(),
            type_con_arities: HashMap::new(),
            record_type_aliases: HashSet::new(),
            type_aliases: HashMap::new(),
            value_fixities: HashMap::new(),
            function_op_aliases: HashSet::new(),
            constrained_class_methods: HashSet::new(),
            module_mode: false,
            scope_conflicts: HashSet::new(),
            operator_class_targets: HashMap::new(),
            op_deferred_constraints: Vec::new(),
            class_fundeps: HashMap::new(),
            has_non_exhaustive_pattern_guards: false,
            signature_constraints: HashMap::new(),
            sig_deferred_constraints: Vec::new(),
            chained_classes: HashSet::new(),
            type_roles: HashMap::new(),
            newtype_names: HashSet::new(),
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
            Expr::Literal { span, lit } => {
                // Check IntOutOfRange for integer literals (not in negate context)
                if let Literal::Int(v) = lit {
                    if *v < -2_147_483_648 || *v > 2_147_483_647 {
                        return Err(TypeError::IntOutOfRange { span: *span, value: *v });
                    }
                }
                self.infer_literal(*span, lit)
            }
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
            Expr::Parens { expr, .. } => {
                // Underscore sections are only valid inside parentheses:
                // `(_ + 1)` or `(f _)` → desugar to lambda
                if self.has_direct_underscore_hole(expr) {
                    return self.infer_underscore_section(env, expr);
                }
                self.infer(env, expr)
            }
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
        // Check for scope conflicts (name imported from multiple modules)
        let resolved_name = if let Some(module) = name.module {
            Self::qualified_symbol(module, name.name)
        } else {
            name.name
        };
        if self.scope_conflicts.contains(&resolved_name) {
            return Err(TypeError::ScopeConflict {
                span,
                name: resolved_name,
            });
        }

        // For qualified names (e.g. OM.foo), construct qualified symbol and look up
        let lookup_result = if let Some(_module) = name.module {
            env.lookup(resolved_name)
        } else {
            env.lookup(name.name)
        };
        match lookup_result {
            Some(scheme) => {
                let ty = self.instantiate(scheme);

                // If this is a class method, capture the constraint during instantiation
                if let Some((class_name, class_tvs)) = self.class_methods.get(&name.name).cloned() {
                    if let Type::Forall(vars, body) = &ty {
                        // Verify that the outer Forall vars match the class type vars.
                        // This avoids mishandling when a non-class value with the same name
                        // shadows the class method (e.g., Data.Function.apply vs Control.Apply.apply).
                        let var_names: Vec<Symbol> = vars.iter().map(|&(v, _)| v).collect();
                        let is_class_forall = !class_tvs.is_empty()
                            && var_names.len() >= class_tvs.len()
                            && var_names[..class_tvs.len()] == class_tvs[..];
                        if is_class_forall {
                            let subst: HashMap<Symbol, Type> = vars
                                .iter()
                                .map(|&(v, _)| (v, Type::Unif(self.state.fresh_var())))
                                .collect();
                            let result = self.apply_symbol_subst(&subst, body);
                            // Also instantiate the method's own forall type vars (e.g. forall b c d.)
                            let result = self.instantiate_forall_type(result)?;

                            // Record constraint with the fresh unif vars for the class type params
                            let constraint_types: Vec<Type> = class_tvs
                                .iter()
                                .filter_map(|tv| subst.get(tv).cloned())
                                .collect();

                            // Check if any class type vars are completely absent from the
                            // method's result type — if so, they're guaranteed to remain
                            // ambiguous (NoInstanceFound). This detects ClassHeadNoVTA cases.
                            // With fundeps, a var absent from the result type might still be
                            // determined. We compute the "reachable" set: vars present in
                            // the result, plus vars determined by fundep closure from those.
                            let result_free = self.state.free_unif_vars(&result);
                            let mut reachable: Vec<usize> = Vec::new();
                            for (i, ct) in constraint_types.iter().enumerate() {
                                if let Type::Unif(id) = ct {
                                    if result_free.contains(id) {
                                        reachable.push(i);
                                    }
                                }
                            }
                            // Apply fundep closure: if all lhs indices are reachable,
                            // add all rhs indices
                            if let Some((_, fundeps)) = self.class_fundeps.get(&class_name) {
                                let mut changed = true;
                                while changed {
                                    changed = false;
                                    for (lhs, rhs) in fundeps {
                                        if lhs.iter().all(|l| reachable.contains(l)) {
                                            for r in rhs {
                                                if !reachable.contains(r) {
                                                    reachable.push(*r);
                                                    changed = true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            // If any class type var is not reachable, it's ambiguous
                            for (i, ct) in constraint_types.iter().enumerate() {
                                if let Type::Unif(_) = ct {
                                    if !reachable.contains(&i) {
                                        return Err(TypeError::NoInstanceFound {
                                            span,
                                            class_name,
                                            type_args: constraint_types.iter()
                                                .map(|t| self.state.zonk(t.clone()))
                                                .collect(),
                                        });
                                    }
                                }
                            }

                            self.deferred_constraints.push((span, class_name, constraint_types));

                            return Ok(result);
                        }
                    }
                }

                // If the scheme's type is a Forall, also instantiate that
                // and propagate any signature constraints
                let lookup_name = name.name;
                match ty {
                    Type::Forall(vars, body) => {
                        let subst: HashMap<Symbol, Type> = vars
                            .iter()
                            .map(|&(v, _)| (v, Type::Unif(self.state.fresh_var())))
                            .collect();
                        let result = self.apply_symbol_subst(&subst, &body);
                        // Propagate constraints from the function's type signature
                        if let Some(constraints) = self.signature_constraints.get(&lookup_name).cloned() {
                            for (class_name, args) in &constraints {
                                let subst_args: Vec<Type> = args
                                    .iter()
                                    .map(|a| self.apply_symbol_subst(&subst, a))
                                    .collect();
                                let class_str = crate::interner::resolve(*class_name).unwrap_or_default();
                                let has_solver = matches!(class_str.as_str(),
                                    "Lacks" | "IsSymbol" | "Append" | "Reflectable"
                                    | "ToString" | "Add" | "Mul" | "Compare"
                                    | "Coercible"
                                );
                                if has_solver {
                                    self.deferred_constraints.push((span, *class_name, subst_args));
                                } else {
                                    self.sig_deferred_constraints.push((span, *class_name, subst_args));
                                }
                            }
                        }
                        Ok(result)
                    }
                    other => Ok(other),
                }
            }
            None => {
                Err(TypeError::UndefinedVariable {
                    span,
                    name: name.name,
                })
            }
        }
    }

    /// Instantiate a type scheme: replace each quantified variable with a fresh unification variable.
    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        if scheme.forall_vars.is_empty() {
            return scheme.ty.clone();
        }
        let subst: HashMap<Symbol, Type> = scheme
            .forall_vars
            .iter()
            .map(|&v| (v, Type::Unif(self.state.fresh_var())))
            .collect();
        self.apply_symbol_subst(&subst, &scheme.ty)
    }

    /// Instantiate a Type::Forall by replacing named Type::Var with fresh unification variables.
    /// This is used for data constructor types which are stored as Type::Forall(symbols, body).
    pub fn instantiate_forall_type(&mut self, ty: Type) -> Result<Type, TypeError> {
        match ty {
            Type::Forall(vars, body) => {
                let subst: HashMap<Symbol, Type> = vars
                    .iter()
                    .map(|&(v, _)| (v, Type::Unif(self.state.fresh_var())))
                    .collect();
                Ok(self.apply_symbol_subst(&subst, &body))
            }
            other => Ok(other),
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
                for (v, _) in vars {
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

    /// Bidirectional type checking: check an expression against an expected type.
    /// For lambda expressions, this pushes the expected parameter types into the
    /// binders, enabling higher-rank polymorphism to be preserved through lambdas.
    pub fn check_against(&mut self, env: &Env, expr: &Expr, expected: &Type) -> Result<Type, TypeError> {
        match expr {
            Expr::Lambda { span, binders, body } => {
                let mut current_env = env.child();
                let mut param_types = Vec::new();
                let mut remaining = self.state.zonk(expected.clone());

                for binder in binders {
                    remaining = self.state.zonk(remaining);
                    // Instantiate any outer Forall on remaining so we can peel Fun args.
                    // This does NOT instantiate Forall types inside param positions —
                    // those are preserved so lambda params get polymorphic types.
                    if let Type::Forall(..) = &remaining {
                        remaining = self.instantiate_forall_type(remaining)?;
                    }
                    match remaining {
                        Type::Fun(param, ret) => {
                            self.infer_binder(&mut current_env, binder, &param)?;
                            param_types.push(*param);
                            remaining = *ret;
                        }
                        _ => {
                            let param_ty = Type::Unif(self.state.fresh_var());
                            self.infer_binder(&mut current_env, binder, &param_ty)?;
                            param_types.push(param_ty);
                        }
                    }
                }

                let body_ty = self.infer(&current_env, body)?;
                self.state.unify(*span, &body_ty, &remaining)?;

                let mut result = body_ty;
                for param_ty in param_types.into_iter().rev() {
                    result = Type::fun(param_ty, result);
                }
                Ok(result)
            }
            _ => {
                let inferred = self.infer(env, expr)?;
                self.state.unify(expr.span(), &inferred, expected)?;
                Ok(inferred)
            }
        }
    }

    fn infer_app(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        func: &Expr,
        arg: &Expr,
    ) -> Result<Type, TypeError> {
        // Detect record update syntax: expr { field = value, ... }
        // The grammar parses this as App(expr, Record { fields }) with is_update=true.
        // In PureScript, record updates bind tighter than function application:
        // `f x { a = 1 }` means `f (x { a = 1 })`, not `(f x) { a = 1 }`.
        if let Expr::Record { fields, .. } = arg {
            if !fields.is_empty() && fields.iter().all(|f| f.is_update && f.value.is_some()) {
                let updates: Vec<crate::cst::RecordUpdate> = fields
                    .iter()
                    .filter_map(|f| {
                        Some(crate::cst::RecordUpdate {
                            span: f.span,
                            label: f.label.clone(),
                            value: f.value.clone()?,
                        })
                    })
                    .collect();
                if !updates.is_empty() {
                    // If func is an App, peel it: the record update binds to the
                    // rightmost atom (inner_arg), then the outer function is applied.
                    if let Expr::App { span: outer_span, func: outer_func, arg: inner_arg } = func {
                        let updated_ty = self.infer_record_update(env, span, inner_arg, &updates)?;
                        let outer_func_ty = self.infer(env, outer_func)?;
                        let result_ty = Type::Unif(self.state.fresh_var());
                        self.state.unify(*outer_span, &outer_func_ty, &Type::fun(updated_ty, result_ty.clone()))?;
                        return Ok(result_ty);
                    }
                    return self.infer_record_update(env, span, func, &updates);
                }
            }
        }

        let func_ty = self.infer(env, func)?;

        // Bidirectional checking for lambda arguments: when the function expects a
        // higher-rank parameter type (one containing Forall), push it into the lambda.
        // This enables `g \f -> if f true then f 0 else f 1` where g expects
        // `(forall a. a -> a) -> Int` — the lambda's `f` must be polymorphic.
        // Only triggers when the param type contains Forall, to avoid interfering
        // with normal monomorphic inference.
        if let Expr::Lambda { .. } = arg {
            let func_ty_z = self.state.zonk(func_ty.clone());
            if let Type::Fun(param, result) = func_ty_z {
                if Self::type_contains_forall(&param) {
                    self.check_against(env, arg, &param)?;
                    return Ok(*result);
                }
            }
        }

        let arg_ty = self.infer(env, arg)?;

        // Higher-rank type checking: when the function expects a polymorphic argument
        // (e.g. `f :: (forall a. a -> a) -> r`), verify the argument is truly polymorphic.
        // After unification, the forall vars must remain free and distinct — if any gets
        // bound to a concrete type, the argument isn't polymorphic enough.
        let func_ty_z = self.state.zonk(func_ty.clone());
        if let Type::Fun(param, result) = &func_ty_z {
            if let Type::Forall(vars, body) = param.as_ref() {
                // Instantiate forall vars with fresh unif vars and record them
                let forall_unif_vars: Vec<(Symbol, crate::typechecker::types::TyVarId)> = vars
                    .iter()
                    .map(|&(v, _)| (v, self.state.fresh_var()))
                    .collect();
                let subst: HashMap<Symbol, Type> = forall_unif_vars
                    .iter()
                    .map(|&(v, tv)| (v, Type::Unif(tv)))
                    .collect();
                let instantiated_param = self.apply_symbol_subst(&subst, body);
                self.state.unify(span, &arg_ty, &instantiated_param)?;

                // Post-unification check: each forall var must be free (unsolved)
                // and all must be distinct (different representatives).
                let mut seen_roots = HashSet::new();
                for &(_sym, tv) in &forall_unif_vars {
                    let resolved = self.state.zonk(Type::Unif(tv));
                    match &resolved {
                        Type::Unif(root_tv) => {
                            // Still free — check distinctness
                            if !seen_roots.insert(root_tv.0) {
                                // Two forall vars resolved to the same unif var
                                return Err(TypeError::UnificationError {
                                    span,
                                    expected: param.as_ref().clone(),
                                    found: self.state.zonk(arg_ty),
                                });
                            }
                        }
                        _ => {
                            // Bound to a concrete type — argument is monomorphic
                            return Err(TypeError::UnificationError {
                                span,
                                expected: param.as_ref().clone(),
                                found: self.state.zonk(arg_ty),
                            });
                        }
                    }
                }
                return Ok(result.as_ref().clone());
            }
        }

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
        // Handle `if _ then a else b` → `\x -> if x then a else b`
        let is_underscore = matches!(cond, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_");

        let cond_ty = self.infer(env, cond)?;
        self.state.unify(cond.span(), &cond_ty, &Type::boolean())?;

        let then_ty = self.infer(env, then_expr)?;
        let else_ty = self.infer(env, else_expr)?;
        self.state.unify(span, &then_ty, &else_ty)?;

        if is_underscore {
            Ok(Type::fun(Type::boolean(), then_ty))
        } else {
            Ok(then_ty)
        }
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
                let converted = convert_type_expr(ty, &self.type_operators, &self.known_types)?;
                let converted = self.instantiate_wildcards(&converted);
                local_sigs.insert(name.value, converted);
            }
        }

        // Check for overlapping names in let bindings.
        // Multi-equation function definitions (same name, lambda exprs) are allowed
        // only if they are adjacent (not separated by other bindings).
        let mut seen_let_names: HashMap<Symbol, Vec<(crate::ast::span::Span, bool)>> = HashMap::new();
        // Track binding order for adjacency check: (name, index) for each value binding
        let mut binding_order: Vec<Symbol> = Vec::new();
        for binding in bindings {
            if let LetBinding::Value { span, binder, expr } = binding {
                if let Binder::Var { name, .. } = binder {
                    let is_func = matches!(expr, Expr::Lambda { .. });
                    seen_let_names.entry(name.value).or_default().push((*span, is_func));
                    binding_order.push(name.value);
                }
            }
        }
        for (name, entries) in &seen_let_names {
            if entries.len() > 1 {
                let all_funcs = entries.iter().all(|(_, is_func)| *is_func);
                if !all_funcs {
                    return Err(TypeError::OverlappingNamesInLet {
                        spans: entries.iter().map(|(s, _)| *s).collect(),
                        name: *name,
                    });
                }
                // All are functions — check they're adjacent in binding order
                let indices: Vec<usize> = binding_order.iter().enumerate()
                    .filter(|(_, n)| **n == *name)
                    .map(|(i, _)| i)
                    .collect();
                let is_adjacent = indices.windows(2).all(|w| w[1] == w[0] + 1);
                if !is_adjacent {
                    return Err(TypeError::OverlappingNamesInLet {
                        spans: entries.iter().map(|(s, _)| *s).collect(),
                        name: *name,
                    });
                }
            }
        }
        // Cycle detection for non-function let bindings that reference themselves.
        // `let x = x in x` is a CycleInDeclaration, but `let f = \x -> f x in f` is OK.
        let let_names: std::collections::HashSet<Symbol> = bindings.iter().filter_map(|b| {
            if let LetBinding::Value { binder: Binder::Var { name, .. }, .. } = b { Some(name.value) } else { None }
        }).collect();
        for binding in bindings.iter() {
            if let LetBinding::Value { span, binder: Binder::Var { name, .. }, expr } = binding {
                if !matches!(expr, Expr::Lambda { .. }) {
                    if expr_references_name(expr, name.value, &let_names) {
                        return Err(TypeError::CycleInDeclaration {
                            name: name.value,
                            span: *span,
                            others_in_cycle: Vec::new(),
                        });
                    }
                }
            }
        }

        // Track which names are multi-equation (skip subsequent equations after first)
        let mut processed_multi_eq: std::collections::HashSet<Symbol> = std::collections::HashSet::new();

        // Second pass: pre-insert types for all named bindings so that recursive
        // references work. For bindings with local type signatures, insert the
        // signature as a proper scheme so each recursive use gets fresh forall
        // instantiation (avoids infinite types from constraint pollution).
        // For bindings without signatures, use a fresh unification variable.
        let mut pre_inserted: HashMap<Symbol, Type> = HashMap::new();
        let mut pre_inserted_names: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        for binding in bindings {
            if let LetBinding::Value { binder: Binder::Var { name, .. }, .. } = binding {
                if pre_inserted_names.contains(&name.value) {
                    continue;
                }
                pre_inserted_names.insert(name.value);
                if let Some(sig_ty) = local_sigs.get(&name.value) {
                    // Has a signature — insert as a proper scheme so recursive
                    // refs get fresh instantiation per use
                    let scheme = match sig_ty {
                        Type::Forall(vars, body) => Scheme {
                            forall_vars: vars.iter().map(|(v, _)| *v).collect(),
                            ty: *body.clone(),
                        },
                        _ => Scheme::mono(sig_ty.clone()),
                    };
                    env.insert_scheme(name.value, scheme);
                } else {
                    let self_ty = Type::Unif(self.state.fresh_var());
                    env.insert_mono(name.value, self_ty.clone());
                    pre_inserted.insert(name.value, self_ty);
                }
            }
        }

        // Third pass: infer value bindings
        for binding in bindings {
            match binding {
                LetBinding::Value { span, binder, expr } => match binder {
                    Binder::Var { name, .. } => {
                        // For multi-equation functions, subsequent equations
                        // still need to be type-checked (to detect type errors)
                        // but shouldn't re-register the scheme.
                        let is_subsequent = processed_multi_eq.contains(&name.value);
                        if !is_subsequent {
                            if seen_let_names.get(&name.value).map_or(false, |e| e.len() > 1) {
                                processed_multi_eq.insert(name.value);
                            }
                        }
                        let binding_ty = self.infer(env, expr)?;
                        // If there's a local signature, unify with it
                        if let Some(sig_ty) = local_sigs.get(&name.value) {
                            let instantiated = self.instantiate_forall_type(sig_ty.clone())?;
                            self.state.unify(*span, &binding_ty, &instantiated)?;
                        }
                        // Unify with pre-inserted type for recursion
                        if let Some(self_ty) = pre_inserted.get(&name.value) {
                            self.state.unify(*span, self_ty, &binding_ty)?;
                        }
                        // Only register the scheme for the first equation
                        if !is_subsequent {
                            let scheme = if let Some(sig_ty) = local_sigs.get(&name.value) {
                                Scheme::mono(sig_ty.clone())
                            } else {
                                env.generalize_local(&mut self.state, binding_ty, name.value)
                            };
                            env.insert_scheme(name.value, scheme);
                        }
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
        let annotated = convert_type_expr(ty_expr, &self.type_operators, &self.known_types)?;
        // Replace wildcard type variables (_) with fresh unification variables
        let annotated = self.instantiate_wildcards(&annotated);
        // Extract annotation constraints for deferred checking (e.g., Fail (Text "..."))
        self.extract_inline_annotation_constraints(ty_expr, span);
        self.state.unify(span, &inferred, &annotated)?;
        Ok(annotated)
    }

    /// Extract constraints from an inline type annotation and add to deferred constraints.
    fn extract_inline_annotation_constraints(
        &mut self,
        ty: &crate::cst::TypeExpr,
        span: crate::ast::span::Span,
    ) {
        use crate::cst::TypeExpr;
        match ty {
            TypeExpr::Constrained { constraints, ty, .. } => {
                for constraint in constraints {
                    let class_str = crate::interner::resolve(constraint.class.name).unwrap_or_default();
                    if class_str == "Partial" || class_str == "Warn" {
                        continue;
                    }
                    let mut args = Vec::new();
                    let mut ok = true;
                    for arg in &constraint.args {
                        match convert_type_expr(arg, &self.type_operators, &self.known_types) {
                            Ok(converted) => args.push(converted),
                            Err(_) => { ok = false; break; }
                        }
                    }
                    if ok {
                        self.deferred_constraints.push((constraint.span, constraint.class.name, args));
                    }
                }
                self.extract_inline_annotation_constraints(ty, span);
            }
            TypeExpr::Forall { ty, .. } | TypeExpr::Parens { ty, .. } => {
                self.extract_inline_annotation_constraints(ty, span);
            }
            _ => {}
        }
    }

    /// Replace all Type::Var("_") (from wildcard type annotations) with fresh unification variables.
    pub fn instantiate_wildcards(&mut self, ty: &Type) -> Type {
        let underscore = crate::interner::intern("_");
        match ty {
            Type::Var(v) if *v == underscore => Type::Unif(self.state.fresh_var()),
            Type::Fun(a, b) => Type::fun(self.instantiate_wildcards(a), self.instantiate_wildcards(b)),
            Type::App(f, a) => Type::app(self.instantiate_wildcards(f), self.instantiate_wildcards(a)),
            Type::Forall(vars, body) => Type::Forall(vars.clone(), Box::new(self.instantiate_wildcards(body))),
            Type::Record(fields, tail) => {
                let fields = fields.iter().map(|(l, t)| (*l, self.instantiate_wildcards(t))).collect();
                let tail = tail.as_ref().map(|t| Box::new(self.instantiate_wildcards(t)));
                Type::Record(fields, tail)
            }
            _ => ty.clone(),
        }
    }

    fn infer_visible_type_app(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        func: &Expr,
        ty_expr: &crate::cst::TypeExpr,
    ) -> Result<Type, TypeError> {
        // Flatten chained VTAs: f @A @B @C → base=f, args=[A, B, C]
        let mut vta_args: Vec<&crate::cst::TypeExpr> = vec![ty_expr];
        let mut base: &Expr = func;
        while let Expr::VisibleTypeApp { func: inner, ty: inner_ty, .. } = base {
            vta_args.push(inner_ty);
            base = inner;
        }
        vta_args.reverse(); // Now in application order

        let func_ty = self.infer_preserving_forall(env, base)?;

        // Check if the base expression is a class method
        let class_info = if let Expr::Var { name, .. } = base {
            self.class_methods.get(&name.name).cloned()
        } else {
            None
        };
        let mut var_subst: HashMap<Symbol, Type> = HashMap::new();

        // Process all VTA args sequentially
        let mut ty = func_ty;
        for (arg_idx, arg_ty_expr) in vta_args.iter().enumerate() {
            let applied_ty = convert_type_expr(arg_ty_expr, &self.type_operators, &self.known_types)?;
            let applied_ty = self.instantiate_wildcards(&applied_ty);
            let is_last = arg_idx == vta_args.len() - 1;

            // Skip invisible forall vars, then apply VTA to the first visible var
            loop {
                match ty {
                    Type::Forall(ref vars, ref body) if !vars.is_empty() => {
                        if vars[0].1 {
                            // First var is visible — apply this VTA arg
                            let mut subst = HashMap::new();
                            subst.insert(vars[0].0, applied_ty.clone());
                            var_subst.insert(vars[0].0, applied_ty);
                            let result = self.apply_symbol_subst(&subst, body);
                            if vars.len() > 1 {
                                ty = Type::Forall(vars[1..].to_vec(), Box::new(result));
                            } else {
                                ty = result;
                            }
                            break; // Move to next VTA arg
                        } else {
                            // Invisible var — instantiate with fresh unif var
                            let fresh = Type::Unif(self.state.fresh_var());
                            let mut subst = HashMap::new();
                            subst.insert(vars[0].0, fresh.clone());
                            var_subst.insert(vars[0].0, fresh);
                            let result = self.apply_symbol_subst(&subst, body);
                            if vars.len() > 1 {
                                ty = Type::Forall(vars[1..].to_vec(), Box::new(result));
                            } else {
                                ty = result;
                            }
                            // Continue loop to skip more invisible vars
                        }
                    }
                    ref other => {
                        if is_last {
                            // No more forall vars but this is the last arg — error
                            return Err(TypeError::CannotApplyExpressionOfTypeOnType {
                                span,
                                type_: other.clone(),
                            });
                        } else {
                            return Err(TypeError::CannotApplyExpressionOfTypeOnType {
                                span,
                                type_: other.clone(),
                            });
                        }
                    }
                }
            }
        }

        // After all VTA args processed, defer class constraint if applicable
        if let Some((class_name, ref class_tvs)) = class_info {
            // Instantiate any remaining forall vars
            if let Type::Forall(ref vars, _) = ty {
                for &(v, _) in vars.iter() {
                    if !var_subst.contains_key(&v) {
                        var_subst.insert(v, Type::Unif(self.state.fresh_var()));
                    }
                }
            }
            let constraint_types: Vec<Type> = class_tvs.iter()
                .map(|tv| var_subst.get(tv).cloned()
                    .unwrap_or_else(|| Type::Unif(self.state.fresh_var())))
                .collect();

            // Reachability check: detect class type vars that can never
            // be determined. Concrete types (from VTA) are determined;
            // Unif vars in the result type are determined; fundep closure
            // propagates determinedness.
            let zonked_ty = self.state.zonk(ty.clone());
            let result_free = self.state.free_unif_vars(&zonked_ty);
            let mut determined: Vec<usize> = Vec::new();
            for (i, ct) in constraint_types.iter().enumerate() {
                match ct {
                    Type::Unif(id) if result_free.contains(id) => {
                        determined.push(i);
                    }
                    Type::Unif(_) => {}
                    _ => {
                        // Concrete type (from VTA) — already determined
                        determined.push(i);
                    }
                }
            }
            if let Some((_, fundeps)) = self.class_fundeps.get(&class_name) {
                let mut changed = true;
                while changed {
                    changed = false;
                    for (lhs, rhs) in fundeps {
                        if lhs.iter().all(|l| determined.contains(l)) {
                            for r in rhs {
                                if !determined.contains(r) {
                                    determined.push(*r);
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
            for (i, ct) in constraint_types.iter().enumerate() {
                if let Type::Unif(_) = ct {
                    if !determined.contains(&i) {
                        return Err(TypeError::NoInstanceFound {
                            span,
                            class_name,
                            type_args: constraint_types.iter()
                                .map(|t| self.state.zonk(t.clone()))
                                .collect(),
                        });
                    }
                }
            }

            self.deferred_constraints.push((span, class_name, constraint_types));
        }

        Ok(ty)
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
            Expr::Parens { expr, .. } => {
                if self.has_direct_underscore_hole(expr) {
                    return self.infer_underscore_section(env, expr);
                }
                self.infer_preserving_forall(env, expr)
            }
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
        // Scheme already uses Type::Var for quantified vars, just wrap in Forall
        // Generalized vars are always invisible (not from user @a syntax)
        Type::Forall(scheme.forall_vars.iter().map(|&v| (v, false)).collect(), Box::new(scheme.ty.clone()))
    }

    fn infer_negate(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        expr: &Expr,
    ) -> Result<Type, TypeError> {
        // Check that `negate` is in scope (module mode only)
        // In PureScript, `-x` desugars to `negate x`, so negate must be imported
        if self.module_mode {
            let negate_sym = crate::interner::intern("negate");
            if env.lookup(negate_sym).is_none() {
                return Err(TypeError::UndefinedVariable { span, name: negate_sym });
            }
        }
        // For negated integer literals, check the negated value is in range:
        // -2147483648 (i.e. negate(2147483648)) is valid Int min
        // But negate(2147483649) would be out of range
        if let Expr::Literal { span: lit_span, lit: Literal::Int(v) } = expr {
            let neg = -*v;
            if neg < -2_147_483_648 || neg > 2_147_483_647 {
                return Err(TypeError::IntOutOfRange { span: *lit_span, value: *v });
            }
            // Skip normal infer to avoid the positive range check in Expr::Literal
            return Ok(Type::int());
        }
        // PureScript negate uses Ring class: negate :: Ring a => a -> a
        // Only Int and Number have Ring instances.
        let ty = self.infer(env, expr)?;
        let zonked = self.state.zonk(ty.clone());
        // If the type is a concrete type constructor, check it's Int or Number
        if let Type::Con(name) = &zonked {
            let name_str = crate::interner::resolve(*name).unwrap_or_default();
            if name_str != "Int" && name_str != "Number" {
                return Err(TypeError::NoInstanceFound {
                    span,
                    class_name: crate::interner::intern("Ring"),
                    type_args: vec![zonked],
                });
            }
        }
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
        // Flatten the right-associative operator chain into a list of operands and operators.
        // The grammar parses `a + b * c` as `Op(a, +, Op(b, *, c))` (right-associative).
        // We flatten to [a, b, c] with operators [+, *] then re-associate using fixity.
        let mut operands: Vec<&Expr> = vec![left];
        let mut operators: Vec<&crate::cst::Spanned<crate::cst::QualifiedIdent>> = vec![op];
        let mut current = right;
        while let Expr::Op { left: rl, op: rop, right: rr, .. } = current {
            operands.push(rl.as_ref());
            operators.push(rop);
            current = rr.as_ref();
        }
        // Handle trailing type annotation: `a <<< b :: T` is parsed as
        // `Op(a, <<<, TypeAnnotation(b, T))` but should be `(a <<< b) :: T`.
        // Extract the annotation and wrap the final result after reassociation.
        let trailing_annotation = if let Expr::TypeAnnotation { expr, ty, .. } = current {
            current = expr.as_ref();
            Some(ty)
        } else {
            None
        };
        operands.push(current);

        // Reject `_` (anonymous argument) in operator expressions that aren't
        // inside parentheses. Operator sections like `(_ + 1)` are valid only
        // inside Parens and are handled by the Parens case of infer.
        let is_underscore = |e: &Expr| matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_");
        for operand in &operands {
            if is_underscore(operand) {
                return Err(TypeError::IncorrectAnonymousArgument { span: operand.span() });
            }
        }

        // If only one operator, do simple binary inference (common case, fast path)
        if operators.len() == 1 {
            return self.infer_op_binary(env, span, operands[0], operators[0], operands[1]);
        }

        // Detect underscore holes for operator sections in chains
        let first_is_hole = Self::is_underscore_hole(operands[0]);
        let last_is_hole = Self::is_underscore_hole(operands[operands.len() - 1]);

        // Infer all operand types (holes get fresh type vars)
        let operand_types: Vec<Type> = operands
            .iter()
            .map(|e| {
                if Self::is_underscore_hole(e) {
                    Ok(Type::Unif(self.state.fresh_var()))
                } else {
                    self.infer(env, e)
                }
            })
            .collect::<Result<_, _>>()?;

        // Save hole types for wrapping later
        let first_hole_ty = if first_is_hole { Some(operand_types[0].clone()) } else { None };
        let last_hole_ty = if last_is_hole { Some(operand_types[operand_types.len() - 1].clone()) } else { None };

        // Look up and instantiate all operator types
        let mut op_types: Vec<Type> = Vec::new();
        for op in &operators {
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
            op_types.push(op_ty);
        }

        // Shunting-yard algorithm: re-associate based on operator precedence
        let mut output: Vec<Type> = Vec::new();
        let mut op_stack: Vec<usize> = Vec::new(); // indices into operators/op_types

        output.push(operand_types[0].clone());

        for i in 0..operators.len() {
            let (assoc_i, prec_i) = self.get_fixity(operators[i].value.name);

            while let Some(&top_idx) = op_stack.last() {
                let (assoc_top, prec_top) = self.get_fixity(operators[top_idx].value.name);
                if prec_top == prec_i {
                    // Same precedence: check for mixed associativity before non-associative
                    if assoc_i != assoc_top {
                        return Err(TypeError::MixedAssociativityError {
                            span: operators[i].span,
                        });
                    }
                    if assoc_i == Associativity::None {
                        return Err(TypeError::NonAssociativeError {
                            span: operators[i].span,
                            op: operators[i].value.name,
                        });
                    }
                }
                let should_pop = prec_top > prec_i
                    || (prec_top == prec_i && assoc_i == Associativity::Left);
                if should_pop {
                    op_stack.pop();
                    let right_ty = output.pop().unwrap();
                    let left_ty = output.pop().unwrap();
                    let result = self.apply_binop(span, &op_types[top_idx], left_ty, right_ty)?;
                    output.push(result);
                } else {
                    break;
                }
            }

            op_stack.push(i);
            output.push(operand_types[i + 1].clone());
        }

        // Pop remaining operators
        while let Some(top_idx) = op_stack.pop() {
            let right_ty = output.pop().unwrap();
            let left_ty = output.pop().unwrap();
            let result = self.apply_binop(span, &op_types[top_idx], left_ty, right_ty)?;
            output.push(result);
        }

        let mut result = output.pop().unwrap();

        // Wrap in function types for operator sections
        if let Some(hole_ty) = last_hole_ty {
            result = Type::fun(hole_ty, result);
        }
        if let Some(hole_ty) = first_hole_ty {
            result = Type::fun(hole_ty, result);
        }

        // Apply trailing type annotation: `a <<< b :: T` → check result against T
        if let Some(ty_expr) = trailing_annotation {
            let annotated = convert_type_expr(ty_expr, &self.type_operators, &self.known_types)?;
            let annotated = self.instantiate_wildcards(&annotated);
            self.extract_inline_annotation_constraints(ty_expr, span);
            self.state.unify(span, &result, &annotated)?;
            result = annotated;
        }

        Ok(result)
    }

    /// Get the fixity (associativity, precedence) for an operator.
    /// Defaults to infixl 9 for operators without declared fixity.
    fn get_fixity(&self, op_name: Symbol) -> (Associativity, u8) {
        self.value_fixities
            .get(&op_name)
            .copied()
            .unwrap_or((Associativity::Left, 9))
    }

    /// Apply a binary operator type to two operand types.
    /// op_ty should be `a -> b -> c`; unifies a with left, b with right, returns c.
    fn apply_binop(
        &mut self,
        span: crate::ast::span::Span,
        op_ty: &Type,
        left_ty: Type,
        right_ty: Type,
    ) -> Result<Type, TypeError> {
        let intermediate_ty = Type::Unif(self.state.fresh_var());
        let result_ty = Type::Unif(self.state.fresh_var());

        self.state
            .unify(span, op_ty, &Type::fun(left_ty, intermediate_ty.clone()))?;
        self.state
            .unify(span, &intermediate_ty, &Type::fun(right_ty, result_ty.clone()))?;

        Ok(result_ty)
    }

    /// Infer the type of a single binary operator expression (no chain flattening).
    /// Check if a type contains any Forall anywhere in its structure.
    fn type_contains_forall(ty: &Type) -> bool {
        match ty {
            Type::Forall(..) => true,
            Type::Fun(a, b) => Self::type_contains_forall(a) || Self::type_contains_forall(b),
            Type::App(f, a) => Self::type_contains_forall(f) || Self::type_contains_forall(a),
            Type::Record(fields, tail) => {
                fields.iter().any(|(_, t)| Self::type_contains_forall(t))
                    || tail.as_ref().is_some_and(|t| Self::type_contains_forall(t))
            }
            _ => false,
        }
    }

    fn is_underscore_hole(e: &Expr) -> bool {
        matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_")
    }

    fn infer_op_binary(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        left: &Expr,
        op: &crate::cst::Spanned<crate::cst::QualifiedIdent>,
        right: &Expr,
    ) -> Result<Type, TypeError> {
        let op_lookup = if let Some(module) = op.value.module {
            let qual_sym = Self::qualified_symbol(module, op.value.name);
            env.lookup(qual_sym)
        } else {
            env.lookup(op.value.name)
        };
        let op_name = op.value.name;
        let op_ty = match op_lookup {
            Some(scheme) => {
                let ty = self.instantiate(scheme);
                // Check if this operator targets a class method; if so, push op deferred constraint
                // (used only for CannotGeneralizeRecursiveFunction, not instance resolution)
                let class_info = self.class_methods.get(&op_name).cloned()
                    .or_else(|| {
                        self.operator_class_targets.get(&op_name)
                            .and_then(|target| self.class_methods.get(target).cloned())
                    });
                if let Some((class_name, class_tvs)) = class_info {
                    if let Type::Forall(vars, body) = &ty {
                        let var_names: Vec<Symbol> = vars.iter().map(|&(v, _)| v).collect();
                        let is_class_forall = !class_tvs.is_empty()
                            && var_names.len() >= class_tvs.len()
                            && var_names[..class_tvs.len()] == class_tvs[..];
                        if is_class_forall {
                            let subst: HashMap<Symbol, Type> = vars
                                .iter()
                                .map(|&(v, _)| (v, Type::Unif(self.state.fresh_var())))
                                .collect();
                            let result = self.apply_symbol_subst(&subst, body);
                            let result = self.instantiate_forall_type(result)?;
                            let constraint_types: Vec<Type> = class_tvs
                                .iter()
                                .filter_map(|tv| subst.get(tv).cloned())
                                .collect();
                            self.op_deferred_constraints.push((span, class_name, constraint_types));
                            result
                        } else {
                            self.instantiate_forall_type(ty)?
                        }
                    } else {
                        self.instantiate_forall_type(ty)?
                    }
                } else {
                    self.instantiate_forall_type(ty)?
                }
            }
            None => {
                return Err(TypeError::UndefinedVariable {
                    span: op.span,
                    name: op.value.name,
                });
            }
        };

        // Operator sections: (_ op expr) or (expr op _) creates a function
        let left_is_hole = Self::is_underscore_hole(left);
        let right_is_hole = Self::is_underscore_hole(right);

        if left_is_hole && right_is_hole {
            // Both holes: (_ op _) → equivalent to (op)
            return Ok(op_ty);
        }

        if left_is_hole {
            // (_ op expr) → \x -> x op expr
            let param_ty = Type::Unif(self.state.fresh_var());
            let right_ty = self.infer(env, right)?;
            let result_ty = self.apply_binop(span, &op_ty, param_ty.clone(), right_ty)?;
            return Ok(Type::fun(param_ty, result_ty));
        }

        if right_is_hole {
            // (expr op _) → \x -> expr op x
            let left_ty = self.infer(env, left)?;
            let param_ty = Type::Unif(self.state.fresh_var());
            let result_ty = self.apply_binop(span, &op_ty, left_ty, param_ty.clone())?;
            return Ok(Type::fun(param_ty, result_ty));
        }

        let left_ty = self.infer(env, left)?;
        let right_ty = self.infer(env, right)?;

        self.apply_binop(span, &op_ty, left_ty, right_ty)
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
        // Detect underscore scrutinees: `case _, _ of` creates a lambda function
        let is_underscore: Vec<bool> = exprs
            .iter()
            .map(|e| matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_"))
            .collect();

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
                return Err(TypeError::CaseBinderLengthDiffers {
                    span: alt.span,
                    expected: scrutinee_types.len(),
                    found: alt.binders.len(),
                });
            }

            // Check for overlapping pattern variables in this alternative
            let binder_refs: Vec<&Binder> = alt.binders.iter().collect();
            if let Some(err) = check_overlapping_pattern_vars(&binder_refs) {
                return Err(err);
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

        // If any scrutinees were underscore holes, wrap the result in function types.
        // `case _, _ of` with scrutinee types [t1, t2] and result r → t1 -> t2 -> r
        let has_underscores = is_underscore.iter().any(|&b| b);
        if has_underscores {
            let mut ty = result_ty;
            for (i, is_us) in is_underscore.iter().enumerate().rev() {
                if *is_us {
                    ty = Type::fun(scrutinee_types[i].clone(), ty);
                }
            }
            Ok(ty)
        } else {
            Ok(result_ty)
        }
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
        // `_` in expression position is PureScript's anonymous function argument.
        // Valid in operator sections, record accessors, case scrutinees, if-then-else, etc.
        // Bare `_` at value binding level is rejected in check_module.
        if crate::interner::resolve(name).unwrap_or_default() == "_" {
            Ok(ty)
        } else {
            Err(TypeError::HoleInferredType { span, name, ty })
        }
    }

    /// Check if an Op/App expression has a DIRECT `_` hole child (not nested).
    /// This prevents infinite recursion — we only desugar at the level where `_` appears.
    fn has_direct_underscore_hole(&self, expr: &Expr) -> bool {
        let is_hole = |e: &Expr| matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_");
        match expr {
            Expr::Op { left, right, .. } => {
                is_hole(left) || is_hole(right)
                    || self.has_direct_underscore_hole(left)
                    || self.has_direct_underscore_hole(right)
            }
            Expr::App { func, arg, .. } => is_hole(func) || is_hole(arg),
            _ => false,
        }
    }

    /// Replace `_` holes in an operator chain with a variable reference.
    fn replace_underscore_in_op_chain(&self, expr: &Expr, replacement_name: Symbol) -> Expr {
        let is_hole = |e: &Expr| matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_");
        if is_hole(expr) {
            return Expr::Var {
                span: expr.span(),
                name: crate::cst::QualifiedIdent { module: None, name: replacement_name },
            };
        }
        match expr {
            Expr::Op { span, left, op, right } => Expr::Op {
                span: *span,
                left: Box::new(self.replace_underscore_in_op_chain(left, replacement_name)),
                op: op.clone(),
                right: Box::new(self.replace_underscore_in_op_chain(right, replacement_name)),
            },
            other => other.clone(),
        }
    }

    /// Desugar underscore sections into lambdas and infer.
    /// `(_ * 1000.0)` → `\x -> x * 1000.0`
    fn infer_underscore_section(
        &mut self,
        env: &Env,
        expr: &Expr,
    ) -> Result<Type, TypeError> {
        let param_ty = Type::Unif(self.state.fresh_var());
        let param_name = crate::interner::intern("$_arg");

        let mut local_env = env.clone();
        local_env.insert_scheme(param_name, Scheme::mono(param_ty.clone()));

        let is_hole = |e: &Expr| matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_");
        let hole_ref = &crate::cst::QualifiedIdent { module: None, name: param_name };

        // Infer the body with direct `_` replaced by the parameter
        let body_ty = match expr {
            Expr::Op { .. } => {
                // Validate that _ appears at the top level after operator precedence.
                // Flatten the chain and check: _ at the left is valid iff the first
                // operator has the lowest (or equal-lowest) precedence; _ at the right
                // is valid iff the last operator has the lowest precedence.
                // e.g., `_ + 2 * 3` → valid (+ is lowest, _ is left operand of +)
                // e.g., `_ * 4 + 1` → invalid (* is NOT lowest, _ is nested inside _ * 4)
                {
                    let mut operands: Vec<&Expr> = Vec::new();
                    let mut operators: Vec<&crate::cst::Spanned<crate::cst::QualifiedIdent>> = Vec::new();
                    let mut current: &Expr = expr;
                    while let Expr::Op { left, op, right, .. } = current {
                        operands.push(left.as_ref());
                        operators.push(op);
                        current = right.as_ref();
                    }
                    operands.push(current);

                    if operators.len() > 1 {
                        // Find which operands are holes
                        let hole_positions: Vec<usize> = operands.iter().enumerate()
                            .filter(|(_, e)| is_hole(e))
                            .map(|(i, _)| i)
                            .collect();

                        // Find the minimum precedence among all operators
                        let min_prec = operators.iter()
                            .map(|op| self.get_fixity(op.value.name).1)
                            .min()
                            .unwrap_or(0);

                        for &pos in &hole_positions {
                            let valid = if pos == 0 {
                                // Left edge: valid iff first operator has the lowest precedence
                                self.get_fixity(operators[0].value.name).1 <= min_prec
                            } else if pos == operands.len() - 1 {
                                // Right edge: valid iff last operator has the lowest precedence
                                self.get_fixity(operators[operators.len() - 1].value.name).1 <= min_prec
                            } else {
                                // Middle: never valid in a multi-operator chain
                                false
                            };
                            if !valid {
                                return Err(TypeError::IncorrectAnonymousArgument {
                                    span: operands[pos].span(),
                                });
                            }
                        }
                    }
                }

                // Replace all `_` holes in the Op chain with variable references,
                // then infer normally (handles nested Op chains like `_ + 2 * 3`)
                let replaced = self.replace_underscore_in_op_chain(expr, param_name);
                self.infer(&local_env, &replaced)?
            }
            Expr::App { span, func, arg } => {
                // Check if this is a record update underscore section: _ {field = value}
                if is_hole(func) {
                    if let Expr::Record { fields, .. } = arg.as_ref() {
                        if !fields.is_empty() && fields.iter().all(|f| f.is_update && f.value.is_some()) {
                            let updates: Vec<crate::cst::RecordUpdate> = fields.iter().filter_map(|f| {
                                Some(crate::cst::RecordUpdate { span: f.span, label: f.label.clone(), value: f.value.clone()? })
                            }).collect();
                            if !updates.is_empty() {
                                // Create a var expression referencing the lambda parameter
                                let param_var = Expr::Var {
                                    span: func.span(),
                                    name: crate::cst::QualifiedIdent { module: None, name: param_name },
                                };
                                return Ok(Type::fun(
                                    param_ty,
                                    self.infer_record_update(&local_env, *span, &param_var, &updates)?,
                                ));
                            }
                        }
                    }
                }
                let func_ty = if is_hole(func) {
                    self.infer_var(&local_env, func.span(), hole_ref)?
                } else {
                    self.infer(&local_env, func)?
                };
                let arg_ty = if is_hole(arg) {
                    self.infer_var(&local_env, arg.span(), hole_ref)?
                } else {
                    self.infer(&local_env, arg)?
                };
                let result_ty = Type::Unif(self.state.fresh_var());
                self.state.unify(*span, &func_ty, &Type::fun(arg_ty, result_ty.clone()))?;
                result_ty
            }
            _ => unreachable!("has_direct_underscore_hole only matches Op/App"),
        };

        Ok(Type::fun(param_ty, body_ty))
    }

    fn infer_record(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        fields: &[crate::cst::RecordField],
    ) -> Result<Type, TypeError> {
        // Check for duplicate labels
        let mut label_spans: HashMap<Symbol, Vec<crate::ast::span::Span>> = HashMap::new();
        for field in fields {
            label_spans.entry(field.label.value).or_default().push(field.span);
        }
        for (name, spans) in &label_spans {
            if spans.len() > 1 {
                return Err(TypeError::DuplicateLabel {
                    record_span: span,
                    field_spans: spans.clone(),
                    name: *name,
                });
            }
        }

        // Check if any field values are `_` holes (anonymous function / operator section).
        // `{ init: _, last: _ }` desugars to `\a b -> { init: a, last: b }`
        let is_underscore_hole = |e: &Expr| matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_");
        let has_underscore_fields = fields.iter().any(|f| f.value.as_ref().map_or(false, |v| is_underscore_hole(v)));

        let mut field_types = Vec::new();
        let mut section_params: Vec<Type> = Vec::new();
        for field in fields {
            let field_ty = if let Some(ref value) = field.value {
                if is_underscore_hole(value) {
                    // Each `_` becomes a fresh lambda parameter
                    let param_ty = Type::Unif(self.state.fresh_var());
                    section_params.push(param_ty.clone());
                    param_ty
                } else {
                    self.infer(env, value)?
                }
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
        let record_ty = Type::Record(field_types, None);
        if has_underscore_fields {
            // Wrap in function type: param1 -> param2 -> ... -> Record
            let mut result = record_ty;
            for param in section_params.into_iter().rev() {
                result = Type::fun(param, result);
            }
            Ok(result)
        } else {
            Ok(record_ty)
        }
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
            Type::Record(fields, tail) => {
                for (label, ty) in &fields {
                    if *label == field.value {
                        // Instantiate forall types: each access to a polymorphic field
                        // (e.g. `forall a. a -> m a`) gets a fresh instantiation.
                        let result = self.instantiate_forall_type(ty.clone())?;
                        return Ok(result);
                    }
                }
                // Field not in known fields — if record is open (has row tail),
                // unify the tail with a record containing the field + fresh tail
                if let Some(tail) = tail {
                    let field_ty = Type::Unif(self.state.fresh_var());
                    let new_tail = Type::Unif(self.state.fresh_var());
                    let extended = Type::Record(
                        vec![(field.value, field_ty.clone())],
                        Some(Box::new(new_tail)),
                    );
                    self.state.unify(span, &tail, &extended)?;
                    return Ok(field_ty);
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
        span: crate::ast::span::Span,
        expr: &Expr,
        updates: &[crate::cst::RecordUpdate],
    ) -> Result<Type, TypeError> {
        // Check if the record expression is an underscore hole (record update section)
        let record_is_section = Self::is_underscore_hole(expr);
        let record_ty = if record_is_section {
            Type::Unif(self.state.fresh_var())
        } else {
            self.infer(env, expr)?
        };

        // Infer update value types, tracking underscore holes for section desugaring
        let mut update_fields = Vec::new();
        let mut section_params: Vec<Type> = Vec::new();
        // Track nested updates: (label, old_field_type) — the old field type will be
        // unified with the record's actual field, so nested updates see the original.
        let mut nested_input_fields: Vec<(crate::interner::Symbol, Type)> = Vec::new();
        self.collect_record_update_fields(env, span, updates, &mut update_fields, &mut section_params, &mut nested_input_fields)?;

        // Build expected input record: { field1 :: old1, field2 :: old2, ... | tail }
        // where old_i are fresh type vars (the original field types before update)
        let tail = Type::Unif(self.state.fresh_var());
        let mut input_fields: Vec<(crate::interner::Symbol, Type)> = update_fields
            .iter()
            .map(|(label, _)| (*label, Type::Unif(self.state.fresh_var())))
            .collect();
        // Add nested update fields with their actual types from nested processing
        for (label, old_ty) in nested_input_fields {
            // Replace the fresh var for this field with the nested-resolved old type
            if let Some(f) = input_fields.iter_mut().find(|(l, _)| *l == label) {
                f.1 = old_ty;
            }
        }
        let input_record = Type::Record(input_fields, Some(Box::new(tail.clone())));

        // Unify the actual record type with our open record to extract the tail
        self.state.unify(span, &record_ty, &input_record)?;

        // Build result record: { field1 :: new1, field2 :: new2, ... | tail }
        let mut result_ty = Type::Record(update_fields, Some(Box::new(tail)));

        // Wrap in function types for each wildcard parameter (right to left)
        for param_ty in section_params.into_iter().rev() {
            result_ty = Type::fun(param_ty, result_ty);
        }

        // Wrap in function type for record section parameter
        if record_is_section {
            result_ty = Type::fun(record_ty, result_ty);
        }

        Ok(result_ty)
    }

    /// Collect update fields from a record update, handling nested updates and wildcards.
    /// Nested updates like `bar { baz = x }` access the original record's `bar` field
    /// and apply the inner updates to it.
    fn collect_record_update_fields(
        &mut self,
        env: &Env,
        span: crate::ast::span::Span,
        updates: &[crate::cst::RecordUpdate],
        update_fields: &mut Vec<(crate::interner::Symbol, Type)>,
        section_params: &mut Vec<Type>,
        nested_input_fields: &mut Vec<(crate::interner::Symbol, Type)>,
    ) -> Result<(), TypeError> {
        for update in updates {
            if Self::is_underscore_hole(&update.value) {
                // Wildcard: creates a lambda parameter
                let param_ty = Type::Unif(self.state.fresh_var());
                section_params.push(param_ty.clone());
                update_fields.push((update.label.value, param_ty));
            } else if let Expr::Record { fields, .. } = &update.value {
                // Check for nested record update: bar { baz = x, qux = y }
                if !fields.is_empty() && fields.iter().all(|f| f.is_update && f.value.is_some()) {
                    // Nested update: the bar field of the original record is accessed,
                    // and the inner fields are applied as updates to it.
                    let inner_updates: Vec<crate::cst::RecordUpdate> = fields.iter().filter_map(|f| {
                        Some(crate::cst::RecordUpdate {
                            span: f.span,
                            label: f.label.clone(),
                            value: f.value.clone()?,
                        })
                    }).collect();

                    // Process nested updates recursively
                    let mut inner_update_fields = Vec::new();
                    let mut inner_nested_input = Vec::new();
                    self.collect_record_update_fields(
                        env, span, &inner_updates,
                        &mut inner_update_fields, section_params, &mut inner_nested_input,
                    )?;

                    // Build nested record type: the old field type is an open record
                    let inner_tail = Type::Unif(self.state.fresh_var());
                    let mut inner_input_fields: Vec<(crate::interner::Symbol, Type)> = inner_update_fields
                        .iter()
                        .map(|(label, _)| (*label, Type::Unif(self.state.fresh_var())))
                        .collect();
                    // Apply deeper nested input fields
                    for (label, old_ty) in inner_nested_input {
                        if let Some(f) = inner_input_fields.iter_mut().find(|(l, _)| *l == label) {
                            f.1 = old_ty;
                        }
                    }
                    let inner_input_record = Type::Record(inner_input_fields, Some(Box::new(inner_tail.clone())));

                    // The old field type of this label in the outer record must match inner_input_record
                    nested_input_fields.push((update.label.value, inner_input_record));

                    // The new field value is the inner record with updated fields
                    let inner_result = Type::Record(inner_update_fields, Some(Box::new(inner_tail)));
                    update_fields.push((update.label.value, inner_result));
                } else {
                    let value_ty = self.infer(env, &update.value)?;
                    update_fields.push((update.label.value, value_ty));
                }
            } else {
                let value_ty = self.infer(env, &update.value)?;
                update_fields.push((update.label.value, value_ty));
            }
        }
        Ok(())
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

        // Pure do-blocks (no `<-` binds) don't require monadic wrapping
        let has_binds = statements
            .iter()
            .any(|s| matches!(s, crate::cst::DoStatement::Bind { .. }));

        // Check that `bind` is in scope when do-notation uses bind (module mode only)
        if self.module_mode && has_binds {
            let bind_sym = crate::interner::intern("bind");
            if env.lookup(bind_sym).is_none() {
                return Err(TypeError::UndefinedVariable { span, name: bind_sym });
            }
        }

        // Check that `discard` is in scope when do-notation has non-last discards
        let has_non_last_discards = statements.len() > 1
            && statements[..statements.len() - 1]
                .iter()
                .any(|s| matches!(s, crate::cst::DoStatement::Discard { .. }));
        if self.module_mode && has_non_last_discards {
            let discard_sym = crate::interner::intern("discard");
            if env.lookup(discard_sym).is_none() {
                return Err(TypeError::UndefinedVariable { span, name: discard_sym });
            }
        }

        for (i, stmt) in statements.iter().enumerate() {
            let is_last = i == statements.len() - 1;
            match stmt {
                crate::cst::DoStatement::Discard { expr, .. } => {
                    let expr_ty = self.infer(&current_env, expr)?;
                    if is_last {
                        if has_binds {
                            // Last statement in monadic do: m a
                            let result_inner = Type::Unif(self.state.fresh_var());
                            let expected = Type::app(monad_ty.clone(), result_inner.clone());
                            self.state.unify(span, &expr_ty, &expected)?;
                        }
                        return Ok(expr_ty);
                    } else if has_binds {
                        // Non-last discard in monadic do: m _
                        let discard_inner = Type::Unif(self.state.fresh_var());
                        let expected = Type::app(monad_ty.clone(), discard_inner);
                        self.state.unify(span, &expr_ty, &expected)?;
                    }
                }
                crate::cst::DoStatement::Bind { binder, expr, .. } => {
                    // Check for reserved do-notation names
                    check_do_reserved_names(binder)?;
                    let expr_ty = self.infer(&current_env, expr)?;
                    // expr : m a, bind binder to a
                    let inner_ty = Type::Unif(self.state.fresh_var());
                    let expected = Type::app(monad_ty.clone(), inner_ty.clone());
                    self.state.unify(span, &expr_ty, &expected)?;
                    self.infer_binder(&mut current_env, binder, &inner_ty)?;
                }
                crate::cst::DoStatement::Let { bindings, .. } => {
                    // Check for reserved do-notation names in let bindings
                    for binding in bindings {
                        if let LetBinding::Value { binder, .. } = binding {
                            check_do_reserved_names(binder)?;
                        }
                    }
                    self.process_let_bindings(&mut current_env, bindings)?;
                }
            }
        }

        // If we get here, the last statement was a Bind or Let
        match statements.last() {
            Some(crate::cst::DoStatement::Bind { span: bind_span, .. }) => {
                Err(TypeError::InvalidDoBind { span: *bind_span })
            }
            Some(crate::cst::DoStatement::Let { span: let_span, .. }) => {
                Err(TypeError::InvalidDoLet { span: *let_span })
            }
            _ => Err(TypeError::NotImplemented {
                span,
                feature: "do block must end with an expression".to_string(),
            })
        }
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
                // Check constructor arity against ctor_details if available
                let lookup_name = if let Some(module) = name.module {
                    Self::qualified_symbol(module, name.name)
                } else {
                    name.name
                };
                if let Some((_, _, field_types)) = self.ctor_details.get(&lookup_name) {
                    let expected_arity = field_types.len();
                    if args.len() != expected_arity {
                        return Err(TypeError::IncorrectConstructorArity {
                            span: *span,
                            name: name.name,
                            expected: expected_arity,
                            found: args.len(),
                        });
                    }
                }

                // Look up constructor type in env (handle qualified names)
                let lookup_result = env.lookup(lookup_name);
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
                                    return Err(TypeError::IncorrectConstructorArity {
                                        span: *span,
                                        name: name.name,
                                        expected: 0,
                                        found: args.len(),
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
                let annotated = convert_type_expr(ty, &self.type_operators, &self.known_types)?;
                let annotated = self.instantiate_wildcards(&annotated);
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
                // Check if the operator aliases a function (not a constructor).
                // Only data constructor operators are valid in binder patterns.
                if self.function_op_aliases.contains(&op.value) {
                    return Err(TypeError::InvalidOperatorInBinder {
                        span: op.span,
                        op: op.value,
                    });
                }
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
                // Check for duplicate labels
                let mut label_spans: HashMap<Symbol, Vec<crate::ast::span::Span>> = HashMap::new();
                for field in fields {
                    label_spans.entry(field.label.value).or_default().push(field.span);
                }
                for (name, spans) in &label_spans {
                    if spans.len() > 1 {
                        return Err(TypeError::DuplicateLabel {
                            record_span: *span,
                            field_spans: spans.clone(),
                            name: *name,
                        });
                    }
                }

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
                let mut found_non_exhaustive_guard = false;
                for guard in guards {
                    // Each guard gets its own environment for pattern bindings.
                    // Pattern guards (`| Pat <- expr`) bind variables that are
                    // available in subsequent guard conditions and the body.
                    let mut guard_env = env.child();
                    for pattern in &guard.patterns {
                        match pattern {
                            GuardPattern::Boolean(expr) => {
                                let ty = self.infer(&guard_env, expr)?;
                                self.state.unify(guard.span, &ty, &Type::boolean())?;
                            }
                            GuardPattern::Pattern(binder, expr) => {
                                let expr_ty = self.infer(&guard_env, expr)?;
                                self.infer_binder(&mut guard_env, binder, &expr_ty)?;
                                // Check if this pattern guard is non-exhaustive.
                                // A guard is non-exhaustive if:
                                // 1. The binder is a literal (literals never cover all cases)
                                // 2. The binder is a constructor and check_exhaustiveness says
                                //    not all constructors are covered
                                // A wildcard or variable binder is always exhaustive.
                                let is_non_exhaustive = match binder {
                                    Binder::Literal { .. } => true,
                                    Binder::Wildcard { .. } | Binder::Var { .. } => false,
                                    _ => {
                                        let zonked_ty = self.state.zonk(expr_ty);
                                        let binders_ref: Vec<&Binder> = vec![binder];
                                        check_exhaustiveness(
                                            &binders_ref,
                                            &zonked_ty,
                                            &self.data_constructors,
                                            &self.ctor_details,
                                        ).is_some()
                                    }
                                };
                                if is_non_exhaustive {
                                    found_non_exhaustive_guard = true;
                                }
                            }
                        }
                    }
                    let body_ty = self.infer(&guard_env, &guard.expr)?;
                    self.state.unify(guard.span, &result_ty, &body_ty)?;
                }
                if found_non_exhaustive_guard {
                    self.has_non_exhaustive_pattern_guards = true;
                }
                Ok(result_ty)
            }
        }
    }
}

/// Check for overlapping variable names within a set of binders (e.g. a case alternative).
/// Returns an error if the same variable appears more than once.
pub fn check_overlapping_pattern_vars(binders: &[&Binder]) -> Option<TypeError> {
    let mut seen: HashMap<Symbol, Vec<crate::ast::span::Span>> = HashMap::new();
    for binder in binders {
        collect_pattern_vars(binder, &mut seen);
    }
    for (name, spans) in seen {
        if spans.len() > 1 {
            return Some(TypeError::OverlappingPattern {
                spans,
                name,
            });
        }
    }
    None
}

fn collect_pattern_vars(binder: &Binder, seen: &mut HashMap<Symbol, Vec<crate::ast::span::Span>>) {
    match binder {
        Binder::Var { name, .. } => {
            seen.entry(name.value).or_default().push(name.span);
        }
        Binder::Constructor { args, .. } => {
            for arg in args {
                collect_pattern_vars(arg, seen);
            }
        }
        Binder::Parens { binder, .. } => collect_pattern_vars(binder, seen),
        Binder::As { name, binder, .. } => {
            seen.entry(name.value).or_default().push(name.span);
            collect_pattern_vars(binder, seen);
        }
        Binder::Typed { binder, .. } => collect_pattern_vars(binder, seen),
        Binder::Array { elements, .. } => {
            for elem in elements {
                collect_pattern_vars(elem, seen);
            }
        }
        Binder::Op { left, right, .. } => {
            collect_pattern_vars(left, seen);
            collect_pattern_vars(right, seen);
        }
        Binder::Record { fields, .. } => {
            for field in fields {
                if let Some(binder) = &field.binder {
                    collect_pattern_vars(binder, seen);
                }
                // Pun { x } is not collected here — duplicate labels are caught by DuplicateLabel
            }
        }
        Binder::Wildcard { .. } | Binder::Literal { .. } => {}
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
        Binder::Op { op, .. } => {
            // Operator patterns (e.g. `a : as` for Cons, `a :| bs` for NonEmpty)
            // contribute to constructor exhaustiveness.
            // The operator itself may be an alias — covered will contain the operator symbol,
            // and check_exhaustiveness will resolve it to the actual constructor.
            if !covered.contains(&op.value) {
                covered.push(op.value);
            }
        }
        Binder::Array { .. } | Binder::Record { .. } => {
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
            for (v, _) in vars {
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
                            n == "otherwise" && (module_name.is_none() || module_name.as_deref() == Some("Prelude") || module_name.as_deref() == Some("Data.Boolean"))
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

    // Resolve operator aliases in covered set: if a covered symbol (e.g. operator `:`)
    // is NOT one of the declared constructors but has identical ctor_details as one,
    // then they are aliases (e.g. `:` is an alias for `Cons`).
    let mut resolved_covered = covered.clone();
    for &op_sym in &covered {
        // Only resolve aliases for symbols that aren't already declared constructors
        if all_ctors.contains(&op_sym) {
            continue;
        }
        if let Some(op_details) = ctor_details.get(&op_sym) {
            for &ctor in all_ctors {
                if !resolved_covered.contains(&ctor) {
                    if let Some(ctor_det) = ctor_details.get(&ctor) {
                        if op_details == ctor_det {
                            resolved_covered.push(ctor);
                        }
                    }
                }
            }
        }
    }

    // Find missing constructors at this level
    let missing_at_this_level: Vec<Symbol> = all_ctors
        .iter()
        .filter(|c| !resolved_covered.contains(c))
        .copied()
        .collect();

    if !missing_at_this_level.is_empty() {
        // Missing constructors — report them
        let missing_strs: Vec<String> = missing_at_this_level
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

/// Check if an expression directly references a given name (not under a lambda).
/// Used for cycle detection in let-bindings: `let x = x in x` is a cycle.
fn expr_references_name(expr: &Expr, target: Symbol, let_names: &HashSet<Symbol>) -> bool {
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => {
            if name.name == target {
                return true;
            }
            // Check for indirect cycles: x = y, y = x (though let bindings
            // don't support mutual references in the same way top-level does)
            false
        }
        Expr::App { func, arg, .. } => {
            expr_references_name(func, target, let_names)
                || expr_references_name(arg, target, let_names)
        }
        Expr::If { cond, then_expr, else_expr, .. } => {
            expr_references_name(cond, target, let_names)
                || expr_references_name(then_expr, target, let_names)
                || expr_references_name(else_expr, target, let_names)
        }
        Expr::Case { exprs, alts, .. } => {
            exprs.iter().any(|e| expr_references_name(e, target, let_names))
                || alts.iter().any(|alt| match &alt.result {
                    GuardedExpr::Unconditional(e) => expr_references_name(e, target, let_names),
                    GuardedExpr::Guarded(guards) => guards.iter().any(|g| expr_references_name(&g.expr, target, let_names)),
                })
        }
        Expr::Parens { expr, .. } => expr_references_name(expr, target, let_names),
        Expr::TypeAnnotation { expr, .. } => expr_references_name(expr, target, let_names),
        Expr::Negate { expr, .. } => expr_references_name(expr, target, let_names),
        Expr::Array { elements, .. } => elements.iter().any(|e| expr_references_name(e, target, let_names)),
        Expr::Record { fields, .. } => fields.iter().any(|f| f.value.as_ref().map_or(false, |v| expr_references_name(v, target, let_names))),
        Expr::RecordAccess { expr, .. } => expr_references_name(expr, target, let_names),
        Expr::RecordUpdate { expr, updates, .. } => {
            expr_references_name(expr, target, let_names)
                || updates.iter().any(|u| expr_references_name(&u.value, target, let_names))
        }
        Expr::Op { left, right, .. } => {
            expr_references_name(left, target, let_names)
                || expr_references_name(right, target, let_names)
        }
        Expr::Do { statements, .. } | Expr::Ado { statements, .. } => {
            statements.iter().any(|s| match s {
                crate::cst::DoStatement::Discard { expr, .. } => expr_references_name(expr, target, let_names),
                crate::cst::DoStatement::Bind { expr, .. } => expr_references_name(expr, target, let_names),
                crate::cst::DoStatement::Let { bindings, .. } => bindings.iter().any(|b| {
                    if let LetBinding::Value { expr, .. } = b { expr_references_name(expr, target, let_names) } else { false }
                }),
            })
        }
        // Lambda creates a new scope — references under lambda are OK (recursion)
        Expr::Lambda { .. } => false,
        // Let creates subscope — skip to avoid false positives
        Expr::Let { .. } => false,
        _ => false,
    }
}
