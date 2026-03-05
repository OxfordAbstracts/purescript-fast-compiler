use std::collections::{HashMap, HashSet};

use crate::ast::{Binder, Expr, GuardPattern, GuardedExpr, LetBinding, Literal};
use crate::cst::{Associativity, QualifiedIdent, unqualified_ident};
use crate::interner::Symbol;
use crate::typechecker::convert::convert_type_expr;
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::{Role, Scheme, Type};
use crate::typechecker::unify::UnifyState;

/// Convert an ast::Expr to an ast::TypeExpr for VTA reinterpretation.
/// Returns None if the expression can't be converted to a type.
fn expr_to_type_expr(expr: &Expr) -> Option<crate::ast::TypeExpr> {
    use crate::ast::TypeExpr;
    use crate::ast::DefinitionSite;
    use crate::cst::Spanned;
    match expr {
        Expr::Var { span, name, .. } => Some(TypeExpr::Var {
            span: *span,
            name: Spanned::new(name.name, *span),
        }),
        Expr::Constructor { span, name, .. } => Some(TypeExpr::Constructor {
            span: *span,
            name: name.clone(),
            definition_site: DefinitionSite::Local(*span),
        }),
        Expr::App { span, func, arg } => Some(TypeExpr::App {
            span: *span,
            constructor: Box::new(expr_to_type_expr(func)?),
            arg: Box::new(expr_to_type_expr(arg)?),
        }),
        Expr::Hole { span, name } => Some(TypeExpr::Hole {
            span: *span,
            name: *name,
        }),
        Expr::Literal { span, lit: Literal::String(s) } => Some(TypeExpr::StringLiteral {
            span: *span,
            value: s.clone(),
        }),
        Expr::Literal { span, lit: Literal::Int(n) } => Some(TypeExpr::IntLiteral {
            span: *span,
            value: *n,
        }),
        _ => None,
    }
}

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
    pub class_methods: HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>)>,
    /// Deferred type class constraints: (span, class_name, [type_args as unif vars]).
    /// Checked after inference to verify instances exist.
    pub deferred_constraints: Vec<(crate::span::Span, QualifiedIdent, Vec<Type>)>,
    /// Map from type constructor name → list of data constructor names.
    /// Used for exhaustiveness checking of case expressions.
    pub data_constructors: HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
    /// Map from type-level operator symbol → target type constructor name.
    /// Populated from `infixr N type TypeName as op` declarations.
    pub type_operators: HashMap<QualifiedIdent, QualifiedIdent>,
    /// Map from data constructor name → (parent type name, type var symbols, field types).
    /// Used for nested exhaustiveness checking to know each constructor's field types.
    pub ctor_details: HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
    /// Number of type parameters for each known type constructor.
    /// Used to detect over-applied types after type alias expansion.
    pub type_con_arities: HashMap<QualifiedIdent, usize>,
    /// Type aliases whose body has kind `Type` (declared with `{ }` record syntax).
    /// Used to detect invalid row tails like `{ | Foo }` where `Foo = { x :: Number }`.
    pub record_type_aliases: HashSet<QualifiedIdent>,
    /// Type aliases: name → (type_var_names, expanded_body).
    /// E.g. `type Fn1 a b = a -> b` → ("Fn1", ([a, b], Fun(Var(a), Var(b))))
    pub type_aliases: HashMap<QualifiedIdent, (Vec<QualifiedIdent>, Type)>,
    /// Qualified type alias names (e.g. "CJ.PropCodec") for disambiguation.
    /// When convert_type_expr encounters a qualified type constructor that's in this set,
    /// it uses the qualified symbol for Type::Con, allowing alias expansion to find the
    /// correct module-specific alias body instead of the last-import-wins unqualified one.
    pub qualified_type_alias_names: HashSet<QualifiedIdent>,
    /// Value-level operator fixities: operator_symbol → (associativity, precedence).
    /// Used for re-associating operator chains during inference.
    pub value_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// Value-level operators that alias functions (NOT constructors).
    /// Used to detect invalid operator usage in binder patterns.
    pub function_op_aliases: HashSet<QualifiedIdent>,
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
    pub operator_class_targets: HashMap<QualifiedIdent, QualifiedIdent>,
    /// Deferred constraints from operator usage (e.g. `<>` → Semigroup constraint).
    /// Only used for CannotGeneralizeRecursiveFunction detection, NOT for instance
    /// resolution (the instance matcher can't handle complex nested types).
    pub op_deferred_constraints: Vec<(crate::span::Span, QualifiedIdent, Vec<Type>)>,
    /// Map from class name → (type_vars, fundeps as (lhs_indices, rhs_indices)).
    /// Used for fundep-aware orphan instance checking.
    pub class_fundeps: HashMap<QualifiedIdent, (Vec<Symbol>, Vec<(Vec<usize>, Vec<usize>)>)>,
    /// Whether the last infer_guarded found non-exhaustive pattern guards.
    /// Set during inference, consumed by check.rs to emit Partial constraint.
    pub has_non_exhaustive_pattern_guards: bool,
    /// Constraints from type signatures: function name → list of (class_name, type_args).
    /// When a function with signature constraints is called, these are instantiated
    /// with the forall substitution and added as deferred constraints.
    pub signature_constraints: HashMap<QualifiedIdent, Vec<(QualifiedIdent, Vec<Type>)>>,
    /// Deferred constraints from signature propagation (separate from main deferred_constraints).
    /// These are only checked for zero-instance classes, since our instance resolution
    /// may not handle complex imported instances correctly.
    pub sig_deferred_constraints: Vec<(crate::span::Span, QualifiedIdent, Vec<Type>)>,
    /// Classes with instance chains (else keyword). Used to route chained class constraints
    /// to deferred_constraints for proper chain ambiguity checking.
    pub chained_classes: std::collections::HashSet<QualifiedIdent>,
    /// Roles for each type constructor: type_name → [Role per type parameter].
    /// Populated from role declarations and inferred from constructor fields.
    pub type_roles: HashMap<Symbol, Vec<Role>>,
    /// Set of type names declared as newtypes (for Coercible solving).
    pub newtype_names: HashSet<QualifiedIdent>,
    /// Type variables in scope from enclosing forall declarations (scoped type variables).
    /// Used to validate that where/let binding type signatures only reference bound vars.
    pub scoped_type_vars: HashSet<Symbol>,
    /// Class names whose constraints are "given" by the current enclosing instance.
    /// Constraints deferred for these classes within instance method bodies are skipped.
    pub given_class_names: HashSet<QualifiedIdent>,
    /// Deferred types to kind-check after inference completes for each declaration.
    /// Collected from lambda inference and type annotations. Each entry is (type, span).
    /// These are zonked and kind-checked post-inference to catch kind errors like
    /// type-level literals used as function arguments (e.g., `"foo" -> String`).
    pub deferred_kind_checks: Vec<(Type, crate::span::Span)>,
    /// Whether a lambda with refutable binders was inferred during the current declaration.
    /// Set during inference, consumed by check.rs to emit NoInstanceFound for Partial.
    /// Unlike has_non_exhaustive_pattern_guards, this is independent of the enclosing
    /// function's guard structure (lambdas are always partial regardless of the caller).
    pub has_partial_lambda: bool,
    /// Functions whose type signature has Partial in a function parameter position,
    /// e.g. `unsafePartial :: (Partial => a) -> a`. When applied to a partial expression,
    /// these functions discharge the Partial constraint.
    pub partial_dischargers: HashSet<QualifiedIdent>,
    /// Map from class parameter unif var ID → application arguments in the method type.
    /// When a class method like `imap :: (a -> b) -> f x y a -> f x y b` is used,
    /// the class parameter `f` is applied to arguments `[x, y, a]`. We store the
    /// fresh unif vars for these args so that at constraint resolution time we can
    /// check kind consistency between the class kind signature and the concrete types.
    pub class_param_app_args: HashMap<crate::typechecker::types::TyVarId, Vec<Type>>,
    /// Canonical class method type schemes, indexed by method name symbol.
    /// Unlike the env, these are NEVER overwritten by value imports.
    /// Used when computing instance method expected types so that an explicit
    /// `import Data.Array (foldl)` does not shadow the `Foldable.foldl` scheme
    /// that the instance checker needs.
    pub class_method_schemes: HashMap<Symbol, Scheme>,
    /// Non-exhaustive pattern errors collected during case expression inference.
    /// Consumed by check.rs to emit NonExhaustivePattern errors.
    pub non_exhaustive_errors: Vec<crate::typechecker::error::TypeError>,
    /// Alias names that were inserted into `state.type_aliases` under unqualified keys
    /// solely because of qualified imports (e.g. `import M as Q`). These should NOT be
    /// re-exported, since in PureScript qualified imports don't make names available
    /// unqualified. If a subsequent unqualified import provides the same alias name,
    /// it's removed from this set.
    pub qualified_import_unqual_aliases: HashSet<Symbol>,
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
            type_con_arities: HashMap::new(),
            record_type_aliases: HashSet::new(),
            type_aliases: HashMap::new(),
            qualified_type_alias_names: HashSet::new(),
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
            given_class_names: HashSet::new(),
            type_roles: HashMap::new(),
            newtype_names: HashSet::new(),
            scoped_type_vars: HashSet::new(),
            deferred_kind_checks: Vec::new(),
            has_partial_lambda: false,
            partial_dischargers: HashSet::new(),
            class_param_app_args: HashMap::new(),
            class_method_schemes: HashMap::new(),
            non_exhaustive_errors: Vec::new(),
            qualified_import_unqual_aliases: HashSet::new(),
        }
    }


    /// Create a qualified symbol by combining a module alias with a name.
    fn qualified_symbol(module: Symbol, name: Symbol) -> Symbol {
        crate::interner::intern_qualified(module, name)
    }

    /// Find the first occurrence of `Unif(target_id)` as the head of an App chain
    /// in the given type, and return the arguments it's applied to.
    /// E.g., in `Fun(?a -> ?b, App(App(App(?f, ?x), ?y), ?a))` with target = ?f's id,
    /// returns `[?x, ?y, ?a]`.
    fn extract_app_args_of(ty: &Type, target_id: crate::typechecker::types::TyVarId) -> Option<Vec<Type>> {
        match ty {
            Type::App(_, _) => {
                // Decompose app chain to find head + args
                let mut args = Vec::new();
                let mut head = ty;
                while let Type::App(f, a) = head {
                    args.push((**a).clone());
                    head = f;
                }
                args.reverse();
                if let Type::Unif(id) = head {
                    if *id == target_id {
                        return Some(args);
                    }
                }
                // Recurse into sub-types
                let mut cur = ty;
                while let Type::App(f, a) = cur {
                    if let Some(found) = Self::extract_app_args_of(a, target_id) {
                        return Some(found);
                    }
                    cur = f;
                }
                None
            }
            Type::Fun(a, b) => {
                Self::extract_app_args_of(a, target_id)
                    .or_else(|| Self::extract_app_args_of(b, target_id))
            }
            Type::Forall(_, body) => Self::extract_app_args_of(body, target_id),
            Type::Record(fields, tail) => {
                for (_, field_ty) in fields {
                    if let Some(found) = Self::extract_app_args_of(field_ty, target_id) {
                        return Some(found);
                    }
                }
                if let Some(t) = tail {
                    return Self::extract_app_args_of(t, target_id);
                }
                None
            }
            _ => None,
        }
    }

    /// Infer the type of an expression in the given environment.
    pub fn infer(&mut self, env: &Env, expr: &Expr) -> Result<Type, TypeError> {
        super::check_deadline();
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
            Expr::Var { span, name, .. } => self.infer_var(env, *span, name),
            Expr::Constructor { span, name, .. } => self.infer_var(env, *span, name),
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
            Expr::Negate { span, expr } => self.infer_negate(env, *span, expr),
            Expr::Case { span, exprs, alts } => self.infer_case(env, *span, exprs, alts),
            Expr::Array { span, elements } => self.infer_array(env, *span, elements),
            Expr::Hole { span, name } => self.infer_hole(*span, *name),
            Expr::Record { span, fields } => self.infer_record(env, *span, fields),
            Expr::RecordAccess { span, expr, field } => self.infer_record_access(env, *span, expr, field),
            Expr::RecordUpdate { span, expr, updates } => self.infer_record_update(env, *span, expr, updates),
            Expr::Do { span, module, statements } => {
                if let Some(m) = module {
                    self.infer_qualified_do(env, *span, *m, statements)
                } else {
                    self.infer_do(env, *span, statements)
                }
            }
            Expr::Ado { span, statements, result, .. } => self.infer_ado(env, *span, statements, result),
            Expr::VisibleTypeApp { span, func, ty } => self.infer_visible_type_app(env, *span, func, ty),
            Expr::AsPattern { span, name, pattern } => {
                match expr_to_type_expr(pattern) {
                    Some(ty_expr) => self.infer_visible_type_app(env, *span, name, &ty_expr),
                    None => Err(TypeError::NotImplemented {
                        span: *span,
                        feature: format!("as-pattern in expression context"),
                    }),
                }
            }
            other => Err(TypeError::NotImplemented {
                span: other.span(),
                feature: format!("inference for this expression form"),
            }),
        }
    }

    fn infer_literal(
        &mut self,
        _span: crate::span::Span,
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
        span: crate::span::Span,
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

        let lookup_result = env.lookup(resolved_name);
        match lookup_result {
            Some(scheme) => {
                let ty = self.instantiate(scheme);

                // If this is a class method (or an operator aliasing one), capture the constraint.
                // Operators like `<>` map to class methods like `append` via operator_class_targets.
                let class_method_lookup = self.class_methods.get(name).cloned()
                    .or_else(|| {
                        self.operator_class_targets.get(name)
                            .and_then(|target| self.class_methods.get(target).cloned())
                    });
                if let Some((class_name, class_tvs)) = class_method_lookup {
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

                            // Record what the class parameter is applied to in the method type.
                            // E.g., for `imap :: (a->b) -> f x y a -> f x y b`, record [?x, ?y, ?a].
                            // Used at constraint resolution time for kind checking.
                            if constraint_types.len() == 1 {
                                if let Type::Unif(param_id) = &constraint_types[0] {
                                    if let Some(args) = Self::extract_app_args_of(&result, *param_id) {
                                        self.class_param_app_args.insert(*param_id, args);
                                    }
                                }
                            }

                            if !self.given_class_names.contains(&class_name) {
                                self.deferred_constraints.push((span, class_name, constraint_types));
                            }

                            return Ok(result);
                        }
                    }
                }

                // If the scheme's type is a Forall, also instantiate that
                // and propagate any signature constraints
                let lookup_name = *name;
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
                                let class_str = crate::interner::resolve(class_name.name).unwrap_or_default();
                                let has_solver = matches!(class_str.as_str(),
                                    "Lacks" | "Append" | "ToString" | "Add" | "Mul" | "Compare" | "Coercible" | "Nub"
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

    /// Skolemize a forall type: replace bound variables with unique rigid Type::Var names.
    /// Unlike instantiate_forall_type (which uses flexible unif vars), this creates rigid
    /// variables that cannot be unified with anything except themselves. Used for rank-2
    /// checking: when a lambda is passed where a polymorphic argument is expected, the
    /// lambda must work for ALL types, not just one specific type.
    fn skolemize_forall_type(&mut self, ty: Type) -> Type {
        match ty {
            Type::Forall(vars, body) => {
                let base = self.state.var_count();
                let subst: HashMap<Symbol, Type> = vars
                    .iter()
                    .enumerate()
                    .map(|(i, &(v, _))| {
                        let name = crate::interner::resolve(v).unwrap_or_default();
                        let rigid_name = crate::interner::intern(&format!("${}_{}", name, base as usize + i));
                        (v, Type::Var(rigid_name))
                    })
                    .collect();
                self.apply_symbol_subst(&subst, &body)
            }
            other => other,
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
                let mut inner_subst = subst.clone();
                for (v, _) in vars {
                    inner_subst.remove(v);
                }
                // Capture-avoiding: check if any forall-bound var name appears
                // free in the substitution values. If so, alpha-rename to avoid capture.
                // Also conservatively rename when substitution values contain unification
                // variables, since those may later be solved to types containing the
                // forall-bound var names, causing capture.
                let mut new_vars = vars.clone();
                let any_subst_has_unif = inner_subst.values().any(|val| super::unify::contains_unif_var(val));
                let needs_rename = any_subst_has_unif || new_vars.iter().any(|(v, _)| {
                    inner_subst.values().any(|val| super::unify::type_has_free_var(val, *v))
                });
                if needs_rename {
                    let mut rename: HashMap<Symbol, Type> = HashMap::new();
                    for (v, _) in &mut new_vars {
                        if any_subst_has_unif || inner_subst.values().any(|val| super::unify::type_has_free_var(val, *v)) {
                            let fresh = super::unify::fresh_type_var_symbol(*v);
                            rename.insert(*v, Type::Var(fresh));
                            *v = fresh;
                        }
                    }
                    let renamed_body = self.apply_symbol_subst(&rename, body);
                    Type::Forall(new_vars, Box::new(self.apply_symbol_subst(&inner_subst, &renamed_body)))
                } else {
                    Type::Forall(new_vars, Box::new(self.apply_symbol_subst(&inner_subst, body)))
                }
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
        _span: crate::span::Span,
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

        // Check for partial lambda: if any binder is refutable and the pattern
        // doesn't cover all constructors, the lambda is partial.
        // We check AFTER inference so parameter types are resolved.
        for (binder, param_ty) in binders.iter().zip(param_types.iter()) {
            if is_refutable(binder) {
                let zonked_ty = self.state.zonk(param_ty.clone());
                let binders_ref: Vec<&Binder> = vec![binder];
                if check_exhaustiveness(&binders_ref, &zonked_ty, &self.data_constructors, &self.ctor_details).is_some() {
                    self.has_partial_lambda = true;
                    break;
                }
                // Record binders with refutable sub-binders (e.g., { sound: Moo })
                // are not caught by check_exhaustiveness (which checks top-level
                // constructors). Detect these by checking if the binder is a record
                // with refutable field sub-binders that are truly refutable (not
                // single-constructor types like newtypes).
                if let Binder::Record { fields, .. } = binder {
                    if fields.iter().any(|f| f.binder.as_ref().map_or(false, |b| {
                        is_truly_refutable(b, &self.data_constructors)
                    })) {
                        self.has_partial_lambda = true;
                        break;
                    }
                }
            }
        }

        // Build the function type right-to-left: t1 -> t2 -> ... -> body_ty
        let mut result = body_ty;
        for param_ty in param_types.into_iter().rev() {
            result = Type::fun(param_ty, result);
        }

        // Defer kind checking of this lambda's type. After inference completes,
        // the param types will be resolved and we can check that function domains
        // have kind Type (catching cases like `"foo" -> String`).
        self.deferred_kind_checks.push((result.clone(), _span));

        Ok(result)
    }

    /// Bidirectional type checking: check an expression against an expected type.
    /// For lambda expressions, this pushes the expected parameter types into the
    /// binders, enabling higher-rank polymorphism to be preserved through lambdas.
    pub fn check_against(&mut self, env: &Env, expr: &Expr, expected: &Type) -> Result<Type, TypeError> {
        super::check_deadline();
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
                            // remaining is not a Fun (e.g. a unif var from a wildcard `_`).
                            // Decompose it: unify remaining = param_ty -> ?ret so that
                            // the signature correctly captures all lambda parameters.
                            let param_ty = Type::Unif(self.state.fresh_var());
                            let ret_ty = Type::Unif(self.state.fresh_var());
                            let fun_ty = Type::fun(param_ty.clone(), ret_ty.clone());
                            let _ = self.state.unify(binder.span(), &remaining, &fun_ty);
                            self.infer_binder(&mut current_env, binder, &param_ty)?;
                            param_types.push(param_ty);
                            remaining = ret_ty;
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
        span: crate::span::Span,
        func: &Expr,
        arg: &Expr,
    ) -> Result<Type, TypeError> {
        // Detect record update syntax: expr { field = value, ... }
        // The grammar parses this as App(expr, Record { fields }) with is_update=true.
        // In PureScript, record updates bind tighter than function application:
        // `f x { a = 1 }` means `f (x { a = 1 })`, not `(f x) { a = 1 }`.
        if let Expr::Record { fields, .. } = arg {
            if !fields.is_empty() && fields.iter().all(|f| f.is_update && f.value.is_some()) {
                let updates: Vec<crate::ast::RecordUpdate> = fields
                    .iter()
                    .filter_map(|f| {
                        Some(crate::ast::RecordUpdate {
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
        if Self::expr_is_lambda(arg) {
            let func_ty_z = self.state.zonk(func_ty.clone());
            if let Type::Fun(param, result) = func_ty_z {
                if Self::type_contains_forall(&param) {
                    // Skolemize top-level Forall in param: replace bound vars with
                    // rigid Type::Var so the lambda must work for ALL types.
                    // Inner Foralls (e.g. in `(forall a. a -> a) -> Int` the param
                    // is Fun(Forall(...), Int)) are NOT at top level, so they pass
                    // through to check_against where they're kept polymorphic.
                    let skolemized_param = self.skolemize_forall_type(*param);
                    self.check_against(env, arg, &skolemized_param)?;
                    return Ok(*result);
                }
            }
        }

        // If the function discharges Partial (has `Partial =>` in its parameter type,
        // e.g. `unsafePartial :: (Partial => a) -> a`), save and restore has_partial_lambda
        // around the argument inference so partial lambdas in the argument are OK.
        let discharges_partial = match func {
            Expr::Var { name, .. } => {
                self.partial_dischargers.contains(name)
            }
            // Handle `unsafePartial $ expr` pattern: the `$` operator desugars to
            // `App(Var("$"), Var("unsafePartial"))`, so the discharger appears as the
            // arg of an inner App (e.g., `apply unsafePartial`).
            Expr::App { arg: inner_arg, .. } => {
                if let Expr::Var { name, .. } = inner_arg.as_ref() {
                    self.partial_dischargers.contains(name)
                } else {
                    false
                }
            }
            _ => false,
        };
        let saved_partial = if discharges_partial {
            let saved_flag = self.has_partial_lambda;
            let saved_errors = std::mem::take(&mut self.non_exhaustive_errors);
            self.has_partial_lambda = false;
            Some((saved_flag, saved_errors))
        } else {
            None
        };

        // Snapshot var count before arg inference so we can distinguish
        // outer-scope vars (potential escape targets) from locally-created vars.
        let pre_arg_var_count = self.state.var_count();
        let arg_ty = self.infer(env, arg)?;

        // Restore has_partial_lambda and discard non-exhaustive errors from inside unsafePartial
        if let Some((saved_flag, saved_errors)) = saved_partial {
            self.has_partial_lambda = saved_flag;
            self.non_exhaustive_errors = saved_errors;
        }

        // Higher-rank type checking: when the function expects a polymorphic argument
        // (e.g. `f :: (forall a. a -> a) -> r`), verify the argument is truly polymorphic.
        // We track "ambient" unif vars from the OUTER scope (created before arg inference).
        // After unification, if any outer-scope var got structurally solved to a type
        // containing a forall var, that's a skolem escape. Vars created during arg
        // inference (e.g. lambda params) are local and don't represent escapes.
        let func_ty_z = self.state.zonk(func_ty.clone());
        if let Type::Fun(param, result) = &func_ty_z {
            if let Type::Forall(vars, body) = param.as_ref() {
                // Create fresh unif vars for the forall-bound variables
                let forall_unif_vars: Vec<(Symbol, crate::typechecker::types::TyVarId)> = vars
                    .iter()
                    .map(|&(v, _)| (v, self.state.fresh_var()))
                    .collect();
                let subst: HashMap<Symbol, Type> = forall_unif_vars
                    .iter()
                    .map(|&(v, tv)| (v, Type::Unif(tv)))
                    .collect();
                let instantiated_param = self.apply_symbol_subst(&subst, body);

                // Collect "ambient" unif vars: vars from outer scope (created before
                // arg inference) that appear in arg_ty. Only these can represent
                // escapes to an enclosing scope (e.g. lambda parameter types).
                let forall_var_set: HashSet<crate::typechecker::types::TyVarId> =
                    forall_unif_vars.iter().map(|&(_, tv)| tv).collect();
                let arg_free = self.state.free_unif_vars(&arg_ty);
                let ambient_vars: Vec<crate::typechecker::types::TyVarId> = arg_free.into_iter()
                    .filter(|v| v.0 < pre_arg_var_count && !forall_var_set.contains(v))
                    .collect();

                // Unify the argument with the instantiated param
                self.state.unify(span, &arg_ty, &instantiated_param)?;

                // Post-check 1: verify no forall var leaked into ambient vars' solutions.
                // Catches escapes like `\x -> foo x` where x's type gets constrained
                // to contain a forall var.
                for &var in &ambient_vars {
                    let resolved = self.state.zonk(Type::Unif(var));
                    if let Type::Unif(_) = &resolved {
                    } else {
                        let free_in_structure = self.state.free_unif_vars(&resolved);
                        for &(sym, fv) in &forall_unif_vars {
                            let fv_root = self.state.find_root(fv);
                            if free_in_structure.iter().any(|v| *v == fv_root) {
                                return Err(TypeError::EscapedSkolem {
                                    span,
                                    name: sym,
                                    ty: self.state.zonk(arg_ty),
                                });
                            }
                        }
                    }
                }

                // Post-check 2: verify no forall var leaked into the result type.
                // Catches escapes like `ST.run (STRef.new 0)` where the result
                // type ?A gets solved to `STRef ?R Int` containing the forall var ?R.
                //
                // However, we must avoid false positives when a forall var appears
                // in the result only through "constructor vars" — unif vars that
                // are the head of an App spine where the forall var is an argument.
                // E.g. in `(forall a. ?f a -> ?g a) -> ...`, `?f` and `?g` are
                // constructor vars. Their solutions may contain the forall var at
                // the monomorphic level, but this doesn't represent a real escape.
                let ctor_vars = collect_constructor_vars(&instantiated_param, &forall_var_set);
                let mut excused_roots: HashSet<crate::typechecker::types::TyVarId> = HashSet::new();
                for &ctor_var in &ctor_vars {
                    let ctor_solution = self.state.zonk(Type::Unif(ctor_var));
                    if matches!(&ctor_solution, Type::Unif(_)) {
                        continue;
                    }
                    let ctor_free = self.state.free_unif_vars(&ctor_solution);
                    for &(_, fv) in &forall_unif_vars {
                        let fv_root = self.state.find_root(fv);
                        if ctor_free.iter().any(|v| *v == fv_root) {
                            excused_roots.insert(fv_root);
                        }
                    }
                }

                let result_zonked = self.state.zonk(result.as_ref().clone());
                let result_free = self.state.free_unif_vars(&result_zonked);
                for &(sym, fv) in &forall_unif_vars {
                    let fv_root = self.state.find_root(fv);
                    if excused_roots.contains(&fv_root) {
                        continue; // Forall var appears through a constructor var — not a real escape
                    }
                    if result_free.iter().any(|v| *v == fv_root) {
                        return Err(TypeError::EscapedSkolem {
                            span,
                            name: sym,
                            ty: self.state.zonk(arg_ty),
                        });
                    }
                }

                return Ok(result_zonked);
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
        span: crate::span::Span,
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
        _span: crate::span::Span,
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
        let mut local_partial_names: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        for binding in bindings {
            if let LetBinding::Signature { name, ty, .. } = binding {
                // Check for undefined type variables (scoped type vars from enclosing forall are OK)
                let mut undef_errors = Vec::new();
                crate::typechecker::check::collect_type_expr_vars(ty, &self.scoped_type_vars, &mut undef_errors);
                if let Some(err) = undef_errors.into_iter().next() {
                    return Err(err);
                }
                let converted = convert_type_expr(ty, &self.type_operators)?;
                let converted = self.instantiate_wildcards(&converted);
                // Expand type aliases so local aliases like `type Builder x y = RB.Builder (Record x) (Record y)`
                // are resolved before unification. Without this, self-referential aliases remain
                // unexpanded in signatures, causing mismatches when the inferred types use the
                // expanded (newtype) form.
                let converted = crate::typechecker::check::expand_type_aliases_limited(&converted, &self.state.type_aliases, 0);
                local_sigs.insert(name.value, converted);
                let sig_constraints = crate::typechecker::check::extract_type_signature_constraints(ty, &self.type_operators);
                if !sig_constraints.is_empty() {
                    self.signature_constraints.insert(QualifiedIdent { module: None, name: name.value }, sig_constraints);
                }
                // Track let bindings with Partial constraint (intentionally non-exhaustive)
                if crate::typechecker::check::has_partial_constraint(ty) {
                    local_partial_names.insert(name.value);
                }
            }
        }

        // Check for overlapping names in let bindings.
        // Multi-equation function definitions (same name, lambda exprs) are allowed
        // only if they are adjacent (not separated by other bindings).
        // (span, is_func, is_guarded_case) per binding
        let mut seen_let_names: HashMap<Symbol, Vec<(crate::span::Span, bool, bool)>> = HashMap::new();
        // Track binding order for adjacency check: (name, index) for each value binding
        let mut binding_order: Vec<Symbol> = Vec::new();
        for binding in bindings {
            if let LetBinding::Value { span, binder, expr } = binding {
                if let Binder::Var { name, .. } = binder {
                    let is_func = matches!(expr, Expr::Lambda { .. });
                    // Guarded value bindings are desugared to case on `true` at parse time
                    let is_guarded = matches!(expr, Expr::Case { exprs, .. }
                        if exprs.len() == 1 && matches!(&exprs[0], Expr::Literal { lit: Literal::Boolean(true), .. }));
                    seen_let_names.entry(name.value).or_default().push((*span, is_func, is_guarded));
                    binding_order.push(name.value);
                }
            }
        }
        for (name, entries) in &seen_let_names {
            if entries.len() > 1 {
                let all_funcs = entries.iter().all(|(_, is_func, _)| *is_func);
                // Multi-equation non-function bindings are only allowed for guarded
                // value definitions (e.g., `i' | cond = val; i' = fallback`).
                // At least one equation must be a guarded case.
                let all_non_funcs = entries.iter().all(|(_, is_func, _)| !*is_func);
                let has_guarded = entries.iter().any(|(_, _, is_guarded)| *is_guarded);
                if !all_funcs && !(all_non_funcs && has_guarded) {
                    return Err(TypeError::OverlappingNamesInLet {
                        spans: entries.iter().map(|(s, _, _)| *s).collect(),
                        name: *name,
                    });
                }
                // All are functions (or guarded values) — check they're adjacent in binding order
                let indices: Vec<usize> = binding_order.iter().enumerate()
                    .filter(|(_, n)| **n == *name)
                    .map(|(i, _)| i)
                    .collect();
                let is_adjacent = indices.windows(2).all(|w| w[1] == w[0] + 1);
                if !is_adjacent {
                    return Err(TypeError::OverlappingNamesInLet {
                        spans: entries.iter().map(|(s, _, _)| *s).collect(),
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

        // Phase 2.5: Eagerly process trivially independent bindings — those whose RHS
        // is a single variable reference that's not another let binding. This covers the
        // common pattern `goTsName = identity` where polymorphic generalization is needed
        // before other bindings use the name at different types.
        let all_binding_names: std::collections::HashSet<Symbol> = seen_let_names.keys().cloned().collect();
        let mut eagerly_processed: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        for binding in bindings {
            if let LetBinding::Value { span, binder: Binder::Var { name, .. }, expr } = binding {
                if eagerly_processed.contains(&name.value) { continue; }
                // Only for bindings without local sigs (sigs are already proper schemes)
                if local_sigs.contains_key(&name.value) { continue; }
                // Skip multi-equation bindings
                if seen_let_names.get(&name.value).map_or(false, |e| e.len() > 1) { continue; }
                // Only handle trivial cases: RHS is a single variable not in this let block
                let is_trivial_independent = match expr {
                    Expr::Var { name: var_name, .. } => {
                        var_name.module.is_some() || !all_binding_names.contains(&var_name.name)
                    }
                    _ => false,
                };
                if !is_trivial_independent { continue; }
                // Trivially independent binding — infer, generalize, insert scheme
                let binding_ty = self.infer(env, expr)?;
                if let Some(self_ty) = pre_inserted.get(&name.value) {
                    self.state.unify(*span, self_ty, &binding_ty)?;
                }
                let scheme = env.generalize_local_batch(&mut self.state, binding_ty, &all_binding_names);
                env.insert_scheme(name.value, scheme);
                eagerly_processed.insert(name.value);
            }
        }

        // Third pass: infer value bindings (all bindings stay monomorphic)
        let mut pending_generalizations: Vec<(Symbol, Type)> = Vec::new();
        for binding in bindings {
            match binding {
                LetBinding::Value { span, binder, expr } => match binder {
                    Binder::Var { name, .. } => {
                        // Skip bindings already processed in Phase 2.5
                        if eagerly_processed.contains(&name.value) {
                            continue;
                        }
                        // For multi-equation functions, subsequent equations
                        // still need to be type-checked (to detect type errors)
                        // but shouldn't re-register the scheme.
                        let is_subsequent = processed_multi_eq.contains(&name.value);
                        let is_multi_eq = seen_let_names.get(&name.value).map_or(false, |e| e.len() > 1);
                        if !is_subsequent && is_multi_eq {
                            processed_multi_eq.insert(name.value);
                        }
                        // Save partial lambda flag: multi-equation functions have
                        // individually partial patterns but are collectively exhaustive.
                        // Also suppress for bindings with Partial constraint in their signature.
                        let has_partial_sig = local_partial_names.contains(&name.value);
                        let saved_partial_lambda = if is_multi_eq || has_partial_sig {
                            let saved = self.has_partial_lambda;
                            self.has_partial_lambda = false;
                            Some(saved)
                        } else {
                            None
                        };
                        // Set scoped type vars from the binding's signature,
                        // so nested where/let signatures can reference them.
                        let prev_scoped = self.scoped_type_vars.clone();
                        if let Some(sig_ty) = local_sigs.get(&name.value) {
                            fn collect_type_vars_for_scope(ty: &Type, vars: &mut HashSet<Symbol>) {
                                match ty {
                                    Type::Var(v) => { vars.insert(*v); }
                                    Type::Forall(bound_vars, body) => {
                                        for &(v, _) in bound_vars {
                                            vars.insert(v);
                                        }
                                        collect_type_vars_for_scope(body, vars);
                                    }
                                    Type::Fun(a, b) => {
                                        collect_type_vars_for_scope(a, vars);
                                        collect_type_vars_for_scope(b, vars);
                                    }
                                    Type::App(f, a) => {
                                        collect_type_vars_for_scope(f, vars);
                                        collect_type_vars_for_scope(a, vars);
                                    }
                                    Type::Record(fields, tail) => {
                                        for (_, t) in fields {
                                            collect_type_vars_for_scope(t, vars);
                                        }
                                        if let Some(t) = tail {
                                            collect_type_vars_for_scope(t, vars);
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            collect_type_vars_for_scope(sig_ty, &mut self.scoped_type_vars);
                        }
                        let binding_ty = if let Some(sig_ty) = local_sigs.get(&name.value) {
                            // Use bidirectional checking: push the annotation into
                            // lambda params so rank-2 types are preserved correctly
                            self.check_against(env, expr, sig_ty)?
                        } else {
                            self.infer(env, expr)?
                        };
                        self.scoped_type_vars = prev_scoped;
                        // Unify with pre-inserted type for recursion
                        if let Some(self_ty) = pre_inserted.get(&name.value) {
                            self.state.unify(*span, self_ty, &binding_ty)?;
                        }
                        // Defer generalization: collect binding types for post-inference generalization
                        if !is_subsequent && !local_sigs.contains_key(&name.value) {
                            pending_generalizations.push((name.value, binding_ty));
                        } else if !is_subsequent {
                            // Bindings with explicit signatures don't need generalization
                            env.insert_scheme(name.value, Scheme::mono(local_sigs[&name.value].clone()));
                        }
                        // Restore partial lambda flag for multi-equation functions
                        if let Some(saved) = saved_partial_lambda {
                            self.has_partial_lambda = saved;
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

        // Fourth pass: generalize all inferred bindings after all are checked.
        // Collect all names being generalized so we exclude the entire batch
        // from environment free vars — otherwise co-defined bindings' pre-inserted
        // unif vars prevent proper polymorphic generalization (e.g., `goTsName = identity`
        // used at both String and TsName in DTS.Types).
        let batch_names: std::collections::HashSet<Symbol> = pending_generalizations.iter()
            .map(|(name, _)| *name).collect();
        for (name, binding_ty) in pending_generalizations {
            let scheme = env.generalize_local_batch(&mut self.state, binding_ty, &batch_names);
            env.insert_scheme(name, scheme);
        }
        Ok(())
    }

    fn infer_annotation(
        &mut self,
        env: &Env,
        span: crate::span::Span,
        expr: &Expr,
        ty_expr: &crate::ast::TypeExpr,
    ) -> Result<Type, TypeError> {
        let inferred = self.infer(env, expr)?;
        let annotated = convert_type_expr(ty_expr, &self.type_operators)?;
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
        ty: &crate::ast::TypeExpr,
        span: crate::span::Span,
    ) {
        use crate::ast::TypeExpr;
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
                        match convert_type_expr(arg, &self.type_operators) {
                            Ok(converted) => args.push(converted),
                            Err(_) => { ok = false; break; }
                        }
                    }
                    if ok {
                        self.deferred_constraints.push((constraint.span, constraint.class, args));
                    }
                }
                self.extract_inline_annotation_constraints(ty, span);
            }
            TypeExpr::Forall { ty, .. } => {
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
        span: crate::span::Span,
        func: &Expr,
        ty_expr: &crate::ast::TypeExpr,
    ) -> Result<Type, TypeError> {
        // Flatten chained VTAs: f @A @B @C → base=f, args=[A, B, C]
        let mut vta_args: Vec<&crate::ast::TypeExpr> = vec![ty_expr];
        let mut base: &Expr = func;
        while let Expr::VisibleTypeApp { func: inner, ty: inner_ty, .. } = base {
            vta_args.push(inner_ty);
            base = inner;
        }
        vta_args.reverse(); // Now in application order

        let func_ty = self.infer_preserving_forall(env, base)?;

        // Check if the base expression is a class method
        let class_info = if let Expr::Var { name, .. } = base {
            self.class_methods.get(name).cloned()
        } else {
            None
        };
        let mut var_subst: HashMap<Symbol, Type> = HashMap::new();

        // Process all VTA args sequentially
        let mut ty = func_ty;
        for (arg_idx, arg_ty_expr) in vta_args.iter().enumerate() {
            let applied_ty = convert_type_expr(arg_ty_expr, &self.type_operators)?;
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

        // After all VTA args processed, instantiate any remaining invisible forall vars.
        // This applies to both class methods and regular functions — without it,
        // remaining invisible foralls leak into the result type (e.g., `forall ty. String`).
        if let Type::Forall(ref vars, ref body) = ty.clone() {
            let mut extra_subst: HashMap<Symbol, Type> = HashMap::new();
            for &(v, _) in vars.iter() {
                if !var_subst.contains_key(&v) {
                    let fresh = Type::Unif(self.state.fresh_var());
                    var_subst.insert(v, fresh.clone());
                    extra_subst.insert(v, fresh);
                }
            }
            if !extra_subst.is_empty() {
                ty = self.apply_symbol_subst(&extra_subst, body);
            }
        }

        // Defer class constraint if applicable
        if let Some((class_name, ref class_tvs)) = class_info {
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

            if !self.given_class_names.contains(&class_name) {
                self.deferred_constraints.push((span, class_name, constraint_types));
            }
        }

        Ok(ty)
    }

    /// Infer the type of an expression, preserving Forall for visible type application.
    /// Unlike `infer`, this does NOT instantiate Forall types — VTA peels them explicitly.
    fn infer_preserving_forall(&mut self, env: &Env, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Var { span, name, .. } | Expr::Constructor { span, name, .. } => {
                let resolved_name = if let Some(module) = name.module {
                    Self::qualified_symbol(module, name.name)
                } else {
                    name.name
                };
                match env.lookup(resolved_name) {
                    Some(scheme) => Ok(self.scheme_to_forall(scheme)),
                    None => Err(TypeError::UndefinedVariable { span: *span, name: name.name }),
                }
            }
            Expr::VisibleTypeApp { span, func, ty } => {
                self.infer_visible_type_app(env, *span, func, ty)
            }
            Expr::AsPattern { span, name, pattern } => {
                match expr_to_type_expr(pattern) {
                    Some(ty_expr) => self.infer_visible_type_app(env, *span, name, &ty_expr),
                    None => self.infer(env, expr),
                }
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
        span: crate::span::Span,
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
        let ty = self.infer(env, expr)?;
        let zonked = self.state.zonk(ty.clone());
        // If the type is a concrete type constructor, check immediately for types known
        // to NOT have Ring instances. Otherwise, defer the constraint to Pass 3 so that
        // imported Ring instances (e.g., Ring BigInt) are checked properly.
        if let Type::Con(name) = &zonked {
            let name_str = crate::interner::resolve(name.name).unwrap_or_default();
            match name_str.as_ref() {
                "Int" | "Number" => {
                    // Known Ring types — no constraint needed
                }
                "Boolean" | "String" | "Char" | "Array" => {
                    // Known non-Ring types — error immediately
                    return Err(TypeError::NoInstanceFound {
                        span,
                        class_name: unqualified_ident("Ring"),
                        type_args: vec![zonked],
                    });
                }
                _ => {
                    // Unknown type constructor — defer to Pass 3
                    self.deferred_constraints.push((
                        span,
                        unqualified_ident("Ring"),
                        vec![ty.clone()],
                    ));
                }
            }
        } else {
            // Non-Con types (Unif, Var, App, etc.) — defer
            self.deferred_constraints.push((
                span,
                unqualified_ident("Ring"),
                vec![ty.clone()],
            ));
        }
        Ok(ty)
    }

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

    /// Check if an expression is a lambda, possibly wrapped in Parens.
    fn expr_is_lambda(e: &Expr) -> bool {
        matches!(e, Expr::Lambda { .. })
    }

    fn is_underscore_hole(e: &Expr) -> bool {
        matches!(e, Expr::Hole { name, .. } if crate::interner::resolve(*name).unwrap_or_default() == "_")
    }

    fn infer_case(
        &mut self,
        env: &Env,
        span: crate::span::Span,
        exprs: &[Expr],
        alts: &[crate::ast::CaseAlternative],
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
                        // Emit NonExhaustivePattern error for the missing constructors
                        self.non_exhaustive_errors.push(
                            crate::typechecker::error::TypeError::NonExhaustivePattern {
                                span,
                                type_name,
                                missing,
                            },
                        );
                        // Also set the partial flag so check.rs can emit Partial
                        // constraint if needed (for unsafePartial support).
                        self.has_partial_lambda = true;
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
        span: crate::span::Span,
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
        span: crate::span::Span,
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

    fn infer_record(
        &mut self,
        env: &Env,
        span: crate::span::Span,
        fields: &[crate::ast::RecordField],
    ) -> Result<Type, TypeError> {
        // Check for duplicate labels
        let mut label_spans: HashMap<Symbol, Vec<crate::span::Span>> = HashMap::new();
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
        span: crate::span::Span,
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
        span: crate::span::Span,
        expr: &Expr,
        updates: &[crate::ast::RecordUpdate],
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
        span: crate::span::Span,
        updates: &[crate::ast::RecordUpdate],
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
                    let inner_updates: Vec<crate::ast::RecordUpdate> = fields.iter().filter_map(|f| {
                        Some(crate::ast::RecordUpdate {
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
        span: crate::span::Span,
        statements: &[crate::ast::DoStatement],
    ) -> Result<Type, TypeError> {
        if statements.is_empty() {
            return Err(TypeError::NotImplemented {
                span,
                feature: "empty do block".to_string(),
            });
        }

        // Pure do-blocks (no `<-` binds) don't require monadic wrapping
        let has_binds = statements
            .iter()
            .any(|s| matches!(s, crate::ast::DoStatement::Bind { .. }));

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
                .any(|s| matches!(s, crate::ast::DoStatement::Discard { .. }));
        if self.module_mode && has_non_last_discards {
            let discard_sym = crate::interner::intern("discard");
            if env.lookup(discard_sym).is_none() {
                return Err(TypeError::UndefinedVariable { span, name: discard_sym });
            }
        }

        if has_binds {
            // Desugar do-notation as applications of bind/discard from the environment.
            // This supports both standard monads (bind :: m a -> (a -> m b) -> m b)
            // and indexed monads via rebindable do-notation (where bind = ibind).
            self.infer_do_bind_stmts(env, span, statements, 0)
        } else {
            // Pure do-block (no binds): just infer each expression
            let mut current_env = env.child();
            for (i, stmt) in statements.iter().enumerate() {
                let is_last = i == statements.len() - 1;
                match stmt {
                    crate::ast::DoStatement::Discard { expr, .. } => {
                        let expr_ty = self.infer(&current_env, expr)?;
                        if is_last {
                            return Ok(expr_ty);
                        }
                    }
                    crate::ast::DoStatement::Let { bindings, .. } => {
                        for binding in bindings {
                            if let LetBinding::Value { binder, .. } = binding {
                                check_do_reserved_names(binder)?;
                            }
                        }
                        self.process_let_bindings(&mut current_env, bindings)?;
                    }
                    crate::ast::DoStatement::Bind { span: bind_span, .. } => {
                        // Shouldn't happen since has_binds is false
                        return Err(TypeError::InvalidDoBind { span: *bind_span });
                    }
                }
            }
            // If we get here, the last statement was a Let
            match statements.last() {
                Some(crate::ast::DoStatement::Let { span: let_span, .. }) => {
                    Err(TypeError::InvalidDoLet { span: *let_span })
                }
                _ => Err(TypeError::NotImplemented {
                    span,
                    feature: "do block must end with an expression".to_string(),
                })
            }
        }
    }

    /// Recursively infer do-notation statements by desugaring binds as
    /// function applications of the `bind` function from the environment.
    /// This handles both standard monads and rebindable do-notation
    /// (e.g., indexed monads with `where bind = ibind`).
    fn infer_do_bind_stmts(
        &mut self,
        env: &Env,
        span: crate::span::Span,
        statements: &[crate::ast::DoStatement],
        idx: usize,
    ) -> Result<Type, TypeError> {
        if idx >= statements.len() {
            return Err(TypeError::NotImplemented {
                span,
                feature: "empty do block".to_string(),
            });
        }

        let is_last = idx == statements.len() - 1;
        let stmt = &statements[idx];

        match stmt {
            crate::ast::DoStatement::Discard { expr, .. } if is_last => {
                // Last statement: just infer its type
                self.infer(env, expr)
            }
            crate::ast::DoStatement::Discard { expr, .. } => {
                // Non-last discard: discard expr (\_ -> rest), fallback to bind
                let discard_sym = crate::interner::intern("discard");
                let func_ty = if let Some(scheme) = env.lookup(discard_sym) {
                    self.instantiate(&scheme)
                } else {
                    let bind_sym = crate::interner::intern("bind");
                    let scheme = env.lookup(bind_sym)
                        .ok_or_else(|| TypeError::UndefinedVariable { span, name: bind_sym })?;
                    self.instantiate(&scheme)
                };

                let expr_ty = self.infer(env, expr)?;
                let rest_ty = self.infer_do_bind_stmts(env, span, statements, idx + 1)?;

                // Apply: func expr (\_ -> rest)
                let after_first = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &func_ty, &Type::fun(expr_ty, after_first.clone()))?;
                let discard_arg = Type::Unif(self.state.fresh_var());
                let cont_ty = Type::fun(discard_arg, rest_ty);
                let result = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &after_first, &Type::fun(cont_ty, result.clone()))?;
                Ok(result)
            }
            crate::ast::DoStatement::Bind { span: bind_span, binder, expr } => {
                if is_last {
                    return Err(TypeError::InvalidDoBind { span: *bind_span });
                }

                check_do_reserved_names(binder)?;

                let bind_sym = crate::interner::intern("bind");
                let scheme = env.lookup(bind_sym)
                    .ok_or_else(|| TypeError::UndefinedVariable { span, name: bind_sym })?;
                let func_ty = self.instantiate(&scheme);

                let expr_ty = self.infer(env, expr)?;

                // Create continuation environment with binder
                let mut cont_env = env.child();
                let binder_ty = Type::Unif(self.state.fresh_var());
                self.infer_binder(&mut cont_env, binder, &binder_ty)?;

                let rest_ty = self.infer_do_bind_stmts(&cont_env, span, statements, idx + 1)?;

                // Apply: bind expr (\binder -> rest)
                let after_first = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &func_ty, &Type::fun(expr_ty, after_first.clone()))?;
                let cont_ty = Type::fun(binder_ty, rest_ty);
                let result = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &after_first, &Type::fun(cont_ty, result.clone()))?;
                Ok(result)
            }
            crate::ast::DoStatement::Let { span: let_span, bindings, .. } => {
                for binding in bindings {
                    if let LetBinding::Value { binder, .. } = binding {
                        check_do_reserved_names(binder)?;
                    }
                }
                let mut let_env = env.child();
                self.process_let_bindings(&mut let_env, bindings)?;
                if is_last {
                    return Err(TypeError::InvalidDoLet { span: *let_span });
                }
                self.infer_do_bind_stmts(&let_env, span, statements, idx + 1)
            }
        }
    }

    /// Infer the type of a qualified do block (e.g. `Module.do`).
    /// Uses the `bind` and `discard` from the specified module instead of
    /// assuming monadic semantics.
    fn infer_qualified_do(
        &mut self,
        env: &Env,
        span: crate::span::Span,
        module: Symbol,
        statements: &[crate::ast::DoStatement],
    ) -> Result<Type, TypeError> {
        self.infer_qualified_do_stmts(env, span, module, statements, 0)
    }

    fn infer_qualified_do_stmts(
        &mut self,
        env: &Env,
        span: crate::span::Span,
        module: Symbol,
        statements: &[crate::ast::DoStatement],
        idx: usize,
    ) -> Result<Type, TypeError> {
        if idx >= statements.len() {
            return Err(TypeError::NotImplemented {
                span,
                feature: "empty qualified do block".to_string(),
            });
        }

        let is_last = idx == statements.len() - 1;
        let stmt = &statements[idx];

        match stmt {
            crate::ast::DoStatement::Discard { expr, .. } if is_last => {
                // Last statement: just infer its type
                self.infer(env, expr)
            }
            crate::ast::DoStatement::Discard { expr, .. } => {
                // Non-last discard: Module.discard expr (\_ -> rest)
                let bind_sym = Self::qualified_symbol(module, crate::interner::intern("discard"));
                let func_ty = if let Some(scheme) = env.lookup(bind_sym) {
                    self.instantiate(&scheme)
                } else {
                    // Fallback to Module.bind if discard not found
                    let bind_sym2 = Self::qualified_symbol(module, crate::interner::intern("bind"));
                    let scheme = env.lookup(bind_sym2)
                        .ok_or_else(|| TypeError::UndefinedVariable { span, name: bind_sym2 })?;
                    self.instantiate(&scheme)
                };

                let expr_ty = self.infer(env, expr)?;
                let rest_ty = self.infer_qualified_do_stmts(env, span, module, statements, idx + 1)?;

                // Apply: func expr (\_ -> rest)
                let after_first = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &func_ty, &Type::fun(expr_ty, after_first.clone()))?;
                let discard_arg_ty = Type::Unif(self.state.fresh_var());
                let cont_ty = Type::fun(discard_arg_ty, rest_ty);
                let result = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &after_first, &Type::fun(cont_ty, result.clone()))?;
                Ok(result)
            }
            crate::ast::DoStatement::Bind { span: bind_span, binder, expr } => {
                if is_last {
                    return Err(TypeError::InvalidDoBind { span: *bind_span });
                }
                // Module.bind expr (\x -> rest)
                let bind_sym = Self::qualified_symbol(module, crate::interner::intern("bind"));
                let scheme = env.lookup(bind_sym)
                    .ok_or_else(|| TypeError::UndefinedVariable { span, name: bind_sym })?;
                let func_ty = self.instantiate(&scheme);

                let expr_ty = self.infer(env, expr)?;

                // Create continuation environment with binder
                let mut cont_env = env.child();
                let binder_ty = Type::Unif(self.state.fresh_var());
                self.infer_binder(&mut cont_env, binder, &binder_ty)?;

                let rest_ty = self.infer_qualified_do_stmts(&cont_env, span, module, statements, idx + 1)?;

                // Apply: func expr (\binder -> rest)
                let after_first = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &func_ty, &Type::fun(expr_ty, after_first.clone()))?;
                let cont_ty = Type::fun(binder_ty, rest_ty);
                let result = Type::Unif(self.state.fresh_var());
                self.state.unify(span, &after_first, &Type::fun(cont_ty, result.clone()))?;
                Ok(result)
            }
            crate::ast::DoStatement::Let { bindings, .. } => {
                let mut let_env = env.child();
                self.process_let_bindings(&mut let_env, bindings)?;
                self.infer_qualified_do_stmts(&let_env, span, module, statements, idx + 1)
            }
        }
    }

    fn infer_ado(
        &mut self,
        env: &Env,
        span: crate::span::Span,
        statements: &[crate::ast::DoStatement],
        result: &Expr,
    ) -> Result<Type, TypeError> {
        let functor_ty = Type::Unif(self.state.fresh_var());
        // In ado (applicative do), `<-` bindings are independent — each `<-` expression
        // runs in the applicative context and can only see the outer env + `let` bindings,
        // NOT other `<-` bindings. `let` bindings CAN see prior `<-` bindings (they get
        // moved into the result expression in the desugaring). The `in` expression sees all.
        //
        // expr_env: for inferring `<-` expressions (accumulates only `let` bindings)
        // result_env: for `let` bindings and the `in` expression (accumulates everything)
        let mut expr_env = env.child();
        let mut result_env = env.child();

        for stmt in statements {
            match stmt {
                crate::ast::DoStatement::Bind { binder, expr, .. } => {
                    // Infer the expression in expr_env (no <- bindings visible)
                    let expr_ty = self.infer(&expr_env, expr)?;
                    let inner_ty = Type::Unif(self.state.fresh_var());
                    let expected = Type::app(functor_ty.clone(), inner_ty.clone());
                    self.state.unify(span, &expr_ty, &expected)?;
                    // Add binder to result_env only (visible in `let` and `in`)
                    self.infer_binder(&mut result_env, binder, &inner_ty)?;
                }
                crate::ast::DoStatement::Let { bindings, .. } => {
                    // Let bindings can see prior <- bindings, so process in result_env.
                    // Then copy newly added names to expr_env for subsequent <- expressions.
                    let before: std::collections::HashSet<Symbol> = result_env.top_bindings().keys().copied().collect();
                    self.process_let_bindings(&mut result_env, bindings)?;
                    for (name, scheme) in result_env.top_bindings() {
                        if !before.contains(name) {
                            expr_env.insert_scheme(*name, scheme.clone());
                        }
                    }
                }
                crate::ast::DoStatement::Discard { expr, .. } => {
                    let expr_ty = self.infer(&expr_env, expr)?;
                    let discard_inner = Type::Unif(self.state.fresh_var());
                    let expected = Type::app(functor_ty.clone(), discard_inner);
                    self.state.unify(span, &expr_ty, &expected)?;
                }
            }
        }

        let result_ty = self.infer(&result_env, result)?;
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
            Binder::Constructor { span, name, args, .. } => {
                let lookup_name = if let Some(module) = name.module {
                    Self::qualified_symbol(module, name.name)
                } else {
                    name.name
                };
                // Look up constructor type in env (handle qualified names)
                let lookup_result = env.lookup(lookup_name);
                match lookup_result {
                    Some(scheme) => {
                        let mut ctor_ty = self.instantiate(scheme);
                        ctor_ty = self.instantiate_forall_type(ctor_ty)?;

                        // Count the expected arity from the constructor type
                        let mut expected_arity = 0;
                        {
                            let mut t = &ctor_ty;
                            while let Type::Fun(_, ret) = t {
                                expected_arity += 1;
                                t = ret;
                            }
                        }
                        if args.len() != expected_arity {
                            return Err(TypeError::IncorrectConstructorArity {
                                span: *span,
                                name: name.name,
                                expected: expected_arity,
                                found: args.len(),
                            });
                        }

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

                        // If the constructor pattern was qualified (e.g. HATS.Linear),
                        // qualify the return type's head constructor ONLY when the
                        // unqualified name conflicts with a type alias. Without this,
                        // unqualified Con(Easing) from the constructor may be incorrectly
                        // expanded as a type alias (e.g. Tick.Easing = Number -> Number)
                        // instead of matching the data type Con(HATS.Easing).
                        if let Some(module) = name.module {
                            if let Some(head_name) = extract_type_con(&ctor_ty) {
                                if self.state.type_aliases.contains_key(&head_name.name) {
                                    ctor_ty = qualify_type_head(ctor_ty, module);
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
            Binder::As { name, binder, .. } => {
                env.insert_mono(name.value, expected.clone());
                self.infer_binder(env, binder, expected)
            }
            Binder::Typed { span, binder, ty } => {
                let annotated = convert_type_expr(ty, &self.type_operators)?;
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
            Binder::Record { span, fields } => {
                // Check for duplicate labels
                let mut label_spans: HashMap<Symbol, Vec<crate::span::Span>> = HashMap::new();
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
    let mut seen: HashMap<Symbol, Vec<crate::span::Span>> = HashMap::new();
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

fn collect_pattern_vars(binder: &Binder, seen: &mut HashMap<Symbol, Vec<crate::span::Span>>) {
    match binder {
        Binder::Var { name, .. } => {
            seen.entry(name.value).or_default().push(name.span);
        }
        Binder::Constructor { args, .. } => {
            for arg in args {
                collect_pattern_vars(arg, seen);
            }
        }
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
pub fn extract_type_con(ty: &Type) -> Option<QualifiedIdent> {
    match ty {
        Type::Con(name) => Some(*name),
        Type::App(f, _) => extract_type_con(f),
        _ => None,
    }
}

/// Classify a binder for exhaustiveness checking.
/// Sets `has_catchall` if the binder matches anything (wildcard, variable, literal).
/// Adds constructor names to `covered` for constructor patterns.
/// Recurses through As and Typed wrappers.
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
        Binder::Typed { binder: inner, .. } => {
            classify_binder(inner, has_catchall, covered);
        }
        Binder::Record { .. } => {
            // Record patterns are irrefutable — they match any value of the record type.
            // Treat them as catchalls so the exhaustiveness checker doesn't falsely report
            // missing constructors when a type alias (e.g. `type Input = { ... }`) collides
            // with a data type of the same name in data_constructors.
            *has_catchall = true;
        }
        Binder::Array { .. } => {
            // Array patterns don't contribute to constructor exhaustiveness
        }
    }
}

/// Check if a binder is refutable (could fail to match).
/// Refutable binders include constructor patterns, literal patterns, and array patterns.
/// Irrefutable binders are wildcard, variable, and wrappers around irrefutable binders.
pub fn is_refutable(binder: &Binder) -> bool {
    match binder {
        Binder::Wildcard { .. } | Binder::Var { .. } => false,
        Binder::Array { .. } => true,
        Binder::Literal { .. } => true,
        Binder::Constructor { .. } => true,
        Binder::Record { fields, .. } => {
            fields.iter().any(|f| {
                f.binder.as_ref().map_or(false, |b| is_refutable(b))
            })
        }
        Binder::As { binder: inner, .. } => is_refutable(inner),
        Binder::Typed { binder: inner, .. } => is_refutable(inner),
    }
}

/// Like `is_refutable`, but treats single-constructor types (newtypes) as irrefutable.
/// For constructor binders, looks up the parent type in `data_constructors` to check
/// if the type has more than one constructor.
pub fn is_truly_refutable(binder: &Binder, data_constructors: &HashMap<QualifiedIdent, Vec<QualifiedIdent>>) -> bool {
    match binder {
        Binder::Wildcard { .. } | Binder::Var { .. } => false,
        Binder::Array { .. } => true,
        Binder::Literal { .. } => true,
        Binder::Constructor { name, args, .. } => {
            // Check if this constructor belongs to a single-constructor type
            let is_single_ctor = data_constructors.values().any(|ctors| {
                ctors.len() == 1 && ctors.iter().any(|c| c.name == name.name)
            });
            if is_single_ctor {
                // Single-constructor type (like newtype) — only refutable if args are
                args.iter().any(|a| is_truly_refutable(a, data_constructors))
            } else {
                true
            }
        }
        Binder::Record { fields, .. } => {
            fields.iter().any(|f| {
                f.binder.as_ref().map_or(false, |b| is_truly_refutable(b, data_constructors))
            })
        }
        Binder::As { binder: inner, .. } => is_truly_refutable(inner, data_constructors),
        Binder::Typed { binder: inner, .. } => is_truly_refutable(inner, data_constructors),
    }
}

/// Extract the outermost type constructor name AND its type arguments from a type.
/// E.g. `Maybe Int` → `Some((Maybe, [Int]))`, `Either String Int` → `Some((Either, [String, Int]))`.
pub fn extract_type_con_and_args(ty: &Type) -> Option<(QualifiedIdent, Vec<Type>)> {
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

/// Unwrap a binder through As and Typed wrappers to get the inner binder.
pub fn unwrap_binder(binder: &Binder) -> &Binder {
    match binder {
        Binder::As { binder: inner, .. }
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
                    GuardPattern::Pattern(binder, _) => !is_refutable(binder),
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
    data_constructors: &HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
    ctor_details: &HashMap<QualifiedIdent, (QualifiedIdent, Vec<Symbol>, Vec<Type>)>,
) -> Option<Vec<String>> {
    let type_name = extract_type_con(scrutinee_ty)?;
    let all_ctors = data_constructors.get(&type_name).or_else(|| {
        // Fallback: if qualified lookup fails, try matching by unqualified name
        if type_name.module.is_some() {
            let unq = QualifiedIdent { module: None, name: type_name.name };
            data_constructors.get(&unq)
        } else {
            // Unqualified lookup failed — search for any qualified variant
            data_constructors.iter()
                .find(|(k, _)| k.name == type_name.name)
                .map(|(_, v)| v)
        }
    })?;

    // Classify all binders
    let mut has_catchall = false;
    let mut covered: Vec<Symbol> = Vec::new();
    for binder in binders {
        classify_binder(binder, &mut has_catchall, &mut covered);
    }

    if has_catchall {
        return None; // Exhaustive via wildcard/variable
    }

    // When multiple types share the same unqualified name (e.g. Data.List.List and
    // Data.List.Lazy.List both map to unqualified "List"), the data_constructors entry
    // may have been overwritten by the wrong type. Detect this by checking if ALL
    // covered constructors appear in all_ctors; if some don't, we have a name collision
    // with partial overlap (e.g. both Action types have "Init" but different other ctors).
    let all_covered_match = !covered.is_empty() && covered.iter().all(|c| all_ctors.iter().any(|ac| ac.name == *c));
    if !all_covered_match && !covered.is_empty() {
        // The data_constructors entry for this type name has been overwritten by a
        // different type from another module (name collision). Since we can't reliably
        // determine the correct constructor set, bail out rather than report false
        // non-exhaustive pattern errors.
        return None;
    }

    // After resolution, re-check: if none of the covered constructors appear in
    // all_ctors, the data_constructors lookup found a wrong type (name collision
    // between modules, e.g. Modal.Output vs some other Output). Bail out rather
    // than reporting false NonExhaustivePattern errors.
    if !covered.is_empty() && !covered.iter().any(|c| all_ctors.iter().any(|ac| ac.name == *c)) {
        return None;
    }

    // Resolve operator aliases in covered set: if a covered symbol (e.g. operator `:`)
    // is NOT one of the declared constructors but has identical ctor_details as one,
    // then they are aliases (e.g. `:` is an alias for `Cons`).
    let mut resolved_covered = covered.clone();
    for &op_sym in &covered {
        // Only resolve aliases for symbols that aren't already declared constructors
        if all_ctors.iter().any(|c| c.name == op_sym) {
            continue;
        }
        let op_qid = QualifiedIdent { module: None, name: op_sym };
        if let Some(op_details) = ctor_details.get(&op_qid) {
            for ctor in all_ctors {
                if !resolved_covered.contains(&ctor.name) {
                    if let Some(ctor_det) = ctor_details.get(ctor) {
                        if op_details == ctor_det {
                            resolved_covered.push(ctor.name);
                        }
                    }
                }
            }
        }
    }

    // Find missing constructors at this level
    let missing_at_this_level: Vec<QualifiedIdent> = all_ctors
        .iter()
        .filter(|c| !resolved_covered.contains(&c.name))
        .copied()
        .collect();

    if !missing_at_this_level.is_empty() {
        // Before reporting, check if the covered constructors completely cover any
        // known type's constructor set. This handles name collisions where
        // data_constructors returns the wrong type's constructors (e.g., two modules
        // export types with overlapping constructor names like Action).
        if !resolved_covered.is_empty() {
            for (_, ctors) in data_constructors {
                if !ctors.is_empty() && ctors.iter().all(|c| resolved_covered.contains(&c.name)) {
                    return None; // Exhaustive for this type
                }
            }
        }
        // Missing constructors — report them
        let missing_strs: Vec<String> = missing_at_this_level
            .iter()
            .map(|c| crate::interner::resolve(c.name).unwrap_or_default())
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
        let (parent_type, type_var_syms, field_types) = details;

        // Verify the ctor_details entry belongs to the correct parent type.
        // Name collisions (e.g. `ResponseUpdate` ctor in both `ResponseUpdate` data type
        // and `Output` data type) can cause ctor_details to contain the wrong entry.
        if parent_type.name != type_name.name {
            continue;
        }

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
                Binder::Constructor { name, args, .. } if name.name == ctor_name.name => {
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
            let ctor_str = crate::interner::resolve(ctor_name.name).unwrap_or_default();
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
fn expr_references_name(expr: &Expr, target: Symbol, _let_names: &HashSet<Symbol>) -> bool {
    // Only flag direct self-references at the expression root.
    // References under any computation (if, case, do, app) are recursion, not cycles.
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => name.name == target,
        Expr::TypeAnnotation { expr, .. } => expr_references_name(expr, target, _let_names),
        _ => false,
    }
}

/// Check if an expression references any name from a given set anywhere in its tree.
/// Used for dependency analysis of let/where bindings.
fn expr_references_any(expr: &Expr, names: &HashSet<Symbol>) -> bool {
    use crate::ast::*;
    match expr {
        Expr::Var { name, .. } if name.module.is_none() => names.contains(&name.name),
        Expr::Var { .. } | Expr::Constructor { .. } | Expr::Hole { .. } => false,
        Expr::Literal { lit, .. } => match lit {
            Literal::Array(es) => es.iter().any(|e| expr_references_any(e, names)),
            _ => false,
        },
        Expr::Array { elements, .. } => elements.iter().any(|e| expr_references_any(e, names)),
        Expr::Record { fields, .. } => fields.iter().any(|f| f.value.as_ref().map_or(false, |v| expr_references_any(v, names))),
        Expr::App { func, arg, .. } => {
            expr_references_any(func, names) || expr_references_any(arg, names)
        }
        Expr::VisibleTypeApp { func, .. } => expr_references_any(func, names),
        Expr::Lambda { body, .. } => expr_references_any(body, names),
        Expr::If { cond, then_expr, else_expr, .. } => {
            expr_references_any(cond, names) || expr_references_any(then_expr, names) || expr_references_any(else_expr, names)
        }
        Expr::Case { exprs, alts, .. } => {
            exprs.iter().any(|e| expr_references_any(e, names)) ||
            alts.iter().any(|alt| match &alt.result {
                GuardedExpr::Unconditional(e) => expr_references_any(e, names),
                GuardedExpr::Guarded(guards) => guards.iter().any(|g| {
                    g.patterns.iter().any(|p| match p {
                        GuardPattern::Boolean(e) => expr_references_any(e, names),
                        GuardPattern::Pattern(_, e) => expr_references_any(e, names),
                    }) || expr_references_any(&g.expr, names)
                }),
            })
        }
        Expr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| match b {
                LetBinding::Value { expr, .. } => expr_references_any(expr, names),
                _ => false,
            }) || expr_references_any(body, names)
        }
        Expr::Do { statements, .. } => {
            statements.iter().any(|s| match s {
                DoStatement::Bind { expr, .. } | DoStatement::Discard { expr, .. } => expr_references_any(expr, names),
                DoStatement::Let { bindings, .. } => bindings.iter().any(|b| match b {
                    LetBinding::Value { expr, .. } => expr_references_any(expr, names),
                    _ => false,
                }),
            })
        }
        Expr::Ado { statements, result, .. } => {
            statements.iter().any(|s| match s {
                DoStatement::Bind { expr, .. } | DoStatement::Discard { expr, .. } => expr_references_any(expr, names),
                DoStatement::Let { bindings, .. } => bindings.iter().any(|b| match b {
                    LetBinding::Value { expr, .. } => expr_references_any(expr, names),
                    _ => false,
                }),
            }) || expr_references_any(result, names)
        }
        Expr::TypeAnnotation { expr, .. } | Expr::Negate { expr, .. }
        | Expr::RecordAccess { expr, .. } => expr_references_any(expr, names),
        Expr::RecordUpdate { expr, updates, .. } => {
            expr_references_any(expr, names) || updates.iter().any(|u| expr_references_any(&u.value, names))
        }
        Expr::AsPattern { name: n, pattern, .. } => {
            expr_references_any(n, names) || expr_references_any(pattern, names)
        }
    }
}

/// Apply a module qualifier to the head type constructor of a type.
/// Walks through nested `App` to reach the head `Con`, then adds the qualifier.
/// Used when a qualified constructor pattern (e.g. `HATS.Linear`) produces a return
/// type with an unqualified head (e.g. `Con(Easing)`) that should be qualified to
/// match the scrutinee type (e.g. `Con(HATS.Easing)`).
fn qualify_type_head(ty: Type, module: Symbol) -> Type {
    match ty {
        Type::Con(qi) if qi.module.is_none() => {
            Type::Con(QualifiedIdent { module: Some(module), name: qi.name })
        }
        Type::App(f, a) => Type::App(Box::new(qualify_type_head(*f, module)), a),
        _ => ty,
    }
}

/// Collect "constructor vars" from an instantiated param type: unification variables
/// that appear as the head of an application spine where a forall variable is an argument.
/// E.g. in `App(?g, ?b_fresh)`, `?g` is a constructor var when `?b_fresh` is a forall var.
/// These vars represent type constructors whose solutions may contain the forall var at
/// the monomorphic level — this is an artifact of App decomposition, not a real escape.
fn collect_constructor_vars(
    ty: &Type,
    forall_vars: &HashSet<crate::typechecker::types::TyVarId>,
) -> Vec<crate::typechecker::types::TyVarId> {
    let mut result = Vec::new();
    collect_ctor_vars_inner(ty, forall_vars, &mut result);
    result
}

fn collect_ctor_vars_inner(
    ty: &Type,
    forall_vars: &HashSet<crate::typechecker::types::TyVarId>,
    result: &mut Vec<crate::typechecker::types::TyVarId>,
) {
    match ty {
        Type::App(_, _) => {
            // Decompose the full application spine
            let mut spine_args: Vec<&Type> = Vec::new();
            let mut head = ty;
            while let Type::App(f, a) = head {
                spine_args.push(a.as_ref());
                head = f.as_ref();
            }
            // Check if any spine arg is (or contains) a forall var
            let has_forall_arg = spine_args.iter().any(|arg| type_has_forall_unif(arg, forall_vars));
            if has_forall_arg {
                // If the head is a unif var, it's a constructor var
                if let Type::Unif(v) = head {
                    if !result.contains(v) {
                        result.push(*v);
                    }
                }
            }
            // Recurse into args (head already decomposed)
            for arg in &spine_args {
                collect_ctor_vars_inner(arg, forall_vars, result);
            }
        }
        Type::Fun(from, to) => {
            collect_ctor_vars_inner(from, forall_vars, result);
            collect_ctor_vars_inner(to, forall_vars, result);
        }
        Type::Forall(_, body) => {
            collect_ctor_vars_inner(body, forall_vars, result);
        }
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                collect_ctor_vars_inner(t, forall_vars, result);
            }
            if let Some(t) = tail {
                collect_ctor_vars_inner(t, forall_vars, result);
            }
        }
        _ => {}
    }
}

/// Check if a type contains any of the given forall unif vars.
fn type_has_forall_unif(
    ty: &Type,
    forall_vars: &HashSet<crate::typechecker::types::TyVarId>,
) -> bool {
    match ty {
        Type::Unif(v) => forall_vars.contains(v),
        Type::App(f, a) => type_has_forall_unif(f, forall_vars) || type_has_forall_unif(a, forall_vars),
        Type::Fun(f, t) => type_has_forall_unif(f, forall_vars) || type_has_forall_unif(t, forall_vars),
        Type::Forall(_, body) => type_has_forall_unif(body, forall_vars),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_has_forall_unif(t, forall_vars))
                || tail.as_ref().map_or(false, |t| type_has_forall_unif(t, forall_vars))
        }
        _ => false,
    }
}
