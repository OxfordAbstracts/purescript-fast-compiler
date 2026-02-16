use std::collections::HashMap;

use crate::interner::{self, Symbol};
use crate::typechecker::types::{Scheme, TyVarId, Type};
use crate::typechecker::unify::UnifyState;

/// Type environment: maps variable names to their type schemes.
/// Supports nested scopes via the `child()` clone pattern.
#[derive(Debug, Clone)]
pub struct Env {
    bindings: HashMap<Symbol, Scheme>,
}

impl Env {
    pub fn new() -> Self {
        Env {
            bindings: HashMap::new(),
        }
    }

    /// Look up a variable's type scheme.
    pub fn lookup(&self, name: Symbol) -> Option<&Scheme> {
        self.bindings.get(&name)
    }

    /// Insert a monomorphic binding (no quantified variables).
    pub fn insert_mono(&mut self, name: Symbol, ty: Type) {
        self.bindings.insert(name, Scheme::mono(ty));
    }

    /// Insert a polymorphic binding.
    pub fn insert_scheme(&mut self, name: Symbol, scheme: Scheme) {
        self.bindings.insert(name, scheme);
    }

    /// Get a reference to the top-level bindings.
    pub fn top_bindings(&self) -> &HashMap<Symbol, Scheme> {
        &self.bindings
    }

    /// Create a child scope (clone for entering a let/lambda body).
    pub fn child(&self) -> Env {
        self.clone()
    }

    /// Generalize a type: quantify over unification variables in `ty`
    /// that are NOT free in the environment.
    /// The resulting scheme uses `Type::Var(Symbol)` for quantified variables,
    /// making it self-contained and safe to export across modules.
    pub fn generalize(&self, state: &mut UnifyState, ty: Type) -> Scheme {
        let ty_vars = state.free_unif_vars(&ty);
        let env_vars = self.free_vars(state);

        let gen_vars: Vec<TyVarId> = ty_vars
            .into_iter()
            .filter(|v| !env_vars.contains(v))
            .collect();

        Self::finalize_scheme(state, gen_vars, ty)
    }

    /// Generalize a type, excluding a specific name's binding from the environment.
    /// Used when generalizing a recursive binding — the self-reference must not
    /// prevent generalization of the binding's own type variables.
    pub fn generalize_excluding(&self, state: &mut UnifyState, ty: Type, exclude: Symbol) -> Scheme {
        let ty_vars = state.free_unif_vars(&ty);
        let env_vars = self.free_vars_excluding(state, exclude);

        let gen_vars: Vec<TyVarId> = ty_vars
            .into_iter()
            .filter(|v| !env_vars.contains(v))
            .collect();

        Self::finalize_scheme(state, gen_vars, ty)
    }

    /// Generalize a local let/where binding, excluding a specific name.
    /// Unlike `generalize_excluding`, this does NOT convert remaining unsolved
    /// unif vars to rigid `$u` vars — they belong to the outer inference context
    /// and must remain flexible for unification.
    pub fn generalize_local(&self, state: &mut UnifyState, ty: Type, exclude: Symbol) -> Scheme {
        let ty_vars = state.free_unif_vars(&ty);
        let env_vars = self.free_vars_excluding(state, exclude);

        let gen_vars: Vec<TyVarId> = ty_vars
            .into_iter()
            .filter(|v| !env_vars.contains(v))
            .collect();

        // Track which unif vars were generalized
        for &var_id in &gen_vars {
            state.generalized_vars.insert(var_id);
        }

        // Zonk first to resolve any already-solved unification vars
        let ty = state.zonk(ty);

        // Map each generalized TyVarId to a fresh named type variable
        let mut subst: HashMap<TyVarId, Type> = HashMap::new();
        let mut forall_vars: Vec<Symbol> = Vec::new();
        for &var_id in &gen_vars {
            let name = interner::intern(&format!("$t{}", var_id.0));
            subst.insert(var_id, Type::Var(name));
            forall_vars.push(name);
        }

        // DON'T convert remaining unif vars — they're still live in the outer context
        let ty = apply_tyvarid_subst(&subst, &ty);
        Scheme { forall_vars, ty }
    }

    /// Convert generalized TyVarIds into named Type::Var symbols in the type,
    /// producing a self-contained Scheme.
    fn finalize_scheme(state: &mut UnifyState, gen_vars: Vec<TyVarId>, ty: Type) -> Scheme {
        // Zonk first to resolve any already-solved unification vars
        let ty = state.zonk(ty);

        // Track which unif vars were generalized (for deferred constraint checking)
        for &var_id in &gen_vars {
            state.generalized_vars.insert(var_id);
        }

        // Map each generalized TyVarId to a fresh named type variable
        let mut subst: HashMap<TyVarId, Type> = HashMap::new();
        let mut forall_vars: Vec<Symbol> = Vec::new();
        for &var_id in &gen_vars {
            let name = interner::intern(&format!("$t{}", var_id.0));
            subst.insert(var_id, Type::Var(name));
            forall_vars.push(name);
        }

        // Also replace any remaining unsolved Type::Unif (free-in-env vars)
        // with Type::Var so the scheme is fully self-contained and safe to export.
        let remaining = collect_unif_vars(&ty);
        for var_id in remaining {
            if !subst.contains_key(&var_id) {
                let name = interner::intern(&format!("$u{}", var_id.0));
                subst.insert(var_id, Type::Var(name));
            }
        }

        let ty = apply_tyvarid_subst(&subst, &ty);
        Scheme { forall_vars, ty }
    }

    /// Collect all free unification variables across all bindings in the environment.
    fn free_vars(&self, state: &mut UnifyState) -> Vec<TyVarId> {
        let mut vars = Vec::new();
        for scheme in self.bindings.values() {
            // Generalized schemes have Type::Var for quantified vars,
            // so free_unif_vars naturally skips them.
            let scheme_vars = state.free_unif_vars(&scheme.ty);
            for v in scheme_vars {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars
    }

    /// Like free_vars but excluding a specific name's binding.
    fn free_vars_excluding(&self, state: &mut UnifyState, exclude: Symbol) -> Vec<TyVarId> {
        let mut vars = Vec::new();
        for (name, scheme) in &self.bindings {
            if *name == exclude {
                continue;
            }
            let scheme_vars = state.free_unif_vars(&scheme.ty);
            for v in scheme_vars {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars
    }
}

/// Collect all Type::Unif var ids in a type (without probing — just structural walk).
fn collect_unif_vars(ty: &Type) -> Vec<TyVarId> {
    let mut vars = Vec::new();
    collect_unif_vars_inner(ty, &mut vars);
    vars
}

fn collect_unif_vars_inner(ty: &Type, vars: &mut Vec<TyVarId>) {
    match ty {
        Type::Unif(v) => {
            if !vars.contains(v) {
                vars.push(*v);
            }
        }
        Type::Fun(from, to) => {
            collect_unif_vars_inner(from, vars);
            collect_unif_vars_inner(to, vars);
        }
        Type::App(f, a) => {
            collect_unif_vars_inner(f, vars);
            collect_unif_vars_inner(a, vars);
        }
        Type::Forall(_, body) => {
            collect_unif_vars_inner(body, vars);
        }
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                collect_unif_vars_inner(t, vars);
            }
            if let Some(t) = tail {
                collect_unif_vars_inner(t, vars);
            }
        }
        Type::Var(_) | Type::Con(_) | Type::TypeString(_) | Type::TypeInt(_) => {}
    }
}

/// Apply a TyVarId → Type substitution to a type.
fn apply_tyvarid_subst(subst: &HashMap<TyVarId, Type>, ty: &Type) -> Type {
    match ty {
        Type::Unif(v) => match subst.get(v) {
            Some(replacement) => replacement.clone(),
            None => ty.clone(),
        },
        Type::Fun(from, to) => Type::fun(
            apply_tyvarid_subst(subst, from),
            apply_tyvarid_subst(subst, to),
        ),
        Type::App(f, a) => Type::app(
            apply_tyvarid_subst(subst, f),
            apply_tyvarid_subst(subst, a),
        ),
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(apply_tyvarid_subst(subst, body)))
        }
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| (*l, apply_tyvarid_subst(subst, t)))
                .collect();
            let tail = tail.as_ref().map(|t| Box::new(apply_tyvarid_subst(subst, t)));
            Type::Record(fields, tail)
        }
        Type::Var(_) | Type::Con(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
    }
}
