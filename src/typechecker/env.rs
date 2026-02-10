use std::collections::HashMap;

use crate::interner::Symbol;
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

    /// Create a child scope (clone for entering a let/lambda body).
    pub fn child(&self) -> Env {
        self.clone()
    }

    /// Generalize a type: quantify over unification variables in `ty`
    /// that are NOT free in the environment.
    pub fn generalize(&self, state: &mut UnifyState, ty: Type) -> Scheme {
        let ty_vars = state.free_unif_vars(&ty);
        let env_vars = self.free_vars(state);

        let forall_vars: Vec<TyVarId> = ty_vars
            .into_iter()
            .filter(|v| !env_vars.contains(v))
            .collect();

        Scheme { forall_vars, ty }
    }

    /// Collect all free unification variables across all bindings in the environment.
    fn free_vars(&self, state: &mut UnifyState) -> Vec<TyVarId> {
        let mut vars = Vec::new();
        for scheme in self.bindings.values() {
            let scheme_vars = state.free_unif_vars(&scheme.ty);
            for v in scheme_vars {
                if !scheme.forall_vars.contains(&v) && !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars
    }
}
