use crate::ast::span::Span;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::{TyVarId, Type};

/// Entry in the union-find table for a unification variable.
#[derive(Debug, Clone)]
enum UfEntry {
    /// Unsolved root variable with a rank for balancing.
    Root(u32),
    /// This variable links to another (path compression target).
    Link(TyVarId),
    /// This variable has been solved to a concrete type.
    Solved(Type),
}

/// Union-find based unification engine.
pub struct UnifyState {
    entries: Vec<UfEntry>,
}

impl UnifyState {
    pub fn new() -> Self {
        UnifyState {
            entries: Vec::new(),
        }
    }

    /// Create a fresh unification variable.
    pub fn fresh_var(&mut self) -> TyVarId {
        let id = TyVarId(self.entries.len() as u32);
        self.entries.push(UfEntry::Root(0));
        id
    }

    /// Find the representative root for a variable, with path compression.
    fn find(&mut self, var: TyVarId) -> TyVarId {
        let idx = var.0 as usize;
        match &self.entries[idx] {
            UfEntry::Link(next) => {
                let next = *next;
                let root = self.find(next);
                // Path compression
                if root != next {
                    self.entries[idx] = UfEntry::Link(root);
                }
                root
            }
            _ => var,
        }
    }

    /// Get the solved type for a variable, if any.
    pub fn probe(&mut self, var: TyVarId) -> Option<Type> {
        let root = self.find(var);
        match &self.entries[root.0 as usize] {
            UfEntry::Solved(ty) => Some(ty.clone()),
            _ => None,
        }
    }

    /// Walk a type, replacing solved unification variables with their solutions.
    pub fn zonk(&mut self, ty: Type) -> Type {
        match ty {
            Type::Unif(v) => {
                match self.probe(v) {
                    Some(solved) => self.zonk(solved),
                    None => Type::Unif(self.find(v)),
                }
            }
            Type::Fun(from, to) => {
                let from = self.zonk(*from);
                let to = self.zonk(*to);
                Type::fun(from, to)
            }
            Type::App(f, a) => {
                let f = self.zonk(*f);
                let a = self.zonk(*a);
                Type::app(f, a)
            }
            Type::Forall(vars, body) => {
                let body = self.zonk(*body);
                Type::Forall(vars, Box::new(body))
            }
            Type::Con(_) | Type::Var(_) => ty,
        }
    }

    /// Check if a unification variable occurs in a type (prevents infinite types).
    fn occurs_in(&mut self, var: TyVarId, ty: &Type) -> bool {
        match ty {
            Type::Unif(v) => {
                let v_root = self.find(*v);
                let var_root = self.find(var);
                if v_root == var_root {
                    return true;
                }
                match self.probe(*v) {
                    Some(solved) => self.occurs_in(var, &solved),
                    None => false,
                }
            }
            Type::Fun(from, to) => self.occurs_in(var, from) || self.occurs_in(var, to),
            Type::App(f, a) => self.occurs_in(var, f) || self.occurs_in(var, a),
            Type::Forall(_, body) => self.occurs_in(var, body),
            Type::Con(_) | Type::Var(_) => false,
        }
    }

    /// Unify two types. Returns Ok(()) on success, Err(TypeError) on failure.
    pub fn unify(&mut self, span: Span, t1: &Type, t2: &Type) -> Result<(), TypeError> {
        let t1 = self.zonk(t1.clone());
        let t2 = self.zonk(t2.clone());

        match (&t1, &t2) {
            // Both are the same unification variable
            (Type::Unif(a), Type::Unif(b)) => {
                let ra = self.find(*a);
                let rb = self.find(*b);
                if ra == rb {
                    return Ok(());
                }
                // Union by rank
                let rank_a = match &self.entries[ra.0 as usize] {
                    UfEntry::Root(r) => *r,
                    _ => 0,
                };
                let rank_b = match &self.entries[rb.0 as usize] {
                    UfEntry::Root(r) => *r,
                    _ => 0,
                };
                if rank_a < rank_b {
                    self.entries[ra.0 as usize] = UfEntry::Link(rb);
                } else if rank_a > rank_b {
                    self.entries[rb.0 as usize] = UfEntry::Link(ra);
                } else {
                    self.entries[rb.0 as usize] = UfEntry::Link(ra);
                    self.entries[ra.0 as usize] = UfEntry::Root(rank_a + 1);
                }
                Ok(())
            }

            // Unification variable with a type
            (Type::Unif(a), t) | (t, Type::Unif(a)) => {
                let root = self.find(*a);
                if self.occurs_in(root, t) {
                    return Err(TypeError::InfiniteType {
                        span,
                        var: root,
                        ty: t.clone(),
                    });
                }
                self.entries[root.0 as usize] = UfEntry::Solved(t.clone());
                Ok(())
            }

            // Same type constructor
            (Type::Con(a), Type::Con(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(TypeError::UnificationError {
                        span,
                        expected: t1,
                        found: t2,
                    })
                }
            }

            // Same rigid variable
            (Type::Var(a), Type::Var(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(TypeError::UnificationError {
                        span,
                        expected: t1,
                        found: t2,
                    })
                }
            }

            // Function types
            (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
                self.unify(span, a1, a2)?;
                self.unify(span, b1, b2)
            }

            // Type application
            (Type::App(f1, a1), Type::App(f2, a2)) => {
                self.unify(span, f1, f2)?;
                self.unify(span, a1, a2)
            }

            // Mismatch
            _ => Err(TypeError::UnificationError {
                span,
                expected: t1,
                found: t2,
            }),
        }
    }

    /// Collect all unsolved unification variable IDs in a type.
    pub fn free_unif_vars(&mut self, ty: &Type) -> Vec<TyVarId> {
        let mut vars = Vec::new();
        self.collect_free_unif_vars(ty, &mut vars);
        vars
    }

    fn collect_free_unif_vars(&mut self, ty: &Type, vars: &mut Vec<TyVarId>) {
        match ty {
            Type::Unif(v) => {
                match self.probe(*v) {
                    Some(solved) => self.collect_free_unif_vars(&solved, vars),
                    None => {
                        let root = self.find(*v);
                        if !vars.contains(&root) {
                            vars.push(root);
                        }
                    }
                }
            }
            Type::Fun(from, to) => {
                self.collect_free_unif_vars(from, vars);
                self.collect_free_unif_vars(to, vars);
            }
            Type::App(f, a) => {
                self.collect_free_unif_vars(f, vars);
                self.collect_free_unif_vars(a, vars);
            }
            Type::Forall(_, body) => {
                self.collect_free_unif_vars(body, vars);
            }
            Type::Con(_) | Type::Var(_) => {}
        }
    }
}
