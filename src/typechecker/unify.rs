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
            Type::Record(fields, tail) => {
                let fields = fields.into_iter().map(|(l, t)| (l, self.zonk(t))).collect();
                let tail = tail.map(|t| Box::new(self.zonk(*t)));
                Type::Record(fields, tail)
            }
            Type::Con(_) | Type::Var(_) | Type::TypeString(_) | Type::TypeInt(_) => ty,
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
            Type::Record(fields, tail) => {
                fields.iter().any(|(_, t)| self.occurs_in(var, t))
                    || tail.as_ref().map_or(false, |t| self.occurs_in(var, t))
            }
            Type::Con(_) | Type::Var(_) | Type::TypeString(_) | Type::TypeInt(_) => false,
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

            // Type-level string literals
            (Type::TypeString(a), Type::TypeString(b)) => {
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

            // Type-level integer literals
            (Type::TypeInt(a), Type::TypeInt(b)) => {
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

            // Record types
            (Type::Record(fields1, tail1), Type::Record(fields2, tail2)) => {
                self.unify_records(span, fields1, tail1, fields2, tail2, &t1, &t2)
            }

            // Mismatch
            _ => Err(TypeError::UnificationError {
                span,
                expected: t1,
                found: t2,
            }),
        }
    }

    /// Unify two record types, handling row polymorphism.
    fn unify_records(
        &mut self,
        span: Span,
        fields1: &Vec<(crate::interner::Symbol, Type)>,
        tail1: &Option<Box<Type>>,
        fields2: &Vec<(crate::interner::Symbol, Type)>,
        tail2: &Option<Box<Type>>,
        t1: &Type,
        t2: &Type,
    ) -> Result<(), TypeError> {
        use std::collections::HashMap;

        let map1: HashMap<_, _> = fields1.iter().map(|(l, t)| (*l, t)).collect();
        let map2: HashMap<_, _> = fields2.iter().map(|(l, t)| (*l, t)).collect();

        // Unify fields present in both
        for (label, ty1) in &map1 {
            if let Some(ty2) = map2.get(label) {
                self.unify(span, ty1, ty2)?;
            }
        }

        // Check for fields only in one side
        let only_in_1: Vec<_> = fields1.iter()
            .filter(|(l, _)| !map2.contains_key(l))
            .cloned()
            .collect();
        let only_in_2: Vec<_> = fields2.iter()
            .filter(|(l, _)| !map1.contains_key(l))
            .cloned()
            .collect();

        match (tail1, tail2) {
            (None, None) => {
                // Closed records — must have exactly the same fields
                if !only_in_1.is_empty() || !only_in_2.is_empty() {
                    return Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    });
                }
                Ok(())
            }
            (Some(tail1), None) => {
                // Left has tail: extra fields from right should be empty,
                // and tail should unify with a record of fields only in left side... no wait
                // Actually: left is open, right is closed. Left's extra fields must not exist.
                if !only_in_1.is_empty() {
                    return Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    });
                }
                // Tail should unify with empty record
                self.unify(span, tail1, &Type::Record(only_in_2, None))
            }
            (None, Some(tail2)) => {
                if !only_in_2.is_empty() {
                    return Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    });
                }
                self.unify(span, tail2, &Type::Record(only_in_1, None))
            }
            (Some(tail1), Some(tail2)) => {
                // Both open: create a fresh tail for the merged record
                let fresh_tail = Type::Unif(self.fresh_var());
                self.unify(span, tail1, &Type::Record(only_in_2, Some(Box::new(fresh_tail.clone()))))?;
                self.unify(span, tail2, &Type::Record(only_in_1, Some(Box::new(fresh_tail))))
            }
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
            Type::Record(fields, tail) => {
                for (_, t) in fields {
                    self.collect_free_unif_vars(t, vars);
                }
                if let Some(tail) = tail {
                    self.collect_free_unif_vars(tail, vars);
                }
            }
            Type::Con(_) | Type::Var(_) | Type::TypeString(_) | Type::TypeInt(_) => {}
        }
    }
}
