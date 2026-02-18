use crate::ast::span::Span;
use crate::typechecker::error::TypeError;
use crate::interner::Symbol;
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
    /// Type aliases: name → (type_var_names, expanded_body).
    pub type_aliases: std::collections::HashMap<crate::interner::Symbol, (Vec<crate::interner::Symbol>, Type)>,
    /// Guard against infinite alias expansion cycles (e.g. `type A = A`).
    expanding_aliases: Vec<crate::interner::Symbol>,
    /// Unification variables that were generalized (part of a polymorphic type scheme).
    /// Used to distinguish polymorphic constraints (skip) from ambiguous ones (error).
    pub generalized_vars: std::collections::HashSet<TyVarId>,
}

impl UnifyState {
    pub fn new() -> Self {
        UnifyState {
            entries: Vec::new(),
            type_aliases: std::collections::HashMap::new(),
            expanding_aliases: Vec::new(),
            generalized_vars: std::collections::HashSet::new(),
        }
    }

    /// Return the number of unification variables currently allocated.
    /// Useful to snapshot before inference and identify which vars are "new".
    pub fn var_count(&self) -> u32 {
        self.entries.len() as u32
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

    /// Public wrapper around find() for external callers that need the root representative.
    pub fn find_root(&mut self, var: TyVarId) -> TyVarId {
        self.find(var)
    }

    /// Check if a unification variable is completely untouched:
    /// still a root with rank 0 and not solved. This means it was never
    /// involved in any unification operation.
    pub fn is_untouched(&mut self, var: TyVarId) -> bool {
        let root = self.find(var);
        if root != var {
            return false; // var was linked to another root
        }
        matches!(&self.entries[root.0 as usize], UfEntry::Root(0))
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
        self.zonk_ref(&ty).unwrap_or(ty)
    }

    /// Zonk by reference. Returns None if the type is unchanged (avoiding allocation).
    fn zonk_ref(&mut self, ty: &Type) -> Option<Type> {
        match ty {
            Type::Unif(v) => {
                match self.probe(*v) {
                    Some(solved) => Some(self.zonk(solved)),
                    None => {
                        let root = self.find(*v);
                        if root != *v { Some(Type::Unif(root)) } else { None }
                    }
                }
            }
            Type::Fun(from, to) => {
                let from_z = self.zonk_ref(from);
                let to_z = self.zonk_ref(to);
                if from_z.is_none() && to_z.is_none() {
                    return None;
                }
                Some(Type::fun(
                    from_z.unwrap_or_else(|| (**from).clone()),
                    to_z.unwrap_or_else(|| (**to).clone()),
                ))
            }
            Type::App(f, a) => {
                let f_z = self.zonk_ref(f);
                let a_z = self.zonk_ref(a);
                let f_resolved = f_z.as_ref().unwrap_or(f);
                let a_resolved = a_z.as_ref().unwrap_or(a);
                // Normalize App(App(Con("->"), from), to) and App(App(Con("Function"), from), to) → Fun(from, to)
                if let Type::App(ff, from) = f_resolved {
                    if let Type::Con(sym) = ff.as_ref() {
                        let name = crate::interner::resolve(*sym).unwrap_or_default();
                        if name == "->" || name == "Function" {
                            return Some(Type::fun(from.as_ref().clone(), a_resolved.clone()));
                        }
                    }
                }
                if f_z.is_none() && a_z.is_none() {
                    // No unif var changes, but still try alias expansion
                    let expanded = self.try_expand_alias(ty.clone());
                    if expanded == *ty { None } else { Some(expanded) }
                } else {
                    let result = Type::app(
                        f_z.unwrap_or_else(|| (**f).clone()),
                        a_z.unwrap_or_else(|| (**a).clone()),
                    );
                    Some(self.try_expand_alias(result))
                }
            }
            Type::Forall(vars, body) => {
                self.zonk_ref(body).map(|body_z| Type::Forall(vars.clone(), Box::new(body_z)))
            }
            Type::Record(fields, tail) => {
                let mut any_changed = false;
                let mut new_fields: Vec<_> = fields.iter().map(|(l, t)| {
                    match self.zonk_ref(t) {
                        Some(t_z) => { any_changed = true; (*l, t_z) }
                        None => (*l, t.clone()),
                    }
                }).collect();
                let new_tail = match tail {
                    Some(t) => match self.zonk_ref(t) {
                        Some(t_z) => { any_changed = true; Some(Box::new(t_z)) }
                        None => Some(t.clone()),
                    }
                    None => None,
                };
                if !any_changed {
                    // Check for record normalization even without unif changes
                    if let Some(ref t) = new_tail {
                        if matches!(t.as_ref(), Type::Record(..)) {
                            any_changed = true;
                        }
                    }
                    if !any_changed {
                        return None;
                    }
                }
                // Normalize: collapse nested record tails
                match new_tail {
                    Some(ref t) => match t.as_ref() {
                        Type::Record(tail_fields, inner_tail) if tail_fields.is_empty() && inner_tail.is_none() => {
                            Some(Type::Record(new_fields, None))
                        }
                        Type::Record(tail_fields, inner_tail) => {
                            new_fields.extend(tail_fields.iter().cloned());
                            Some(Type::Record(new_fields, inner_tail.clone()))
                        }
                        _ => Some(Type::Record(new_fields, new_tail)),
                    }
                    None => Some(Type::Record(new_fields, None)),
                }
            }
            Type::Con(sym) => {
                let name = crate::interner::resolve(*sym).unwrap_or_default();
                if name == "Function" {
                    return Some(Type::Con(crate::interner::intern("->")));
                }
                if self.type_aliases.is_empty() {
                    return None;
                }
                // Try to expand zero-arg type aliases (e.g. `Size` → `Int`)
                let expanded = self.try_expand_alias(ty.clone());
                if expanded == *ty { None } else { Some(expanded) }
            }
            Type::Var(_) | Type::TypeString(_) | Type::TypeInt(_) => None,
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
        // Fast path for leaf types: avoid clone+zonk when both sides are simple
        match (t1, t2) {
            (Type::Con(a), Type::Con(b)) if a == b => {
                return Ok(());
            }
            // Don't fast-fail Con mismatches — one side may be a type alias
            (Type::Var(a), Type::Var(b)) => {
                return if a == b {
                    Ok(())
                } else {
                    Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    })
                };
            }
            (Type::TypeString(a), Type::TypeString(b)) => {
                return if a == b {
                    Ok(())
                } else {
                    Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    })
                };
            }
            (Type::TypeInt(a), Type::TypeInt(b)) => {
                return if a == b {
                    Ok(())
                } else {
                    Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    })
                };
            }
            _ => {}
        }

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

            // Same type constructor (already handled in fast path, but zonk may have reduced to Con)
            (Type::Con(a), Type::Con(b)) => {
                if a == b {
                    Ok(())
                } else {
                    let t1_exp = self.try_expand_alias(t1.clone());
                    let t2_exp = self.try_expand_alias(t2.clone());
                    if t1_exp != t1 || t2_exp != t2 {
                        return self.unify(span, &t1_exp, &t2_exp);
                    }
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

            // Fun(a, b) vs App(f, arg): decompose structurally.
            // Fun(a, b) = App(App(Con(->), a), b), so unify arg with b
            // and f with App(Con(->), a). We can't convert the whole Fun to App
            // because zonk normalizes App(App(Con(->),a),b) back to Fun(a,b),
            // which would cause infinite recursion.
            (Type::Fun(a, b), Type::App(f, arg)) => {
                let partial_arrow = Type::app(Type::Con(crate::interner::intern("->")), (**a).clone());
                self.unify(span, &partial_arrow, f)?;
                self.unify(span, b, arg)
            }
            (Type::App(f, arg), Type::Fun(a, b)) => {
                let partial_arrow = Type::app(Type::Con(crate::interner::intern("->")), (**a).clone());
                self.unify(span, f, &partial_arrow)?;
                self.unify(span, arg, b)
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

            // App(Con("Record"), row) vs Record(fields, tail):
            // `Record r` is equivalent to `{ | r }`, i.e. Record([], Some(r)).
            // Convert to Record form and unify as records.
            (Type::App(f, row), Type::Record(fields2, tail2)) if {
                matches!(f.as_ref(), Type::Con(sym) if crate::interner::resolve(*sym).unwrap_or_default() == "Record")
            } => {
                let empty: Vec<(Symbol, Type)> = vec![];
                self.unify_records(span, &empty, &Some(Box::new((**row).clone())), fields2, tail2, &t1, &t2)
            }
            (Type::Record(fields1, tail1), Type::App(f, row)) if {
                matches!(f.as_ref(), Type::Con(sym) if crate::interner::resolve(*sym).unwrap_or_default() == "Record")
            } => {
                let empty: Vec<(Symbol, Type)> = vec![];
                self.unify_records(span, fields1, tail1, &empty, &Some(Box::new((**row).clone())), &t1, &t2)
            }

            // Forall types: instantiate with fresh vars and unify bodies
            (Type::Forall(vars, body), _) => {
                let instantiated = self.instantiate_forall(vars, body);
                self.unify(span, &instantiated, &t2)
            }
            (_, Type::Forall(vars, body)) => {
                let instantiated = self.instantiate_forall(vars, body);
                self.unify(span, &t1, &instantiated)
            }

            // Mismatch — try alias expansion as a last resort
            _ => {
                let t1_exp = self.try_expand_alias(t1.clone());
                let t2_exp = self.try_expand_alias(t2.clone());
                if t1_exp != t1 || t2_exp != t2 {
                    return self.unify(span, &t1_exp, &t2_exp);
                }
                Err(TypeError::UnificationError {
                    span,
                    expected: t1,
                    found: t2,
                })
            }
        }
    }

    /// Unify two record types, handling row polymorphism.
    /// Supports duplicate labels: each field in row1 consumes the first matching
    /// field in row2, allowing `(x :: A, x :: B | r)` to work correctly.
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
        // Match fields from fields1 against fields2, consuming matched entries.
        // This correctly handles duplicate labels: (x :: A, x :: B) matches
        // two x entries from the other side, one at a time.
        let mut remaining2: Vec<(crate::interner::Symbol, Type)> = fields2.to_vec();
        let mut only_in_1: Vec<(crate::interner::Symbol, Type)> = Vec::new();

        for (label1, ty1) in fields1 {
            if let Some(idx) = remaining2.iter().position(|(l, _)| *l == *label1) {
                let (_, ty2) = remaining2.remove(idx);
                self.unify(span, ty1, &ty2)?;
            } else {
                only_in_1.push((*label1, ty1.clone()));
            }
        }
        let only_in_2 = remaining2;

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
                if !only_in_1.is_empty() {
                    return Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    });
                }
                if only_in_2.is_empty() {
                    self.unify(span, tail1, &Type::Record(vec![], None))
                } else {
                    self.unify(span, tail1, &Type::Record(only_in_2, None))
                }
            }
            (None, Some(tail2)) => {
                if !only_in_2.is_empty() {
                    return Err(TypeError::UnificationError {
                        span,
                        expected: t1.clone(),
                        found: t2.clone(),
                    });
                }
                if only_in_1.is_empty() {
                    self.unify(span, tail2, &Type::Record(vec![], None))
                } else {
                    self.unify(span, tail2, &Type::Record(only_in_1, None))
                }
            }
            (Some(tail1), Some(tail2)) => {
                if only_in_1.is_empty() && only_in_2.is_empty() {
                    self.unify(span, tail1, tail2)
                } else {
                    // Check if both tails resolve to the same unification variable.
                    // If so, unifying `?r ~ { fields | ?fresh }` twice creates an
                    // infinite type.
                    let t1z = self.zonk((**tail1).clone());
                    let t2z = self.zonk((**tail2).clone());
                    if let (Type::Unif(a), Type::Unif(b)) = (&t1z, &t2z) {
                        if self.find(*a) == self.find(*b) && !only_in_1.is_empty() && !only_in_2.is_empty() {
                            return Err(TypeError::UnificationError {
                                span,
                                expected: t1.clone(),
                                found: t2.clone(),
                            });
                        }
                    }
                    let fresh_tail = Type::Unif(self.fresh_var());
                    // When one side has no extra fields, unify its tail directly
                    // with the fresh tail (avoid creating Record([], Some(tail))
                    // which fails to unify with rigid type variables).
                    let ext1 = if only_in_2.is_empty() {
                        fresh_tail.clone()
                    } else {
                        Type::Record(only_in_2, Some(Box::new(fresh_tail.clone())))
                    };
                    let ext2 = if only_in_1.is_empty() {
                        fresh_tail
                    } else {
                        Type::Record(only_in_1, Some(Box::new(fresh_tail)))
                    };
                    self.unify(span, tail1, &ext1)?;
                    self.unify(span, tail2, &ext2)
                }
            }
        }
    }

    /// Try to expand a type alias application.
    /// Collects args from nested App(App(Con(alias), a1), a2) and substitutes into the alias body.
    fn try_expand_alias(&mut self, ty: Type) -> Type {
        if self.type_aliases.is_empty() {
            return ty;
        }
        // Collect the head constructor and arguments from nested App chains
        let mut args = Vec::new();
        let mut head = &ty;
        loop {
            match head {
                Type::App(f, a) => {
                    args.push(a.as_ref());
                    head = f.as_ref();
                }
                _ => break,
            }
        }
        if let Type::Con(name) = head {
            // Guard against infinite alias expansion (e.g. `type Number = P.Number`
            // where P.Number resolves back to Con("Number"))
            if self.expanding_aliases.contains(name) {
                return ty;
            }
            if let Some((params, body)) = self.type_aliases.get(name).cloned() {
                // Args collected in reverse order (outermost last)
                args.reverse();
                if args.len() == params.len() {
                    // Fully saturated alias — expand
                    let subst: std::collections::HashMap<crate::interner::Symbol, Type> = params
                        .iter()
                        .zip(args.iter())
                        .map(|(&p, &a)| (p, a.clone()))
                        .collect();
                    let expanded = self.apply_symbol_subst(&subst, &body);
                    // Zonk the result in case expansion introduces more structure
                    self.expanding_aliases.push(*name);
                    let result = self.zonk(expanded);
                    self.expanding_aliases.pop();
                    return result;
                }
                // Partially applied alias — return as-is
            }
        }
        ty
    }

    /// Instantiate a Forall type by replacing each bound variable with a fresh unif var.
    fn instantiate_forall(&mut self, vars: &[(crate::interner::Symbol, bool)], body: &Type) -> Type {
        use std::collections::HashMap;
        let subst: HashMap<crate::interner::Symbol, Type> = vars
            .iter()
            .map(|&(v, _)| (v, Type::Unif(self.fresh_var())))
            .collect();
        self.apply_symbol_subst(&subst, body)
    }

    /// Apply a substitution of symbol names to types (for forall instantiation).
    fn apply_symbol_subst(
        &self,
        subst: &std::collections::HashMap<crate::interner::Symbol, Type>,
        ty: &Type,
    ) -> Type {
        match ty {
            Type::Var(sym) => subst.get(sym).cloned().unwrap_or_else(|| ty.clone()),
            Type::Fun(from, to) => Type::fun(
                self.apply_symbol_subst(subst, from),
                self.apply_symbol_subst(subst, to),
            ),
            Type::App(f, a) => Type::app(
                self.apply_symbol_subst(subst, f),
                self.apply_symbol_subst(subst, a),
            ),
            Type::Forall(vars, body) => {
                let mut inner_subst = subst.clone();
                for (v, _) in vars {
                    inner_subst.remove(v);
                }
                // Capture-avoiding: check if any forall-bound var name appears
                // free in the substitution values. If so, alpha-rename to avoid capture.
                let mut new_vars = vars.clone();
                let needs_rename = new_vars.iter().any(|(v, _)| {
                    inner_subst.values().any(|val| type_has_free_var(val, *v))
                });
                if needs_rename {
                    use std::collections::HashMap;
                    let mut rename: HashMap<Symbol, Type> = HashMap::new();
                    for (v, _) in &mut new_vars {
                        if inner_subst.values().any(|val| type_has_free_var(val, *v)) {
                            let fresh = fresh_type_var_symbol(*v);
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
                let fields = fields
                    .iter()
                    .map(|(l, t)| (*l, self.apply_symbol_subst(subst, t)))
                    .collect();
                let tail = tail
                    .as_ref()
                    .map(|t| Box::new(self.apply_symbol_subst(subst, t)));
                Type::Record(fields, tail)
            }
            Type::Unif(_) | Type::Con(_) | Type::TypeString(_) | Type::TypeInt(_) => ty.clone(),
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

/// Check if a type contains a free (not forall-bound) Type::Var with the given name.
pub fn type_has_free_var(ty: &Type, name: Symbol) -> bool {
    match ty {
        Type::Var(v) => *v == name,
        Type::Fun(a, b) => type_has_free_var(a, name) || type_has_free_var(b, name),
        Type::App(f, a) => type_has_free_var(f, name) || type_has_free_var(a, name),
        Type::Forall(vars, body) => {
            if vars.iter().any(|(v, _)| *v == name) {
                false // shadowed by this forall
            } else {
                type_has_free_var(body, name)
            }
        }
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_has_free_var(t, name))
                || tail.as_ref().map_or(false, |t| type_has_free_var(t, name))
        }
        Type::Unif(_) | Type::Con(_) | Type::TypeString(_) | Type::TypeInt(_) => false,
    }
}

/// Generate a fresh unique symbol for alpha-renaming forall-bound variables.
pub fn fresh_type_var_symbol(base: Symbol) -> Symbol {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let base_name = crate::interner::resolve(base).unwrap_or_default();
    crate::interner::intern(&format!("{}${}", base_name, n))
}
