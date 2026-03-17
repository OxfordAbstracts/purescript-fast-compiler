use crate::span::Span;
use crate::cst::{QualifiedIdent, unqualified_ident};
use crate::typechecker::error::TypeError;
use crate::interner::Symbol;
use crate::typechecker::types::{TyVarId, Type};
use std::collections::HashSet;

/// Check if a type body contains `Con(name)` applied to exactly `expected_args`
/// arguments anywhere in the type tree. Used to detect truly self-referential
/// aliases where expanding the alias produces a usage that would trigger
/// re-expansion with the same arity.
///
/// For example, if alias `Codec` has 1 param and its expanded body contains
/// `Con("Codec")` with 5 args (the data type), that's NOT self-referential
/// because 5 != 1. But if it contains `Con("Codec")` with 1 arg, it IS
/// self-referential because it would be re-expanded as the same alias.
fn contains_self_referential_usage(ty: &Type, name: Symbol, expected_args: usize) -> bool {
    match ty {
        // Only unqualified Con references count as self-referential.
        // Qualified references like `AskForReview.Model` are different types,
        // not self-references to the local `Model` alias.
        Type::Con(n) => n.name == name && n.module.is_none() && expected_args == 0,
        Type::App(_, _) => {
            // Collect the full App spine
            let mut head = ty;
            let mut args: Vec<&Type> = Vec::new();
            while let Type::App(f, a) = head {
                args.push(a.as_ref());
                head = f.as_ref();
            }
            // Check if this App chain is headed by Con(name)
            if let Type::Con(n) = head {
                if n.name == name && n.module.is_none() {
                    // For zero-param aliases, ANY occurrence of the name in the body is
                    // self-referential — zonk_ref expands bare Con eagerly, then recurses
                    // into App components, reaching the inner bare Con again (infinite loop).
                    // For non-zero-param aliases, only matching arg counts are self-referential.
                    if expected_args == 0 || args.len() == expected_args {
                        return true;
                    }
                }
            }
            // Recurse into head and all args
            contains_self_referential_usage(head, name, expected_args)
                || args.iter().any(|a| contains_self_referential_usage(a, name, expected_args))
        }
        Type::Fun(from, to) => {
            contains_self_referential_usage(from, name, expected_args)
                || contains_self_referential_usage(to, name, expected_args)
        }
        Type::Forall(_, body) => contains_self_referential_usage(body, name, expected_args),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| contains_self_referential_usage(t, name, expected_args))
                || tail.as_ref().map_or(false, |t| contains_self_referential_usage(t, name, expected_args))
        }
        _ => false,
    }
}

/// Quick check: does a type body reference any Con name from the given set?
/// Used as a pre-filter to skip aliases that can't possibly be self-referential.
fn type_references_any_name(ty: &Type, names: &HashSet<Symbol>) -> bool {
    match ty {
        Type::Con(n) => names.contains(&n.name),
        Type::App(f, a) => type_references_any_name(f, names) || type_references_any_name(a, names),
        Type::Fun(from, to) => type_references_any_name(from, names) || type_references_any_name(to, names),
        Type::Forall(_, body) => type_references_any_name(body, names),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_references_any_name(t, names))
                || tail.as_ref().map_or(false, |t| type_references_any_name(t, names))
        }
        _ => false,
    }
}

/// Collect the head and arguments of an App chain.
/// E.g. `App(App(Con(X), a), b)` → `(Con(X), [a, b])`.
fn collect_app_spine(ty: &Type) -> (&Type, Vec<&Type>) {
    let mut head = ty;
    let mut args: Vec<&Type> = Vec::new();
    while let Type::App(f, a) = head {
        args.push(a.as_ref());
        head = f.as_ref();
    }
    args.reverse();
    (head, args)
}

/// Cached well-known symbols to avoid repeated interner lookups on hot paths.
struct WellKnownSyms {
    arrow: QualifiedIdent,
    function: QualifiedIdent,
    record: QualifiedIdent,
}

static WELL_KNOWN: std::sync::LazyLock<WellKnownSyms> = std::sync::LazyLock::new(|| {
    WellKnownSyms {
        arrow: unqualified_ident("->"),
        function: unqualified_ident("Function"),
        record: unqualified_ident("Record"),
    }
});

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
    /// Recursion depth for unify to prevent stack overflow.
    unify_depth: u32,
    /// Unification variables that were generalized (part of a polymorphic type scheme).
    /// Used to distinguish polymorphic constraints (skip) from ambiguous ones (error).
    pub generalized_vars: std::collections::HashSet<TyVarId>,
    /// Aliases whose fully-expanded body still contains Con(alias_name).
    /// These must not be eagerly re-expanded during unification to prevent infinite loops.
    pub self_referential_aliases: std::collections::HashSet<crate::interner::Symbol>,
    /// Maps import qualifier aliases to canonical (full) module names.
    /// Used during kind unification to detect when two `Type::Con` with the same
    /// unqualified name but different module qualifiers actually refer to different types
    /// (e.g., `LibA.DemoKind` vs `LibB.DemoKind`). Only populated for kind-level UnifyState.
    pub qualifier_to_canonical: std::collections::HashMap<crate::interner::Symbol, crate::interner::Symbol>,
    /// Type constructor arities: used to disambiguate alias vs data type when they share
    /// the same name (e.g., `type Codec a = ...` with 1 param vs `data Codec m i o a b` with 5).
    /// Maps QualifiedIdent → param count. Populated from check.rs.
    pub type_con_arities: std::collections::HashMap<QualifiedIdent, usize>,
    /// Maps canonical module paths to import-alias module names.
    /// E.g. "Components.AskForReview" → "AskForReview".
    /// Used in `try_expand_alias` to resolve canonical qualified type constructors
    /// (from exported types) back to import-alias-qualified alias keys.
    pub canonical_to_qualifier: std::collections::HashMap<crate::interner::Symbol, crate::interner::Symbol>,
    /// Zero-arg alias names that genuinely collide with data types from different modules.
    /// When set (non-empty), zonk_ref's Type::Con branch skips expansion for these names.
    /// Only populated temporarily during export-time zonking. Unlike con_zero_blockers
    /// (which scans imported alias bodies), this uses registry type_con_arities to verify
    /// that the name is actually a data type in some module (not just a blocked alias).
    pub zonk_con_blockers: std::collections::HashSet<crate::interner::Symbol>,
}

impl UnifyState {
    pub fn new() -> Self {
        UnifyState {
            entries: Vec::new(),
            type_aliases: std::collections::HashMap::new(),
            expanding_aliases: Vec::new(),
            unify_depth: 0,
            generalized_vars: std::collections::HashSet::new(),
            self_referential_aliases: std::collections::HashSet::new(),
            qualifier_to_canonical: std::collections::HashMap::new(),
            type_con_arities: std::collections::HashMap::new(),
            canonical_to_qualifier: std::collections::HashMap::new(),
            zonk_con_blockers: std::collections::HashSet::new(),
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

    /// Ensure a TyVarId has an entry. Stale IDs from other modules' UnifyStates
    /// get accommodated by extending the entries array.
    fn ensure_entry(&mut self, var: TyVarId) {
        let idx = var.0 as usize;
        if idx >= self.entries.len() {
            self.entries.resize(idx + 1, UfEntry::Root(0));
        }
    }

    /// Find the representative root for a variable, with path compression.
    fn find(&mut self, var: TyVarId) -> TyVarId {
        let idx = var.0 as usize;
        if idx >= self.entries.len() {
            // Stale TyVarId from another module's UnifyState — extend to accommodate
            self.ensure_entry(var);
            return var;
        }
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

    /// Check if two type constructors with the same unqualified name actually conflict
    /// because they come from different modules (different canonical origins).
    /// Returns true if they conflict (should NOT unify).
    /// Only applies when both sides have explicit module qualifiers and the
    /// qualifier_to_canonical mapping is populated (kind-level unification).
    fn con_modules_conflict(&self, a: &crate::cst::QualifiedIdent, b: &crate::cst::QualifiedIdent) -> bool {
        if self.qualifier_to_canonical.is_empty() {
            return false;
        }
        if let (Some(mod_a), Some(mod_b)) = (a.module, b.module) {
            if mod_a == mod_b {
                return false; // Same qualifier → same module
            }
            let canon_a = self.qualifier_to_canonical.get(&mod_a).copied().unwrap_or(mod_a);
            let canon_b = self.qualifier_to_canonical.get(&mod_b).copied().unwrap_or(mod_b);
            canon_a != canon_b
        } else {
            false
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
        self.zonk_ref(&ty).unwrap_or(ty)
    }

    /// Zonk by reference. Returns None if the type is unchanged (avoiding allocation).
    fn zonk_ref(&mut self, ty: &Type) -> Option<Type> {
        stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || self.zonk_ref_impl(ty))
    }

    fn zonk_ref_impl(&mut self, ty: &Type) -> Option<Type> {
        super::check_deadline();
        match ty {
            Type::Unif(v) => {
                // Guard against stale TyVarIds from another module's UnifyState
                if (v.0 as usize) >= self.entries.len() {
                    return None;
                }
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
            Type::App(_, _) => {
                // Collect the full application spine to avoid alias-expanding
                // partial applications. Without this, App(Con("Codec"), x) inside
                // a 5-arg application would be incorrectly expanded as a 1-param
                // alias, causing exponential type growth.
                let mut spine_args: Vec<&Type> = Vec::new();
                let mut head = ty;
                while let Type::App(f, a) = head {
                    spine_args.push(a.as_ref());
                    head = f.as_ref();
                }
                spine_args.reverse();

                // Zonk the head
                let head_z = self.zonk_ref(head);
                let head_resolved = head_z.as_ref().unwrap_or(&head);

                // Zonk each argument
                let mut any_changed = head_z.is_some();
                let mut args_z: Vec<Option<Type>> = Vec::with_capacity(spine_args.len());
                for arg in &spine_args {
                    let z = self.zonk_ref(arg);
                    if z.is_some() { any_changed = true; }
                    args_z.push(z);
                }

                // Normalize arrow: App(App(Con("->"), from), to) → Fun(from, to)
                if spine_args.len() >= 2 {
                    if let Type::Con(sym) = head_resolved {
                        let wk = &*WELL_KNOWN;
                        if *sym == wk.arrow || *sym == wk.function {
                            if spine_args.len() == 2 {
                                let from = args_z[0].clone().unwrap_or_else(|| (*spine_args[0]).clone());
                                let to = args_z[1].clone().unwrap_or_else(|| (*spine_args[1]).clone());
                                return Some(Type::fun(from, to));
                            }
                        }
                    }
                }

                if !any_changed {
                    // No subterm changes — try alias expansion on the full spine
                    if self.is_alias_app_non_self_referential(ty) {
                        let expanded = self.try_expand_alias(ty.clone());
                        if expanded == *ty { None } else {
                            // Recursively zonk the expanded body so that nested aliases
                            // (e.g. zero-arg aliases like `ResponseUpdate` inside the
                            // body of a multi-arg alias like `HTML`) are also expanded.
                            Some(self.zonk(expanded))
                        }
                    } else {
                        None
                    }
                } else {
                    // Rebuild from zonked parts
                    let mut result = head_z.unwrap_or_else(|| head.clone());
                    for (i, arg) in spine_args.iter().enumerate() {
                        let a = args_z[i].clone().unwrap_or_else(|| (*arg).clone());
                        result = Type::app(result, a);
                    }
                    // Try alias expansion on the full rebuilt type
                    if self.is_alias_app_non_self_referential(&result) {
                        let expanded = self.try_expand_alias(result);
                        // Recursively zonk so nested aliases in the expanded body
                        // are also expanded.
                        Some(self.zonk(expanded))
                    } else {
                        Some(result)
                    }
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
                let wk = &*WELL_KNOWN;
                if *sym == wk.function {
                    return Some(Type::Con(wk.arrow));
                }
                // Skip expansion if this name is in the zonk_con_blockers set
                // (zero-arg alias genuinely colliding with a data type from a different module).
                if !self.zonk_con_blockers.is_empty() && self.zonk_con_blockers.contains(&sym.name) {
                    return None;
                }
                // Try to expand zero-arg type aliases (e.g. `Size` → `Int`, `NegOne` → -1).
                // Skip self-referential aliases to avoid infinite expansion.
                // Use qualified key when module qualifier is present (e.g. Tick.Easing).
                let alias_key = if let Some(module) = sym.module {
                    let mod_str = crate::interner::resolve(module).unwrap_or_default();
                    let name_str = crate::interner::resolve(sym.name).unwrap_or_default();
                    crate::interner::intern(&format!("{}.{}", mod_str, name_str))
                } else {
                    sym.name
                };
                let is_zero_arg = self.type_aliases.get(&alias_key)
                    .map_or(false, |(params, _)| params.is_empty());
                if !self.self_referential_aliases.contains(&sym.name) && is_zero_arg
                {
                    let expanded = self.try_expand_alias(ty.clone());
                    if expanded == *ty {
                        None
                    } else if contains_self_referential_usage(&expanded, sym.name, 0) {
                        // Runtime detection: the expanded body still references the
                        // same name — this alias is self-referential through imports.
                        // Mark it to prevent future expansion attempts.
                        self.self_referential_aliases.insert(sym.name);
                        None
                    } else {
                        // Recursively zonk the expanded body so that nested aliases
                        // within the zero-arg alias body are also expanded.
                        Some(self.zonk(expanded))
                    }
                } else {
                    None
                }
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
        self.unify_depth += 1;
        let result = self.unify_inner(span, t1, t2);
        self.unify_depth -= 1;
        result
    }

    fn unify_inner(&mut self, span: Span, t1: &Type, t2: &Type) -> Result<(), TypeError> {
        stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || self.unify_inner_impl(span, t1, t2))
    }

    fn unify_inner_impl(&mut self, span: Span, t1: &Type, t2: &Type) -> Result<(), TypeError> {
        if self.unify_depth > 800 {
            // Even at extreme depth, identical types should unify trivially
            if t1 == t2 {
                return Ok(());
            }
            return Err(TypeError::UnificationError {
                span,
                expected: t1.clone(),
                found: t2.clone(),
            });
        }
        super::check_deadline();
        // Fast path for leaf types: avoid clone+zonk when both sides are simple
        match (t1, t2) {
            (Type::Con(a), Type::Con(b)) if a.name == b.name && !self.con_modules_conflict(a, b) => {
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

        // Eagerly expand type aliases after zonk so structural matching
        // sees the expanded forms (e.g., `Except e a` → `ExceptT e Identity a`).
        // Skip transitively self-referential aliases to prevent infinite loops
        // where App-App recursion re-discovers partially-applied fragments.
        let t1 = if self.is_alias_app_non_self_referential(&t1) {
            self.try_expand_alias(t1.clone())
        } else {
            t1
        };
        let t2 = if self.is_alias_app_non_self_referential(&t2) {
            self.try_expand_alias(t2.clone())
        } else {
            t2
        };

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
                if a.name == b.name && !self.con_modules_conflict(a, b) {
                    Ok(())
                } else {
                    let t1_exp = self.try_expand_alias(t1.clone());
                    let t2_exp = self.try_expand_alias(t2.clone());
                    if t1_exp != t1 || t2_exp != t2 {
                        return self.unify(span, &t1_exp, &t2_exp);
                    }
                    // Eta-expand partially applied aliases
                    let missing1 = self.partially_applied_alias_missing(&t1);
                    let missing2 = self.partially_applied_alias_missing(&t2);
                    let n = missing1.max(missing2);
                    if n > 0 {
                        let fresh_vars: Vec<Type> = (0..n).map(|_| Type::Unif(self.fresh_var())).collect();
                        let mut t1_eta = t1.clone();
                        let mut t2_eta = t2.clone();
                        for v in &fresh_vars {
                            t1_eta = Type::app(t1_eta, v.clone());
                            t2_eta = Type::app(t2_eta, v.clone());
                        }
                        return self.unify(span, &t1_eta, &t2_eta);
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
                let partial_arrow = Type::app(Type::Con(WELL_KNOWN.arrow), (**a).clone());
                self.unify(span, &partial_arrow, f)?;
                self.unify(span, b, arg)
            }
            (Type::App(f, arg), Type::Fun(a, b)) => {
                let partial_arrow = Type::app(Type::Con(WELL_KNOWN.arrow), (**a).clone());
                self.unify(span, f, &partial_arrow)?;
                self.unify(span, arg, b)
            }

            // Type application
            (Type::App(_, _), Type::App(_, _)) => {
                // Collect full App spines to compare at the correct granularity.
                let (head1, args1) = collect_app_spine(&t1);
                let (head2, args2) = collect_app_spine(&t2);

                // When both heads are the same Con and arg counts match, unify args
                // directly without creating intermediate App sub-expressions. This
                // prevents spurious alias expansion when a name is both a type alias
                // (N params) and a data type (M params, M > N): structural decomposition
                // of the M-arg chain would create an N-arg sub-expression that looks
                // like the alias and triggers infinite re-expansion.
                if let (Type::Con(a), Type::Con(b)) = (head1, head2) {
                    if a.name == b.name && args1.len() == args2.len() {
                        for (a1, a2) in args1.iter().zip(args2.iter()) {
                            self.unify(span, a1, a2)?;
                        }
                        return Ok(());
                    }
                }

                // When spine lengths differ, one side may be an alias that needs
                // expanding before structural decomposition can match.
                if args1.len() != args2.len() {
                    let t1_is_alias = self.is_alias_app_non_self_referential(&t1);
                    let t2_is_alias = self.is_alias_app_non_self_referential(&t2);
                    if t1_is_alias || t2_is_alias {
                        let t1_exp = if t1_is_alias { self.try_expand_alias(t1.clone()) } else { t1.clone() };
                        let t2_exp = if t2_is_alias { self.try_expand_alias(t2.clone()) } else { t2.clone() };
                        if t1_exp != t1 || t2_exp != t2 {
                            return self.unify(span, &t1_exp, &t2_exp);
                        }
                    }
                }

                // Default: pairwise structural decomposition
                if let (Type::App(f1, a1), Type::App(f2, a2)) = (&t1, &t2) {
                    self.unify(span, f1, f2)?;
                    self.unify(span, a1, a2)
                } else {
                    unreachable!()
                }
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
                matches!(f.as_ref(), Type::Con(sym) if *sym == WELL_KNOWN.record)
            } => {
                let empty: Vec<(Symbol, Type)> = vec![];
                self.unify_records(span, &empty, &Some(Box::new((**row).clone())), fields2, tail2, &t1, &t2)
            }
            (Type::Record(fields1, tail1), Type::App(f, row)) if {
                matches!(f.as_ref(), Type::Con(sym) if *sym == WELL_KNOWN.record)
            } => {
                let empty: Vec<(Symbol, Type)> = vec![];
                self.unify_records(span, fields1, tail1, &empty, &Some(Box::new((**row).clone())), &t1, &t2)
            }

            // App(f, a) vs Record — when f is not Con("Record") (e.g. a unif var),
            // convert the Record to App(Con("Record"), row) and unify structurally.
            // This handles `g row` matching `{ fields }` by solving g = Record.
            (Type::App(f, a), Type::Record(fields, tail)) => {
                let record_con = Type::Con(WELL_KNOWN.record);
                self.unify(span, f, &record_con)?;
                let row = Type::Record(fields.clone(), tail.clone());
                self.unify(span, a, &row)
            }
            (Type::Record(fields, tail), Type::App(f, a)) => {
                let record_con = Type::Con(WELL_KNOWN.record);
                self.unify(span, f, &record_con)?;
                let row = Type::Record(fields.clone(), tail.clone());
                self.unify(span, a, &row)
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
                // Try eta-expanding partially applied type aliases.
                // e.g., `Tree` (alias `type Tree a = Cofree Array a`) vs `Cofree Array`:
                // apply a fresh var to both → `Tree ?v` vs `(Cofree Array) ?v`,
                // then expand Tree → `(Cofree Array) ?v` — now they match.
                let missing1 = self.partially_applied_alias_missing(&t1);
                let missing2 = self.partially_applied_alias_missing(&t2);
                let n = missing1.max(missing2);
                if n > 0 {
                    let fresh_vars: Vec<Type> = (0..n).map(|_| Type::Unif(self.fresh_var())).collect();
                    let mut t1_eta = t1.clone();
                    let mut t2_eta = t2.clone();
                    for v in &fresh_vars {
                        t1_eta = Type::app(t1_eta, v.clone());
                        t2_eta = Type::app(t2_eta, v.clone());
                    }
                    return self.unify(span, &t1_eta, &t2_eta);
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
                    return Err(TypeError::RecordLabelMismatch {
                        span,
                        missing: only_in_1.iter().map(|(l, _)| *l).collect(),
                        extra: only_in_2.iter().map(|(l, _)| *l).collect(),
                        expected: t1.clone(),
                        found: t2.clone(),
                    });
                }
                Ok(())
            }
            (Some(tail1), None) => {
                if !only_in_1.is_empty() {
                    return Err(TypeError::RecordLabelMismatch {
                        span,
                        missing: only_in_1.iter().map(|(l, _)| *l).collect(),
                        extra: vec![],
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
                    return Err(TypeError::RecordLabelMismatch {
                        span,
                        missing: vec![],
                        extra: only_in_2.iter().map(|(l, _)| *l).collect(),
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

    /// Pre-compute which aliases are transitively self-referential.
    /// An alias is self-referential if fully expanding its body (including inner aliases)
    /// produces a type that still contains `Con(alias_name)`.
    /// For example: `type Codec a = Codec' (Except DecodeError) JSON a` where
    /// `type Codec' m a b = Codec m a a b b` — expanding Codec produces a type
    /// containing the data type `Codec`.
    /// Must be called after all type aliases are registered.
    pub fn compute_self_referential_aliases(&mut self) {
        let alias_names: Vec<Symbol> = self.type_aliases.keys().cloned().collect();
        let alias_name_set: HashSet<Symbol> = alias_names.iter().cloned().collect();
        for name in alias_names {
            // Skip aliases already known to be self-referential (imported from other modules).
            if self.self_referential_aliases.contains(&name) {
                continue;
            }
            let (params, body) = self.type_aliases[&name].clone();
            // Quick pre-filter: if the alias body doesn't reference any alias name,
            // it cannot be self-referential (even transitively).
            if !type_references_any_name(&body, &alias_name_set) {
                continue;
            }
            let param_count = params.len();
            // Build a fully-applied type: App(...App(Con(name), Var(p1)), ..., Var(pN))
            let mut ty = Type::Con(QualifiedIdent { module: None, name });
            for p in &params {
                ty = Type::app(ty, Type::Var(*p));
            }
            // Expand it (try_expand_alias handles cycles via expanding_aliases)
            let expanded = self.try_expand_alias(ty);
            // Check if the expanded form contains Con(name) applied to exactly
            // param_count args (i.e., a usage that would trigger re-expansion).
            // This is arity-aware: if an alias `Codec` (1 param) expands to a body
            // containing `Con("Codec")` with 5 args (the data type), that's NOT
            // self-referential because 5 != 1.
            if contains_self_referential_usage(&expanded, name, param_count) {
                self.self_referential_aliases.insert(name);
            }
        }
    }

    /// Like `is_alias_app`, but also rejects "self-referential" aliases whose
    /// fully-expanded body contains the same Con name. These cause infinite
    /// re-expansion loops when the App-App unification case recursively
    /// discovers partially-applied fragments of the expanded type.
    fn is_alias_app_non_self_referential(&self, ty: &Type) -> bool {
        if self.type_aliases.is_empty() {
            return false;
        }
        let mut head = ty;
        let mut arg_count = 0usize;
        loop {
            match head {
                Type::App(f, _) => {
                    arg_count += 1;
                    head = f.as_ref();
                }
                Type::Con(name) => {
                    let alias_key = if let Some(module) = name.module {
                        let mod_str = crate::interner::resolve(module).unwrap_or_default();
                        let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                        crate::interner::intern(&format!("{}.{}", mod_str, name_str))
                    } else {
                        name.name
                    };
                    // Check self-referential using the proper alias key (qualified when
                    // available) to avoid false positives: "AskForReview.Model" should NOT
                    // be blocked just because a different "Model" alias is self-referential.
                    if self.self_referential_aliases.contains(&alias_key) {
                        return false;
                    }
                    if let Some((params, _)) = self.type_aliases.get(&alias_key) {
                        return params.len() == arg_count;
                    }
                    // Try canonical → import-alias mapping (e.g. "Components.AskForReview.Model"
                    // → "AskForReview.Model") before falling back to unqualified.
                    if let Some(module) = name.module {
                        if let Some(&alias_mod) = self.canonical_to_qualifier.get(&module) {
                            let alias_mod_str = crate::interner::resolve(alias_mod).unwrap_or_default();
                            let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                            let import_key = crate::interner::intern(&format!("{}.{}", alias_mod_str, name_str));
                            if self.self_referential_aliases.contains(&import_key) {
                                return false;
                            }
                            if let Some((params, _)) = self.type_aliases.get(&import_key) {
                                return params.len() == arg_count;
                            }
                        }
                    }
                    // Do NOT fall back to unqualified — the existing try_expand_alias
                    // unqualified fallback handles that with proper cycle guards.
                    return false;
                }
                _ => return false,
            }
        }
    }

    /// How many extra args does a partially-applied alias need to become saturated?
    /// Returns 0 if the type isn't headed by a known alias, or if already saturated.
    fn partially_applied_alias_missing(&self, ty: &Type) -> usize {
        let mut head = ty;
        let mut applied = 0usize;
        loop {
            match head {
                Type::App(f, _) => {
                    applied += 1;
                    head = f.as_ref();
                }
                _ => break,
            }
        }
        if let Type::Con(name) = head {
            let alias_key = if let Some(module) = name.module {
                let mod_str = crate::interner::resolve(module).unwrap_or_default();
                let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                crate::interner::intern(&format!("{}.{}", mod_str, name_str))
            } else {
                name.name
            };
            if self.self_referential_aliases.contains(&alias_key) {
                return 0;
            }
            if let Some((params, _)) = self.type_aliases.get(&alias_key) {
                if params.len() > applied {
                    return params.len() - applied;
                }
                return 0;
            }
            // Try canonical → import-alias mapping
            if let Some(module) = name.module {
                if let Some(&alias_mod) = self.canonical_to_qualifier.get(&module) {
                    let alias_mod_str = crate::interner::resolve(alias_mod).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let import_key = crate::interner::intern(&format!("{}.{}", alias_mod_str, name_str));
                    if self.self_referential_aliases.contains(&import_key) {
                        return 0;
                    }
                    if let Some((params, _)) = self.type_aliases.get(&import_key) {
                        if params.len() > applied {
                            return params.len() - applied;
                        }
                        return 0;
                    }
                }
            }
        }
        0
    }

    fn try_expand_alias(&mut self, ty: Type) -> Type {
        if self.type_aliases.is_empty() {
            return ty;
        }
        super::check_deadline();
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
            // Compute the actual alias lookup key — use qualified form when module
            // qualifier is present, to distinguish e.g. local `Tree` from imported `Y.Tree`.
            let alias_key = if let Some(module) = name.module {
                let mod_str = crate::interner::resolve(module).unwrap_or_default();
                let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                crate::interner::intern(&format!("{}.{}", mod_str, name_str))
            } else {
                name.name
            };
            // Guard against infinite alias expansion (e.g. `type Number = P.Number`
            // where P.Number resolves back to Con("Number"))
            if self.expanding_aliases.contains(&alias_key) {
                return ty;
            }
            // For qualified keys, if the exact qualified form isn't found, fall back
            // to the unqualified name. This handles cross-module canonicalization where
            // module A canonicalizes Con("Model") to Con("AdminDashboard.Model.Model"),
            // but module B (which inherits the qualified form) doesn't have the alias
            // under the qualified key — only under the unqualified "Model" key.
            // When falling back, also check the unqualified name in expanding_aliases
            // to prevent cycles (e.g. `type Number = P.Number` where P.Number falls
            // back to unqualified "Number").
            let (actual_alias_key, alias_entry) = if let Some(entry) = self.type_aliases.get(&alias_key).cloned() {
                (alias_key, Some(entry))
            } else if let Some(module) = name.module {
                // Try mapping canonical module path → import-alias-qualified key.
                // E.g. "Components.AskForReview.Model" → "AskForReview.Model" when
                // `import Components.AskForReview as AskForReview`.
                let import_alias_result = self.canonical_to_qualifier.get(&module).and_then(|&alias_mod| {
                    let alias_mod_str = crate::interner::resolve(alias_mod).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    let import_key = crate::interner::intern(&format!("{}.{}", alias_mod_str, name_str));
                    if self.expanding_aliases.contains(&import_key) {
                        return None;
                    }
                    self.type_aliases.get(&import_key).cloned().map(|entry| (import_key, entry))
                });
                if let Some((key, entry)) = import_alias_result {
                    (key, Some(entry))
                } else if self.canonical_to_qualifier.contains_key(&module) {
                    // Module is known (in canonical_to_qualifier) but alias not found
                    // under the import-qualified key. This type was explicitly qualified
                    // (e.g. canonicalized to avoid local alias collision). Don't fall
                    // back to unqualified — that would incorrectly expand a data type
                    // constructor using a local alias of the same name.
                    (alias_key, None)
                } else if name.module.is_some() {
                    // The Con has a module qualifier but neither the exact qualified key
                    // nor any import-alias-qualified key matched an alias. The module isn't
                    // in canonical_to_qualifier either. This means the type comes from a
                    // module we don't have a direct import relationship with (e.g., it
                    // appeared in an imported type scheme). Don't fall back to unqualified —
                    // that would incorrectly expand a foreign data type (like
                    // `GraphQL.Client.Types.Client`) using a local alias of the same name.
                    (alias_key, None)
                } else {
                    // Unqualified Con: check cycle guard then try alias expansion
                    if self.expanding_aliases.contains(&name.name) {
                        return ty;
                    }
                    if let Some(entry) = self.type_aliases.get(&name.name).cloned() {
                        (name.name, Some(entry))
                    } else {
                        (alias_key, None)
                    }
                }
            } else {
                (alias_key, None)
            };
            if let Some((params, body)) = alias_entry {
                // Args collected in reverse order (outermost last)
                args.reverse();
                if args.len() >= params.len() {
                    // Over-saturated expansion: block when the name also exists as a
                    // data type and arg count fits the data type arity (alias/data-type
                    // name collision, e.g. `type Codec a = ...` vs `data Codec m i o a b`).
                    if args.len() > params.len() {
                        if self.self_referential_aliases.contains(&actual_alias_key) {
                            return ty;
                        }
                    }
                    // Expand alias body with the first params.len() args, then apply remaining
                    let subst: std::collections::HashMap<crate::interner::Symbol, Type> = params
                        .iter()
                        .zip(args.iter())
                        .map(|(&p, &a)| (p, a.clone()))
                        .collect();
                    let mut expanded = self.apply_symbol_subst(&subst, &body);
                    // Apply remaining over-saturated args
                    for extra_arg in &args[params.len()..] {
                        expanded = Type::App(Box::new(expanded), Box::new((*extra_arg).clone()));
                    }
                    self.expanding_aliases.push(actual_alias_key);
                    // Also guard the original canonical key and unqualified name
                    // to prevent re-entry when the body re-introduces either form.
                    let guard_canonical = alias_key != actual_alias_key;
                    if guard_canonical {
                        self.expanding_aliases.push(alias_key);
                    }
                    // Guard unqualified name too to prevent cross-module expansion
                    // of a different alias with the same unqualified name.
                    let guard_unqual = name.module.is_some() && name.name != actual_alias_key && name.name != alias_key;
                    if guard_unqual {
                        self.expanding_aliases.push(name.name);
                    }
                    // Recursively expand nested aliases in the result
                    let result = self.try_expand_alias(expanded);
                    if guard_unqual {
                        self.expanding_aliases.pop();
                    }
                    if guard_canonical {
                        self.expanding_aliases.pop();
                    }
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
                // Also conservatively rename when substitution values contain unification
                // variables, since those may later be solved to types containing the
                // forall-bound var names, causing capture.
                let mut new_vars = vars.clone();
                let any_subst_has_unif = inner_subst.values().any(|val| contains_unif_var(val));
                let needs_rename = any_subst_has_unif || new_vars.iter().any(|(v, _)| {
                    inner_subst.values().any(|val| type_has_free_var(val, *v))
                });
                if needs_rename {
                    use std::collections::HashMap;
                    let mut rename: HashMap<Symbol, Type> = HashMap::new();
                    for (v, _) in &mut new_vars {
                        if any_subst_has_unif || inner_subst.values().any(|val| type_has_free_var(val, *v)) {
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
                // Guard against stale TyVarIds from another module's UnifyState
                if (v.0 as usize) >= self.entries.len() {
                    return;
                }
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

/// Check if a type contains any unification variables (unsolved or solved).
pub fn contains_unif_var(ty: &Type) -> bool {
    match ty {
        Type::Unif(_) => true,
        Type::Fun(a, b) => contains_unif_var(a) || contains_unif_var(b),
        Type::App(f, a) => contains_unif_var(f) || contains_unif_var(a),
        Type::Forall(_, body) => contains_unif_var(body),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| contains_unif_var(t))
                || tail.as_ref().map_or(false, |t| contains_unif_var(t))
        }
        Type::Var(_) | Type::Con(_) | Type::TypeString(_) | Type::TypeInt(_) => false,
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
