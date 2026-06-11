//! Inference environment: top-level schemes + local monomorphic bindings.
//!
//! `Env` is effectively a frozen snapshot used to infer one SCC of value
//! declarations. Its contents come from the SCC's dependency schemes
//! (cached outputs of `infer_value_scc` on earlier groups) and its own
//! decl-level locals introduced by lambdas / let / where bindings.

use std::collections::HashMap;
use std::sync::Arc;

use crate::typecheck_db::types::{AliasMap, QName, Scheme, Type};
use crate::typecheck_db::unify::UnifyState;

#[derive(Debug, Clone, Default)]
pub struct Env {
    /// The module this `Env` is checking. Used by the SCC inference
    /// to bind pre-insert slots under `QName::qualified(self_module,
    /// name)` so resolved self-references (e.g. `Some("M").fib`) hit
    /// the SCC's mono slot rather than the (possibly Hole-bearing)
    /// sig scheme. Empty string when not set (test-only `Env::new()`).
    pub self_module: String,
    /// Qualified top-level schemes (values, constructors, class methods).
    /// `Arc`-shared so the import path can bind a single scheme under
    /// multiple `QName` keys (qualifier + origin) with one
    /// `Arc::clone` per key instead of a deep `Scheme::clone`. Reads
    /// deref through to `&Scheme` so existing callers don't change.
    pub top_level: HashMap<QName, Arc<Scheme>>,
    /// Unqualified local bindings introduced by lambdas, case binders, etc.
    /// Monomorphic: lambda/pattern binders are not let-polymorphic.
    pub locals: Vec<HashMap<String, Type>>,
    /// Unqualified local **schemes** introduced by generalized `let`
    /// bindings. Walked in the same scope order as `locals`; a local scheme
    /// shadows a same-named top-level entry but is shadowed by a
    /// same-named monomorphic local.
    pub local_schemes: Vec<HashMap<String, Scheme>>,
    /// Type-alias map visible in this module's scope. Populated at
    /// module-check time (local `type Foo = …` decls + every
    /// imported module's exported aliases). Consumed by
    /// `convert_type_expr`-calling passes (type annotations,
    /// let-binding sigs, constructor fields) to expand aliases
    /// before unification — so `Foo Number` unifies with
    /// `Array Number` when `type Foo a = Array a`.
    pub aliases: AliasMap,
    /// Value decl names that have an explicit `Decl::TypeSignature`
    /// sibling in the current module. Populated by
    /// `bind_local_ctors`. Used by the value-SCC inference to
    /// decide whether to run bidirectional check-mode against the
    /// declared sig. Class methods and imported values aren't in
    /// this set even though their schemes appear in `top_level` —
    /// only user-declared top-level sigs opt into check-mode.
    pub local_signed: std::collections::HashSet<String>,
    /// Scoped type variables — outer-forall names that have been
    /// skolemised during check-mode. Consulted by
    /// `convert_type_expr` call sites (typed binders, let-sigs,
    /// inline `expr :: T` annotations) so a body reference to
    /// `a` in `\\(x :: a) -> …` resolves to the SAME skolem
    /// introduced for the enclosing `forall a.` on the decl's
    /// sig.
    pub scoped_tys: HashMap<String, Type>,
    /// Per-decl type-level hole sites collected from
    /// `Decl::TypeSignature`'s body. Each entry is `(span,
    /// hole_name)` in source order — `convert_type_expr` lowers
    /// `?test` to `Type::Hole(name)` (no span), so the SCC inference
    /// reads spans from here when emitting `HoleDiagnostic`s for
    /// type-level holes.
    pub local_signed_hole_sites:
        HashMap<String, Vec<(crate::span::Span, String)>>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            self_module: String::new(),
            top_level: HashMap::new(),
            locals: vec![HashMap::new()],
            local_schemes: vec![HashMap::new()],
            aliases: AliasMap::default(),
            local_signed: std::collections::HashSet::new(),
            scoped_tys: HashMap::new(),
            local_signed_hole_sites: HashMap::new(),
        }
    }

    pub fn bind_scheme(&mut self, name: QName, scheme: Scheme) {
        self.top_level.insert(name, Arc::new(scheme));
    }

    /// Like `bind_scheme` but accepts a pre-`Arc`-wrapped scheme so
    /// the import path can share a single allocation across the
    /// qualifier-keyed and origin-keyed bindings.
    pub fn bind_scheme_arc(&mut self, name: QName, scheme: Arc<Scheme>) {
        self.top_level.insert(name, scheme);
    }

    pub fn push_scope(&mut self) {
        self.locals.push(HashMap::new());
        self.local_schemes.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        self.locals.pop();
        self.local_schemes.pop();
        if self.locals.is_empty() {
            self.locals.push(HashMap::new());
        }
        if self.local_schemes.is_empty() {
            self.local_schemes.push(HashMap::new());
        }
    }

    pub fn bind_local(&mut self, name: impl Into<String>, ty: Type) {
        if let Some(top) = self.locals.last_mut() {
            top.insert(name.into(), ty);
        }
    }

    pub fn bind_local_scheme(&mut self, name: impl Into<String>, scheme: Scheme) {
        if let Some(top) = self.local_schemes.last_mut() {
            top.insert(name.into(), scheme);
        }
    }

    /// Look up an unqualified name. Walks scopes inner-to-outer, and
    /// at EACH scope checks both `locals` (monomorphic) and
    /// `local_schemes` (let-generalised) before moving to the
    /// outer scope. This is what lets a `let total = …` in an inner
    /// `do` properly shadow an outer `let { total, … } = …` even
    /// when `infer_let`'s Pass 4 has moved the inner binding from
    /// `locals` to `local_schemes` while the outer is still in
    /// `locals` — without per-scope interleaving, the outer
    /// `locals` would win and the shadowing leak (caught as
    /// Mismatch(Int, ToAddTotal) in DrStripeRefundAttendee-shape
    /// fixtures).
    pub fn lookup_unqualified(&self, name: &str) -> Lookup<'_> {
        // locals and local_schemes are always pushed/popped together
        // via push_scope / pop_scope, so they have the same length.
        // Defensive zip for the same-length invariant.
        let scope_iter = self
            .locals
            .iter()
            .rev()
            .zip(self.local_schemes.iter().rev());
        for (loc, sch) in scope_iter {
            if let Some(ty) = loc.get(name) {
                return Lookup::Local(ty);
            }
            if let Some(s) = sch.get(name) {
                return Lookup::Scheme(s);
            }
        }
        if let Some(s) = self
            .top_level
            .get(&QName { module: None, name: name.to_string() })
        {
            return Lookup::Scheme(s.as_ref());
        }
        Lookup::Missing
    }

    /// Look up a qualified name against the top-level scheme map.
    /// Falls back to the unqualified key when the module-qualified
    /// form isn't bound AND the unqualified scheme doesn't carry a
    /// `Type::Hole`. Hole-bearing sigs are deliberately left unbound
    /// under the qualified key so SCC-recursive references hit the
    /// `env.locals` mono slot via `infer_var`'s fallback path; if
    /// we fell back to None.name here, the hole-bearing sig would
    /// be picked up again and the body would unify against the
    /// Hole instead of the fresh unif.
    pub fn lookup_qualified(&self, q: &QName) -> Option<&Scheme> {
        if let Some(s) = self.top_level.get(q) {
            return Some(s.as_ref());
        }
        if q.module.is_some() {
            if let Some(s) = self
                .top_level
                .get(&QName { module: None, name: q.name.clone() })
            {
                if !crate::typecheck_db::types::type_contains_hole(&s.as_ref().ty) {
                    return Some(s.as_ref());
                }
            }
        }
        None
    }

    /// Every unification variable free in any local or top-level type.
    /// Used by `generalize` to avoid quantifying vars that appear in the
    /// surrounding env.
    pub fn free_unif_vars(&self, state: &UnifyState) -> std::collections::HashSet<u32> {
        let mut out = std::collections::HashSet::new();
        for scope in &self.locals {
            for ty in scope.values() {
                out.extend(state.free_unif_vars(ty));
            }
        }
        // Top-level schemes have already been generalized — their quantified
        // vars are `Type::Var`, and any residual Unif there would be a bug.
        // Still, conservatively fold them in.
        for scheme in self.top_level.values() {
            out.extend(state.free_unif_vars(&scheme.as_ref().ty));
        }
        // Same reasoning for local schemes.
        for scope in &self.local_schemes {
            for scheme in scope.values() {
                out.extend(state.free_unif_vars(&scheme.ty));
            }
        }
        out
    }
}

#[derive(Debug)]
pub enum Lookup<'a> {
    Scheme(&'a Scheme),
    Local(&'a Type),
    Missing,
}

impl<'a> Lookup<'a> {
    pub fn local_ty(&self) -> Option<&'a Type> {
        match self {
            Lookup::Local(t) => Some(*t),
            _ => None,
        }
    }
}
