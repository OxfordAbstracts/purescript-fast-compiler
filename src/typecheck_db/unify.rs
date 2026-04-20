//! Union-find unification over [`Type`].
//!
//! Scoped per inference run — there is no module-global state, which is the
//! whole point of the per-decl cache design. `UnifyState` allocates fresh
//! variables, records their solved bindings, and provides `zonk` to read
//! the fully-resolved form of a type.

use std::collections::HashSet;

use thiserror::Error;

use crate::typecheck_db::types::{Constraint, Type};

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum UnifyError {
    #[error("cannot unify {0} with {1}")]
    Mismatch(Type, Type),
    #[error("infinite type: ?{var} occurs in {ty}")]
    Infinite { var: u32, ty: Type },
}

pub struct UnifyState {
    // bindings[i] = Some(ty) when ?i is solved, None when fresh.
    bindings: Vec<Option<Type>>,
    // Deferred diagnostics: case expressions / multi-equation groups
    // encountered during inference that need their scrutinee types
    // zonked before exhaustiveness can be decided. The caller
    // (`infer_value_scc_with_registries`) drains this after the SCC
    // finishes and passes each record to the exhaustiveness pass.
    //
    // Lives on UnifyState rather than on a separate context so the
    // call-chain through infer_* doesn't grow a new parameter. When
    // the constraint solver lands it'll likely motivate a richer
    // `InferCtx` wrapper, but until then this is a single-file
    // change and crucially doesn't touch any existing test.
    pending_exhaust:
        Vec<crate::typecheck_db::passes::infer_value::PendingExhaust>,
    // Constraint collection counterpart to `pending_exhaust`: every
    // time `infer_var` peels a `Type::Constrained` off a freshly-
    // instantiated scheme, the leftover constraint lands here and is
    // drained by the SCC driver into the matching `InferredScheme`.
    pending_constraints:
        Vec<crate::typecheck_db::passes::constraints::PendingConstraint>,
    // Name of the decl currently being inferred; read by
    // `record_pending_exhaust` so each entry is attributed to the
    // right decl, routed into the matching `InferredScheme`.
    current_decl: Option<String>,
}

impl UnifyState {
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
            pending_exhaust: Vec::new(),
            pending_constraints: Vec::new(),
            current_decl: None,
        }
    }

    /// Push one pending constraint, stamping it with the current decl
    /// name so the draining caller can route it to the right
    /// `InferredScheme`.
    pub fn record_pending_constraint(
        &mut self,
        mut entry: crate::typecheck_db::passes::constraints::PendingConstraint,
    ) {
        entry.decl_name = self.current_decl.clone();
        self.pending_constraints.push(entry);
    }

    /// Drain every recorded pending constraint.
    pub fn take_pending_constraints(
        &mut self,
    ) -> Vec<crate::typecheck_db::passes::constraints::PendingConstraint> {
        std::mem::take(&mut self.pending_constraints)
    }

    /// Capture the current union-find bindings so a later
    /// `restore_bindings` call can undo every unification performed
    /// between the two points. Used by the instance-match trial
    /// loop to reject a candidate without leaking partial bindings
    /// into the outer state.
    pub fn snapshot_bindings(&self) -> Vec<Option<Type>> {
        self.bindings.clone()
    }

    /// Restore bindings previously captured via `snapshot_bindings`.
    /// Safe only when the caller has kept the snapshot's lifetime
    /// scoped to a single unification attempt.
    pub fn restore_bindings(&mut self, snapshot: Vec<Option<Type>>) {
        self.bindings = snapshot;
    }

    /// Scope-bind the "currently inferring" decl name. Used by
    /// `record_pending_exhaust` to stamp each entry with its owning
    /// decl so downstream drains can route results correctly.
    pub fn set_current_decl(&mut self, name: Option<String>) {
        self.current_decl = name;
    }

    /// The decl name last set via `set_current_decl`, or `None`.
    pub fn current_decl(&self) -> Option<&str> {
        self.current_decl.as_deref()
    }

    /// Record one case / multi-equation group for post-inference
    /// exhaustiveness analysis. `scrutinee_tys` may still contain
    /// unification variables at the time of the call; the caller is
    /// expected to zonk before running the check.
    ///
    /// The entry's `decl_name` is overwritten with the currently-set
    /// decl name so attribution stays consistent regardless of what
    /// the caller passes.
    pub fn record_pending_exhaust(
        &mut self,
        mut entry: crate::typecheck_db::passes::infer_value::PendingExhaust,
    ) {
        entry.decl_name = self.current_decl.clone();
        self.pending_exhaust.push(entry);
    }

    /// Drain and return every pending exhaustiveness record.
    pub fn take_pending_exhaust(
        &mut self,
    ) -> Vec<crate::typecheck_db::passes::infer_value::PendingExhaust> {
        std::mem::take(&mut self.pending_exhaust)
    }

    /// Allocate a fresh unification variable.
    pub fn fresh(&mut self) -> Type {
        let id = self.bindings.len() as u32;
        self.bindings.push(None);
        Type::Unif(id)
    }

    /// Return the currently-bound type for `id`, if any.
    pub fn probe(&self, id: u32) -> Option<&Type> {
        self.bindings.get(id as usize).and_then(|o| o.as_ref())
    }

    fn assign(&mut self, id: u32, ty: Type) {
        // Grow the bindings vec if `id` is out of range. This
        // happens when a cached scheme carries a `Type::Unif(old_id)`
        // from a previous `UnifyState`; `instantiate` usually
        // rewrites those, but we keep this safety net so any
        // remaining stray id is bound cleanly instead of panicking.
        let slot = id as usize;
        if slot >= self.bindings.len() {
            self.bindings.resize(slot + 1, None);
        }
        self.bindings[slot] = Some(ty);
    }

    /// Fully resolve a type by following bindings. Idempotent.
    pub fn zonk(&self, ty: &Type) -> Type {
        match ty {
            Type::Unif(id) => match self.probe(*id) {
                Some(bound) => self.zonk(&bound.clone()),
                None => ty.clone(),
            },
            Type::App(f, a) => Type::app(self.zonk(f), self.zonk(a)),
            Type::Fun(a, b) => Type::Fun(Box::new(self.zonk(a)), Box::new(self.zonk(b))),
            Type::Forall(vars, body) => {
                let vars = vars
                    .iter()
                    .map(|(n, v, k)| (n.clone(), *v, k.as_ref().map(|k| Box::new(self.zonk(k)))))
                    .collect();
                Type::Forall(vars, Box::new(self.zonk(body)))
            }
            Type::Constrained(cs, body) => {
                let cs = cs
                    .iter()
                    .map(|c| Constraint {
                        class: c.class.clone(),
                        args: c.args.iter().map(|a| self.zonk(a)).collect(),
                    })
                    .collect();
                Type::Constrained(cs, Box::new(self.zonk(body)))
            }
            Type::Record(fields, tail) => {
                let fs = fields.iter().map(|(l, t)| (l.clone(), self.zonk(t))).collect();
                let t = tail.as_ref().map(|t| Box::new(self.zonk(t)));
                Type::Record(fs, t)
            }
            Type::Row(fields, tail) => {
                let fs = fields.iter().map(|(l, t)| (l.clone(), self.zonk(t))).collect();
                let t = tail.as_ref().map(|t| Box::new(self.zonk(t)));
                Type::Row(fs, t)
            }
            Type::Kinded(t, k) => {
                Type::Kinded(Box::new(self.zonk(t)), Box::new(self.zonk(k)))
            }
            _ => ty.clone(),
        }
    }

    /// Unify two types, updating `self` with any new bindings.
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), UnifyError> {
        let a = self.zonk(a);
        let b = self.zonk(b);
        self.unify_inner(&a, &b)
    }

    fn unify_inner(&mut self, a: &Type, b: &Type) -> Result<(), UnifyError> {
        match (a, b) {
            (Type::Unif(i), Type::Unif(j)) if i == j => Ok(()),
            (Type::Unif(id), other) | (other, Type::Unif(id)) => self.bind_var(*id, other),
            (Type::Var(n1), Type::Var(n2)) if n1 == n2 => Ok(()),
            (Type::Con(c1), Type::Con(c2)) if c1 == c2 => Ok(()),
            (Type::App(f1, a1), Type::App(f2, a2)) => {
                self.unify(f1, f2)?;
                self.unify(a1, a2)
            }
            (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
                self.unify(a1, a2)?;
                self.unify(b1, b2)
            }
            // `Fun(a, b) ↔ App(App(α, x), y)` where α is an unif var
            // arises when a class method like `identity :: forall a t.
            // Category a => a t t` gets instantiated inside a body
            // that expects a function type. The `Category (->)`
            // instance will eventually pin `α = Con("->")` so the
            // heads align, but the unifier sees the raw shapes first.
            // Equate them proactively: bind `α = Con("->")` and
            // unify the spine pairwise. `Type::app` then rewrites any
            // concrete `App(App(Con("->"), _), _)` back into `Fun`.
            (Type::Fun(fa, fb), Type::App(outer_f, outer_a))
            | (Type::App(outer_f, outer_a), Type::Fun(fa, fb)) => {
                // Two-arg form: `App(App(head, x), y) ↔ Fun(a, b)`.
                // Head must be `Con("->")` (or a unif var that we
                // bind to `Con("->")`); then the spine unifies
                // pairwise.
                if let Type::App(inner_f, inner_a) = outer_f.as_ref() {
                    let head_ok = match inner_f.as_ref() {
                        Type::Unif(_) => {
                            self.unify(
                                inner_f,
                                &Type::Con(
                                    crate::typecheck_db::types::QName::unqualified("->"),
                                ),
                            )?;
                            true
                        }
                        Type::Con(qn) if qn.name == "->" || qn.name == "Function" => true,
                        _ => false,
                    };
                    if head_ok {
                        self.unify(fa, inner_a)?;
                        return self.unify(fb, outer_a);
                    }
                }
                // One-arg form: `App(α, x) ↔ Fun(a, b)`. The only
                // way this can hold is `α = App(Con("->"), a)` and
                // `x = b`. Arises when class methods like
                // `identity :: forall a t. Category a => a t t`
                // get instantiated in positions expecting a
                // function type — the constructor half of the
                // arrow stays folded inside the head unif until
                // the solver discharges `Category a` with `->`.
                if let Type::Unif(_) = outer_f.as_ref() {
                    let arrow =
                        Type::Con(crate::typecheck_db::types::QName::unqualified("->"));
                    self.unify(
                        outer_f,
                        &Type::App(Box::new(arrow), Box::new((**fa).clone())),
                    )?;
                    return self.unify(outer_a, fb);
                }
                Err(UnifyError::Mismatch(a.clone(), b.clone()))
            }
            (Type::TypeString(s1), Type::TypeString(s2)) if s1 == s2 => Ok(()),
            (Type::TypeInt(n1), Type::TypeInt(n2)) if n1 == n2 => Ok(()),
            // Forall-vs-Forall: accept the simplest case where
            // both sides quantify over the same number of vars
            // and the bodies unify after alpha-renaming one
            // side's vars to match the other's. Avoids spurious
            // mismatches when the same polymorphic type appears
            // on both sides of an annotation (e.g. declaring
            // `x :: forall a. Array a` and using `x` at a call
            // site that also expects `forall a. Array a`).
            (Type::Forall(vs1, body1), Type::Forall(vs2, body2)) if vs1.len() == vs2.len() => {
                let mut renamed = (**body1).clone();
                if vs1.iter().zip(vs2.iter()).any(|((n1, _, _), (n2, _, _))| n1 != n2) {
                    let mut subst: std::collections::HashMap<String, Type> =
                        std::collections::HashMap::new();
                    for ((n1, _, _), (n2, _, _)) in vs1.iter().zip(vs2.iter()) {
                        subst.insert(n1.clone(), Type::Var(n2.clone()));
                    }
                    renamed = crate::typecheck_db::generalize::apply_var_subst(&renamed, &subst);
                }
                self.unify(&renamed, body2)
            }
            (Type::Record(f1, t1), Type::Record(f2, t2)) => unify_fields(self, f1, t1, f2, t2),
            (Type::Row(f1, t1), Type::Row(f2, t2)) => unify_fields(self, f1, t1, f2, t2),
            // `Record r` (parsed as `App(Con("Record"), r)`) is
            // equivalent to `{ | r }` — an open record whose
            // tail is `r`. Unify as `Record([], Some(r))` so
            // call-site `{ a :: Int }` literal records align
            // with the kind-level `Record` constructor.
            (Type::App(f, row), Type::Record(fields, tail))
            | (Type::Record(fields, tail), Type::App(f, row))
                if matches!(f.as_ref(), Type::Con(qn) if qn.name == "Record") =>
            {
                let empty: Vec<(String, Type)> = Vec::new();
                let tail_box: Option<Box<Type>> = Some(Box::new((**row).clone()));
                // Canonical order: `Record` side as the first arg
                // keeps diagnostic messages consistent.
                unify_fields(self, &empty, &tail_box, fields, tail)
            }
            (Type::Kinded(t, _), other) | (other, Type::Kinded(t, _)) => self.unify(t, other),
            (Type::Wildcard, _) | (_, Type::Wildcard) => Ok(()),
            _ => Err(UnifyError::Mismatch(a.clone(), b.clone())),
        }
    }

    fn bind_var(&mut self, id: u32, other: &Type) -> Result<(), UnifyError> {
        if let Type::Unif(j) = other {
            if *j == id {
                return Ok(());
            }
        }
        if occurs_in(id, other) {
            return Err(UnifyError::Infinite { var: id, ty: other.clone() });
        }
        self.assign(id, other.clone());
        Ok(())
    }

    /// Collect every unsolved unification variable reachable in `ty`.
    pub fn free_unif_vars(&self, ty: &Type) -> HashSet<u32> {
        let mut out = HashSet::new();
        collect_free(&self.zonk(ty), &mut out);
        out
    }
}

impl Default for UnifyState {
    fn default() -> Self {
        Self::new()
    }
}

/// Row / record unification with open tails.
///
/// Given two record (or row) types `{ f1 | t1 }` and `{ f2 | t2 }`:
///
/// 1. For every label present in both: unify the two field types.
/// 2. Labels only on one side must be absorbed by the other side's tail.
///    A closed tail (`None`) can't absorb extras — that's a mismatch. An
///    open tail (`Some(_)`) gets unified with a synthesized row fragment
///    carrying the missing labels.
/// 3. When both sides have unique labels, a fresh common tail mediates:
///    each side's tail is solved to the other side's unique labels plus
///    the fresh tail.
fn unify_fields(
    state: &mut UnifyState,
    f1: &[(String, Type)],
    t1: &Option<Box<Type>>,
    f2: &[(String, Type)],
    t2: &Option<Box<Type>>,
) -> Result<(), UnifyError> {
    use std::collections::HashMap;

    let m1: HashMap<&str, &Type> = f1.iter().map(|(l, t)| (l.as_str(), t)).collect();
    let m2: HashMap<&str, &Type> = f2.iter().map(|(l, t)| (l.as_str(), t)).collect();

    // Step 1: unify common labels.
    for (l, t1v) in &m1 {
        if let Some(t2v) = m2.get(l) {
            state.unify(t1v, t2v)?;
        }
    }

    let only1: Vec<(String, Type)> = f1
        .iter()
        .filter(|(l, _)| !m2.contains_key(l.as_str()))
        .cloned()
        .collect();
    let only2: Vec<(String, Type)> = f2
        .iter()
        .filter(|(l, _)| !m1.contains_key(l.as_str()))
        .cloned()
        .collect();

    match (only1.is_empty(), only2.is_empty()) {
        (true, true) => unify_opt_tails(state, t1, t2),
        (false, true) => absorb_extras(state, t2, only1, t1.clone()),
        (true, false) => absorb_extras(state, t1, only2, t2.clone()),
        (false, false) => {
            let fresh = state.fresh();
            absorb_extras(state, t1, only2, Some(Box::new(fresh.clone())))?;
            absorb_extras(state, t2, only1, Some(Box::new(fresh)))
        }
    }
}

fn unify_opt_tails(
    state: &mut UnifyState,
    t1: &Option<Box<Type>>,
    t2: &Option<Box<Type>>,
) -> Result<(), UnifyError> {
    match (t1, t2) {
        (None, None) => Ok(()),
        (Some(a), Some(b)) => state.unify(a, b),
        // Closed vs open: the open tail must resolve to the empty
        // closed row.
        (Some(t), None) | (None, Some(t)) => state.unify(t, &Type::Record(vec![], None)),
    }
}

/// `t` must end up containing exactly `extras`, with `rest` as its own
/// (possibly open) tail. If `t` is closed, it can only match if there
/// are no extras and `rest` is also closed.
fn absorb_extras(
    state: &mut UnifyState,
    t: &Option<Box<Type>>,
    extras: Vec<(String, Type)>,
    rest: Option<Box<Type>>,
) -> Result<(), UnifyError> {
    match t {
        Some(tail) => state.unify(tail, &Type::Record(extras, rest)),
        None => {
            if !extras.is_empty() {
                return Err(UnifyError::Mismatch(
                    Type::Record(vec![], None),
                    Type::Record(extras, rest),
                ));
            }
            match rest {
                None => Ok(()),
                Some(r) => state.unify(&r, &Type::Record(vec![], None)),
            }
        }
    }
}

fn occurs_in(id: u32, ty: &Type) -> bool {
    match ty {
        Type::Unif(j) => *j == id,
        Type::App(f, a) => occurs_in(id, f) || occurs_in(id, a),
        Type::Fun(a, b) => occurs_in(id, a) || occurs_in(id, b),
        Type::Forall(_, body) => occurs_in(id, body),
        Type::Constrained(cs, b) => {
            cs.iter().any(|c| c.args.iter().any(|a| occurs_in(id, a))) || occurs_in(id, b)
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            fs.iter().any(|(_, t)| occurs_in(id, t))
                || tail.as_ref().map_or(false, |t| occurs_in(id, t))
        }
        Type::Kinded(t, k) => occurs_in(id, t) || occurs_in(id, k),
        _ => false,
    }
}

fn collect_free(ty: &Type, out: &mut HashSet<u32>) {
    match ty {
        Type::Unif(id) => {
            out.insert(*id);
        }
        Type::App(f, a) => {
            collect_free(f, out);
            collect_free(a, out);
        }
        Type::Fun(a, b) => {
            collect_free(a, out);
            collect_free(b, out);
        }
        Type::Forall(_, body) => collect_free(body, out),
        Type::Constrained(cs, body) => {
            for c in cs {
                for a in &c.args {
                    collect_free(a, out);
                }
            }
            collect_free(body, out);
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            for (_, t) in fs {
                collect_free(t, out);
            }
            if let Some(t) = tail {
                collect_free(t, out);
            }
        }
        Type::Kinded(t, k) => {
            collect_free(t, out);
            collect_free(k, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typecheck_db::types::QName;

    fn int() -> Type {
        Type::Con(QName::unqualified("Int"))
    }

    fn bool_ty() -> Type {
        Type::Con(QName::unqualified("Boolean"))
    }

    #[test]
    fn fresh_vars_are_distinct() {
        let mut s = UnifyState::new();
        let a = s.fresh();
        let b = s.fresh();
        assert_ne!(a, b);
    }

    #[test]
    fn unify_con_with_same_con() {
        let mut s = UnifyState::new();
        s.unify(&int(), &int()).unwrap();
    }

    #[test]
    fn unify_unif_with_con_solves() {
        let mut s = UnifyState::new();
        let a = s.fresh();
        s.unify(&a, &int()).unwrap();
        assert_eq!(s.zonk(&a), int());
    }

    #[test]
    fn unify_two_unifs_links_then_solves() {
        let mut s = UnifyState::new();
        let a = s.fresh();
        let b = s.fresh();
        s.unify(&a, &b).unwrap();
        s.unify(&b, &int()).unwrap();
        assert_eq!(s.zonk(&a), int());
    }

    #[test]
    fn unify_different_con_fails() {
        let mut s = UnifyState::new();
        assert!(s.unify(&int(), &bool_ty()).is_err());
    }

    #[test]
    fn unify_function_types() {
        let mut s = UnifyState::new();
        let a = s.fresh();
        let b = s.fresh();
        s.unify(&Type::fun(a.clone(), b.clone()), &Type::fun(int(), bool_ty()))
            .unwrap();
        assert_eq!(s.zonk(&a), int());
        assert_eq!(s.zonk(&b), bool_ty());
    }

    #[test]
    fn occurs_check_rejects_infinite_type() {
        let mut s = UnifyState::new();
        let a = s.fresh();
        let inner = Type::fun(a.clone(), int());
        let err = s.unify(&a, &inner).unwrap_err();
        assert!(matches!(err, UnifyError::Infinite { .. }));
    }

    #[test]
    fn free_unif_vars_reports_unsolved() {
        let mut s = UnifyState::new();
        let a = s.fresh();
        let b = s.fresh();
        s.unify(&a, &int()).unwrap();
        let free = s.free_unif_vars(&Type::fun(a.clone(), b.clone()));
        // a is solved; b is still free.
        if let Type::Unif(id_b) = b {
            assert!(free.contains(&id_b));
            assert_eq!(free.len(), 1);
        } else {
            panic!();
        }
    }
}
