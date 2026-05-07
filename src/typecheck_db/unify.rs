//! Union-find unification over [`Type`].
//!
//! Scoped per inference run — there is no module-global state, which is the
//! whole point of the per-decl cache design. `UnifyState` allocates fresh
//! variables, records their solved bindings, and provides `zonk` to read
//! the fully-resolved form of a type.

use std::collections::HashSet;

use thiserror::Error;

use crate::span::Span;
use crate::typecheck_db::types::{Constraint, Type};

/// True when the Forall body's outermost App head is a `Con` that
/// matches the other side's outermost App head. This lets us
/// distinguish the rank-N instantiation case (`forall r. ST r a` vs
/// `ST U1 U2` — both headed by `Con("ST")`) from the rank-2
/// violation case (`forall a. a -> a` vs `Number -> Number` — the
/// Forall body is `Fun(Var, Var)` while the other is `Fun(Con,
/// Con)`, and we must NOT let this unification succeed by
/// instantiating `a = Number`).
fn forall_head_matches(body: &Type, other: &Type) -> bool {
    fn app_head(ty: &Type) -> Option<&Type> {
        let mut cur = ty;
        loop {
            match cur {
                Type::App(f, _) => cur = f,
                _ => return Some(cur),
            }
        }
    }
    match (app_head(body), app_head(other)) {
        (Some(Type::Con(a)), Some(Type::Con(b))) => a == b,
        // The other side's head is a unification variable —
        // we don't know its identity yet, but instantiating the
        // Forall and recursing lets the unif bind to whatever
        // the Forall's body resolves to. Skolem-escape catches
        // rank-2 violations downstream.
        (Some(_), Some(Type::Unif(_))) => true,
        // Both sides have `Fun` heads AND the other side's leaf
        // positions are entirely unifs (no concrete `Con` or
        // `Var`). This handles the mutual-recursion / inferred-
        // lam_ty case where a polymorphic sig is being unified
        // against a freshly-inferred function body that hasn't
        // been pinned to anything concrete yet — instantiating
        // the Forall lets the unifs bind compatibly. Concrete-
        // headed `other` (like `Int -> Int`) keeps failing,
        // preserving rank-2 violation rejection.
        (Some(Type::Fun(_, _)), Some(Type::Fun(_, _)))
            if leaves_all_unif(other) =>
        {
            true
        }
        _ => false,
    }
}

/// True when every leaf type inside `ty` (walking through
/// `Fun`, `App`) is a `Type::Unif` — no concrete `Con`s, `Var`s,
/// or other heads. Used to gate Fun-Fun forall-head instantiation
/// to the safe "still polymorphic" case.
fn leaves_all_unif(ty: &Type) -> bool {
    match ty {
        Type::Unif(_) => true,
        Type::Fun(a, b) => leaves_all_unif(a) && leaves_all_unif(b),
        Type::App(f, a) => leaves_all_unif(f) && leaves_all_unif(a),
        _ => false,
    }
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum UnifyError {
    #[error("cannot unify {0} with {1}")]
    Mismatch(Type, Type),
    #[error("infinite type: ?{var} occurs in {ty}")]
    Infinite { var: u32, ty: Type },
    #[error("skolem !s{skolem} escapes its scope via ?{var}")]
    SkolemEscape { var: u32, skolem: u32, ty: Type },
}

/// `UnifyError` augmented with source-location info. Constructed at
/// the `infer_value.rs::?` boundary by `unify_here` reading the
/// state-tracked `current_unify_span` / `current_expected_span` /
/// `current_decl_span` / `current_decl`. The unifier's internal
/// recursion still produces span-free `UnifyError`s — they only get
/// located when they cross out of the unifier into the inference
/// layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocatedUnifyError {
    /// Where the offending expression lives (the "actual" side).
    pub primary: Option<Span>,
    /// Where the expected type came from (when known) — typically the
    /// callee's sig position, the case scrutinee, or the surrounding
    /// expression that supplied the expected type.
    pub expected_from: Option<Span>,
    /// Enclosing decl's name, mirror of `current_decl`.
    pub decl_name: Option<String>,
    /// Enclosing decl's source span.
    pub decl_span: Option<Span>,
    /// The original unifier error.
    pub kind: UnifyError,
}

impl std::fmt::Display for LocatedUnifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)?;
        if let Some(s) = &self.primary {
            write!(f, " at {:?}", s)?;
        }
        if let Some(s) = &self.expected_from {
            write!(f, " (expected from {:?})", s)?;
        }
        if let Some(name) = &self.decl_name {
            write!(f, " in decl `{}`", name)?;
        }
        Ok(())
    }
}

pub struct UnifyState {
    // bindings[i] = Some(ty) when ?i is solved, None when fresh.
    bindings: Vec<Option<Type>>,
    // Skolem ids are monotonically allocated from `next_skolem`.
    // Each unification variable records the skolem-counter value
    // AT ITS ALLOCATION TIME (`unif_skolem_levels[i]`): the unif
    // is only allowed to be bound to a type whose skolems all have
    // id `< unif_skolem_levels[i]`. A skolem with id `>= level[i]`
    // was introduced AFTER the unif existed and binding would leak
    // the skolem past its scope — caught as `SkolemEscape`.
    unif_skolem_levels: Vec<u32>,
    next_skolem: u32,
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
    // Typed-hole records. Same routing story as the other `pending_*`
    // vectors: stamped with `current_decl` on record, drained and
    // zonked at SCC end, routed into the matching `InferredScheme`.
    pending_holes:
        Vec<crate::typecheck_db::passes::infer_value::HoleDiagnostic>,
    // Name of the decl currently being inferred; read by
    // `record_pending_exhaust` so each entry is attributed to the
    // right decl, routed into the matching `InferredScheme`.
    current_decl: Option<String>,
    // Given-constraint stack. `check_equation` pushes constraints
    // peeled off the expected sig's outer `Constrained` layer
    // here; the solver consults this list BEFORE attempting
    // instance lookup. A pending constraint whose zonked shape
    // structurally matches any given is discharged as a local
    // hypothesis — this is what lets `composeFlipped` call
    // `compose` (which re-raises `Semigroupoid a =>`) inside a
    // check-mode sig body without tripping `NoInstanceFound`
    // against a skolem.
    //
    // Flat (not a stack-of-frames) because every push in
    // check-mode is accompanied by a scope that ends with
    // `clear_givens_to(snapshot_len)` on exit.
    givens: Vec<Constraint>,
    /// Maps skolem id → the `forall` var name it stood in for.
    /// Populated by `fresh_named_skolem` during check-mode
    /// skolemisation. Consumed by `deskolemise` when hole
    /// diagnostics need to present types in their source-level
    /// shape (the reference compiler reports holes with rigid
    /// `Var("r")`, not `!s0`).
    skolem_names: std::collections::HashMap<u32, String>,
    /// Recursion guard for `unify`. Set in the top-level call;
    /// any deeper call that would push past 1024 frames bails out
    /// with `Mismatch` rather than blow the stack.
    unify_depth: usize,
    /// Current "actual"-side source span. Set by callers (typically
    /// `infer_expr` / `check_expr`) at expression entry via the
    /// `with_unify_span` RAII helper, and read at error-construction
    /// time by `locate` to populate `LocatedUnifyError::primary`.
    current_unify_span: Option<Span>,
    /// Current "expected from" source span. Set by call sites that
    /// know where the expected type was sourced (the callee's func
    /// position, the case's first alt's body span, etc.) via
    /// `with_expected_span` for the duration of one unify call.
    /// Read at error-construction time to populate
    /// `LocatedUnifyError::expected_from`.
    current_expected_span: Option<Span>,
    /// Current decl's source span — parallel to `current_decl`.
    /// Set at the SCC loop entry alongside `set_current_decl` and
    /// read by `locate` for `LocatedUnifyError::decl_span`.
    current_decl_span: Option<Span>,
}

impl UnifyState {
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
            unif_skolem_levels: Vec::new(),
            next_skolem: 0,
            pending_exhaust: Vec::new(),
            pending_constraints: Vec::new(),
            pending_holes: Vec::new(),
            current_decl: None,
            givens: Vec::new(),
            skolem_names: std::collections::HashMap::new(),
            unify_depth: 0,
            current_unify_span: None,
            current_expected_span: None,
            current_decl_span: None,
        }
    }

    /// Allocate a fresh skolem AND record its source-level name.
    /// The name is later used by `deskolemise` to present hole
    /// diagnostics in the reference compiler's `Var("r")` style
    /// instead of the internal `!s0` notation.
    pub fn fresh_named_skolem(&mut self, name: &str) -> u32 {
        let id = self.fresh_skolem();
        self.skolem_names.insert(id, name.to_string());
        id
    }

    /// Replace every `Type::Skolem(id)` whose name was captured
    /// via `fresh_named_skolem` with `Type::Var(name)`. Used at
    /// hole drain time so the reference-compiler hole format
    /// (rigid `Var`) is preserved.
    pub fn deskolemise(&self, ty: &Type) -> Type {
        match ty {
            Type::Skolem(id) => match self.skolem_names.get(id) {
                Some(n) => Type::Var(n.clone()),
                None => Type::Skolem(*id),
            },
            Type::App(f, a) => Type::app(self.deskolemise(f), self.deskolemise(a)),
            Type::Fun(a, b) => Type::fun(self.deskolemise(a), self.deskolemise(b)),
            Type::Forall(vs, body) => {
                Type::Forall(vs.clone(), Box::new(self.deskolemise(body)))
            }
            Type::Constrained(cs, body) => Type::Constrained(
                cs.iter()
                    .map(|c| Constraint {
                        class: c.class.clone(),
                        args: c.args.iter().map(|a| self.deskolemise(a)).collect(),
                    })
                    .collect(),
                Box::new(self.deskolemise(body)),
            ),
            Type::Record(fs, tail) => Type::Record(
                fs.iter()
                    .map(|(l, t)| (l.clone(), self.deskolemise(t)))
                    .collect(),
                tail.as_ref().map(|t| Box::new(self.deskolemise(t))),
            ),
            Type::Row(fs, tail) => Type::Row(
                fs.iter()
                    .map(|(l, t)| (l.clone(), self.deskolemise(t)))
                    .collect(),
                tail.as_ref().map(|t| Box::new(self.deskolemise(t))),
            ),
            Type::Kinded(t, k) => Type::Kinded(
                Box::new(self.deskolemise(t)),
                Box::new(self.deskolemise(k)),
            ),
            other => other.clone(),
        }
    }

    /// Push a batch of givens onto the stack; returns the snapshot
    /// length for a later `pop_givens_to`.
    pub fn push_givens(&mut self, cs: Vec<Constraint>) -> usize {
        let snapshot = self.givens.len();
        self.givens.extend(cs);
        snapshot
    }

    /// Restore the given stack to a prior snapshot length.
    pub fn pop_givens_to(&mut self, snapshot: usize) {
        self.givens.truncate(snapshot);
    }

    /// Does any given constraint structurally match `c` after
    /// zonking both sides? Used by the solver as a discharge
    /// shortcut for constraints that were promised by an enclosing
    /// sig's `Constrained` layer.
    pub fn given_discharges(&self, c: &Constraint) -> bool {
        let zc = self.zonk_constraint(c);
        self.givens.iter().any(|g| {
            let zg = self.zonk_constraint(g);
            constraints_structurally_eq(&zg, &zc)
        })
    }

    /// Snapshot of the live givens stack. Combined by the solver
    /// with each `PendingConstraint`'s stamped givens — they may
    /// differ since a pending recorded in an inner scope keeps
    /// its givens after the scope is popped.
    pub fn givens_snapshot(&self) -> Vec<Constraint> {
        self.givens.clone()
    }

    fn zonk_constraint(&self, c: &Constraint) -> Constraint {
        Constraint {
            class: c.class.clone(),
            args: c.args.iter().map(|a| self.zonk(a)).collect(),
        }
    }

    /// Allocate a fresh skolem. Returns its id; every subsequent
    /// unification variable carries this id as its skolem boundary,
    /// so attempting to bind an earlier variable to a type
    /// containing this skolem will be rejected by `bind_var`.
    pub fn fresh_skolem(&mut self) -> u32 {
        let id = self.next_skolem;
        self.next_skolem += 1;
        id
    }

    /// Current skolem counter; used by `check_expr` to snapshot
    /// the boundary before introducing a group of skolems.
    pub fn skolem_level(&self) -> u32 {
        self.next_skolem
    }

    /// Push one pending constraint, stamping it with the current decl
    /// name so the draining caller can route it to the right
    /// `InferredScheme`. Also snapshots the current givens stack so
    /// the solver can consult it later, after the sig's Constrained
    /// layer has been popped from `self.givens`.
    pub fn record_pending_constraint(
        &mut self,
        mut entry: crate::typecheck_db::passes::constraints::PendingConstraint,
    ) {
        entry.decl_name = self.current_decl.clone();
        if entry.givens.is_empty() {
            entry.givens = self.givens.clone();
        }
        self.pending_constraints.push(entry);
    }

    /// Drain every recorded pending constraint.
    pub fn take_pending_constraints(
        &mut self,
    ) -> Vec<crate::typecheck_db::passes::constraints::PendingConstraint> {
        std::mem::take(&mut self.pending_constraints)
    }

    /// Number of pending constraints currently recorded. Callers use
    /// this as a bookmark — constraints born _after_ the bookmark are
    /// the ones to associate with a hole seen at that point.
    pub fn pending_constraints_len(&self) -> usize {
        self.pending_constraints.len()
    }

    /// Push one typed-hole diagnostic, stamping it with the current
    /// decl name so the draining caller can route it to the right
    /// [`InferredScheme`].
    pub fn record_pending_hole(
        &mut self,
        mut hole: crate::typecheck_db::passes::infer_value::HoleDiagnostic,
    ) {
        hole.decl_name = self.current_decl.clone();
        self.pending_holes.push(hole);
    }

    /// Drain every recorded pending hole.
    pub fn take_pending_holes(
        &mut self,
    ) -> Vec<crate::typecheck_db::passes::infer_value::HoleDiagnostic> {
        std::mem::take(&mut self.pending_holes)
    }

    /// Set of decl names that have at least one pending hole.
    pub fn decls_with_holes(&self) -> std::collections::HashSet<String> {
        self.pending_holes
            .iter()
            .filter_map(|h| h.decl_name.clone())
            .collect()
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

    /// Set the "currently inferring" decl's source span. Parallel to
    /// `set_current_decl` — both are typically updated together at
    /// the SCC loop's per-decl boundary.
    pub fn set_current_decl_span(&mut self, span: Option<Span>) {
        self.current_decl_span = span;
    }

    /// The decl span last set via `set_current_decl_span`.
    pub fn current_decl_span(&self) -> Option<Span> {
        self.current_decl_span
    }

    /// The current "actual"-side unify span (set by `with_unify_span`).
    pub fn current_unify_span(&self) -> Option<Span> {
        self.current_unify_span
    }

    /// Imperative setter for `current_unify_span`. Intended for the
    /// save+restore pattern in `infer_expr` / `check_expr`'s thin
    /// wrapper:
    /// ```ignore
    /// let prev = state.current_unify_span();
    /// state.set_current_unify_span(Some(expr.span()));
    /// let r = inner(state, …);
    /// state.set_current_unify_span(prev);
    /// ```
    /// `with_unify_span` is the closure-flavoured equivalent, but
    /// it's awkward to wrap a giant match around because of borrow
    /// limitations on captured `env: &mut Env`.
    pub fn set_current_unify_span(&mut self, span: Option<Span>) {
        self.current_unify_span = span;
    }

    /// The current "expected from" unify span (set by `with_expected_span`).
    pub fn current_expected_span(&self) -> Option<Span> {
        self.current_expected_span
    }

    /// Replace `current_unify_span` for the duration of `f`'s call,
    /// restoring the previous value when `f` returns. Use this at
    /// every `infer_expr` / `check_expr` entry so internal unifies
    /// inherit the surrounding expression's span without manual
    /// push/pop.
    pub fn with_unify_span<R>(&mut self, span: Span, f: impl FnOnce(&mut Self) -> R) -> R {
        let prev = self.current_unify_span.replace(span);
        let r = f(self);
        self.current_unify_span = prev;
        r
    }

    /// Replace `current_expected_span` for the duration of `f`'s
    /// call. Used by hot call sites that know where the expected
    /// type was sourced (e.g. `infer_app` setting `func.span()` so
    /// arg-type mismatches point at the function rather than the
    /// arg's own location).
    pub fn with_expected_span<R>(
        &mut self,
        span: Span,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let prev = self.current_expected_span.replace(span);
        let r = f(self);
        self.current_expected_span = prev;
        r
    }

    /// Build a `LocatedUnifyError` from a span-free `UnifyError` by
    /// reading the four `current_*` fields. Called by `unify_here`
    /// in `infer_value.rs` at the unifier-to-inference boundary.
    pub fn locate(&self, err: UnifyError) -> LocatedUnifyError {
        LocatedUnifyError {
            primary: self.current_unify_span,
            expected_from: self.current_expected_span,
            decl_name: self.current_decl.clone(),
            decl_span: self.current_decl_span,
            kind: err,
        }
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
        self.unif_skolem_levels.push(self.next_skolem);
        Type::Unif(id)
    }

    /// Number of unification variables currently allocated. Used by
    /// `generalize::instantiate` to detect "foreign" unif ids carried
    /// in a cached scheme — ids `>= bindings_len()` were allocated
    /// against a different state and need rebasing; ids strictly less
    /// are current-state unifs that must be preserved verbatim (e.g.
    /// the unif a `HoleDiagnostic` is tracking).
    pub fn bindings_len(&self) -> u32 {
        self.bindings.len() as u32
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
            // Grow levels in parallel. Stray unifs (from cached
            // schemes) get level 0 — conservative: they predate
            // any skolem introduction.
            self.unif_skolem_levels.resize(slot + 1, 0);
        }
        self.bindings[slot] = Some(ty);
    }

    /// Fully resolve a type by following bindings. Idempotent.
    pub fn zonk(&self, ty: &Type) -> Type {
        self.zonk_depth(ty, 0)
    }

    fn zonk_depth(&self, ty: &Type, depth: usize) -> Type {
        if depth > 4096 {
            // Cycle in unif bindings: a unif var ultimately
            // resolves through a chain that loops back to itself
            // via structural types whose occurs_in didn't fire.
            // Treat as opaque to break the loop — downstream
            // mismatch will be reported as Mismatch instead of
            // crashing the process.
            return ty.clone();
        }
        match ty {
            Type::Unif(id) => match self.probe(*id) {
                Some(bound) => self.zonk_depth(&bound.clone(), depth + 1),
                None => ty.clone(),
            },
            Type::App(f, a) => Type::app(
                self.zonk_depth(f, depth + 1),
                self.zonk_depth(a, depth + 1),
            ),
            Type::Fun(a, b) => Type::Fun(
                Box::new(self.zonk_depth(a, depth + 1)),
                Box::new(self.zonk_depth(b, depth + 1)),
            ),
            Type::Forall(vars, body) => {
                let vars = vars
                    .iter()
                    .map(|(n, v, k)| {
                        (
                            n.clone(),
                            *v,
                            k.as_ref().map(|k| Box::new(self.zonk_depth(k, depth + 1))),
                        )
                    })
                    .collect();
                Type::Forall(vars, Box::new(self.zonk_depth(body, depth + 1)))
            }
            Type::Constrained(cs, body) => {
                let cs = cs
                    .iter()
                    .map(|c| Constraint {
                        class: c.class.clone(),
                        args: c.args.iter().map(|a| self.zonk_depth(a, depth + 1)).collect(),
                    })
                    .collect();
                Type::Constrained(cs, Box::new(self.zonk_depth(body, depth + 1)))
            }
            Type::Record(fields, tail) => {
                let fs = fields
                    .iter()
                    .map(|(l, t)| (l.clone(), self.zonk_depth(t, depth + 1)))
                    .collect();
                let t = tail
                    .as_ref()
                    .map(|t| Box::new(self.zonk_depth(t, depth + 1)));
                Type::Record(fs, t)
            }
            Type::Row(fields, tail) => {
                let fs = fields
                    .iter()
                    .map(|(l, t)| (l.clone(), self.zonk_depth(t, depth + 1)))
                    .collect();
                let t = tail
                    .as_ref()
                    .map(|t| Box::new(self.zonk_depth(t, depth + 1)));
                Type::Row(fs, t)
            }
            Type::Kinded(t, k) => Type::Kinded(
                Box::new(self.zonk_depth(t, depth + 1)),
                Box::new(self.zonk_depth(k, depth + 1)),
            ),
            _ => ty.clone(),
        }
    }

    /// Unify two types, updating `self` with any new bindings.
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), UnifyError> {
        // Recursion guard against pathological row patterns where a
        // mutual chain of fresh tails would unfold forever (e.g. the
        // Hylograph SimNode/SimulationNode nested rows where two
        // SimulationNode-headed records share a polymorphic tail
        // and each reduction round produces a same-shape mismatch).
        // 1024 is well past any legitimate user nesting.
        self.unify_depth += 1;
        let result = if self.unify_depth > 1024 {
            Err(UnifyError::Mismatch(a.clone(), b.clone()))
        } else {
            let a = self.zonk(a);
            let b = self.zonk(b);
            self.unify_inner(&a, &b)
        };
        self.unify_depth -= 1;
        result
    }

    fn unify_inner(&mut self, a: &Type, b: &Type) -> Result<(), UnifyError> {
        match (a, b) {
            (Type::Unif(i), Type::Unif(j)) if i == j => Ok(()),
            (Type::Unif(id), other) | (other, Type::Unif(id)) => self.bind_var(*id, other),
            (Type::Var(n1), Type::Var(n2)) if n1 == n2 => Ok(()),
            (Type::Con(c1), Type::Con(c2)) if c1 == c2 => Ok(()),
            // Lenient module-qualifier comparison: `Core.ForceHandle`
            // (qualified through an `import M as Core` alias) and
            // `ForceHandle` (unqualified, referring to the same
            // imported type) refer to the same underlying type. We
            // unify whenever the names match AND one side has no
            // module qualifier OR both have the same module string.
            // We deliberately stay strict when both sides carry
            // DIFFERENT explicit qualifiers (e.g. `LibA.DemoKind`
            // vs `LibB.DemoKind`) — that's a real mismatch.
            (Type::Con(c1), Type::Con(c2))
                if c1.name == c2.name
                    && (c1.module.is_none() || c2.module.is_none()) =>
            {
                Ok(())
            }
            // Skolems are rigid — they unify only with themselves.
            // A skolem-vs-anything-else mismatch is exactly how
            // rank-2 violations get rejected: a lambda `\\n -> n + 1`
            // checked against `forall a. a -> a` introduces a skolem
            // for `a`, then `+` needs `Semiring skolem` which can't
            // be solved, or unification against `Number -> Number`
            // fails because `Number` ≠ skolem.
            (Type::Skolem(i), Type::Skolem(j)) if i == j => Ok(()),
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
            // Two constrained types: unify constraints + bodies.
            // Constraint lists must match in length, and args
            // unify pairwise.
            (Type::Constrained(cs1, b1), Type::Constrained(cs2, b2))
                if cs1.len() == cs2.len() =>
            {
                for (c1, c2) in cs1.iter().zip(cs2.iter()) {
                    if c1.class != c2.class || c1.args.len() != c2.args.len() {
                        return Err(UnifyError::Mismatch(a.clone(), b.clone()));
                    }
                    for (x, y) in c1.args.iter().zip(c2.args.iter()) {
                        self.unify(x, y)?;
                    }
                }
                self.unify(b1, b2)
            }
            // A `Constrained(cs, body)` against a non-constrained
            // type: only compatible if `cs` is empty (no
            // obligations left). Otherwise leave as Mismatch so
            // the caller sees the stuck constraint.
            (Type::Constrained(cs, body), other)
            | (other, Type::Constrained(cs, body))
                if cs.is_empty() =>
            {
                self.unify(body, other)
            }
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
            // `Forall` against a structurally-concrete head that
            // shares the Forall body's shape: this is the rank-N
            // instantiation-on-argument case. For `forall r. ST r a`
            // unified with `ST U1 U2`, we instantiate `r` to a fresh
            // unif and continue. We deliberately limit this to the
            // case where both sides have the same App-head so we
            // don't accept `(forall a. a -> a)` being "instantiated"
            // against `Number -> Number` — that's a rank-2
            // violation which legitimately fails to unify.
            (Type::Forall(vs, body), other) | (other, Type::Forall(vs, body))
                if forall_head_matches(body, other) =>
            {
                let mut subst: std::collections::HashMap<String, Type> =
                    std::collections::HashMap::new();
                for (n, _, _) in vs {
                    subst.insert(n.clone(), self.fresh());
                }
                let inst =
                    crate::typecheck_db::generalize::apply_var_subst(body, &subst);
                self.unify(&inst, other)
            }
            (Type::Record(f1, t1), Type::Record(f2, t2)) => unify_fields(self, f1, t1, f2, t2),
            (Type::Row(f1, t1), Type::Row(f2, t2)) => unify_fields(self, f1, t1, f2, t2),
            // Row ↔ Record bridging: a `Row` at the type level
            // and a `Record` at the value level can both represent
            // the same labeled-field shape. This arises when an F2
            // signature pin pulls a Row alias through a Record-
            // headed instance head — the unifier sees `Row` on
            // one side and `Record` on the other but the actual
            // shape is identical. Unify field-wise.
            (Type::Row(f1, t1), Type::Record(f2, t2))
            | (Type::Record(f1, t1), Type::Row(f2, t2)) => {
                unify_fields(self, f1, t1, f2, t2)
            }
            // `Record r` (parsed as `App(Con("Record"), r)`) is
            // equivalent to `{ | r }` — an open record whose
            // tail is `r`. Unify as `Record([], Some(r))` so
            // call-site `{ a :: Int }` literal records align
            // with the kind-level `Record` constructor.
            //
            // When the App head is a unif var (`App(?f, ?row)`),
            // bind `?f := Con("Record")` and proceed — analogous
            // to the `Fun ↔ App(App(α,x),y)` reconciliation that
            // binds α to `Con("->")`. This lets a polymorphic
            // function like `apply :: forall f a. f a -> f a`
            // unify against a record literal at the call site
            // (`apply { x: 42 }`).
            (Type::App(f, row), Type::Record(fields, tail))
            | (Type::Record(fields, tail), Type::App(f, row))
                if matches!(f.as_ref(), Type::Con(qn) if qn.name == "Record")
                    || matches!(f.as_ref(), Type::Unif(_)) =>
            {
                if let Type::Unif(_) = f.as_ref() {
                    self.unify(
                        f,
                        &Type::Con(crate::typecheck_db::types::QName::unqualified(
                            "Record",
                        )),
                    )?;
                }
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
        // Escape check: `id`'s skolem boundary is the skolem
        // counter value at its allocation time. `other` may only
        // reference skolems introduced BEFORE that boundary. A
        // skolem with id >= boundary was introduced AFTER the unif
        // existed, so binding would leak the skolem out of its
        // scope — exactly the rank-2 violation pattern.
        let boundary = self
            .unif_skolem_levels
            .get(id as usize)
            .copied()
            .unwrap_or(u32::MAX);
        if let Some(skolem) = max_skolem_in(other) {
            if skolem >= boundary {
                return Err(UnifyError::SkolemEscape {
                    var: id,
                    skolem,
                    ty: other.clone(),
                });
            }
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

    // Step 1: unify common labels. Field-level subsumption: when
    // exactly one side is `Forall(vs, body)`, instantiate the
    // polymorphic side with fresh unifs before unifying — this is
    // the record/row analogue of Peyton-Jones §5's sigma-vs-rho
    // subsumption. The escape check in `bind_var` still protects
    // against rank-2 violations whose skolems would leak. We don't
    // touch the top-level App case (`forall_head_matches`) because
    // a function-arg shape mismatch like `(forall a. a -> a) -> N`
    // applied to `\n -> n + 1` must keep failing — the subsumption
    // there belongs to a check-mode lambda check, not to plain
    // unification.
    for (l, t1v) in &m1 {
        if let Some(t2v) = m2.get(l) {
            let z1 = state.zonk(t1v);
            let z2 = state.zonk(t2v);
            match (&z1, &z2) {
                (Type::Forall(vs, body), other)
                | (other, Type::Forall(vs, body))
                    if !matches!(other, Type::Forall(_, _)) =>
                {
                    use crate::typecheck_db::generalize::apply_var_subst;
                    let mut subst: std::collections::HashMap<String, Type> =
                        std::collections::HashMap::new();
                    for (n, _, _) in vs {
                        subst.insert(n.clone(), state.fresh());
                    }
                    let inst = apply_var_subst(body, &subst);
                    state.unify(&inst, other)?;
                }
                _ => {
                    state.unify(t1v, t2v)?;
                }
            }
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
            // If both tails point to the same unif var AND each
            // side has extras the other doesn't, the row would
            // need to contain itself — type mismatch. Detect this
            // up-front; without it `unify {a :: Int | r}
            // {b :: Int | r}` recurses forever as fresh tails are
            // re-introduced and each round produces the same
            // mismatch. Reference compiler reports as
            // `TypesDoNotUnify` (UnificationError) so we use
            // Mismatch rather than Infinite here.
            //
            // Generalise: detect when the unify is structurally
            // self-referential — even if t1 and t2 are
            // *different* unif vars, if zonking each produces the
            // SAME type whose tail is one of those unifs (i.e.
            // the binding chain has merged through earlier
            // unifications), the next iteration will produce the
            // same shape and recurse forever.
            if let (Some(a), Some(b)) = (t1.as_deref(), t2.as_deref()) {
                let za = state.zonk(a);
                let zb = state.zonk(b);
                if let (Type::Unif(i), Type::Unif(j)) = (&za, &zb) {
                    if i == j {
                        return Err(UnifyError::Mismatch(
                            Type::Record(only1.clone(), t1.clone()),
                            Type::Record(only2.clone(), t2.clone()),
                        ));
                    }
                }
            }
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

/// Maximum skolem id appearing anywhere in `ty`, or `None` if the
/// type contains no skolems. Used by `bind_var`'s escape check.
fn max_skolem_in(ty: &Type) -> Option<u32> {
    match ty {
        Type::Skolem(id) => Some(*id),
        Type::App(f, a) | Type::Fun(f, a) | Type::Kinded(f, a) => {
            match (max_skolem_in(f), max_skolem_in(a)) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            }
        }
        Type::Forall(_, body) => max_skolem_in(body),
        Type::Constrained(cs, b) => {
            let cs_max = cs
                .iter()
                .flat_map(|c| c.args.iter())
                .filter_map(max_skolem_in)
                .max();
            let b_max = max_skolem_in(b);
            match (cs_max, b_max) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            }
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            let fs_max = fs.iter().filter_map(|(_, t)| max_skolem_in(t)).max();
            let tail_max = tail.as_ref().and_then(|t| max_skolem_in(t));
            match (fs_max, tail_max) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            }
        }
        _ => None,
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

/// Structural equality of two zonked constraints — same class
/// name (including module qualifier) and pair-wise structurally-
/// equal args. Used by `given_discharges` to match a pending
/// constraint against a peeled-from-sig hypothesis. Stricter than
/// `unify` on purpose: givens are promises from the caller, so
/// matching is syntactic over the zonked form — no fresh-unif
/// binding allowed.
fn constraints_structurally_eq(a: &Constraint, b: &Constraint) -> bool {
    a.class == b.class
        && a.args.len() == b.args.len()
        && a.args.iter().zip(b.args.iter()).all(|(x, y)| type_eq(x, y))
}

fn type_eq(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Var(x), Type::Var(y)) => x == y,
        (Type::Con(x), Type::Con(y)) => x == y,
        (Type::Unif(x), Type::Unif(y)) => x == y,
        (Type::Skolem(x), Type::Skolem(y)) => x == y,
        (Type::TypeString(x), Type::TypeString(y)) => x == y,
        (Type::TypeInt(x), Type::TypeInt(y)) => x == y,
        (Type::App(f1, a1), Type::App(f2, a2))
        | (Type::Fun(f1, a1), Type::Fun(f2, a2)) => type_eq(f1, f2) && type_eq(a1, a2),
        (Type::Forall(vs1, b1), Type::Forall(vs2, b2)) => {
            vs1.len() == vs2.len()
                && vs1.iter().zip(vs2.iter()).all(|((n1, _, _), (n2, _, _))| n1 == n2)
                && type_eq(b1, b2)
        }
        (Type::Constrained(c1, b1), Type::Constrained(c2, b2)) => {
            c1.len() == c2.len()
                && c1.iter().zip(c2.iter()).all(|(x, y)| constraints_structurally_eq(x, y))
                && type_eq(b1, b2)
        }
        (Type::Record(f1, t1), Type::Record(f2, t2))
        | (Type::Row(f1, t1), Type::Row(f2, t2)) => {
            f1.len() == f2.len()
                && f1.iter().zip(f2.iter()).all(|((l1, t1), (l2, t2))| {
                    l1 == l2 && type_eq(t1, t2)
                })
                && match (t1, t2) {
                    (None, None) => true,
                    (Some(a), Some(b)) => type_eq(a, b),
                    _ => false,
                }
        }
        (Type::Kinded(t1, k1), Type::Kinded(t2, k2)) => type_eq(t1, t2) && type_eq(k1, k2),
        (Type::Hole(x), Type::Hole(y)) => x == y,
        (Type::Wildcard, Type::Wildcard) => true,
        _ => false,
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
