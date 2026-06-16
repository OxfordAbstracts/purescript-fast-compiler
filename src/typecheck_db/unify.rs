//! Union-find unification over [`Type`].
//!
//! Scoped per inference run — there is no module-global state, which is the
//! whole point of the per-decl cache design. `UnifyState` allocates fresh
//! variables, records their solved bindings, and provides `zonk` to read
//! the fully-resolved form of a type.

use std::collections::HashSet;
use std::sync::Arc;

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
                // Peel outer `Constrained` so a body shaped
                // `Constrained([C a], Fun(...))` (e.g. the
                // `Webb.AffList.Data.Node.Parent::wrap` shape
                // `forall z. Parent z => z -> r`) is treated as
                // `Fun`-headed. The constraint becomes a pending
                // obligation post-instantiation; the unify still
                // proceeds on the Fun spine.
                Type::Constrained(_, inner) => cur = inner,
                _ => return Some(cur),
            }
        }
    }
    match (app_head(body), app_head(other)) {
        (Some(Type::Con(a)), Some(Type::Con(b))) => {
            // Lenient module-qualifier comparison (mirrors the unify
            // arm): names must match; one side may be None-qualified
            // when the other is Some(defining_module). Lets a forall
            // body's qualified `Z3` instantiate against a call-site
            // unqualified `Z3` (legacy synthesizer didn't qualify).
            a == b
                || (a.name == b.name
                    && (a.module.is_none() || b.module.is_none()))
        }
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
        // Structurally compatible Fun heads. When the Forall body
        // shares the outer scaffolding of `other` (matching
        // `Con`s, matching `Skolem`s, recurse through `Fun`/`App`)
        // and the body's `Var` positions correspond to the
        // forall-quantified slots, instantiation is safe: each
        // Var becomes a fresh unif and the subsequent unify
        // refines it (or fails on a real mismatch).
        //
        // Catches the Codensity::apply / Ran::lift' / Webb
        // ::wrap / Routing.Duplex.Generic::sum / Data.Lens.*
        // family where the LHS arrives with concrete `Con` heads
        // (`Forget`, RouteDuplex`, etc.) and the original
        // `leaves_all_unif` gate rejected as `Mismatch`.
        //
        // Genuine rank-2 violations (`Int -> Int` against
        // `forall a. a -> a`) are NOT silently accepted: this
        // rule still instantiates the forall to `?u_a -> ?u_a`,
        // and the follow-up unify will bind `?u_a := Int` and
        // then reject `Int ~ String` (or `Int ~ Sk_x` in a
        // skolem-context) as `Mismatch` / `SkolemEscape`.
        (Some(Type::Fun(_, _)), Some(Type::Fun(_, _)))
            if structurally_compatible(body, other) =>
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

/// True when the Forall `body` and `other` share enough outer
/// scaffolding that instantiating the Forall is safe. `Var`s on
/// the body side (forall-quantified slots) match anything;
/// `Unif`s on either side match anything; matching `Con`/`Skolem`
/// at the same position must agree; `Fun`/`App` recurse.
///
/// Used as a secondary gate for the rank-2 instantiation rule
/// alongside `leaves_all_unif`. The follow-up unify still
/// validates concrete mismatches after instantiation — this rule
/// is purely about deciding whether to TRY instantiation.
fn structurally_compatible(body: &Type, other: &Type) -> bool {
    match (body, other) {
        // Body-side inner `Forall` / `Constrained` will be peeled by
        // a subsequent unify iteration after we instantiate the
        // current outer Forall. Treat them as transparent here so a
        // rank-N body like `forall a. f a -> forall b. (a -> b) -> g
        // b` (the `Codensity::lift` shape — Ran's type alias unfolds
        // to nested `forall` under a `Fun`) matches an instantiated
        // `f ?u_a -> (?u_a -> b) -> g b` on the other side.
        (Type::Forall(_, inner), _) => structurally_compatible(inner, other),
        (Type::Constrained(_, inner), _) => structurally_compatible(inner, other),
        (Type::Var(_), _) => true,
        (Type::Unif(_), _) | (_, Type::Unif(_)) => true,
        // Lenient module-qualifier comparison: mirrors the
        // `forall_head_matches` / outer unify clauses so a body
        // with `Con(Some("M"), "Thunk")` is compatible with an
        // `other` carrying `Con(None, "Thunk")` (legacy synthesizer
        // didn't qualify) or vice versa.
        (Type::Con(a), Type::Con(b)) => {
            a == b
                || (a.name == b.name
                    && (a.module.is_none() || b.module.is_none()))
        }
        (Type::Skolem(a), Type::Skolem(b)) => a == b,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            structurally_compatible(f1, f2) && structurally_compatible(a1, a2)
        }
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            structurally_compatible(a1, a2) && structurally_compatible(b1, b2)
        }
        // Records / rows: same labels in same order, each field
        // value structurally compatible. Both tails compatible
        // (None vs None, or each present and compatible).
        (Type::Record(f1, t1), Type::Record(f2, t2))
        | (Type::Row(f1, t1), Type::Row(f2, t2)) => {
            if f1.len() != f2.len() {
                return false;
            }
            for ((l1, v1), (l2, v2)) in f1.iter().zip(f2.iter()) {
                if l1 != l2 || !structurally_compatible(v1, v2) {
                    return false;
                }
            }
            match (t1, t2) {
                (None, None) => true,
                (Some(a), Some(b)) => structurally_compatible(a, b),
                _ => false,
            }
        }
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
    /// Per-decl deadline expired during typechecking. Carries the
    /// budget in ms so the diagnostic shows what was exceeded.
    /// Configured via the `TYPECHECK_DECL_TIMEOUT_MS` env var (set
    /// to `0` to disable). `LocatedUnifyError::decl_name`
    /// /`decl_span` carry the attribution.
    #[error("typecheck exceeded {budget_ms}ms decl deadline")]
    Timeout { budget_ms: u64 },
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
    // Per-unif declared kind, parallel to `bindings`. `None` when
    // the kind is unknown (no annotation propagated to fresh()).
    // `Some(kind)` populated by `fresh_with_kind`. Used by
    // `bind_var` to refuse a kind-mismatched binding (e.g. a
    // higher-kinded unif being pinned to a Type-kind value).
    unif_kinds: Vec<Option<Type>>,
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
    /// Per-decl typecheck deadline. `unify_inner` polls this on
    /// entry and bails with `UnifyError::Timeout` when the deadline
    /// is past, so a pathological decl (e.g. fundep-driven solver
    /// loop, deeply nested alias expansion) can't stall the whole
    /// SCC. Set per decl by `infer_value_scc_with_all`; `None`
    /// disables the check entirely.
    deadline: Option<std::time::Instant>,
    /// Budget that produced the current `deadline`, in ms. Recorded
    /// so the `Timeout` error variant can surface what was exceeded
    /// rather than re-deriving from `Instant`.
    deadline_budget_ms: u64,
    /// Undo trail for `bindings` mutations. Every assignment that
    /// overwrites a slot pushes `(slot, previous_value)` so a
    /// later `restore_bindings` can replay them in reverse. This
    /// is what makes snapshot O(1) and restore O(delta) — the
    /// instance-trial loop snapshots once per candidate, and
    /// without a trail the previous full-`bindings.clone()` cost
    /// dominated for big modules (e.g. one decl's solver bill of
    /// 6000 constraints × 446 EncodeOa candidates × ~50k-slot
    /// state was 600+ seconds in the OA application sweep).
    binding_trail: Vec<(usize, Option<Type>)>,
    /// Pendings that already received a successful fundep
    /// improvement, keyed by `(span.start, class name)`. The
    /// improvement apply can pin a determined position to a type
    /// that itself contains bare unifs (e.g. `Newtype (NT ?u) ?a`
    /// pins `?a := ?u`); the "determined still bare" check then
    /// re-runs the full match+apply — including a structural unify
    /// over the (possibly huge) determiner types — on EVERY solver
    /// iteration. Marking the pending after its first apply makes
    /// improvement once-per-pending. Improvement is an
    /// optimisation; skipping repeats can't lose solutions.
    improved_pendings: std::collections::HashSet<(u32, String)>,
}

/// Captures the union-find state at a point so a later
/// `restore_bindings` undoes every assignment performed between
/// the two calls — restoring slot values via the trail and
/// shrinking any fresh allocations.
#[derive(Debug, Clone, Copy)]
pub struct BindingSnapshot {
    trail_len: usize,
    bindings_len: usize,
    skolem_levels_len: usize,
}

impl UnifyState {
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
            unif_kinds: Vec::new(),
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
            deadline: None,
            deadline_budget_ms: 0,
            binding_trail: Vec::new(),
            improved_pendings: std::collections::HashSet::new(),
        }
    }

    /// Record that `pending` (identified by its span start + class
    /// name) received a successful fundep improvement. See the
    /// field docs on `improved_pendings`.
    pub fn mark_improved(&mut self, span_start: usize, class: &str) {
        self.improved_pendings
            .insert((span_start as u32, class.to_string()));
    }

    /// Was a fundep improvement already applied for this pending?
    pub fn was_improved(&self, span_start: usize, class: &str) -> bool {
        self.improved_pendings
            .contains(&(span_start as u32, class.to_string()))
    }

    /// Arm the per-decl typecheck deadline. Callers pass the
    /// budget in ms together with the deadline `Instant` so the
    /// `Timeout` error can report what was exceeded.
    pub fn set_deadline(&mut self, deadline: Option<std::time::Instant>, budget_ms: u64) {
        self.deadline = deadline;
        self.deadline_budget_ms = budget_ms;
    }

    /// Drop the deadline (re-enable unbounded unification). Used
    /// on the error paths in `infer_value_scc_with_all` so a
    /// stale deadline doesn't leak into the next SCC.
    pub fn clear_deadline(&mut self) {
        self.deadline = None;
        self.deadline_budget_ms = 0;
    }

    /// True iff a deadline is armed and the current instant is past
    /// it. Cheap (one `Instant::now()` plus a compare) — `unify_inner`
    /// polls this on entry, and the solver / coercible-check
    /// fixed-point loops poll it at the top of each iteration.
    pub fn deadline_exceeded(&self) -> bool {
        match self.deadline {
            Some(d) => std::time::Instant::now() >= d,
            None => false,
        }
    }

    /// Budget that armed the current deadline, in ms. Read at
    /// timeout-error construction so the variant carries the
    /// exceeded budget.
    pub fn deadline_budget_ms(&self) -> u64 {
        self.deadline_budget_ms
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
                Type::Forall(vs.clone(), Arc::new(self.deskolemise(body)))
            }
            Type::Constrained(cs, body) => Type::Constrained(
                cs.iter()
                    .map(|c| Constraint {
                        class: c.class.clone(),
                        args: c.args.iter().map(|a| self.deskolemise(a)).collect(),
                    })
                    .collect(),
                Arc::new(self.deskolemise(body)),
            ),
            Type::Record(fs, tail) => Type::Record(
                fs.iter()
                    .map(|(l, t)| (l.clone(), self.deskolemise(t)))
                    .collect(),
                tail.as_ref().map(|t| Arc::new(self.deskolemise(t))),
            ),
            Type::Row(fs, tail) => Type::Row(
                fs.iter()
                    .map(|(l, t)| (l.clone(), self.deskolemise(t)))
                    .collect(),
                tail.as_ref().map(|t| Arc::new(self.deskolemise(t))),
            ),
            Type::Kinded(t, k) => Type::Kinded(
                Arc::new(self.deskolemise(t)),
                Arc::new(self.deskolemise(k)),
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

    /// `true` when no givens are in scope. Cheap peek over
    /// `givens_snapshot` for hot paths that early-exit when the
    /// live givens stack is empty (e.g. `given_discharges_pending`
    /// inside the solver's `solve_one`).
    pub fn givens_is_empty(&self) -> bool {
        self.givens.is_empty()
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

    /// Capture the current union-find state so a later
    /// `restore_bindings` call can undo every unification performed
    /// between the two points. Used by the instance-match trial
    /// loop to reject a candidate without leaking partial bindings
    /// into the outer state. O(1) — only records lengths, not a
    /// clone of the bindings vector.
    /// Current length of the undo trail. Used as a watermark by
    /// `solve_all` to detect whether new bindings were made
    /// between two probes: if the length is unchanged, no
    /// `assign` happened.
    pub fn binding_trail_len(&self) -> usize {
        self.binding_trail.len()
    }

    /// Slot id of the trail entry at `idx`. Used by `solve_all` to
    /// iterate `[old_len..new_len)` and learn which unifs were
    /// newly bound, so deferred constraints whose dependent unifs
    /// are disjoint from the newly-bound set can skip a redundant
    /// `solve_one`.
    pub fn binding_trail_slot_at(&self, idx: usize) -> u32 {
        self.binding_trail[idx].0 as u32
    }

    pub fn snapshot_bindings(&self) -> BindingSnapshot {
        BindingSnapshot {
            trail_len: self.binding_trail.len(),
            bindings_len: self.bindings.len(),
            skolem_levels_len: self.unif_skolem_levels.len(),
        }
    }

    /// Restore bindings previously captured via `snapshot_bindings`.
    /// Safe only when the caller has kept the snapshot's lifetime
    /// scoped to a single unification attempt. O(delta) — pops the
    /// trail back to the snapshot's watermark, restoring each
    /// slot's previous value, then shrinks any fresh allocations
    /// from `assign`'s resize / `fresh`'s push.
    pub fn restore_bindings(&mut self, snapshot: BindingSnapshot) {
        while self.binding_trail.len() > snapshot.trail_len {
            let (slot, prev) = self.binding_trail.pop().unwrap();
            if slot < snapshot.bindings_len {
                self.bindings[slot] = prev;
            }
            // Slots beyond `bindings_len` were allocated AFTER the
            // snapshot; they're discarded by the `truncate` below,
            // so the trail entry can be ignored.
        }
        self.bindings.truncate(snapshot.bindings_len);
        self.unif_kinds.truncate(snapshot.bindings_len);
        self.unif_skolem_levels.truncate(snapshot.skolem_levels_len);
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

    /// Allocate a fresh unification variable with unknown kind.
    pub fn fresh(&mut self) -> Type {
        let id = self.bindings.len() as u32;
        self.bindings.push(None);
        self.unif_kinds.push(None);
        self.unif_skolem_levels.push(self.next_skolem);
        Type::Unif(id)
    }

    /// Allocate a fresh unification variable with a declared kind.
    /// Used by `instantiate` for Forall vars carrying explicit
    /// kind annotations, and by ad-hoc call sites that know the
    /// kind they're slotting (e.g. an App-head fresh that must be
    /// `Type -> Type`).
    pub fn fresh_with_kind(&mut self, kind: Type) -> Type {
        let id = self.bindings.len() as u32;
        self.bindings.push(None);
        self.unif_kinds.push(Some(kind));
        self.unif_skolem_levels.push(self.next_skolem);
        Type::Unif(id)
    }

    /// Read a unif's declared kind, if known.
    pub fn unif_kind(&self, id: u32) -> Option<&Type> {
        self.unif_kinds
            .get(id as usize)
            .and_then(|o| o.as_ref())
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
        // Record the prior value on the undo trail so a snapshot
        // taken before this point can roll back the assignment.
        let prev = self.bindings[slot].take();
        self.binding_trail.push((slot, prev));
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
        // Fast path: when `ty` has no Unif anywhere, zonk is a
        // pure clone-walk that allocates O(N) fresh Arcs only to
        // produce a structurally-identical tree. With Arc<Type>
        // recursive fields, `ty.clone()` is O(1) per node (refcount
        // bump on each Arc field) — vastly cheaper than the walk.
        // The `has_any_unif` check is itself O(N), but allocation-
        // free; net win whenever zonk's input is already-resolved
        // (the common case during constraint-solver retries on
        // deep `<>`-chains).
        if !has_any_unif(ty) {
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
                Arc::new(self.zonk_depth(a, depth + 1)),
                Arc::new(self.zonk_depth(b, depth + 1)),
            ),
            Type::Forall(vars, body) => {
                let vars = vars
                    .iter()
                    .map(|(n, v, k)| {
                        (
                            n.clone(),
                            *v,
                            k.as_ref().map(|k| Arc::new(self.zonk_depth(k, depth + 1))),
                        )
                    })
                    .collect();
                Type::Forall(vars, Arc::new(self.zonk_depth(body, depth + 1)))
            }
            Type::Constrained(cs, body) => {
                let cs = cs
                    .iter()
                    .map(|c| Constraint {
                        class: c.class.clone(),
                        args: c.args.iter().map(|a| self.zonk_depth(a, depth + 1)).collect(),
                    })
                    .collect();
                Type::Constrained(cs, Arc::new(self.zonk_depth(body, depth + 1)))
            }
            Type::Record(fields, tail) => {
                let fs = fields
                    .iter()
                    .map(|(l, t)| (l.clone(), self.zonk_depth(t, depth + 1)))
                    .collect();
                let t = tail
                    .as_ref()
                    .map(|t| Arc::new(self.zonk_depth(t, depth + 1)));
                Type::Record(fs, t)
            }
            Type::Row(fields, tail) => {
                let fs = fields
                    .iter()
                    .map(|(l, t)| (l.clone(), self.zonk_depth(t, depth + 1)))
                    .collect();
                let t = tail
                    .as_ref()
                    .map(|t| Arc::new(self.zonk_depth(t, depth + 1)));
                Type::Row(fs, t)
            }
            Type::Kinded(t, k) => Type::Kinded(
                Arc::new(self.zonk_depth(t, depth + 1)),
                Arc::new(self.zonk_depth(k, depth + 1)),
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
        } else if !has_any_unif(a) && !has_any_unif(b) {
            // Fast path: when neither side mentions a Unif, zonk is a
            // pure clone-walk. Skip it. Two O(N) walks (one per arg)
            // replace one O(N) walk-plus-clone per arg — net win
            // because the clone allocates fresh boxes for every node
            // and shows up as the dominant cost in solver-heavy
            // modules.
            self.unify_inner(a, b)
        } else {
            let a = self.zonk(a);
            let b = self.zonk(b);
            self.unify_inner(&a, &b)
        };
        self.unify_depth -= 1;
        result
    }

    fn unify_inner(&mut self, a: &Type, b: &Type) -> Result<(), UnifyError> {
        // Per-decl deadline check. `infer_value_scc_with_all` arms
        // the deadline before each decl's body inference (and once
        // more for the post-body SCC phases); a pathological
        // recursion / fundep-driven solver loop will go through
        // `unify` densely enough that this single `Instant::now()`
        // compare per call reliably surfaces the timeout. The
        // helper bails fast when no deadline is armed.
        if self.deadline_exceeded() {
            return Err(UnifyError::Timeout {
                budget_ms: self.deadline_budget_ms,
            });
        }
        match (a, b) {
            (Type::Unif(i), Type::Unif(j)) if i == j => Ok(()),
            (Type::Unif(id), other) | (other, Type::Unif(id)) => self.bind_var(*id, other),
            (Type::Var(n1), Type::Var(n2)) if n1 == n2 => Ok(()),
            (Type::Con(c1), Type::Con(c2)) if c1 == c2 => Ok(()),
            // Lenient module-qualifier comparison. After the resolve
            // pass + Prim helpers + CtorInfo parent_module + IR
            // Resolved<N> migration, most Type::Con cells carry
            // Some(defining_module). But many synthesizer + test sites
            // still produce None-qualified Type::Con's. This lenient
            // clause bridges them. Remove once all production
            // synthesizers carry origins.
            (Type::Con(c1), Type::Con(c2))
                if c1.name == c2.name
                    && (c1.module.is_none() || c2.module.is_none()) =>
            {
                Ok(())
            }
            // `->` is the type-level operator alias for `Prim.Function`.
            // Equate the two names so a Type::Con-carried arrow head
            // (produced by some legacy synthesizer that didn't desugar
            // `->` into `Type::Fun`) unifies with `Prim.Function` from
            // the prim helpers.
            (Type::Con(c1), Type::Con(c2))
                if (c1.name == "->" && c2.name == "Function")
                    || (c1.name == "Function" && c2.name == "->") =>
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
                                &crate::typecheck_db::types::prim_function(),
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
                    let arrow = crate::typecheck_db::types::prim_function();
                    self.unify(
                        outer_f,
                        &Type::App(Arc::new(arrow), Arc::new((**fa).clone())),
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
            // `Constrained(cs, body)` against a non-constrained
            // type: peel `cs` as pending obligations and continue
            // unifying `body` with `other`. This is the
            // subsumption rule for a "polymorphic" type with
            // dictionary args: the recipient is responsible for
            // discharging the constraints, and the body must
            // unify with the expected shape. Arises after
            // `forall_head_matches` instantiates a `forall z.
            // Parent z => z -> r`-shaped binder type and the
            // unifier then sees `Constrained([Parent ?u_z],
            // Fun(?u_z, ?u_r))` against the expected `Fun(...)`.
            // The constraints get recorded with the current
            // expression's span; the solver picks them up after
            // body inference.
            (Type::Constrained(cs, body), other)
            | (other, Type::Constrained(cs, body)) => {
                use crate::typecheck_db::passes::constraints::{
                    ConstraintOrigin, PendingConstraint,
                };
                let span = self.current_unify_span.unwrap_or(Span { start: 0, end: 0 });
                for c in cs {
                    self.record_pending_constraint(PendingConstraint {
                        decl_name: None,
                        span,
                        constraint: c.clone(),
                        origin: ConstraintOrigin::Signature,
                        givens: Vec::new(),
                    });
                }
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
                    self.unify(f, &crate::typecheck_db::types::prim_record())?;
                }
                let empty: Vec<(String, Type)> = Vec::new();
                let tail_box: Option<Arc<Type>> = Some(Arc::new((**row).clone()));
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
            // Kind propagation between unifs: when we bind one
            // unif to another, the resulting equivalence class
            // shares whatever kind either side knew. Copy from the
            // known side into the unknown side BEFORE the bind so
            // a subsequent `bind_var(j, Record(...))` (or a fresh
            // App-head unification) sees the inherited kind and
            // can refuse a kind-mismatched value.
            if std::env::var("TYPECHECK_DB_KIND_CHECK").is_ok() {
                let id_kind = self
                    .unif_kinds
                    .get(id as usize)
                    .and_then(|o| o.as_ref())
                    .cloned();
                let j_kind = self
                    .unif_kinds
                    .get(*j as usize)
                    .and_then(|o| o.as_ref())
                    .cloned();
                match (id_kind, j_kind) {
                    (Some(k), None) => {
                        if (*j as usize) < self.unif_kinds.len() {
                            self.unif_kinds[*j as usize] = Some(k);
                        }
                    }
                    (None, Some(k)) => {
                        if (id as usize) < self.unif_kinds.len() {
                            self.unif_kinds[id as usize] = Some(k);
                        }
                    }
                    _ => {}
                }
            }
        }
        if occurs_in(id, other) {
            return Err(UnifyError::Infinite { var: id, ty: other.clone() });
        }
        // Kind-discipline check. Gated by env var while we validate
        // the structural rules don't over-reject. When enabled:
        // refuse a higher-kinded unif (`Type -> Type`+) from being
        // unified with a `Type`-kind concrete value (Record, known
        // Type-kind Con). This catches the parallel cluster bug
        // where `f :: Type -> Type` got pinned to a Record.
        if std::env::var("TYPECHECK_DB_KIND_CHECK").is_ok() {
            if let Some(expected_kind) = self
                .unif_kinds
                .get(id as usize)
                .and_then(|o| o.as_ref())
                .cloned()
            {
                if is_higher_kind(&expected_kind) {
                    if let Some(actual_kind) = kind_of_value(self, other) {
                        if !kinds_compatible(&expected_kind, &actual_kind) {
                            return Err(UnifyError::Mismatch(
                                Type::Unif(id),
                                other.clone(),
                            ));
                        }
                    }
                }
            }
        }
        // Skolem-level reconciliation. `id`'s skolem boundary is the
        // skolem counter value at its allocation time; `other` may
        // reference skolems with id >= that boundary when this is a
        // rank-2 subsumption: an outer unif (e.g. `mutate`'s `b`)
        // gets bound to a type containing a skolem from the
        // arg-side `forall` (e.g. `r` in `forall r. STObject r a ->
        // ST r b`). The reference compiler (PureScript) accepts
        // this bind during unification and defers the escape
        // verdict to a separate `skolemEscapeCheck` over the
        // typed AST (see `Language.PureScript.TypeChecker.Skolems`).
        //
        // We promote `id`'s level to admit the skolem and rely on
        // a downstream pass (decl-level free-skolem walk in
        // `infer_value_scc_with_all`) to flag genuine escapes.
        // Without this, valid rank-2 patterns like
        // `mutate (OST.poke k v)` and `ST.run (STRef.new 0)` are
        // rejected here even though the would-be-captured unifs
        // are inert (never reach the outer scheme).
        if let Some(skolem) = max_skolem_in(other) {
            let slot = id as usize;
            if slot < self.unif_skolem_levels.len() {
                let cur = self.unif_skolem_levels[slot];
                if skolem >= cur {
                    self.unif_skolem_levels[slot] = skolem.saturating_add(1);
                }
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

    /// True if any `Type::Skolem` appears anywhere in `ty`. Used for
    /// the post-hoc escape check at decl-finalize time: a skolem
    /// surviving in a generalized scheme means it leaked out of its
    /// `forall` introduction site (since generalize can't quantify
    /// rigid skolems — only unif vars). Mirrors the reference
    /// compiler's `skolemEscapeCheck` over typed values.
    pub fn contains_free_skolem(&self, ty: &Type) -> Option<u32> {
        max_skolem_in(&self.zonk(ty))
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
    t1: &Option<Arc<Type>>,
    f2: &[(String, Type)],
    t2: &Option<Arc<Type>>,
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
                    // Pass the already-zonked versions so unify's
                    // top-level zonk has no work (`has_any_unif`
                    // fast-path returns).
                    state.unify(&z1, &z2)?;
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
            absorb_extras(state, t1, only2, Some(Arc::new(fresh.clone())))?;
            absorb_extras(state, t2, only1, Some(Arc::new(fresh)))
        }
    }
}

fn unify_opt_tails(
    state: &mut UnifyState,
    t1: &Option<Arc<Type>>,
    t2: &Option<Arc<Type>>,
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
    t: &Option<Arc<Type>>,
    extras: Vec<(String, Type)>,
    rest: Option<Arc<Type>>,
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

/// True iff `ty` mentions any `Type::Unif(_)` anywhere. Used to
/// short-circuit `unify`'s top-level zonk on fully-concrete inputs
/// (the common case for non-polymorphic typeclass dispatch over
/// `Type::Con` heads). Skipping the clone-walk that zonk performs
/// on those inputs measurably speeds up large solver runs.
pub fn has_any_unif(ty: &Type) -> bool {
    match ty {
        Type::Unif(_) => true,
        Type::App(f, a) => has_any_unif(f) || has_any_unif(a),
        Type::Fun(a, b) => has_any_unif(a) || has_any_unif(b),
        Type::Forall(_, body) => has_any_unif(body),
        Type::Constrained(cs, b) => {
            cs.iter().any(|c| c.args.iter().any(has_any_unif)) || has_any_unif(b)
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            fs.iter().any(|(_, t)| has_any_unif(t))
                || tail.as_ref().map_or(false, |t| has_any_unif(t))
        }
        Type::Kinded(t, k) => has_any_unif(t) || has_any_unif(k),
        _ => false,
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

/// True when `kind` is shape `_ -> _` (a function kind, i.e. the
/// var ranges over a higher-kinded thing like `Type -> Type`).
/// The Parallel cluster bug needs this distinction: parallel's
/// `f` is higher-kinded and must NOT be bound to a `Type`-kind
/// value. Lower-kinded vars (kind `Type`) bind freely.
fn is_higher_kind(kind: &Type) -> bool {
    match kind {
        Type::Fun(_, _) => true,
        Type::Kinded(t, _) => is_higher_kind(t),
        _ => false,
    }
}

/// Compute the kind of a concrete-shaped type — `Type` for value-
/// kind shapes (Record, Row-of-Type, Fun, TypeString, TypeInt,
/// known type Cons), and `kind_of_app_head(...) - 1 arg` for
/// applications (decompose the spine). Returns `None` for opaque
/// shapes (variables, skolems, unifs whose kind we don't track,
/// unknown Cons heads) — `bind_var` skips its kind check in those
/// cases. Deliberately conservative: we'd rather miss a kind error
/// than reject a legitimate binding.
fn kind_of_value(state: &UnifyState, ty: &Type) -> Option<Type> {
    use crate::typecheck_db::types::{prim_kind_type, prim_int, prim_symbol};
    match ty {
        // Records and rows of value types are kind Type. Open rows
        // with a tail still resolve to Type if the tail does.
        Type::Record(_, _) => Some(prim_kind_type()),
        // A Row literal is kind `Row k` for some k. Without
        // tracking the element kind we conservatively return None
        // — we don't want to refuse a row-vs-rowish bind on weak
        // inference.
        Type::Row(_, _) => None,
        // Functions are kind Type.
        Type::Fun(_, _) => Some(prim_kind_type()),
        // Type-level literals.
        Type::TypeString(_) => Some(prim_symbol()),
        Type::TypeInt(_) => Some(prim_int()),
        // A Kinded annotation publishes the kind directly.
        Type::Kinded(_, k) => Some((**k).clone()),
        // Application: decompose the spine. The HEAD's kind must
        // be of shape `k1 -> ... -> kn -> result`; we apply n args
        // (concrete spine length) and return the result kind.
        Type::App(_, _) => {
            let (head, args) = decompose_app(ty);
            let head_kind = kind_of_head(state, &head)?;
            apply_kind(&head_kind, args.len())
        }
        Type::Con(qn) => {
            // Only recognise the small set of Prim Type-kind
            // constructors here. Unknown Cons heads fall through to
            // None (no check); the kind tracker would need a
            // registry to know about user types' kinds.
            if is_known_type_kind_con(qn) {
                Some(prim_kind_type())
            } else {
                None
            }
        }
        Type::Unif(id) => state.unif_kind(*id).cloned(),
        // Skolems / Vars / Forall / Constrained / Hole / Wildcard:
        // not enough info to decide a concrete kind here.
        _ => None,
    }
}

/// Walk an App spine to its head + args (left-to-right).
fn decompose_app(ty: &Type) -> (Type, Vec<Type>) {
    let mut args: Vec<Type> = Vec::new();
    let mut cur = ty.clone();
    loop {
        match cur {
            Type::App(f, a) => {
                args.push((*a).clone());
                cur = (*f).clone();
            }
            other => {
                args.reverse();
                return (other, args);
            }
        }
    }
}

/// Kind of an App spine's head. For Con heads, we look up the
/// kind from a small set of well-known constructors. Returns None
/// for unknowns.
fn kind_of_head(state: &UnifyState, head: &Type) -> Option<Type> {
    match head {
        Type::Con(qn) => kind_of_known_con(qn),
        Type::Unif(id) => state.unif_kind(*id).cloned(),
        _ => None,
    }
}

/// Apply a kind to `n` arguments by peeling outer arrows. Returns
/// the residual kind, or None if there aren't enough arrows.
fn apply_kind(kind: &Type, n: usize) -> Option<Type> {
    if n == 0 {
        return Some(kind.clone());
    }
    match kind {
        Type::Fun(_, ret) => apply_kind(ret, n - 1),
        _ => None,
    }
}

/// `true` when `qn` names a Prim constructor that has kind `Type`.
fn is_known_type_kind_con(qn: &crate::typecheck_db::types::QName) -> bool {
    let module = qn.module.as_deref();
    let name = qn.name.as_str();
    matches!(module, Some("Prim"))
        && matches!(
            name,
            "Int" | "Number" | "String" | "Char" | "Boolean" | "Partial"
        )
}

/// Kind of a small set of well-known constructors. None for the
/// rest — we'd need a full kind registry for user types.
fn kind_of_known_con(qn: &crate::typecheck_db::types::QName) -> Option<Type> {
    use crate::typecheck_db::types::{prim_kind_type, prim_symbol};
    let module = qn.module.as_deref();
    let name = qn.name.as_str();
    let type_kind = || prim_kind_type();
    let row_kind = || Type::Fun(
        Arc::new(type_kind()),
        Arc::new(type_kind()),
    );
    match (module, name) {
        (Some("Prim"), "Array") | (Some("Prim"), "Record") => {
            // `Array :: Type -> Type`, `Record :: Row Type -> Type`.
            // We approximate both as `Type -> Type` for the bind-time
            // check (treats Record's arg as Type-kind, conservative).
            Some(row_kind())
        }
        (Some("Prim"), "Function") => Some(Type::Fun(
            Arc::new(type_kind()),
            Arc::new(Type::Fun(Arc::new(type_kind()), Arc::new(type_kind()))),
        )),
        (Some("Prim"), "Int" | "Number" | "String" | "Char" | "Boolean")
        | (Some("Prim"), "Partial") => Some(type_kind()),
        (Some("Prim"), "Symbol") => Some(type_kind()),
        (Some("Prim"), "Type") => Some(type_kind()),
        (_, _) if qn == &crate::typecheck_db::types::QName::qualified("Effect.Aff", "Aff") => {
            Some(row_kind())
        }
        (_, _) if qn == &crate::typecheck_db::types::QName::qualified("Effect", "Effect") => {
            Some(row_kind())
        }
        (_, _) if name == "Symbol" && module == Some("Prim") => Some(prim_symbol()),
        _ => None,
    }
}

/// `true` when two kinds are compatible enough for a bind. We use
/// structural equality after stripping outer Kinded wrappers, with
/// one relaxation: `Type::Var(_)` and `Type::Unif(_)` on either
/// side are treated as "unknown / agrees" (conservative). The aim
/// is to catch egregious mismatches (Type vs Type -> Type) without
/// false-rejecting on partial-info kinds.
fn kinds_compatible(expected: &Type, actual: &Type) -> bool {
    match (expected, actual) {
        // Any side being a kind variable / unif → accept.
        (Type::Var(_), _) | (_, Type::Var(_)) => true,
        (Type::Unif(_), _) | (_, Type::Unif(_)) => true,
        // Strip Kinded wrappers.
        (Type::Kinded(t, _), other) | (other, Type::Kinded(t, _)) => {
            kinds_compatible(t, other)
        }
        // Function kinds: arrows align.
        (Type::Fun(a1, b1), Type::Fun(a2, b2)) => {
            kinds_compatible(a1, a2) && kinds_compatible(b1, b2)
        }
        // App: zip spine.
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            kinds_compatible(f1, f2) && kinds_compatible(a1, a2)
        }
        // Cons: structural equality.
        (Type::Con(qn1), Type::Con(qn2)) => qn1 == qn2,
        // Everything else falls back to structural equality, which
        // is safe — kind types are tiny in practice.
        (e, a) => type_eq(e, a),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typecheck_db::types::QName;

    fn int() -> Type {
        crate::typecheck_db::types::prim_int()
    }

    fn bool_ty() -> Type {
        crate::typecheck_db::types::prim_boolean()
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
    fn expired_deadline_returns_timeout() {
        let mut s = UnifyState::new();
        // Arm with a deadline already in the past.
        let past = std::time::Instant::now() - std::time::Duration::from_secs(1);
        s.set_deadline(Some(past), 1000);
        assert!(s.deadline_exceeded());
        match s.unify(&int(), &int()) {
            Err(UnifyError::Timeout { budget_ms }) => assert_eq!(budget_ms, 1000),
            other => panic!("expected Timeout, got {other:?}"),
        }
    }

    #[test]
    fn future_deadline_does_not_fire() {
        let mut s = UnifyState::new();
        let future =
            std::time::Instant::now() + std::time::Duration::from_secs(60);
        s.set_deadline(Some(future), 60_000);
        assert!(!s.deadline_exceeded());
        s.unify(&int(), &int()).unwrap();
    }

    #[test]
    fn no_deadline_armed_disables_check() {
        let mut s = UnifyState::new();
        s.set_deadline(None, 0);
        assert!(!s.deadline_exceeded());
        s.unify(&int(), &int()).unwrap();
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
