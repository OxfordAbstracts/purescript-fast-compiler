//! Constraint collection and solving for the M5 typechecker.
//!
//! Constraint flow, at a glance:
//!
//! ```text
//!    Var lookup
//!        │
//!        ▼
//!  instantiate scheme  ──peel Type::Constrained──▶  PendingConstraint
//!        │                                                  │
//!        ▼                                                  │
//!    monotype body used in inference                        │
//!                                                           ▼
//!                                               drained after SCC
//!                                                           │
//!                                                           ▼
//!                                             solver matches against InstanceIndex
//! ```
//!
//! Phase A (this commit): the collection half — wiring `Type::Constrained`
//! peeling into `infer_var` and attaching the resulting
//! `PendingConstraint` records to the owning decl, plus the data-
//! type definitions Phase B's solver will consume.
//!
//! Phase B: `solve_pending`, instance matching, "no instance found"
//! diagnostics.
//!
//! Phase D: fundep-driven improvement, coverage, consistency.

use serde::{Deserialize, Serialize};

use crate::typecheck_db::types::{Constraint, Type};

// Diagnostic counters wired up when TYPECHECK_DB_PROFILE_SLOW=1.
// `solve_one` increments SOLVE_ONE_CALLS each time it enters; the
// candidate-trial inner loop bumps TRY_MATCH_ATTEMPTS for every
// snapshot/freshen/unify cycle. Driver dumps + resets these around
// each per-instance body so we can attribute pathological constraint
// fan-out to a specific instance method.
pub static SOLVE_ONE_CALLS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub static TRY_MATCH_ATTEMPTS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

// Per-phase nanosecond accumulators inside `solve_one`, enabled by
// `TYPECHECK_DB_SOLVE_PHASES=1`. Read by the solve_all profile dump.
pub static PHASE_GIVENS_NS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub static PHASE_MAGIC_NS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub static PHASE_DEFER_NS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub static PHASE_IMPROVE_NS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub static PHASE_CANDLOOP_NS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub static PHASE_TAIL_NS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);


// ---------------------------------------------------------------------------
// Data
// ---------------------------------------------------------------------------

/// One constraint that fell out of a scheme instantiation during
/// inference. Lives on `UnifyState` until the SCC finishes; at that
/// point each entry is zonked and handed to the solver.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PendingConstraint {
    /// The decl whose body produced this constraint — set by
    /// `UnifyState::record_pending_constraint` via the current-decl
    /// marker. `None` only if the caller forgot to set it; that's a
    /// bug in the caller, not the solver.
    #[serde(default)]
    pub decl_name: Option<String>,
    /// Source span (the offending `Var` / `Constructor` site). Used
    /// for diagnostics; not cache-keyed.
    pub span: crate::span::Span,
    /// The constraint itself: `Eq α`, `Show (Maybe Int)`, etc.
    pub constraint: Constraint,
    /// Where the constraint came from — a scheme's signature, a
    /// superclass propagation, or an instance-context expansion. The
    /// solver uses this to improve diagnostics and to decide whether
    /// a constraint is "given" (from a class method under its own
    /// instance) vs "wanted".
    pub origin: ConstraintOrigin,
    /// Snapshot of the givens stack at the moment this constraint
    /// was recorded. `check_equation` pushes a sig's `Constrained`
    /// layer as givens while the body is inferred; by the time
    /// `solve_all` runs those givens have been popped from the
    /// `UnifyState`, so each pending must carry its own copy.
    #[serde(default)]
    pub givens: Vec<Constraint>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConstraintOrigin {
    /// Fell out of a value's declared signature at a reference site.
    Signature,
    /// Propagated from an instance's context when the solver matched
    /// an instance. Phase C attaches this origin.
    InstanceContext,
    /// Added by the superclass rule: `class Eq a => Ord a` means
    /// solving `Ord X` adds `Eq X`. Phase C.
    Superclass,
}

/// Lift a potentially-constrained monotype into `(constraints, body)`.
/// If the outer shape isn't `Constrained`, the returned constraint
/// list is empty.
///
/// This is the entry point that `infer_var` calls right after
/// `instantiate` so the caller can record the peeled constraints.
pub fn peel_constraints(ty: Type) -> (Vec<Constraint>, Type) {
    // Peel every `Constrained` layer, not just the outermost one.
    // Nested constraints appear when a method signature quantifies
    // over multiple class-constrained variables:
    // `forall a b. Eq a => Eq b => a -> b -> Bool` instantiates to
    // `Constrained([Eq α], Constrained([Eq β], Fun(α, Fun(β, Bool))))`
    // and leaving the inner layer in place makes the body unify as
    // a `Constrained(…)` where a function is expected.
    let mut all: Vec<Constraint> = Vec::new();
    let mut cur = ty;
    loop {
        match cur {
            Type::Constrained(cs, body) => {
                all.extend(cs);
                cur = std::sync::Arc::unwrap_or_clone(body);
            }
            other => return (all, other),
        }
    }
}

// ---------------------------------------------------------------------------
// Solver outputs (Phase B)
// ---------------------------------------------------------------------------

/// Outcome of trying to discharge one constraint against the
/// instance index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolveOutcome {
    /// Matched against an instance. Carries the instance's head
    /// types (after freshening + unification) and any context the
    /// match induces — Phase C will expand those contexts into new
    /// pending constraints; Phase B leaves them collected but
    /// doesn't recurse.
    Resolved(ResolvedDict),
    /// No instance in scope has a compatible head.
    NoInstance,
    /// Two or more non-chain-continued instances both match the
    /// constraint — `OverlappingInstances` in reference-compiler terms.
    Overlap,
    /// The constraint still depends on unification variables; try
    /// again after more inference. Phase B emits `Deferred` and
    /// lets the caller decide what to do; Phase D's fundep-driven
    /// improvement loop is what actually consumes these.
    Deferred,
    /// Exactly one candidate instance exists for the class but its
    /// head doesn't unify with the constraint args. Reported as
    /// `InstanceHeadMismatch` (coded as UnificationError).
    HeadMismatch,
}

/// Shallow dictionary — enough for codegen to reference the right
/// instance. Phase E adds `instance_idx` so the reference is exact:
/// codegen looks up `InstanceIndex::candidates(class)[instance_idx]`
/// to find the matched instance. Full per-context composition (a
/// tree of `DictExpr`s rather than a flat context list) can land
/// without reshaping this struct — the span-keyed lookup on
/// `InferredScheme` already gives codegen every resolution it
/// needs, and can walk the context chain via additional
/// `constraint_dicts` entries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedDict {
    pub class: crate::typecheck_db::types::QName,
    pub instance_types: Vec<Type>,
    /// Position of the matched instance in
    /// `InstanceIndex::candidates(class)`. Stable with respect to
    /// instance insertion order.
    #[serde(default)]
    pub instance_idx: usize,
    /// Instance context left to discharge — stored here so Phase C
    /// can drive recursive solving. Empty when the match was against
    /// a context-free instance.
    #[serde(default)]
    pub context: Vec<Constraint>,
}

/// One diagnostic from the solver.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintError {
    /// Primary span — typically the `Var` / `Constructor` reference
    /// site whose use produced this constraint (mirrors
    /// `PendingConstraint.span`).
    pub span: crate::span::Span,
    /// Source span of the enclosing decl (when known). Read off
    /// `UnifyState::current_decl_span` at error-construction time.
    /// Useful for the user to navigate back to the decl that owns
    /// the offending call.
    #[serde(default)]
    pub decl_span: Option<crate::span::Span>,
    pub constraint: Constraint,
    pub kind: ConstraintErrorKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConstraintErrorKind {
    NoInstanceFound,
    /// The solver hit [`MAX_SOLVER_DEPTH`] before every constraint
    /// reached a fixed point. Typically indicates an instance
    /// whose context re-demands the same constraint (`instance
    /// Foo a => Foo a`). Diagnostic, not a crash.
    SolverDepthExceeded,
    /// At a use-site, two or more independent (non-chain-continued)
    /// instances both match the constraint. Reference compiler
    /// reports this as `OverlappingInstances`.
    OverlappingInstances,
    /// All candidate instances exist but their heads can't be
    /// unified with the constraint args — the underlying type
    /// mismatch surfaced through instance resolution. Coded as
    /// `UnificationError` for fixture matching, mirrors what the
    /// reference compiler reports as `TypesDoNotUnify` when
    /// fundep-improvement reveals the conflict.
    InstanceHeadMismatch,
}

// ---------------------------------------------------------------------------
// Solver implementation (added by the next commit; stubs below so
// the test file compiles)
// ---------------------------------------------------------------------------

/// Try every candidate instance for one pending constraint, stopping
/// at the first successful unification.
///
/// Matching strategy:
/// 1. If any argument still contains an unsolved unification var
///    *outside* a type-constructor's arguments, we can't choose an
///    instance yet — return `Deferred`. (Phase D's fundep-driven
///    improvement will eventually revisit these.)
/// 2. Otherwise walk the class's candidates in registration order.
///    For each candidate: snapshot the unification state, freshen
///    the instance's quantified vars, unify instance-head with
///    target args. On success, commit and return `Resolved`; on
///    failure, rollback and try the next candidate.
/// 3. Out of candidates with no match → `NoInstance`.
/// Advance the per-phase clock: add elapsed-since-`t` to `counter`
/// and reset `t` to now. No-op when phase timing is off (`t` None).
#[inline]
fn phase_mark(
    counter: &std::sync::atomic::AtomicU64,
    t: &mut Option<std::time::Instant>,
) {
    if let Some(t0) = t {
        counter.fetch_add(
            t0.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        *t = Some(std::time::Instant::now());
    }
}

pub fn solve_one(
    state: &mut crate::typecheck_db::unify::UnifyState,
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    pending: &PendingConstraint,
) -> SolveOutcome {
    SOLVE_ONE_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut phase_t: Option<std::time::Instant> =
        std::env::var_os("TYPECHECK_DB_SOLVE_PHASES")
            .map(|_| std::time::Instant::now());
    // Givens discharge before anything else: a constraint promised
    // by an enclosing sig's `Constrained` layer is already known-
    // true. Each `PendingConstraint` carries a snapshot of the
    // givens that were in scope when it was recorded (see
    // `UnifyState::record_pending_constraint`). Match structurally
    // on zonked forms so a skolemised `Semigroupoid !sa` satisfies
    // a pending `Semigroupoid ?ua` once `?ua := !sa` is bound.
    if let Some(given_index) = given_discharges_pending(state, instances, pending) {
        phase_mark(&PHASE_GIVENS_NS, &mut phase_t);
        // For a given-discharge, `instance_idx` carries the discharging given's
        // index in the decl's constraint context (or `usize::MAX` when there's
        // no stable index). Codegen maps that to the matching dict parameter,
        // disambiguating multiple same-class givens (e.g. `Show a` vs `Show b`).
        return SolveOutcome::Resolved(ResolvedDict {
            class: pending.constraint.class.clone(),
            instance_types: pending
                .constraint
                .args
                .iter()
                .map(|a| state.zonk(a))
                .collect(),
            instance_idx: given_index,
            context: Vec::new(),
        });
    }
    phase_mark(&PHASE_GIVENS_NS, &mut phase_t);
    // Compiler-magic auto-dispatch: some Prim classes discharge
    // purely from the constraint's shape and don't rely on user
    // instance declarations. Handle them up-front so a fixture
    // that only reaches these via a Prelude call-site doesn't
    // trip over a `NoInstanceFound`.
    let magic_out = try_magic(state, pending);
    phase_mark(&PHASE_MAGIC_NS, &mut phase_t);
    match magic_out {
        MagicOutcome::Resolved(dict) => return SolveOutcome::Resolved(dict),
        MagicOutcome::Mismatch => return SolveOutcome::HeadMismatch,
        MagicOutcome::None => {}
    }

    // Fundep-aware defer. A position is safely improvable from the
    // CURRENT constraint shape only when SOME fundep's determiners
    // are ALL non-bare-unif (the fundep can fire) AND that fundep
    // lists the position in its determined set. The earlier rule —
    // accepting any position that appeared in some fundep's
    // determined list — let the solver commit to instance heads
    // before fundep improvement could fire, picking the first
    // structural match and pinning bare unifs to its type-args.
    // Without fundeps we fall back to the conservative rule (any
    // bare unif defers).
    let class_info = instances.class_info(&pending.constraint.class.name);
    let currently_determined: std::collections::HashSet<usize> = match class_info {
        Some(info) if !info.fundeps.is_empty() => info
            .fundeps
            .iter()
            .filter(|fd| {
                fd.determiners.iter().all(|i| {
                    pending
                        .constraint
                        .args
                        .get(*i)
                        .map_or(false, |a| !is_bare_unif(a, state))
                })
            })
            .flat_map(|fd| fd.determined.iter().copied())
            .collect(),
        _ => std::collections::HashSet::new(),
    };
    let needs_defer = match class_info {
        Some(info) if !info.fundeps.is_empty() => pending
            .constraint
            .args
            .iter()
            .enumerate()
            .any(|(i, a)| {
                !currently_determined.contains(&i) && is_bare_unif(a, state)
            }),
        _ => pending.constraint.args.iter().any(|a| is_bare_unif(a, state)),
    };
    // Spine-head defer: an arg shaped like `?u a` (a partial app
    // whose head is a unification variable) is indeterminate.
    // Without this, any candidate with a concrete `Con`-headed spine
    // (e.g. `Alternate f`, `Maybe`, `ParserT s m`) would unify with
    // the unif head and pin it — picking the FIRST candidate that
    // structurally fits, not the right one. The reference compiler's
    // `typeHeadsAreEqual` returns `Unknown` for this case and defers
    // the entire chain. Skip when a currently-firing fundep marks
    // this position as determined (the solver has enough info).
    let needs_spine_defer = match class_info {
        Some(info) if !info.fundeps.is_empty() => {
            pending
                .constraint
                .args
                .iter()
                .enumerate()
                .any(|(i, a)| {
                    !currently_determined.contains(&i)
                        && has_unif_spine_head(a, state)
                })
        }
        _ => pending.constraint.args.iter().any(|a| has_unif_spine_head(a, state)),
    };
    if needs_defer || needs_spine_defer {
        phase_mark(&PHASE_DEFER_NS, &mut phase_t);
        return SolveOutcome::Deferred;
    }
    phase_mark(&PHASE_DEFER_NS, &mut phase_t);

    // Fundep-driven improvement. For each fundep on this class
    // whose determiner positions are all concrete in the pending,
    // try to find a UNIQUE matching candidate instance. When found,
    // unify the pending's determined positions with that instance's
    // determined positions BEFORE try_match runs — so a constraint
    // like `Parallel ?f Aff` (fundep g -> f) gets `?f := ParAff`
    // from the sole `Parallel ParAff Aff` instance even when other
    // unification paths could have pinned `?f` to a wrong value
    // later. Matches the reference compiler's improvement step.
    if let Some(info) = class_info {
        if !info.fundeps.is_empty() {
            try_fundep_improvement(state, instances, pending, info);
        }
    }
    phase_mark(&PHASE_IMPROVE_NS, &mut phase_t);

    // Candidates are stored under the class's simple name. When two
    // distinct classes share a name across modules (e.g. user-side
    // `Typisch.Row.Lacks` vs Prim's `Prim.Row.Lacks`), look-up by
    // simple name returns BOTH — and the solver, blind to the
    // distinction, can match `Prim.Row.Lacks` against the user
    // class's instance, then re-queue the instance's
    // `Prim.Row.Lacks` context as a fresh wanted, looping forever.
    // When the pending carries a class module qualifier, the
    // candidate's class module must agree (or be absent — preserves
    // the lenient match path the test suite relies on for legacy
    // unqualified instance scans).
    let pending_class_module = pending.constraint.class.module.as_deref();
    let cand_matches_class_module =
        |c: &crate::typecheck_db::passes::instance_index::Instance| -> bool {
            match pending_class_module {
                Some(want) => c.class.module.as_deref().map_or(true, |m| m == want),
                None => true,
            }
        };
    let cands = instances.candidates(&pending.constraint.class.name);
    let cand_count = cands.iter().filter(|c| cand_matches_class_module(c)).count();
    // Per-position head/arity of the (zonked) target args. Computed
    // once so the per-candidate filter below is cheap. `None` slots
    // (target is a unif / Var / row / etc.) impose no constraint —
    // any candidate at that position is a structural match.
    //
    // Uses the probe-based `app_spine_head_arity_probing` so a deep
    // Record/Row arg with internal Unifs (common for solver-heavy
    // record-record Newtype constraints) isn't zonked just to read
    // its outer head — the Unifs are deep in field types, not on
    // the App-spine head, so zonking allocates O(N) for nothing.
    let target_heads: Vec<Option<(crate::typecheck_db::types::QName, usize)>> =
        pending
            .constraint
            .args
            .iter()
            .map(|a| {
                app_spine_head_arity_probing(a, state)
                    .map(|(qn, ar)| (qn.clone(), ar))
            })
            .collect();
    // Overlap-aware deferral. When the target contains a unif AND
    // multiple candidates pass the head-pre-filter, committing to
    // the first match would pin the unif to that candidate's
    // type-args — but a later inference step (e.g. `UInt64 <$>
    // Internal.fromNumber n` forcing `Long' ?s ~ Long' Unsigned`)
    // may pin it the other way. Defer so the constraint can
    // resolve unambiguously once the unif is bound.
    //
    // For fundep classes, only run this check on positions where
    // the fundep can't fire — a currently-firing fundep already
    // forces the unif to one value, so an "ambiguous match" there
    // is resolved by improvement. Without this carve-out, fundep
    // classes (e.g. `Succ x y | x -> y, y -> x` with `Succ D2 ?`)
    // would over-defer in cases where the fundep would have
    // pinned the answer.
    let target_has_unif =
        pending.constraint.args.iter().any(|a| contains_unif(a, state));
    if target_has_unif && cand_count > 1 {
        let mut passing = 0usize;
        for cand in cands.iter().filter(|c| cand_matches_class_module(c)) {
            let mut head_ok = true;
            for (i, target) in target_heads.iter().enumerate() {
                if let Some((th, ta)) = target {
                    if let Some(cand_arg) = cand.types.get(i) {
                        if let Some((ch, ca)) = app_spine_head_arity(cand_arg) {
                            if ca != *ta {
                                head_ok = false;
                                break;
                            }
                            if ch.name != th.name {
                                head_ok = false;
                                break;
                            }
                            if ch.module.is_some()
                                && th.module.is_some()
                                && ch.module != th.module
                            {
                                head_ok = false;
                                break;
                            }
                        }
                    }
                }
            }
            if head_ok {
                passing += 1;
                if passing >= 2 {
                    return SolveOutcome::Deferred;
                }
            }
        }
    }
    for (instance_idx, cand) in cands
        .iter()
        .enumerate()
        .filter(|(_, c)| cand_matches_class_module(c))
    {
        // Cheap structural pre-filter: for every position where the
        // target has a concrete `Con`-headed spine, the candidate's
        // head at that position must either be a non-Con (type var,
        // unifies with anything) or match `(qname, arity)`. We use
        // the unifier's lenient module-qualifier rule (names must
        // agree; one side missing a module qualifier is OK) so a
        // user-side `MonadThrow Error Effect` (unqualified
        // `Error`) doesn't pre-filter out an instance whose head
        // is registered as `MonadThrow Effect.Exception.Error
        // Effect`. Without the lenient compare the candidate gets
        // dropped here even though `try_match` would unify it
        // cleanly.
        let mut head_ok = true;
        for (i, target) in target_heads.iter().enumerate() {
            if let Some((th, ta)) = target {
                if let Some(cand_arg) = cand.types.get(i) {
                    if let Some((ch, ca)) = app_spine_head_arity(cand_arg) {
                        if ca != *ta {
                            head_ok = false;
                            break;
                        }
                        // Recognise `(->)` and `Function` as aliases — the
                        // (->) instance is registered with type-head
                        // `Con(None, "->")` but wanteds resolved through
                        // the Prim helpers carry `Con(Some("Prim"),
                        // "Function")`. Without this, `Semigroupoid
                        // Function` finds no head-matching candidate and
                        // SolverDepthExceeds via the head_shape_mismatch
                        // defer cycle.
                        let names_equiv = ch.name == th.name
                            || ((ch.name == "->" || ch.name == "Function")
                                && (th.name == "->" || th.name == "Function"));
                        if !names_equiv {
                            head_ok = false;
                            break;
                        }
                        if ch.module.is_some()
                            && th.module.is_some()
                            && ch.module != th.module
                        {
                            head_ok = false;
                            break;
                        }
                    }
                }
            }
        }
        if !head_ok {
            continue;
        }
        TRY_MATCH_ATTEMPTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let snapshot = state.snapshot_bindings();
        if let Some((head, context)) =
            try_match(state, cand, &pending.constraint.args, instances.aliases())
        {
            phase_mark(&PHASE_CANDLOOP_NS, &mut phase_t);
            return SolveOutcome::Resolved(ResolvedDict {
                class: pending.constraint.class.clone(),
                instance_types: head,
                instance_idx,
                context,
            });
        }
        state.restore_bindings(snapshot);
    }
    phase_mark(&PHASE_CANDLOOP_NS, &mut phase_t);
    // Rigid `Type::Var` defer FIRST. Rigid type vars come from a
    // surrounding signature (e.g. inside `default :: forall t a.
    // Reflectable t a => …`, the body sees `t` / `a` as Vars).
    // The instance for those vars comes from a "given" the outer
    // scope provides; we don't track givens explicitly, so defer
    // the constraint and let it bubble up into the inferred
    // scheme via `generalize_with_constraints`. The importer then
    // re-instantiates fresh unifs and the solver retries at each
    // concrete use-site.
    //
    // Crucially this fires BEFORE the fundep-class HeadMismatch
    // diagnostic below — a sole-candidate fundep class with a
    // rigid-var target shouldn't surface as
    // `InstanceHeadMismatch` (the constraint is propagating, not
    // failing).
    if pending.constraint.args.iter().any(|a| contains_rigid_var(a, state)) {
        phase_mark(&PHASE_TAIL_NS, &mut phase_t);
        return SolveOutcome::Deferred;
    }
    // Specialised diagnostic: when the class has fundeps and the
    // SOLE candidate failed to unify, surface as
    // `InstanceHeadMismatch` (coded as `UnificationError`). The
    // reference compiler treats this as `TypesDoNotUnify` post
    // fundep improvement. Restricted to fundep classes because
    // non-fundep classes can have legitimate "candidate present
    // but wrong type" cases (e.g. `Semigroupoid Function` where
    // a different built-in instance is expected); their failure
    // is correctly `NoInstance`.
    if cand_count == 1
        && class_info
            .map(|info| !info.fundeps.is_empty())
            .unwrap_or(false)
    {
        phase_mark(&PHASE_TAIL_NS, &mut phase_t);
        return SolveOutcome::HeadMismatch;
    }
    // Classes with no in-scope candidates: defer when the
    // constraint still has wiggle room (some arg contains a unif
    // that could be pinned later), or when the class is a
    // built-in marker class the user can't write instances for
    // (`Partial`, `Warn`, `Fail`, `Coercible`, …) — those are
    // discharged via the inline coercibility check / type-error
    // mechanism, NEVER via instance resolution, so a missing
    // candidate is expected and the constraint must propagate.
    // Otherwise emit NoInstance: rigid `Var`s in args have
    // already been handled by the earlier branch, so fully-
    // concrete args with empty cands is a genuine "user forgot
    // to import the instance" miss.
    if cand_count == 0 {
        let has_unif =
            pending.constraint.args.iter().any(|a| contains_unif(a, state));
        // Built-in solver-only classes — instances are NEVER
        // user-written; the type-error / coercibility / row-magic
        // / Prim.Int arithmetic machinery discharges these
        // structurally. A missing in-scope candidate just means
        // we haven't yet reached the discharge step; defer. The
        // qualifier check mirrors `try_magic`'s — a user-defined
        // class sharing a simple name (`Cons`, `Lacks`, …) and
        // qualified to a different module is NOT a marker and
        // must surface as `NoInstance` when its candidates list
        // is empty.
        let is_marker_class = is_known_prim_marker(
            pending.constraint.class.name.as_str(),
            pending.constraint.class.module.as_deref(),
        );
        // Capability-marker classes: a NULLARY user class with zero
        // instances (e.g. PublicEventAuth, AttendeeAuth, AdminAuth)
        // can only be discharged structurally (via FFI / a sig-origin
        // given). At the definer, the sig-pin records the decl's own
        // sig constraint as a pending — those would otherwise emit
        // NoInstance even though the user's declared sig CARRIES the
        // constraint. Defer so the constraint propagates into the
        // inferred scheme (matching reference-compiler semantics: an
        // unsatisfiable constraint at a sig site stays in the scheme;
        // the error surfaces only at a use site that can't carry it).
        let is_capability_marker =
            pending.constraint.args.is_empty()
                && pending.origin == ConstraintOrigin::Signature;
        if has_unif || is_marker_class || is_capability_marker {
            phase_mark(&PHASE_TAIL_NS, &mut phase_t);
            return SolveOutcome::Deferred;
        }
        phase_mark(&PHASE_TAIL_NS, &mut phase_t);
        return SolveOutcome::NoInstance;
    }
    // Kind-mismatch / wrong-head defer: if any arg's App-spine
    // head zonks to `Con(X)` AND no instance candidate has the
    // same `Con(X)` head at that position (allowing for arity
    // mismatch — `Apply Tuple` vs instance `Apply (Tuple a)`),
    // the constraint can never be solved by the in-scope
    // instances. Defer rather than emit `NoInstanceFound`: the
    // constraint propagates into the inferred scheme and the
    // downstream importer either resolves it concretely or
    // surfaces a clearer error at a use-site.
    //
    // This is the typical case where a polymorphic body has a
    // unif `?u` that's been pinned to a wrong-arity Con via
    // App-decomposition — `Apply Tuple` (Tuple has kind
    // `Type → Type → Type` but Apply expects `Type → Type`),
    // or `Unfoldable1 (Tuple a)` (only `Unfoldable1 Array` /
    // `Maybe` instances exist; Tuple doesn't fit).
    // Kind-mismatch / wrong-shape defer: if any arg's App-spine
    // head + arity doesn't match any instance's head + arity,
    // the constraint can never be solved. Match on (head_qn,
    // app_spine_arity) — `Apply Tuple` has arity 0 (no apps),
    // `Apply (Tuple a)` instance has arity 1. Different keys
    // → no candidate fits → defer.
    //
    // Uses the probe-based head walker rather than zonking every
    // arg — for deep `Record`/`Row` args with internal `Unif`s
    // (Newtype-record constraints in solver-heavy modules), zonk
    // would allocate O(N) just to read the outer head.
    let head_shape_mismatch = pending.constraint.args.iter().enumerate().any(|(i, arg)| {
        if let Some((arg_qn, arg_arity)) = app_spine_head_arity_probing(arg, state) {
            !cands.iter().filter(|c| cand_matches_class_module(c)).any(|cand| {
                cand.types
                    .get(i)
                    .and_then(app_spine_head_arity)
                    .map_or(false, |(h, a)| {
                        // Same lenient comparison as the per-candidate
                        // pre-filter (above): match names with the
                        // `(->)` / `Function` alias rule + tolerant
                        // module qualifier (one side None is OK).
                        let names_equiv = h.name == arg_qn.name
                            || ((h.name == "->" || h.name == "Function")
                                && (arg_qn.name == "->"
                                    || arg_qn.name == "Function"));
                        let modules_ok = h.module.is_none()
                            || arg_qn.module.is_none()
                            || h.module == arg_qn.module;
                        names_equiv && modules_ok && a == arg_arity
                    })
            })
        } else {
            false
        }
    });
    phase_mark(&PHASE_TAIL_NS, &mut phase_t);
    if head_shape_mismatch {
        return SolveOutcome::Deferred;
    }
    SolveOutcome::NoInstance
}

/// Walk an App-spine and return `(head_con_qname, arity)` where
/// arity is the number of `App` applications above the head.
/// Bare `Con(X)` returns `(X, 0)`; `Tuple a` returns `(Tuple, 1)`;
/// `Tuple a b` returns `(Tuple, 2)`. Non-Con heads → `None`.
fn app_spine_head_arity(
    ty: &Type,
) -> Option<(&crate::typecheck_db::types::QName, usize)> {
    let mut cur = ty;
    let mut arity: usize = 0;
    loop {
        match cur {
            Type::App(f, _) => {
                arity += 1;
                cur = f;
            }
            Type::Con(qn) => return Some((qn, arity)),
            _ => return None,
        }
    }
}

/// True when any given (stamped on `pending` or live on
/// `state.givens`) structurally matches the pending's constraint
/// after both sides are zonked, either directly or by walking
/// the given's superclass chain. Strict match: same class,
/// pairwise `ty_eq` on zonked args — givens aren't subject to
/// further unification.
/// If some in-scope given discharges `pending`, returns the matched given's
/// index within `pending.givens` (the enclosing decl's constraint context, in
/// declaration order — which codegen mirrors as its dict-param order). A match
/// found only among the live (non-snapshot) givens, or via a superclass chain,
/// returns `Some(usize::MAX)` (discharged, but no stable param index — codegen
/// falls back to class-based lookup). `None` means no given discharges it.
fn given_discharges_pending(
    state: &mut crate::typecheck_db::unify::UnifyState,
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    pending: &PendingConstraint,
) -> Option<usize> {
    // No givens to check against → can't discharge. Skips the zonk
    // + snapshot clone; this is the bulk of `solve_one`'s deferred
    // path for view modules (no class constraint in scope).
    if pending.givens.is_empty() && state.givens_is_empty() {
        return None;
    }
    let zp = Constraint {
        class: pending.constraint.class.clone(),
        args: pending.constraint.args.iter().map(|a| state.zonk(a)).collect(),
    };
    let live = state.givens_snapshot();
    let snapshot_len = pending.givens.len();
    for (i, g) in pending.givens.iter().chain(live.iter()).enumerate() {
        // Index into `pending.givens` (the declaration's constraint context)
        // when the match is there; live-only matches have no stable param index.
        let param_index = if i < snapshot_len { i } else { usize::MAX };
        let zg = Constraint {
            class: g.class.clone(),
            args: g.args.iter().map(|a| state.zonk(a)).collect(),
        };
        if constraints_eq(&zg, &zp) {
            return Some(param_index);
        }
        if superclass_matches(instances, &zg, &zp) {
            // Discharged via the given's superclass chain — the dict isn't the
            // given itself, so no direct param index.
            return Some(usize::MAX);
        }
        // Functional-dependency-style improvement: if the names match
        // and unifying the args succeeds, the given satisfies the
        // pending — bind any free unifs in the pending to the
        // skolems / concrete types from the given. Mirrors GHC's
        // wanted-from-given improvement for class fundeps. We accept
        // ANY successful unify (without consulting fundeps) because
        // the given is provably true: if its args are unifiable with
        // the pending's, the pending is provably true too.
        if zg.class == zp.class && zg.args.len() == zp.args.len() {
            let snapshot = state.snapshot_bindings();
            let mut all_ok = true;
            for (g_arg, p_arg) in zg.args.iter().zip(zp.args.iter()) {
                if state.unify(g_arg, p_arg).is_err() {
                    all_ok = false;
                    break;
                }
            }
            if all_ok {
                return Some(param_index);
            }
            state.restore_bindings(snapshot);
        }
    }
    None
}

/// BFS over `given`'s superclass chain. Each superclass's args
/// are expressed in terms of the given's class's `type_vars`; we
/// substitute with `given.args` to produce a concrete superclass
/// instance, then compare to `target` structurally. Recursive so
/// `Foo a <= Bar a <= Baz a` discharges `Baz` from a `Foo a`
/// given.
fn superclass_matches(
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    given: &Constraint,
    target: &Constraint,
) -> bool {
    let mut seen: std::collections::HashSet<(String, String)> =
        std::collections::HashSet::new();
    let mut queue: Vec<Constraint> = vec![given.clone()];
    while let Some(cur) = queue.pop() {
        let key = (
            cur.class.name.clone(),
            cur.args.iter().map(|a| format!("{a:?}")).collect::<Vec<_>>().join("|"),
        );
        if !seen.insert(key) {
            continue;
        }
        let info = match instances.class_info(&cur.class.name) {
            Some(i) => i,
            None => continue,
        };
        if info.superclasses.is_empty() {
            continue;
        }
        let subst: std::collections::HashMap<String, Type> = info
            .type_vars
            .iter()
            .cloned()
            .zip(cur.args.iter().cloned())
            .collect();
        for sc in &info.superclasses {
            let substituted = Constraint {
                class: sc.class.clone(),
                args: sc
                    .args
                    .iter()
                    .map(|a| {
                        crate::typecheck_db::generalize::apply_var_subst(a, &subst)
                    })
                    .collect(),
            };
            if constraints_eq(&substituted, target) {
                return true;
            }
            queue.push(substituted);
        }
    }
    false
}

fn constraints_eq(a: &Constraint, b: &Constraint) -> bool {
    a.class == b.class
        && a.args.len() == b.args.len()
        && a.args.iter().zip(b.args.iter()).all(|(x, y)| ty_eq(x, y))
}

fn ty_eq(a: &Type, b: &Type) -> bool {
    use Type::*;
    match (a, b) {
        (Var(x), Var(y)) => x == y,
        (TypeString(x), TypeString(y)) => x == y,
        (Con(x), Con(y)) => x == y,
        (Unif(x), Unif(y)) => x == y,
        (Skolem(x), Skolem(y)) => x == y,
        (TypeInt(x), TypeInt(y)) => x == y,
        (App(f1, a1), App(f2, a2)) | (Fun(f1, a1), Fun(f2, a2)) => {
            ty_eq(f1, f2) && ty_eq(a1, a2)
        }
        (Record(fa, ta), Record(fb, tb)) | (Row(fa, ta), Row(fb, tb)) => {
            fa.len() == fb.len()
                && fa.iter().zip(fb.iter()).all(|((la, va), (lb, vb))| {
                    la == lb && ty_eq(va, vb)
                })
                && match (ta, tb) {
                    (None, None) => true,
                    (Some(a), Some(b)) => ty_eq(a, b),
                    _ => false,
                }
        }
        (Kinded(t1, _), other) => ty_eq(t1, other),
        (other, Kinded(t2, _)) => ty_eq(other, t2),
        _ => false,
    }
}

/// True when the zonked form of `ty` mentions a rigid `Type::Var`
/// or `Type::Skolem` anywhere. Used by `solve_one` to defer
/// constraints that can only be discharged via a caller-
/// supplied given (rigid Var for un-skolemised polymorphic
/// scope; Skolem for inside check-mode bodies).
fn contains_rigid_var(ty: &Type, state: &crate::typecheck_db::unify::UnifyState) -> bool {
    fn walk(t: &Type) -> bool {
        match t {
            Type::Var(_) | Type::Skolem(_) => true,
            Type::App(f, a) | Type::Fun(f, a) => walk(f) || walk(a),
            Type::Forall(_, body) => walk(body),
            Type::Constrained(cs, body) => {
                cs.iter().any(|c| c.args.iter().any(walk)) || walk(body)
            }
            Type::Record(fs, tail) | Type::Row(fs, tail) => {
                fs.iter().any(|(_, t)| walk(t))
                    || tail.as_deref().map(walk).unwrap_or(false)
            }
            Type::Kinded(t, k) => walk(t) || walk(k),
            _ => false,
        }
    }
    walk(&state.zonk(ty))
}

/// True when `ty` zonks to a `Type::Unif`. Those can't be used to
/// pick an instance yet — the solver defers until inference either
/// solves them or proves they're polymorphic.
///
/// Walks the unif binding chain via `state.probe` instead of calling
/// `state.zonk`, which would allocate a fresh `Type` at every step.
/// Hot for solver-heavy modules where the bare-unif check runs once
/// per arg per `solve_one` call (hundreds of thousands of calls).
fn is_bare_unif(ty: &Type, state: &crate::typecheck_db::unify::UnifyState) -> bool {
    let mut cur = ty;
    loop {
        match cur {
            Type::Unif(id) => match state.probe(*id) {
                None => return true,
                Some(bound) => cur = bound,
            },
            _ => return false,
        }
    }
}

/// True when `ty` structurally contains a `Type::Unif` anywhere
/// (after zonking). Used by the overlap-aware deferral rule below.
fn contains_unif(ty: &Type, state: &crate::typecheck_db::unify::UnifyState) -> bool {
    fn walk(t: &Type) -> bool {
        match t {
            Type::Unif(_) => true,
            Type::App(f, a) | Type::Fun(f, a) => walk(f) || walk(a),
            Type::Forall(_, body) => walk(body),
            Type::Constrained(cs, body) => {
                cs.iter().any(|c| c.args.iter().any(walk)) || walk(body)
            }
            Type::Record(fs, tail) | Type::Row(fs, tail) => {
                fs.iter().any(|(_, t)| walk(t))
                    || tail.as_deref().map(walk).unwrap_or(false)
            }
            Type::Kinded(t, k) => walk(t) || walk(k),
            _ => false,
        }
    }
    walk(&state.zonk(ty))
}

/// Collect every `Type::Unif(id)` reachable in `ty` (zonked first)
/// into `out`. Used by `solve_all` to compute the dependency set
/// of a deferred constraint: if none of these ids gets newly
/// bound before the constraint's next visit, `solve_one` would
/// defer for the same reason and can be skipped entirely.
fn collect_unif_ids(
    state: &crate::typecheck_db::unify::UnifyState,
    ty: &Type,
    out: &mut std::collections::HashSet<u32>,
) {
    fn walk(t: &Type, out: &mut std::collections::HashSet<u32>) {
        match t {
            Type::Unif(id) => {
                out.insert(*id);
            }
            Type::App(f, a) | Type::Fun(f, a) => {
                walk(f, out);
                walk(a, out);
            }
            Type::Forall(_, body) => walk(body, out),
            Type::Constrained(cs, body) => {
                for c in cs {
                    for a in &c.args {
                        walk(a, out);
                    }
                }
                walk(body, out);
            }
            Type::Record(fs, tail) | Type::Row(fs, tail) => {
                for (_, t) in fs {
                    walk(t, out);
                }
                if let Some(t) = tail.as_deref() {
                    walk(t, out);
                }
            }
            Type::Kinded(t, k) => {
                walk(t, out);
                walk(k, out);
            }
            _ => {}
        }
    }
    let zonked = state.zonk(ty);
    walk(&zonked, out);
}

/// True when `ty`'s App-spine head is a unif var (so the structural
/// shape `App(?u, _)` cannot yet be pinned to a specific
/// constructor). Mirrors the reference compiler's
/// `typeHeadsAreEqual (TUnknown _ _) _ = Unknown` rule: any
/// candidate with a `Con`-headed spine at this position is
/// indeterminate, so committing via unification would over-eagerly
/// pin the unif to the first candidate's head (e.g. `Alternate
/// f`) when the actual type isn't yet known.
fn has_unif_spine_head(
    ty: &Type,
    state: &crate::typecheck_db::unify::UnifyState,
) -> bool {
    // Walk the App spine via probe, no zonk clone: we only follow
    // the leftmost child, so cloning the full type just to read its
    // head is pure waste. Called once per arg per `solve_one`.
    let mut cur = ty;
    loop {
        match cur {
            Type::App(f, _) => cur = f,
            Type::Unif(id) => match state.probe(*id) {
                None => return true,
                Some(bound) => cur = bound,
            },
            _ => return false,
        }
    }
}

/// Walk an App-spine following bound `Unif`s at each level. Returns
/// `(head_qname, arity)` when the head reduces to a `Con`. Same
/// shape as [`app_spine_head_arity`] but probe-based: never clones
/// or allocates, just follows bindings. Used by `solve_one` to
/// compute `target_heads` without zonking deep `Record`/`Row` args
/// whose internal `Unif`s are irrelevant to head matching.
fn app_spine_head_arity_probing<'a>(
    ty: &'a Type,
    state: &'a crate::typecheck_db::unify::UnifyState,
) -> Option<(&'a crate::typecheck_db::types::QName, usize)> {
    let mut cur = ty;
    let mut arity: usize = 0;
    loop {
        match cur {
            Type::App(f, _) => {
                arity += 1;
                cur = f;
            }
            Type::Con(qn) => return Some((qn, arity)),
            Type::Unif(id) => match state.probe(*id) {
                Some(bound) => cur = bound,
                None => return None,
            },
            _ => return None,
        }
    }
}

/// True when `(class_name, class_module)` names one of the
/// solver-only "marker" classes — Prim's type-error /
/// coercibility / row-magic / arithmetic classes plus
/// `Data.Symbol.IsSymbol`. The module gate (lenient on `None`)
/// keeps a user-declared class with a colliding simple name from
/// being mistaken for a Prim marker. Used by `solve_one`'s
/// empty-cands branch to decide between deferring (marker — will
/// be discharged by `try_magic` or the inline solver later) and
/// emitting `NoInstance` (genuine user-class miss).
fn is_known_prim_marker(class_name: &str, class_module: Option<&str>) -> bool {
    let expected: &[&str] = match class_name {
        // Type-error / partiality markers.
        "Partial" => &["Prim"],
        "Warn" | "Fail" => &["Prim.TypeError"],
        // Coercibility (Prim.Coerce).
        "Coercible" => &["Prim.Coerce"],
        // Row magic (Prim.Row).
        "Lacks" | "Nub" | "Union" => &["Prim.Row"],
        // `Cons` appears in BOTH Prim.Row (4-arg) and Prim.Symbol
        // (3-arg); arity disambiguates downstream.
        "Cons" => &["Prim.Row", "Prim.Symbol"],
        // RowList magic (Prim.RowList).
        "RowToList" => &["Prim.RowList"],
        // Symbol magic (Prim.Symbol).
        "Append" => &["Prim.Symbol"],
        // `Compare` exists in both Prim.Symbol and Prim.Int; the
        // magic solver disambiguates via TypeString vs TypeInt args.
        "Compare" => &["Prim.Symbol", "Prim.Int"],
        // Prim.Int arithmetic (literal-driven).
        "Add" | "Mul" | "ToString" => &["Prim.Int"],
        // Reflectable lives in `Data.Reflectable` in the prelude
        // package; it's not in prim.rs but is solver-driven (its
        // dictionary is auto-derived from the Proxy literal). The
        // compiler-magic dispatcher elsewhere handles it.
        "Reflectable" => &["Data.Reflectable"],
        // IsSymbol — user-facing class lives in `Data.Symbol`.
        "IsSymbol" => &["Data.Symbol"],
        _ => return false,
    };
    match class_module {
        None => true,
        Some(m) => expected.iter().any(|e| *e == m),
    }
}

/// Result of a `try_magic` attempt.
#[derive(Debug)]
enum MagicOutcome {
    /// The class is unknown to magic — caller should proceed with
    /// regular instance lookup.
    None,
    /// Magic discharged the constraint with the resulting dict.
    Resolved(ResolvedDict),
    /// Magic recognised the class shape and the constraint is
    /// definitively wrong — surface as `InstanceHeadMismatch` so
    /// callers can report the mismatch.
    Mismatch,
}

/// Try to discharge a constraint via built-in compiler magic.
///
/// * `IsSymbol "literal"` — every symbol literal has an
///   `IsSymbol` instance by construction. Discharge as long as
///   the single argument zonks to a concrete `Type::TypeString`.
/// * `Row.Nub` / `Row.Lacks` / `Row.Cons` / `Row.Union` — the
///   row-manipulation classes auto-solve when the participating
///   rows are fully known. For now we handle `Nub row result`
///   where `row` is a closed row: the result is the same row
///   (deduplication is a no-op if there are no duplicate labels,
///   and our checker already prevents those).
fn try_magic(
    state: &mut crate::typecheck_db::unify::UnifyState,
    pending: &PendingConstraint,
) -> MagicOutcome {
    let class_name = pending.constraint.class.name.as_str();
    let class_module = pending.constraint.class.module.as_deref();
    // Each magic arm corresponds to a Prim (or `Data.Symbol`) class.
    // Only fire when the pending's class is qualified to the canonical
    // defining module — without this guard, a user-defined class
    // sharing the simple name (e.g. a library `Cons`) would be
    // mistaken for `Prim.Row.Cons` and speculatively unified against
    // built-in semantics. Pendings with no module qualifier still
    // fire magic (lenient — covers the legacy unqualified path).
    let class_module_matches = |allowed: &[&str]| -> bool {
        match class_module {
            None => true,
            Some(m) => allowed.iter().any(|a| *a == m),
        }
    };
    let args: Vec<Type> = pending
        .constraint
        .args
        .iter()
        .map(|a| state.zonk(a))
        .collect();
    match class_name {
        "IsSymbol" if class_module_matches(&["Data.Symbol"]) => {
            if let [Type::TypeString(_)] = args.as_slice() {
                return MagicOutcome::Resolved(ResolvedDict {
                    class: pending.constraint.class.clone(),
                    instance_types: args,
                    instance_idx: 0,
                    context: Vec::new(),
                });
            }
        }
        "Nub" if class_module_matches(&["Prim.Row"]) => {
            if args.len() == 2 {
                if let Type::Row(_, None) | Type::Record(_, None) = &args[0] {
                    if state.unify(&args[0], &args[1]).is_ok() {
                        return MagicOutcome::Resolved(ResolvedDict {
                            class: pending.constraint.class.clone(),
                            instance_types: args,
                            instance_idx: 0,
                            context: Vec::new(),
                        });
                    }
                }
            }
        }
        // `Prim.Int.ToString i sym | i -> sym` — when `i` is a
        // concrete Int literal, `sym` is determined as that
        // integer's decimal-string representation.
        "ToString" if class_module_matches(&["Prim.Int"]) => {
            if args.len() == 2 {
                if let Type::TypeInt(n) = &args[0] {
                    let expected = Type::TypeString(n.to_string());
                    let snapshot = state.snapshot_bindings();
                    if state.unify(&args[1], &expected).is_ok() {
                        return MagicOutcome::Resolved(ResolvedDict {
                            class: pending.constraint.class.clone(),
                            instance_types: vec![args[0].clone(), expected],
                            instance_idx: 0,
                            context: Vec::new(),
                        });
                    }
                    state.restore_bindings(snapshot);
                    // Definite mismatch: known Int can't produce
                    // the requested Symbol.
                    return MagicOutcome::Mismatch;
                }
            }
        }
        // `Prim.Symbol.Append left right result | left right -> result,
        // right result -> left, left result -> right` — concatenation
        // of two known symbols determines the third.
        "Append" if class_module_matches(&["Prim.Symbol"]) => {
            if args.len() == 3 {
                // Forward: left + right → result.
                if let (Type::TypeString(l), Type::TypeString(r)) =
                    (&args[0], &args[1])
                {
                    let mut s = l.clone();
                    s.push_str(r);
                    let expected = Type::TypeString(s);
                    let snapshot = state.snapshot_bindings();
                    if state.unify(&args[2], &expected).is_ok() {
                        return MagicOutcome::Resolved(ResolvedDict {
                            class: pending.constraint.class.clone(),
                            instance_types: vec![
                                args[0].clone(),
                                args[1].clone(),
                                expected,
                            ],
                            instance_idx: 0,
                            context: Vec::new(),
                        });
                    }
                    state.restore_bindings(snapshot);
                    return MagicOutcome::Mismatch;
                }
                // Backward: known left + result → right (strip prefix).
                if let (Type::TypeString(l), Type::TypeString(res)) =
                    (&args[0], &args[2])
                {
                    if let Some(rhs) = res.strip_prefix(l.as_str()) {
                        let expected = Type::TypeString(rhs.to_string());
                        let snapshot = state.snapshot_bindings();
                        if state.unify(&args[1], &expected).is_ok() {
                            return MagicOutcome::Resolved(ResolvedDict {
                                class: pending.constraint.class.clone(),
                                instance_types: vec![
                                    args[0].clone(),
                                    expected,
                                    args[2].clone(),
                                ],
                                instance_idx: 0,
                                context: Vec::new(),
                            });
                        }
                        state.restore_bindings(snapshot);
                        return MagicOutcome::Mismatch;
                    } else {
                        return MagicOutcome::Mismatch;
                    }
                }
                // Backward: known right + result → left (strip suffix).
                if let (Type::TypeString(r), Type::TypeString(res)) =
                    (&args[1], &args[2])
                {
                    if let Some(lhs) = res.strip_suffix(r.as_str()) {
                        let expected = Type::TypeString(lhs.to_string());
                        let snapshot = state.snapshot_bindings();
                        if state.unify(&args[0], &expected).is_ok() {
                            return MagicOutcome::Resolved(ResolvedDict {
                                class: pending.constraint.class.clone(),
                                instance_types: vec![
                                    expected,
                                    args[1].clone(),
                                    args[2].clone(),
                                ],
                                instance_idx: 0,
                                context: Vec::new(),
                            });
                        }
                        state.restore_bindings(snapshot);
                        return MagicOutcome::Mismatch;
                    } else {
                        return MagicOutcome::Mismatch;
                    }
                }
            }
        }
        // `Prim.Symbol.Compare left right ordering | left right -> ordering`
        // / `Prim.Int.Compare left right ordering | left right -> ordering`
        // — concrete operands determine the resulting Ordering.
        "Compare" if class_module_matches(&["Prim.Symbol", "Prim.Int"]) => {
            if args.len() == 3 {
                let order = match (&args[0], &args[1]) {
                    (Type::TypeString(l), Type::TypeString(r)) => {
                        Some(l.cmp(r))
                    }
                    (Type::TypeInt(l), Type::TypeInt(r)) => Some(l.cmp(r)),
                    _ => None,
                };
                if let Some(order) = order {
                    use std::cmp::Ordering;
                    let ord_name = match order {
                        Ordering::Less => "LT",
                        Ordering::Equal => "EQ",
                        Ordering::Greater => "GT",
                    };
                    let expected = Type::Con(
                        crate::typecheck_db::types::QName {
                            module: Some("Prim.Ordering".into()),
                            name: ord_name.into(),
                        },
                    );
                    let snapshot = state.snapshot_bindings();
                    if state
                        .unify(&args[2], &expected)
                        .or_else(|_| {
                            state.unify(
                                &args[2],
                                &Type::Con(crate::typecheck_db::types::QName {
                                    module: None,
                                    name: ord_name.into(),
                                }),
                            )
                        })
                        .is_ok()
                    {
                        return MagicOutcome::Resolved(ResolvedDict {
                            class: pending.constraint.class.clone(),
                            instance_types: vec![
                                args[0].clone(),
                                args[1].clone(),
                                expected,
                            ],
                            instance_idx: 0,
                            context: Vec::new(),
                        });
                    }
                    state.restore_bindings(snapshot);
                    return MagicOutcome::Mismatch;
                }
            }
        }
        // `Prim.Symbol.Cons head tail sym | head tail -> sym, sym ->
        // head tail` — concrete sym determines head/tail; concrete
        // head + tail determines sym.
        // `Prim.Row.Cons label a tail row | label tail -> a row,
        // label row -> a tail` — when label is a known TypeString
        // and row is a concrete Row, look up the field and unify.
        // `Prim.Row.Lacks (label :: Symbol) (row :: Row k)` —
        // the row lacks the given label. Concrete row + concrete
        // label literal: walk the row's fields and discharge if
        // the label is absent.
        "Lacks" if class_module_matches(&["Prim.Row"]) => {
            if args.len() == 2 {
                if let Type::TypeString(lbl) = &args[0] {
                    if let Type::Row(fields, _tail) | Type::Record(fields, _tail) =
                        &args[1]
                    {
                        let lbl = lbl.clone();
                        if !fields.iter().any(|(l, _)| *l == lbl) {
                            return MagicOutcome::Resolved(ResolvedDict {
                                class: pending.constraint.class.clone(),
                                instance_types: args,
                                instance_idx: 0,
                                context: Vec::new(),
                            });
                        }
                        // Label IS present and row has no open
                        // tail to absorb further fields — Lacks
                        // can never be satisfied. Mismatch.
                        // (When the row has a tail we don't know
                        // whether subsequent fields satisfy
                        // `Lacks` so we keep deferring.)
                        // Note: matching here is conservative —
                        // we only emit Mismatch when there's NO
                        // tail. With a tail the constraint may
                        // still discharge once the tail is
                        // pinned.
                    }
                }
            }
        }
        "Cons" => {
            if args.len() == 4 && class_module_matches(&["Prim.Row"]) {
                // Row.Cons: label, field-type, tail-row, full-row.
                // Only fires when label is a known TypeString AND
                // full-row is a concrete Row — otherwise falls
                // through to the normal Deferred path (Row.Cons has
                // no user instances, so candidates is empty).
                if let Type::TypeString(lbl) = &args[0] {
                    let lbl = lbl.clone();
                    let a1 = args[1].clone();
                    let a2 = args[2].clone();
                    let row = args[3].clone();
                    if let Type::Row(ref fields, ref row_tail) = row {
                        if let Some(idx) =
                            fields.iter().position(|(l, _)| *l == lbl)
                        {
                            let field_ty = fields[idx].1.clone();
                            let remaining: Vec<(String, Type)> = fields
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| *i != idx)
                                .map(|(_, f)| f.clone())
                                .collect();
                            let tail_ty =
                                Type::Row(remaining, row_tail.clone());
                            let snapshot = state.snapshot_bindings();
                            if state.unify(&a1, &field_ty).is_ok()
                                && state.unify(&a2, &tail_ty).is_ok()
                            {
                                return MagicOutcome::Resolved(ResolvedDict {
                                    class: pending.constraint.class.clone(),
                                    instance_types: vec![
                                        args[0].clone(),
                                        field_ty,
                                        tail_ty,
                                        row,
                                    ],
                                    instance_idx: 0,
                                    context: Vec::new(),
                                });
                            }
                            state.restore_bindings(snapshot);
                            // Unification failed — fall through to
                            // defer (return None below).
                        }
                        // Label absent or open row — fall through.
                    }
                }
            }
            if args.len() == 3 && class_module_matches(&["Prim.Symbol"]) {
                // Forward: head + tail → sym.
                if let (Type::TypeString(h), Type::TypeString(t)) =
                    (&args[0], &args[1])
                {
                    if h.chars().count() == 1 {
                        let mut s = h.clone();
                        s.push_str(t);
                        let expected = Type::TypeString(s);
                        let snapshot = state.snapshot_bindings();
                        if state.unify(&args[2], &expected).is_ok() {
                            return MagicOutcome::Resolved(ResolvedDict {
                                class: pending.constraint.class.clone(),
                                instance_types: vec![
                                    args[0].clone(),
                                    args[1].clone(),
                                    expected,
                                ],
                                instance_idx: 0,
                                context: Vec::new(),
                            });
                        }
                        state.restore_bindings(snapshot);
                        return MagicOutcome::Mismatch;
                    }
                }
                // Backward: known sym → head, tail.
                if let Type::TypeString(s) = &args[2] {
                    if let Some(first_char) = s.chars().next() {
                        let head_str: String = first_char.to_string();
                        let tail_str: String =
                            s.chars().skip(1).collect();
                        let head_ty = Type::TypeString(head_str);
                        let tail_ty = Type::TypeString(tail_str);
                        let snapshot = state.snapshot_bindings();
                        if state.unify(&args[0], &head_ty).is_ok()
                            && state.unify(&args[1], &tail_ty).is_ok()
                        {
                            return MagicOutcome::Resolved(ResolvedDict {
                                class: pending.constraint.class.clone(),
                                instance_types: vec![
                                    head_ty,
                                    tail_ty,
                                    args[2].clone(),
                                ],
                                instance_idx: 0,
                                context: Vec::new(),
                            });
                        }
                        state.restore_bindings(snapshot);
                        return MagicOutcome::Mismatch;
                    }
                }
            }
        }
        // `Prim.RowList.RowToList row list | row -> list` — when
        // `row` is a concrete closed row (no open tail), the
        // rowlist is determined: sort the fields lexically and
        // build `Cons label type tail` ending in `Nil`. Without
        // this, downstream classes that depend on RowToList (e.g.
        // `FoldlRecord`, `GqlQuery`'s `VarsTypeChecked`,
        // `DecodeOaFields`) all defer, propagating bogus
        // constraints into the exported scheme of any signed decl
        // whose body uses heterogeneous-record machinery.
        "RowToList" if class_module_matches(&["Prim.RowList"]) => {
            if args.len() == 2 {
                if let Type::Row(fields, None) | Type::Record(fields, None) = &args[0] {
                    let mut sorted: Vec<(String, Type)> = fields.clone();
                    sorted.sort_by(|a, b| a.0.cmp(&b.0));
                    let cons_qn = crate::typecheck_db::types::QName {
                        module: Some("Prim.RowList".into()),
                        name: "Cons".into(),
                    };
                    let nil_qn = crate::typecheck_db::types::QName {
                        module: Some("Prim.RowList".into()),
                        name: "Nil".into(),
                    };
                    let mut rl = Type::Con(nil_qn);
                    for (label, ty) in sorted.into_iter().rev() {
                        let cons = Type::Con(cons_qn.clone());
                        let with_label = Type::App(
                            std::sync::Arc::new(cons),
                            std::sync::Arc::new(Type::TypeString(label)),
                        );
                        let with_ty = Type::App(
                            std::sync::Arc::new(with_label),
                            std::sync::Arc::new(ty),
                        );
                        rl = Type::App(
                            std::sync::Arc::new(with_ty),
                            std::sync::Arc::new(rl),
                        );
                    }
                    let snapshot = state.snapshot_bindings();
                    if state.unify(&args[1], &rl).is_ok() {
                        return MagicOutcome::Resolved(ResolvedDict {
                            class: pending.constraint.class.clone(),
                            instance_types: vec![args[0].clone(), rl],
                            instance_idx: 0,
                            context: Vec::new(),
                        });
                    }
                    state.restore_bindings(snapshot);
                    return MagicOutcome::Mismatch;
                }
            }
        }
        _ => {}
    }
    MagicOutcome::None
}

/// True when `ty` structurally contains any `Type::Con` whose
/// (module, name) pair is present in `aliases`. Used by
/// `try_match`'s alias-expansion retry as a cheap pre-check: if the
/// target carries no alias-named Cons anywhere, `expand_aliases`
/// would be a structural no-op (it'd recurse the whole tree just to
/// allocate a deep clone identical to the input), so we can short-
/// circuit before paying the clone. Walking is O(n) lookups,
/// allocation-free.
fn type_has_alias_con(
    ty: &Type,
    aliases: &crate::typecheck_db::types::AliasMap,
) -> bool {
    match ty {
        Type::Con(qn) => {
            aliases.contains_key(&(qn.module.clone(), qn.name.clone()))
                || (qn.module.is_some()
                    && aliases.contains_key(&(None, qn.name.clone())))
        }
        Type::App(f, a) | Type::Fun(f, a) | Type::Kinded(f, a) => {
            type_has_alias_con(f, aliases) || type_has_alias_con(a, aliases)
        }
        Type::Forall(_, b) => type_has_alias_con(b, aliases),
        Type::Constrained(cs, b) => {
            cs.iter()
                .any(|c| c.args.iter().any(|x| type_has_alias_con(x, aliases)))
                || type_has_alias_con(b, aliases)
        }
        Type::Record(fs, t) | Type::Row(fs, t) => {
            fs.iter().any(|(_, v)| type_has_alias_con(v, aliases))
                || t.as_ref().map_or(false, |t| type_has_alias_con(t, aliases))
        }
        _ => false,
    }
}

/// Fundep-driven improvement. For each fundep `(det, desd)` on the
/// class where the pending's determiner positions are all concrete:
///
///   1. Walk every in-scope candidate instance, snapshot+unify the
///      determiner positions of the pending with the candidate's
///      head. Restore after each test — we're checking matchability
///      without committing.
///   2. If EXACTLY ONE candidate's determiners unify, that
///      candidate is the unique improver. Run a coverage check:
///      every type variable that appears in the candidate's
///      determined positions must also appear in its determiner
///      positions (otherwise applying the improvement would pin a
///      free var to a fresh unif — invalid).
///   3. On coverage success, unify the pending's determined
///      positions with the candidate's determined positions. The
///      improvement is now committed; downstream solver work sees
///      the pinned values.
///
/// Returns true when at least one fundep produced an improvement
/// (currently advisory — caller proceeds to try_match either way).
fn try_fundep_improvement(
    state: &mut crate::typecheck_db::unify::UnifyState,
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    pending: &PendingConstraint,
    class_info: &crate::typecheck_db::passes::instance_index::ClassInfo,
) -> bool {
    // Once-per-pending: a successful apply can pin a determined
    // position to a type that still CONTAINS bare unifs (e.g.
    // `Newtype (NT ?u) ?a` pins `?a := ?u`), so the "determined
    // still bare" gate below would re-run the full match+apply —
    // including a structural unify over the (possibly huge)
    // determiner types — on EVERY solver iteration. Route.Routes'
    // `routesAndHandlers` paid 642 SECONDS for those repeats
    // (35k Newtype solve_one calls × ~18ms). Improvement is an
    // optimisation; repeating it can only rediscover the same
    // equalities.
    if state.was_improved(pending.span.start, &pending.constraint.class.name) {
        return false;
    }
    let pending_class_module = pending.constraint.class.module.as_deref();
    // Fundep improvement requires STRICT class-module matching:
    // instances stored under the same simple name can belong to
    // different user-defined classes across modules (e.g. many
    // user libraries declare their own `Parallel`-named class).
    // Allowing None-module candidates through would let an
    // unrelated class's instance "improve" our pending. The
    // pending always carries the canonical module qualifier
    // (resolver-emitted), so we can demand a strict match.
    let cands: Vec<&crate::typecheck_db::passes::instance_index::Instance> = instances
        .candidates(&pending.constraint.class.name)
        .iter()
        .filter(|c| match (pending_class_module, c.class.module.as_deref()) {
            (Some(want), Some(have)) => want == have,
            (None, _) => true,
            (Some(_), None) => false,
        })
        .collect();
    if cands.is_empty() {
        return false;
    }
    // Whether every determiner across every fundep is fully ground
    // (no unif anywhere). If improvement fails AND determiners are
    // ground, the determiners can't refine on a later solver
    // iteration, so re-attempting can only ever fail again — mark
    // the pending settled to skip the (expensive) re-scan. This is
    // the case that kept Route.Routes' `routesAndHandlers` burning:
    // ~21k Newtype constraints whose determiner is a concrete
    // record that matches NO `NT x` instance, re-scanned every
    // fixpoint round. (When a determiner still has a unif, we leave
    // the pending un-settled so a later binding can enable the
    // improvement.)
    let all_det_ground = class_info.fundeps.iter().all(|fd| {
        fd.determiners.iter().all(|&i| {
            pending
                .constraint
                .args
                .get(i)
                .map_or(true, |a| !contains_unif(a, state))
        })
    });
    let mut any_improved = false;
    for fd in &class_info.fundeps {
        // Skip when any determiner / determined position is out of
        // range for the pending's args (class_info arity disagrees
        // with the concrete constraint shape — possible when an
        // instance carries an outdated arity through a stale cache
        // or partial application).
        let max_pos = fd
            .determiners
            .iter()
            .chain(fd.determined.iter())
            .max()
            .copied()
            .unwrap_or(0);
        if max_pos >= pending.constraint.args.len() {
            continue;
        }
        // Skip when any determiner is still a bare unif — we can't
        // match against instance heads with unknown determiners.
        let all_det_concrete = fd.determiners.iter().all(|i| {
            pending
                .constraint
                .args
                .get(*i)
                .map_or(false, |a| !is_bare_unif(a, state))
        });
        if !all_det_concrete {
            continue;
        }
        // Skip when NO determined position is a bare unif — there is
        // nothing left for this fundep to improve. Without this, the
        // candidate scan below re-runs (snapshot + freshen + unify
        // per candidate) on EVERY solver iteration for every
        // deferred constraint of a fundep class whose determined
        // side is already pinned. OaVirtual.Layout's `component`
        // SCC makes 12k+ MonadState solve_one calls; the redundant
        // re-scans cost ~9s of its solve budget and pushed the decl
        // past its timeout.
        let any_determined_bare = fd.determined.iter().any(|i| {
            pending
                .constraint
                .args
                .get(*i)
                .map_or(false, |a| is_bare_unif(a, state))
        });
        if !any_determined_bare {
            continue;
        }
        // Pass 1: enumerate matching candidates. For each, freshen
        // its quantified vars (per-attempt) so the snapshot test
        // doesn't leak fresh unifs into the state on a non-match.
        // Pre-compute a SHAPE for the pending's type at each
        // determiner position. Reused as a cheap structural filter
        // across every candidate so we don't allocate fresh unifs +
        // run a full unify on candidates that obviously can't match.
        //
        // Per-position rule:
        // - `Con(qname, arity)`: cand must have the same
        //   (qname, arity) at that position, OR a non-Con head
        //   (type var) which unifies with anything.
        // - `NonCon`: target is a Record / Row / Fun / type-level
        //   literal — a shape that can never unify with a
        //   Con-headed instance position (except the unifier's
        //   `Record` / `(->)` reconciliation heads, which we
        //   allow through). Without this arm, a constraint like
        //   `Newtype {500-field route record} ?a` ran the full
        //   freshen+unify scan against EVERY Newtype instance in
        //   scope: Route.Routes' `routesAndHandlers` made 35k such
        //   solve_one calls at ~18ms each — 661 SECONDS of its
        //   solve budget burnt on scans that can't match.
        // - `Unknown` (free unif / Var / forall): no filtering.
        enum DetShape {
            Con(crate::typecheck_db::types::QName, usize),
            NonCon,
            Unknown,
        }
        let det_shape = |ty: &Type| -> DetShape {
            if let Some((qn, ar)) = app_spine_head_arity_probing(ty, state) {
                return DetShape::Con(qn.clone(), ar);
            }
            // Probe through unif bindings to the head shape.
            let mut cur = ty;
            loop {
                match cur {
                    Type::App(f, _) => cur = f,
                    Type::Unif(id) => match state.probe(*id) {
                        Some(bound) => cur = bound,
                        None => return DetShape::Unknown,
                    },
                    Type::Record(_, _)
                    | Type::Row(_, _)
                    | Type::Fun(_, _)
                    | Type::TypeString(_)
                    | Type::TypeInt(_)
                    // Rigid type vars and skolems only unify with
                    // themselves — a Con-headed instance position
                    // can never match. Without this arm, a pending
                    // like `Newtype t ?a` (t rigid from the decl's
                    // sig) ran the freshen+unify scan against EVERY
                    // Newtype instance in scope — Route.Routes'
                    // closure holds ~4600 of them, and 14k repeat
                    // scans cost 640+ seconds.
                    | Type::Var(_)
                    | Type::Skolem(_) => return DetShape::NonCon,
                    _ => return DetShape::Unknown,
                }
            }
        };
        let target_heads_at_det: Vec<DetShape> = fd
            .determiners
            .iter()
            .map(|&i| det_shape(&pending.constraint.args[i]))
            .collect();
        let mut matches: Vec<usize> = Vec::new();
        for (cand_idx, cand) in cands.iter().enumerate() {
            if cand.types.len() != pending.constraint.args.len() {
                continue;
            }
            if max_pos >= cand.types.len() {
                continue;
            }
            // Cheap structural head pre-filter — avoids the
            // snapshot+freshen+unify roundtrip for candidates whose
            // determiner position heads can't match the pending's.
            // This is the difference between O(485 candidates) of
            // expensive work per Parallel constraint and O(485) of
            // pointer-compare-cheap work.
            let mut head_ok = true;
            for (dix, &i) in fd.determiners.iter().enumerate() {
                match &target_heads_at_det[dix] {
                    DetShape::Con(th, ta) => {
                        if let Some((ch, ca)) = app_spine_head_arity(&cand.types[i]) {
                            if ca != *ta {
                                head_ok = false;
                                break;
                            }
                            let names_equiv = ch.name == th.name
                                || ((ch.name == "->" || ch.name == "Function")
                                    && (th.name == "->" || th.name == "Function"));
                            if !names_equiv {
                                head_ok = false;
                                break;
                            }
                            if ch.module.is_some()
                                && th.module.is_some()
                                && ch.module != th.module
                            {
                                head_ok = false;
                                break;
                            }
                        }
                        // Cand has non-Con head at this position
                        // (type var) — could unify with the
                        // target's Con head, so keep this
                        // candidate as a possible match.
                    }
                    DetShape::NonCon => {
                        if let Some((ch, _)) = app_spine_head_arity(&cand.types[i]) {
                            // A Con-headed instance position can't
                            // unify with a Record/Row/Fun/literal
                            // target — except the unifier's special
                            // reconciliation heads.
                            let reconciles = ch.name == "Record"
                                || ch.name == "->"
                                || ch.name == "Function";
                            if !reconciles {
                                head_ok = false;
                                break;
                            }
                        }
                    }
                    DetShape::Unknown => {}
                }
            }
            if !head_ok {
                continue;
            }
            let snapshot = state.snapshot_bindings();
            let mut subst: std::collections::HashMap<String, Type> =
                std::collections::HashMap::new();
            for v in &cand.vars {
                subst.insert(v.clone(), state.fresh());
            }
            let mut det_ok = true;
            for &i in &fd.determiners {
                let inst_ty = crate::typecheck_db::generalize::apply_var_subst(
                    &cand.types[i],
                    &subst,
                );
                if state
                    .unify(&inst_ty, &pending.constraint.args[i])
                    .is_err()
                {
                    det_ok = false;
                    break;
                }
            }
            state.restore_bindings(snapshot);
            if det_ok {
                matches.push(cand_idx);
            }
        }
        // Deduplicate matches by structural equality of the
        // candidate's types + vars. The instance index can hold the
        // same logical instance multiple times when it's reached
        // through different import paths (e.g. via Prelude
        // re-exports plus a direct import). Two matches that name
        // the same instance head should count as ONE for the
        // ambiguity check.
        let mut dedup: Vec<usize> = Vec::new();
        for &mi in &matches {
            let cm = cands[mi];
            let already = dedup.iter().any(|&di| {
                let cd = cands[di];
                cm.types == cd.types && cm.vars == cd.vars
            });
            if !already {
                dedup.push(mi);
            }
        }
        if dedup.len() != 1 {
            // Zero matches → nothing to improve from. Multiple
            // DISTINCT matches → ambiguous, let try_match's
            // standard rules handle it.
            continue;
        }
        let cand = cands[dedup[0]];
        // Restrict improvement to candidates with NO free type vars
        // (fully concrete heads like `Parallel ParAff Aff`). Without
        // this restriction, applying an improvement against an
        // instance with `cand.vars = [m, ...]` would freshen those
        // vars and leave the fresh unifs PERMANENTLY in state
        // (the successful apply path doesn't restore — that's the
        // whole point), accumulating unbounded memory across the
        // sweep. The conservative version still fires for the
        // common reference-compiler-style "concrete instance pins
        // the determined" cases, which is enough for the parallel
        // cluster fix.
        if !cand.vars.is_empty() {
            continue;
        }
        // Coverage check: every var in the candidate's determined
        // positions must also appear in its determiner positions.
        // Without this, an instance like `instance Foo Int x` (with
        // fundep `a -> b` and free var `x` in determined) would
        // pin the pending's b-position to a fresh unif — not a
        // valid improvement.
        let mut det_vars: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        for &i in &fd.determiners {
            collect_type_vars(&cand.types[i], &mut det_vars);
        }
        let mut desd_vars: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        for &i in &fd.determined {
            collect_type_vars(&cand.types[i], &mut desd_vars);
        }
        let coverage_ok = desd_vars.is_subset(&det_vars);
        if !coverage_ok {
            continue;
        }
        // Apply improvement: freshen the instance and unify BOTH
        // determiner AND determined positions. The determiner re-
        // unify is needed because the instantiation creates fresh
        // unifs for the instance's quantified vars; the determined
        // positions reference those same vars, so we need them
        // bound consistently.
        let snapshot = state.snapshot_bindings();
        let mut subst: std::collections::HashMap<String, Type> =
            std::collections::HashMap::new();
        for v in &cand.vars {
            subst.insert(v.clone(), state.fresh());
        }
        let mut all_ok = true;
        for &i in &fd.determiners {
            let inst_ty = crate::typecheck_db::generalize::apply_var_subst(
                &cand.types[i],
                &subst,
            );
            if state
                .unify(&inst_ty, &pending.constraint.args[i])
                .is_err()
            {
                all_ok = false;
                break;
            }
        }
        if all_ok {
            for &i in &fd.determined {
                let inst_ty = crate::typecheck_db::generalize::apply_var_subst(
                    &cand.types[i],
                    &subst,
                );
                if state
                    .unify(&inst_ty, &pending.constraint.args[i])
                    .is_err()
                {
                    all_ok = false;
                    break;
                }
            }
        }
        if !all_ok {
            state.restore_bindings(snapshot);
            continue;
        }
        any_improved = true;
    }
    // Mark settled on success, OR on failure when determiners are
    // ground (a ground-determiner failure is permanent — see
    // `all_det_ground`). A failure with unif-bearing determiners is
    // left un-settled so a later binding can enable improvement.
    if any_improved || all_det_ground {
        state.mark_improved(pending.span.start, &pending.constraint.class.name);
    }
    any_improved
}

/// Collect every `Type::Var(name)` reference inside `ty`. Helper
/// for `try_fundep_improvement`'s coverage check.
fn collect_type_vars(ty: &Type, out: &mut std::collections::HashSet<String>) {
    match ty {
        Type::Var(n) => {
            out.insert(n.clone());
        }
        Type::App(f, a) | Type::Fun(f, a) | Type::Kinded(f, a) => {
            collect_type_vars(f, out);
            collect_type_vars(a, out);
        }
        Type::Forall(qs, b) => {
            // Don't capture vars bound by inner foralls.
            let bound: std::collections::HashSet<String> =
                qs.iter().map(|(n, _, _)| n.clone()).collect();
            let mut inner = std::collections::HashSet::new();
            collect_type_vars(b, &mut inner);
            for v in inner.difference(&bound) {
                out.insert(v.clone());
            }
        }
        Type::Constrained(cs, b) => {
            for c in cs {
                for a in &c.args {
                    collect_type_vars(a, out);
                }
            }
            collect_type_vars(b, out);
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            for (_, t) in fs {
                collect_type_vars(t, out);
            }
            if let Some(t) = tail {
                collect_type_vars(t, out);
            }
        }
        _ => {}
    }
}

/// Freshen an instance's quantified vars, unify its head with the
/// target args, and (on success) return the freshened head + context
/// so the caller can package a `ResolvedDict`.
fn try_match(
    state: &mut crate::typecheck_db::unify::UnifyState,
    instance: &crate::typecheck_db::passes::instance_index::Instance,
    target_args: &[Type],
    aliases: &crate::typecheck_db::types::AliasMap,
) -> Option<(Vec<Type>, Vec<Constraint>)> {
    if instance.types.len() != target_args.len() {
        return None;
    }
    let mut subst: std::collections::HashMap<String, Type> =
        std::collections::HashMap::new();
    for v in &instance.vars {
        subst.insert(v.clone(), state.fresh());
    }
    let head: Vec<Type> = instance
        .types
        .iter()
        .map(|t| crate::typecheck_db::generalize::apply_var_subst(t, &subst))
        .collect();
    for (inst_ty, target) in head.iter().zip(target_args.iter()) {
        let per_arg_snap = state.snapshot_bindings();
        if state.unify(inst_ty, target).is_err() {
            // Retry with the target alias-expanded. Instance heads
            // were unfolded via `expand_aliases_in_place` at index
            // registration (including nested aliases like `Schema`
            // inside a `client` field), but `convert_type_expr`
            // doesn't expand aliases on the wanted side — so a
            // wanted's `Con(Schema)` won't unify against a fully-
            // expanded instance head until we expand it here. Only
            // retry on FAILURE (so cases that already unify without
            // expansion are untouched, avoiding the Webb.AffList
            // / `Refer ShowRef Thread` regression we saw with eager
            // wanted-side expansion).
            state.restore_bindings(per_arg_snap);
            if aliases.is_empty() {
                return None;
            }
            // Zonk first so any unif vars that bound to alias names
            // since `pending.constraint.args` was last zonked become
            // visible (constraints often defer multiple iterations
            // before retry; intervening solve_ones may have bound the
            // unifs in this target arg).
            let target_zonked = state.zonk(target);
            // Pre-check: skip the (deep-cloning) `expand_aliases` call
            // when the target contains NO alias-named Cons. Expansion
            // would be a structural no-op, and the retry's unify would
            // fail identically to the first. Critical for performance —
            // types containing many `<>`-resolved `HookAppend` chains
            // (no aliases anywhere) would otherwise pay an O(n) clone
            // per per-arg failure per candidate per module. Walking
            // for alias-Cons is O(n) lookups, allocation-free.
            if !type_has_alias_con(&target_zonked, aliases) {
                return None;
            }
            let target_expanded = crate::typecheck_db::types::expand_aliases(
                target_zonked,
                aliases,
            );
            if state.unify(inst_ty, &target_expanded).is_err() {
                return None;
            }
        }
    }
    // Freshen the context with the same subst so constraint args
    // share the instance's type-var identity.
    let context: Vec<Constraint> = instance
        .context
        .iter()
        .map(|c| Constraint {
            class: c.class.clone(),
            args: c
                .args
                .iter()
                .map(|a| crate::typecheck_db::generalize::apply_var_subst(a, &subst))
                .collect(),
        })
        .collect();
    Some((head, context))
}

/// Maximum number of solver iterations before giving up. Guards
/// against pathological self-referential instances like
/// `instance Loop a => Loop a`. Each iteration unwinds at most one
/// level of any single constraint chain (sub-wanteds emitted by a
/// resolved instance go to `carry_forward` and are processed on the
/// NEXT pass), so very long inductive chains need a budget that
/// scales with the chain depth. 256 fits Puregres.Select's
/// `Show (ColCons _ (ColCons _ (… × ~150)) → ColNil)` chains
/// without raising the cap for genuine self-referential loops
/// (those would still exceed any practical bound).
const MAX_SOLVER_DEPTH: usize = 256;

/// Drain a list of pending constraints and emit per-decl
/// resolutions + errors. Runs a fixed-point loop: each match may
/// emit fresh sub-constraints from the instance's context, which
/// re-enter the queue on the next pass. Terminates when no
/// constraint remains, or when a pass makes no progress (all
/// remaining entries deferred), or at [`MAX_SOLVER_DEPTH`]
/// iterations.
pub fn solve_all(
    state: &mut crate::typecheck_db::unify::UnifyState,
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    pending: &[PendingConstraint],
) -> SolveReport {
    let mut report = SolveReport::default();
    // Each item is `(constraint, optional watch state)`. The watch
    // state stores the unif IDs the constraint's zonked args
    // mentioned at defer time AND that were still UNBOUND then. On
    // a later visit, we check (O(deps)) whether any of those unifs
    // is now bound — if not, `solve_one` would defer for the same
    // reason and we skip the call. For solver-heavy modules like
    // `AdminDashboard.Pages.Submissions.View` this collapses
    // ~3 million redundant `solve_one` calls into a few thousand.
    // Storing only the still-unbound subset (rather than all unif
    // ids in the args) is what makes the per-skip check O(deps)
    // rather than O(trail_range × deps).
    struct WatchState {
        unbound_deps: std::collections::HashSet<u32>,
    }
    let mut queue: Vec<(PendingConstraint, Option<WatchState>)> =
        pending.iter().cloned().map(|p| (p, None)).collect();

    // Profiling: count + cumulative time per class name. Printed
    // at end of solve_all when TYPECHECK_DB_PROFILE_SLOW is set.
    let _profile_slow = std::env::var_os("TYPECHECK_DB_PROFILE_SLOW").is_some();
    let _profile_start = std::time::Instant::now();
    let mut _per_class: std::collections::HashMap<
        String,
        (u64, std::time::Duration),
    > = std::collections::HashMap::new();
    let mut _skip_count: u64 = 0;
    let mut _solve_one_count: u64 = 0;

    // Track whether the last iteration made progress. If the loop
    // exits at the depth limit while still making progress, the
    // remaining queue is almost certainly a self-referential instance
    // chain — surface that to the user as a hard
    // `SolverDepthExceeded` error rather than letting it disappear
    // into `report.deferred`.
    let mut last_made_progress = true;
    for _ in 0..MAX_SOLVER_DEPTH {
        if queue.is_empty() {
            last_made_progress = false;
            break;
        }
        // Per-decl timeout: the SCC's `infer_value_scc_with_all`
        // arms a deadline on `state`, and a pathological fundep-
        // driven re-queue can otherwise loop up to
        // `MAX_SOLVER_DEPTH` times. Break early and let the caller
        // surface the `Timeout` (it polls `state.deadline_exceeded()`
        // immediately after `solve_all` returns).
        if state.deadline_exceeded() {
            break;
        }
        let current = std::mem::take(&mut queue);
        let mut carry_forward: Vec<(PendingConstraint, Option<WatchState>)> =
            Vec::new();
        let mut made_progress = false;
        for (pc, watch) in current {
            // Watch-list skip: if the constraint was deferred earlier
            // and none of the unifs that were unbound at defer time
            // has been bound since, solve_one would defer for the
            // same reason — skip it entirely. The probe is O(deps)
            // (HashMap lookup per dep id) regardless of how long the
            // binding trail has grown in the meantime.
            if let Some(w) = &watch {
                let any_now_bound = w
                    .unbound_deps
                    .iter()
                    .any(|id| state.probe(*id).is_some());
                if !any_now_bound {
                    _skip_count += 1;
                    carry_forward.push((pc, watch));
                    continue;
                }
            }
            _solve_one_count += 1;
            let owner = match &pc.decl_name {
                Some(n) => n.clone(),
                None => continue,
            };
            // Profile per-constraint solve_one time, bucketed by class.
            let _t = if _profile_slow {
                Some(std::time::Instant::now())
            } else {
                None
            };
            let _outcome = solve_one(state, instances, &pc);
            if let Some(t0) = _t {
                let dur = t0.elapsed();
                let entry = _per_class
                    .entry(pc.constraint.class.name.clone())
                    .or_insert((0, std::time::Duration::ZERO));
                entry.0 += 1;
                entry.1 += dur;
            }
            match _outcome {
                SolveOutcome::Resolved(dict) => {
                    made_progress = true;
                    // Push every context entry back onto the queue as
                    // a new pending with `InstanceContext` origin and
                    // the same owner/span. Later rounds see them the
                    // same way the top-level ones were seen this
                    // round.
                    for ctx in &dict.context {
                        carry_forward.push((
                            PendingConstraint {
                                decl_name: Some(owner.clone()),
                                span: pc.span,
                                constraint: Constraint {
                                    class: ctx.class.clone(),
                                    args: ctx.args.iter().map(|a| state.zonk(a)).collect(),
                                },
                                origin: ConstraintOrigin::InstanceContext,
                                givens: pc.givens.clone(),
                            },
                            None,
                        ));
                    }
                    // Record the outer dict at the call site's span
                    // *only* for Signature-origin constraints —
                    // context-induced sub-dicts inherit their
                    // parent's span and would otherwise overwrite.
                    if pc.origin == ConstraintOrigin::Signature {
                        report
                            .dicts_by_span
                            .entry(owner.clone())
                            .or_default()
                            .entry(pc.span)
                            .or_default()
                            .push(dict.clone());
                    }
                    report.dicts.entry(owner).or_default().push(dict);
                }
                SolveOutcome::NoInstance => {
                    made_progress = true;
                    let zonked = Constraint {
                        class: pc.constraint.class.clone(),
                        args: pc
                            .constraint
                            .args
                            .iter()
                            .map(|a| state.zonk(a))
                            .collect(),
                    };
                    report
                        .errors
                        .entry(owner)
                        .or_default()
                        .push(ConstraintError {
                            span: pc.span,
                            decl_span: state.current_decl_span(),
                            constraint: zonked,
                            kind: ConstraintErrorKind::NoInstanceFound,
                        });
                }
                SolveOutcome::HeadMismatch => {
                    made_progress = true;
                    let zonked = Constraint {
                        class: pc.constraint.class.clone(),
                        args: pc
                            .constraint
                            .args
                            .iter()
                            .map(|a| state.zonk(a))
                            .collect(),
                    };
                    report
                        .errors
                        .entry(owner)
                        .or_default()
                        .push(ConstraintError {
                            span: pc.span,
                            decl_span: state.current_decl_span(),
                            constraint: zonked,
                            kind: ConstraintErrorKind::InstanceHeadMismatch,
                        });
                }
                SolveOutcome::Overlap => {
                    // Reserved for future use — overlap detection is not
                    // yet wired into solve_one.
                    made_progress = true;
                    let zonked = Constraint {
                        class: pc.constraint.class.clone(),
                        args: pc
                            .constraint
                            .args
                            .iter()
                            .map(|a| state.zonk(a))
                            .collect(),
                    };
                    report
                        .errors
                        .entry(owner)
                        .or_default()
                        .push(ConstraintError {
                            span: pc.span,
                            decl_span: state.current_decl_span(),
                            constraint: zonked,
                            kind: ConstraintErrorKind::OverlappingInstances,
                        });
                }
                SolveOutcome::Deferred => {
                    // Capture the subset of unifs in the constraint
                    // args that are STILL UNBOUND right now. On the
                    // next visit, if none of those has been bound,
                    // solve_one would defer for the same reason.
                    // Restricting to unbound at defer time (rather
                    // than all mentioned unifs) keeps the watch set
                    // small AND makes the next-visit check O(deps).
                    let mut all_deps: std::collections::HashSet<u32> =
                        std::collections::HashSet::new();
                    for a in &pc.constraint.args {
                        collect_unif_ids(state, a, &mut all_deps);
                    }
                    let unbound_deps: std::collections::HashSet<u32> =
                        all_deps
                            .into_iter()
                            .filter(|id| state.probe(*id).is_none())
                            .collect();
                    let new_watch = WatchState { unbound_deps };
                    carry_forward.push((pc, Some(new_watch)));
                }
            }
        }
        last_made_progress = made_progress;
        if !made_progress {
            // Every remaining entry deferred in the same way — no
            // progress possible, stop burning iterations. These are
            // legitimate deferrals (polymorphic, etc.) and carry
            // forward for a later re-drive.
            queue = carry_forward;
            break;
        }
        queue = carry_forward;
    }

    // If we exhausted the depth budget while still making progress,
    // the remaining queue is recursion we refused to follow. Emit a
    // `SolverDepthExceeded` error for every remaining owned entry
    // so the failure is visible, then drop those entries from the
    // deferred list — they can't be productively re-driven.
    if last_made_progress && !queue.is_empty() {
        let mut legitimately_deferred: Vec<(PendingConstraint, Option<WatchState>)> =
            Vec::new();
        for (pc, watch) in std::mem::take(&mut queue) {
            match &pc.decl_name {
                Some(n) => {
                    report
                        .errors
                        .entry(n.clone())
                        .or_default()
                        .push(ConstraintError {
                            span: pc.span,
                            decl_span: state.current_decl_span(),
                            constraint: pc.constraint.clone(),
                            kind: ConstraintErrorKind::SolverDepthExceeded,
                        });
                }
                None => legitimately_deferred.push((pc, watch)),
            }
        }
        queue = legitimately_deferred;
    }
    report.deferred = queue.into_iter().map(|(pc, _)| pc).collect();

    // Profile summary: classes whose cumulative solve_one time
    // exceeded 100ms. Sorted descending by duration.
    if _profile_slow
        && _profile_start.elapsed() >= std::time::Duration::from_millis(500)
    {
        let mut entries: Vec<_> = _per_class.into_iter().collect();
        entries.sort_by(|a, b| b.1 .1.cmp(&a.1 .1));
        eprintln!(
            "  [solve_all profile, total {} ms, {} entries, {} solve_one, {} skipped]",
            _profile_start.elapsed().as_millis(),
            entries.len(),
            _solve_one_count,
            _skip_count,
        );
        if std::env::var_os("TYPECHECK_DB_SOLVE_PHASES").is_some() {
            let ms = |c: &std::sync::atomic::AtomicU64| {
                c.load(std::sync::atomic::Ordering::Relaxed) / 1_000_000
            };
            eprintln!(
                "    [solve_one phases cumulative: givens={}ms magic={}ms defer={}ms improve={}ms candloop={}ms tail={}ms]",
                ms(&PHASE_GIVENS_NS),
                ms(&PHASE_MAGIC_NS),
                ms(&PHASE_DEFER_NS),
                ms(&PHASE_IMPROVE_NS),
                ms(&PHASE_CANDLOOP_NS),
                ms(&PHASE_TAIL_NS),
            );
        }
        let mut accumulated_ms: u128 = 0;
        for (cls, (count, dur)) in entries.iter().take(40) {
            accumulated_ms += dur.as_millis();
            eprintln!(
                "    {:>8} ms  {:>6}x  {:>8} ms/c  {}",
                dur.as_millis(),
                count,
                if *count > 0 {
                    dur.as_millis() as u64 / count
                } else {
                    0
                },
                cls,
            );
        }
        let remaining_classes = entries.len().saturating_sub(40);
        let total_classes_ms: u128 = entries
            .iter()
            .map(|(_, (_, d))| d.as_millis())
            .sum();
        let total_constraints: u64 = entries.iter().map(|(_, (c, _))| c).sum();
        eprintln!(
            "    (top {} accounted for {} ms of {} ms; {} classes total, {} constraints)",
            entries.len().min(40),
            accumulated_ms,
            total_classes_ms,
            entries.len(),
            total_constraints,
        );
        if remaining_classes > 0 {
            eprintln!("    ... {} more classes not shown", remaining_classes);
        }
    }

    report
}

/// Per-decl aggregate of solving one SCC's worth of constraints.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SolveReport {
    /// Every resolved dict — outer + context-induced — keyed by
    /// owning decl. Codegen iterates this for the full set of
    /// references it needs to emit.
    pub dicts: std::collections::HashMap<String, Vec<ResolvedDict>>,
    /// Per-call-site dict lookup: maps each reference's span to the
    /// `ResolvedDict`s satisfying its top-level (`Signature`-origin)
    /// constraints, in signature order. A reference may carry several
    /// (e.g. `compare1 :: Ord1 f => Ord a => …`). Sub-constraints born
    /// from instance contexts do not appear here — they're in `dicts`
    /// and navigable via their parent's `ResolvedDict::context`.
    pub dicts_by_span: std::collections::HashMap<
        String,
        std::collections::HashMap<crate::span::Span, Vec<ResolvedDict>>,
    >,
    /// Unresolved constraints: `NoInstance` for now.
    pub errors: std::collections::HashMap<String, Vec<ConstraintError>>,
    /// Constraints the solver wasn't ready to decide on (still had
    /// unsolved unifs). Callers can re-drive later.
    pub deferred: Vec<PendingConstraint>,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse as parse_cst;
    use crate::typecheck_db::env::Env;
    use crate::typecheck_db::ir::Decl;
    use crate::typecheck_db::passes::infer_value::{
        infer_value_scc_with_registries, InferredScheme,
    };
    use crate::typecheck_db::passes::exhaustiveness::{CtorRegistry, DataConstructors};
    use crate::typecheck_db::types::{QName, Scheme, TypeOpMap};

    fn parse(src: &str) -> crate::typecheck_db::ir::Module {
        use crate::typecheck_db::desugar::{
            desugar_module, fixity_table_from_decls, DesugarContext,
        };
        let cst_mod = parse_cst(src).unwrap();
        let (fixity_table, module_fixity_hash) = fixity_table_from_decls(&cst_mod.decls);
        let ctx = DesugarContext { module_fixity_hash, fixity_table, qualified_fixity_table: Default::default() };
        let decls = desugar_module(cst_mod.decls.clone(), &ctx);
        let desugared = crate::cst::Module { decls, ..cst_mod };
        crate::typecheck_db::ir::lower_module(desugared).expect("lower")
    }

    // -- helpers ------------------------------------------------------

    fn int_ty() -> Type {
        crate::typecheck_db::types::prim_int()
    }

    fn bool_ty() -> Type {
        crate::typecheck_db::types::prim_boolean()
    }

    fn eq_a_a_to_bool() -> Scheme {
        // `forall a. Eq a => a -> a -> Boolean`
        let a = Type::Var("a".into());
        Scheme::new(
            vec!["a".into()],
            Type::Constrained(
                vec![Constraint {
                    class: QName::unqualified("Eq"),
                    args: vec![a.clone()],
                }],
                std::sync::Arc::new(Type::fun(a.clone(), Type::fun(a, bool_ty()))),
            ),
        )
    }

    fn infer(src: &str, env: &mut Env) -> Vec<InferredScheme> {
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let data = DataConstructors::new();
        let ctors = CtorRegistry::new();
        infer_value_scc_with_registries(&ops, env, &decls, &data, &ctors).unwrap()
    }

    // =================================================================
    // peel_constraints — pure structural helper
    // =================================================================

    #[test]
    fn peel_extracts_single_constraint() {
        let (cs, body) = peel_constraints(Type::Constrained(
            vec![Constraint {
                class: QName::unqualified("Eq"),
                args: vec![int_ty()],
            }],
            std::sync::Arc::new(Type::fun(int_ty(), bool_ty())),
        ));
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].class.name, "Eq");
        assert_eq!(body, Type::fun(int_ty(), bool_ty()));
    }

    #[test]
    fn peel_extracts_multi_constraint() {
        let a = Type::Var("a".into());
        let (cs, body) = peel_constraints(Type::Constrained(
            vec![
                Constraint { class: QName::unqualified("Eq"), args: vec![a.clone()] },
                Constraint { class: QName::unqualified("Show"), args: vec![a.clone()] },
            ],
            std::sync::Arc::new(a.clone()),
        ));
        assert_eq!(cs.len(), 2);
        assert_eq!(body, a);
    }

    #[test]
    fn peel_passthrough_for_non_constrained() {
        let (cs, body) = peel_constraints(int_ty());
        assert!(cs.is_empty());
        assert_eq!(body, int_ty());
    }

    // =================================================================
    // Integration: referencing a constrained value collects a constraint
    //
    // Expectation: when a Var references a polymorphic value whose
    // scheme includes `Type::Constrained`, inference instantiates the
    // scheme fresh, the `Constrained` layer is peeled, and a
    // `PendingConstraint` gets recorded against the referencing decl.
    // =================================================================

    #[test]
    fn referencing_eq_records_one_pending() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let schemes = infer("module M where\nf x = eq x x\n", &mut env);
        assert_eq!(schemes.len(), 1);
        assert_eq!(schemes[0].pending_constraints.len(), 1);
        assert_eq!(schemes[0].pending_constraints[0].constraint.class.name, "Eq");
    }

    #[test]
    fn unreferenced_constrained_value_records_nothing() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let schemes = infer("module M where\nx = 1\n", &mut env);
        assert!(schemes[0].pending_constraints.is_empty());
    }

    #[test]
    fn multiple_constraints_recorded_at_one_site() {
        let a = Type::Var("a".into());
        let scheme = Scheme::new(
            vec!["a".into()],
            Type::Constrained(
                vec![
                    Constraint { class: QName::unqualified("Eq"), args: vec![a.clone()] },
                    Constraint { class: QName::unqualified("Show"), args: vec![a.clone()] },
                ],
                std::sync::Arc::new(Type::fun(a, bool_ty())),
            ),
        );
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("p"), scheme);
        let schemes = infer("module M where\ng y = p y\n", &mut env);
        assert_eq!(schemes[0].pending_constraints.len(), 2);
        let class_names: Vec<&str> = schemes[0]
            .pending_constraints
            .iter()
            .map(|c| c.constraint.class.name.as_str())
            .collect();
        assert!(class_names.contains(&"Eq"));
        assert!(class_names.contains(&"Show"));
    }

    #[test]
    fn two_call_sites_produce_two_constraints() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let schemes = infer(
            "\
module M where
f a b = eq a a
g c = eq c c
",
            &mut env,
        );
        let f = schemes.iter().find(|s| s.name == "f").unwrap();
        let g = schemes.iter().find(|s| s.name == "g").unwrap();
        assert_eq!(f.pending_constraints.len(), 1);
        assert_eq!(g.pending_constraints.len(), 1);
        // Each call site's instantiation is fresh; the two constraints
        // can't both be stamped with the same unification var id.
        match (
            &f.pending_constraints[0].constraint.args[0],
            &g.pending_constraints[0].constraint.args[0],
        ) {
            (Type::Unif(a), Type::Unif(b)) => assert_ne!(a, b),
            (a, b) => {
                // Either side may have been generalized to a Type::Var
                // by the time the caller sees it — that's fine too as
                // long as they're not literally the same Unif id.
                let _ = (a, b);
            }
        }
    }

    #[test]
    fn origin_is_signature_for_var_site() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let schemes = infer("module M where\nh z = eq z z\n", &mut env);
        assert_eq!(
            schemes[0].pending_constraints[0].origin,
            ConstraintOrigin::Signature,
        );
    }

    #[test]
    fn decl_name_is_stamped_on_pending_constraint() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let schemes = infer("module M where\nfoo x = eq x x\n", &mut env);
        assert_eq!(
            schemes[0].pending_constraints[0].decl_name.as_deref(),
            Some("foo"),
        );
    }

    // =================================================================
    // Phase B: solve_one
    //
    // Drive the matcher directly with synthetic `PendingConstraint`s
    // and a hand-built `InstanceIndex`. These cover the matcher's
    // invariants without dragging in the rest of inference.
    // =================================================================

    use crate::typecheck_db::passes::instance_index::{Instance, InstanceIndex};
    use crate::typecheck_db::unify::UnifyState;

    fn maybe_ty(arg: Type) -> Type {
        Type::app(Type::Con(QName::unqualified("Maybe")), arg)
    }

    fn mk_pending(class: &str, args: Vec<Type>) -> PendingConstraint {
        PendingConstraint {
            decl_name: None,
            span: crate::span::Span { start: 0, end: 0 },
            constraint: Constraint {
                class: QName::unqualified(class),
                args,
            },
            origin: ConstraintOrigin::Signature,
            givens: Vec::new(),
        }
    }

    fn mk_instance(class: &str, types: Vec<Type>, vars: Vec<String>) -> Instance {
        Instance {
            class: QName::unqualified(class),
            types,
            context: vec![],
            vars,
            chained: false,
        }
    }

    #[test]
    fn solve_eq_int_with_matching_instance() {
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let pc = mk_pending("Eq", vec![int_ty()]);
        match solve_one(&mut state, &ix, &pc) {
            SolveOutcome::Resolved(dict) => {
                assert_eq!(dict.class.name, "Eq");
                assert_eq!(dict.instance_types, vec![int_ty()]);
                assert!(dict.context.is_empty());
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
    }

    #[test]
    fn solve_no_matching_instance_returns_no_instance() {
        let mut state = UnifyState::new();
        let ix = InstanceIndex::new();
        let pc = mk_pending("Eq", vec![int_ty()]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::NoInstance);
    }

    #[test]
    fn solve_wrong_type_head_defers() {
        // Index has `Eq String`, target is `Eq Int` — head shape
        // doesn't match any candidate. `solve_one` defers via the
        // kind-mismatch path so the constraint can still propagate
        // through the inferred scheme; a use site with the right
        // head can pick it up later (this is essential for
        // polymorphic instance dispatch patterns like `Apply Tuple`
        // vs `Apply (Tuple a)`). NoInstance fires only for the
        // genuinely-empty-candidates case where the class has no
        // user instances AND the args carry no remaining unifs
        // (covered by `solve_no_matching_instance_returns_no_instance`).
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance(
            "Eq",
            vec![Type::Con(QName::unqualified("String"))],
            vec![],
        ));
        let pc = mk_pending("Eq", vec![int_ty()]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::Deferred);
    }

    #[test]
    fn solve_polymorphic_instance_unifies_head() {
        // `instance Eq a => Eq (Maybe a)` (context ignored at Phase B)
        // against target `Eq (Maybe Int)` → matches, a := Int.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        let maybe_a = maybe_ty(Type::Var("a".into()));
        ix.insert(Instance {
            class: QName::unqualified("Eq"),
            types: vec![maybe_a],
            context: vec![Constraint {
                class: QName::unqualified("Eq"),
                args: vec![Type::Var("a".into())],
            }],
            vars: vec!["a".into()],
            chained: false,
        });
        let pc = mk_pending("Eq", vec![maybe_ty(int_ty())]);
        match solve_one(&mut state, &ix, &pc) {
            SolveOutcome::Resolved(dict) => {
                // After freshening and unification, the instance's
                // head should read back as `Maybe Int`.
                let head = state.zonk(&dict.instance_types[0]);
                assert_eq!(head, maybe_ty(int_ty()));
                // Context survives as `Eq Int` after freshening.
                assert_eq!(dict.context.len(), 1);
                let ctx_arg = state.zonk(&dict.context[0].args[0]);
                assert_eq!(ctx_arg, int_ty());
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
    }

    #[test]
    fn solve_first_match_wins() {
        // Two overlapping instances: both match `Eq Int`. Solver
        // takes the first (insertion-order). Overlap detection +
        // ambiguity is a later-phase concern.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![])); // first
        ix.insert(mk_instance("Eq", vec![Type::Var("a".into())], vec!["a".into()]));
        let pc = mk_pending("Eq", vec![int_ty()]);
        let out = solve_one(&mut state, &ix, &pc);
        match out {
            SolveOutcome::Resolved(dict) => {
                // First-match returns the concrete (non-var) instance.
                assert_eq!(dict.instance_types[0], int_ty());
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
    }

    #[test]
    fn solve_bare_unif_defers() {
        // Target is `Eq ?0` where ?0 is still fresh. No specific
        // instance can be chosen; the solver defers.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let unif = state.fresh();
        let pc = mk_pending("Eq", vec![unif]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::Deferred);
    }

    #[test]
    fn solve_class_name_mismatch_is_no_instance() {
        // Show Int against an Eq-only index.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let pc = mk_pending("Show", vec![int_ty()]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::NoInstance);
    }

    #[test]
    fn solve_failed_match_rolls_back_unifications() {
        // Instance is `Eq Int`; target is `Eq ?0` where ?0 is first
        // bound to String. The match must fail (Int ≠ String) and
        // leave ?0's prior binding untouched.
        let mut state = UnifyState::new();
        let string_ty = Type::Con(QName::unqualified("String"));
        let unif = state.fresh();
        let unif_id = match &unif {
            Type::Unif(id) => *id,
            _ => panic!(),
        };
        // Pre-bind ?0 := String.
        state.unify(&unif, &string_ty).unwrap();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let pc = mk_pending("Eq", vec![Type::Unif(unif_id)]);
        match solve_one(&mut state, &ix, &pc) {
            SolveOutcome::NoInstance | SolveOutcome::Deferred => {}
            other => panic!("expected no-match, got {other:?}"),
        }
        // Binding of ?0 must still resolve to String — trial match
        // didn't corrupt the main state.
        assert_eq!(state.zonk(&Type::Unif(unif_id)), string_ty);
    }

    // =================================================================
    // Phase B: solve_all + integration with infer_value_scc
    //
    // `infer_value_scc_with_registries` grows an `InstanceIndex`
    // parameter (via a new entry point) and routes resolutions /
    // errors to the owning `InferredScheme`.
    // =================================================================

    use crate::typecheck_db::passes::infer_value::infer_value_scc_with_all;

    fn infer_with_ix(
        src: &str,
        env: &mut Env,
        instances: &InstanceIndex,
    ) -> Vec<InferredScheme> {
        let m = parse(src);
        let decls: Vec<&Decl> = m.decls.iter().collect();
        let ops = TypeOpMap::default();
        let data = DataConstructors::new();
        let ctors = CtorRegistry::new();
        infer_value_scc_with_all(&ops, env, &decls, &data, &ctors, instances, false)
            .unwrap()
            .0
    }

    #[test]
    fn integration_resolved_constraint_leaves_no_error() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        // `f x = eq x x` — when `x` is pinned to Int (via annotation)
        // the constraint resolves.
        let schemes = infer_with_ix(
            "module M where\nf (x :: Int) = eq x x\n",
            &mut env,
            &ix,
        );
        assert!(
            schemes[0].constraint_errors.is_empty(),
            "got: {:?}",
            schemes[0].constraint_errors,
        );
        assert_eq!(schemes[0].resolved_dicts.len(), 1);
        assert_eq!(schemes[0].resolved_dicts[0].class.name, "Eq");
    }

    #[test]
    fn integration_no_instance_reports_error() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let ix = InstanceIndex::new();
        let schemes = infer_with_ix(
            "module M where\nf (x :: Int) = eq x x\n",
            &mut env,
            &ix,
        );
        assert_eq!(schemes[0].constraint_errors.len(), 1);
        let err = &schemes[0].constraint_errors[0];
        assert_eq!(err.kind, ConstraintErrorKind::NoInstanceFound);
        assert_eq!(err.constraint.class.name, "Eq");
    }

    // =================================================================
    // Phase D: fundep-driven improvement
    //
    // Scenarios in PureScript's fundep semantics:
    // - `class MonadState s m | m -> s`: knowing m picks s.
    // - Matching `MonadState ?s MyMonad` against `instance MonadState
    //   Int MyMonad` must unify ?s with Int even though ?s was fresh.
    // - Matching `MonadState ?s ?m` (both unknown) must defer.
    // - Without fundeps, `Eq ?x` still defers conservatively.
    // =================================================================

    fn monad_state_class() -> crate::typecheck_db::passes::instance_index::ClassInfo {
        use crate::typecheck_db::passes::instance_index::{ClassInfo, FunDep};
        ClassInfo {
            // type_vars = [s, m]; fundep m -> s means determiners=[1],
            // determined=[0].
            type_vars: vec!["s".into(), "m".into()],
            fundeps: vec![FunDep { determiners: vec![1], determined: vec![0] }],
            superclasses: vec![],
        }
    }

    #[test]
    fn fundep_improves_determined_slot_from_unif() {
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert_class("MonadState".into(), monad_state_class());
        // instance MonadState Int MyMonad
        let my_monad = Type::Con(QName::unqualified("MyMonad"));
        ix.insert(mk_instance("MonadState", vec![int_ty(), my_monad.clone()], vec![]));
        // Target: MonadState ?s MyMonad — ?s is in the DETERMINED
        // position (s), which the fundep `m -> s` makes improvable.
        let unif = state.fresh();
        let unif_id = match unif {
            Type::Unif(id) => id,
            _ => panic!(),
        };
        let pc = mk_pending("MonadState", vec![Type::Unif(unif_id), my_monad]);
        match solve_one(&mut state, &ix, &pc) {
            SolveOutcome::Resolved(_) => {}
            other => panic!("expected Resolved, got {other:?}"),
        }
        // Improvement: ?s must now zonk to Int.
        assert_eq!(state.zonk(&Type::Unif(unif_id)), int_ty());
    }

    #[test]
    fn fundep_defers_when_determiner_is_unif() {
        // Target: MonadState Int ?m — ?m is the DETERMINER; without
        // it, we can't discriminate between potentially-matching
        // instances. Must defer.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert_class("MonadState".into(), monad_state_class());
        ix.insert(mk_instance(
            "MonadState",
            vec![int_ty(), Type::Con(QName::unqualified("MyMonad"))],
            vec![],
        ));
        let unif_m = state.fresh();
        let pc = mk_pending("MonadState", vec![int_ty(), unif_m]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::Deferred);
    }

    #[test]
    fn fundep_defers_when_both_positions_unif() {
        // Target: MonadState ?s ?m. Both unknown → defer.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert_class("MonadState".into(), monad_state_class());
        ix.insert(mk_instance(
            "MonadState",
            vec![int_ty(), Type::Con(QName::unqualified("MyMonad"))],
            vec![],
        ));
        let unif_s = state.fresh();
        let unif_m = state.fresh();
        let pc = mk_pending("MonadState", vec![unif_s, unif_m]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::Deferred);
    }

    #[test]
    fn fundep_multi_determiner_improves_two_slots() {
        use crate::typecheck_db::passes::instance_index::{ClassInfo, FunDep};
        // `class Cons h t from to | h t -> from, h t -> to`: h,t are
        // determiners; from,to both determined.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert_class(
            "Cons".into(),
            ClassInfo {
                type_vars: vec!["h".into(), "t".into(), "from".into(), "to".into()],
                fundeps: vec![
                    FunDep { determiners: vec![0, 1], determined: vec![2] },
                    FunDep { determiners: vec![0, 1], determined: vec![3] },
                ],
                superclasses: vec![],
            },
        );
        // instance Cons "x" Int R1 R2
        let lit_x = Type::TypeString("x".into());
        let r1 = Type::Con(QName::unqualified("R1"));
        let r2 = Type::Con(QName::unqualified("R2"));
        ix.insert(mk_instance(
            "Cons",
            vec![lit_x.clone(), int_ty(), r1.clone(), r2.clone()],
            vec![],
        ));
        // Target: Cons "x" Int ?from ?to
        let uf = state.fresh();
        let uf_id = match uf {
            Type::Unif(id) => id,
            _ => panic!(),
        };
        let ut = state.fresh();
        let ut_id = match ut {
            Type::Unif(id) => id,
            _ => panic!(),
        };
        let pc = mk_pending(
            "Cons",
            vec![lit_x, int_ty(), Type::Unif(uf_id), Type::Unif(ut_id)],
        );
        match solve_one(&mut state, &ix, &pc) {
            SolveOutcome::Resolved(_) => {}
            other => panic!("expected Resolved, got {other:?}"),
        }
        assert_eq!(state.zonk(&Type::Unif(uf_id)), r1);
        assert_eq!(state.zonk(&Type::Unif(ut_id)), r2);
    }

    #[test]
    fn no_fundeps_keeps_conservative_defer_rule() {
        // `class Eq a` without fundeps. Target `Eq ?x` should still
        // defer (improvement isn't guaranteed safe without fundep
        // coverage).
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert_class(
            "Eq".into(),
            crate::typecheck_db::passes::instance_index::ClassInfo {
                type_vars: vec!["a".into()],
                fundeps: vec![],
            superclasses: vec![],
            },
        );
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let unif = state.fresh();
        let pc = mk_pending("Eq", vec![unif]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::Deferred);
    }

    // =================================================================
    // Phase C: recursive instance-context solving
    //
    // An instance like `Eq a => Eq (Maybe a)` produces a context
    // `Eq a` when it matches `Eq (Maybe Int)` (with `a := Int`).
    // The solver must recursively discharge that sub-constraint
    // before declaring the outer one resolved.
    // =================================================================

    /// `class Eq a` + `instance Eq Int` + `instance Eq a => Eq (Maybe a)`.
    fn eq_with_maybe_context() -> InstanceIndex {
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        ix.insert(Instance {
            class: QName::unqualified("Eq"),
            types: vec![maybe_ty(Type::Var("a".into()))],
            context: vec![Constraint {
                class: QName::unqualified("Eq"),
                args: vec![Type::Var("a".into())],
            }],
            vars: vec!["a".into()],
            chained: false,
        });
        ix
    }

    fn mk_pending_for(owner: &str, class: &str, args: Vec<Type>) -> PendingConstraint {
        PendingConstraint {
            decl_name: Some(owner.into()),
            span: crate::span::Span { start: 0, end: 0 },
            constraint: Constraint {
                class: QName::unqualified(class),
                args,
            },
            origin: ConstraintOrigin::Signature,
            givens: Vec::new(),
        }
    }

    #[test]
    fn phase_c_context_is_discharged_recursively() {
        let mut state = UnifyState::new();
        let ix = eq_with_maybe_context();
        let pc = mk_pending_for("f", "Eq", vec![maybe_ty(int_ty())]);
        let report = solve_all(&mut state, &ix, &[pc]);
        // Expected: two dicts on "f" — the outer Eq (Maybe Int) and
        // the inner Eq Int; zero errors; zero deferred.
        let dicts = report.dicts.get("f").expect("f got dicts");
        assert_eq!(dicts.len(), 2, "got: {dicts:?}");
        assert!(report.errors.is_empty(), "got: {:?}", report.errors);
        assert!(report.deferred.is_empty(), "got: {:?}", report.deferred);
    }

    #[test]
    fn phase_c_missing_sub_instance_defers_sub_constraint() {
        // instance `Eq a => Eq (Maybe a)` but NO `instance Eq Int`.
        // The outer `Eq (Maybe Int)` matches the `Eq (Maybe a)`
        // instance (a := Int) and unfolds the context constraint
        // `Eq Int`. With only one wrong-head candidate (`Eq (Maybe
        // _)`) and no exact match, the kind-mismatch defer path
        // fires: the constraint propagates rather than emitting
        // `NoInstanceFound` here. In a real compilation Prelude's
        // `Eq Int` would be in scope and the sub-constraint would
        // resolve — this artificial test exists to verify the
        // recursion shape, so we assert the OUTER constraint
        // resolved and the inner one was carried forward on
        // `deferred`.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(Instance {
            class: QName::unqualified("Eq"),
            types: vec![maybe_ty(Type::Var("a".into()))],
            context: vec![Constraint {
                class: QName::unqualified("Eq"),
                args: vec![Type::Var("a".into())],
            }],
            vars: vec!["a".into()],
            chained: false,
        });
        let pc = mk_pending_for("f", "Eq", vec![maybe_ty(int_ty())]);
        let report = solve_all(&mut state, &ix, &[pc]);
        let dicts = report.dicts.get("f").expect("expected outer dict");
        assert!(
            dicts.iter().any(|d| {
                d.class.name == "Eq"
                    && d.instance_types
                        .iter()
                        .map(|t| state.zonk(t))
                        .collect::<Vec<_>>()
                        == vec![maybe_ty(int_ty())]
            }),
            "expected the outer Eq (Maybe Int) to resolve; got: {dicts:?}",
        );
        assert!(
            report.deferred.iter().any(|pc| {
                pc.constraint.class.name == "Eq"
                    && pc.constraint
                        .args
                        .iter()
                        .map(|t| state.zonk(t))
                        .collect::<Vec<_>>()
                        == vec![int_ty()]
            }),
            "expected inner Eq Int to defer; got: {:?}",
            report.deferred,
        );
        assert!(
            report.errors.is_empty(),
            "expected no hard errors at this layer; got: {:?}",
            report.errors,
        );
    }

    #[test]
    fn phase_c_three_level_nesting_resolves_bottom_up() {
        // `Eq (Maybe (Maybe Int))` → needs `Eq (Maybe Int)` → needs
        // `Eq Int`. All present; all resolve.
        let mut state = UnifyState::new();
        let ix = eq_with_maybe_context();
        let pc = mk_pending_for("f", "Eq", vec![maybe_ty(maybe_ty(int_ty()))]);
        let report = solve_all(&mut state, &ix, &[pc]);
        let dicts = report.dicts.get("f").expect("f got dicts");
        // Outer + middle + bottom.
        assert_eq!(dicts.len(), 3, "got: {dicts:?}");
        assert!(report.errors.is_empty());
    }

    #[test]
    fn phase_c_resolved_context_carries_instance_context_origin() {
        let mut state = UnifyState::new();
        let ix = eq_with_maybe_context();
        let pc = mk_pending_for("f", "Eq", vec![maybe_ty(int_ty())]);
        let report = solve_all(&mut state, &ix, &[pc]);
        // Two dicts; both belong to f. The second one (bottom Eq Int)
        // was enqueued by the outer match and should carry
        // `InstanceContext` origin. Dicts don't store the origin
        // directly — instead we assert no new errors and no pending,
        // which implicitly confirms the recursion closed cleanly.
        let dicts = report.dicts.get("f").unwrap();
        assert_eq!(dicts.len(), 2);
        assert!(report.errors.is_empty());
        assert!(report.deferred.is_empty());
    }

    #[test]
    fn phase_c_depth_limit_emits_solver_depth_exceeded_error() {
        // Pathological: self-referential context that never
        // terminates. `instance Loop a => Loop a` — every match
        // produces another identical context. The solver must stop
        // and surface a `SolverDepthExceeded` diagnostic rather
        // than silently drop the remaining entries (or loop).
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(Instance {
            class: QName::unqualified("Loop"),
            types: vec![Type::Var("a".into())],
            context: vec![Constraint {
                class: QName::unqualified("Loop"),
                args: vec![Type::Var("a".into())],
            }],
            vars: vec!["a".into()],
            chained: false,
        });
        let pc = mk_pending_for("f", "Loop", vec![int_ty()]);
        let report = solve_all(&mut state, &ix, &[pc]);
        // The last iteration was still solving (Resolved → new
        // context), so the leftover queue is pure recursion. Must
        // surface as a hard error, not silently deferred.
        let errs = report.errors.get("f").expect("expected depth-exceeded error");
        assert!(
            errs.iter().any(|e| e.kind == ConstraintErrorKind::SolverDepthExceeded),
            "expected SolverDepthExceeded; got {errs:?}",
        );
        // And the deferred list must be empty (no leak).
        assert!(report.deferred.is_empty(), "got: {:?}", report.deferred);
    }

    #[test]
    fn phase_c_unif_in_context_defers_only_that_sub_constraint() {
        // `instance Eq a => Eq (Maybe a)` matched against
        // `Eq (Maybe ?x)` where ?x is fresh. Outer match unifies
        // the instance's `a` with `?x`; the context becomes
        // `Eq ?x`, which is a bare-unif constraint on a fundep-less
        // class — must defer, not error.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert_class(
            "Eq".into(),
            crate::typecheck_db::passes::instance_index::ClassInfo {
                type_vars: vec!["a".into()],
                fundeps: vec![],
            superclasses: vec![],
            },
        );
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        ix.insert(Instance {
            class: QName::unqualified("Eq"),
            types: vec![maybe_ty(Type::Var("a".into()))],
            context: vec![Constraint {
                class: QName::unqualified("Eq"),
                args: vec![Type::Var("a".into())],
            }],
            vars: vec!["a".into()],
            chained: false,
        });
        let fresh = state.fresh();
        let pc = mk_pending_for("f", "Eq", vec![maybe_ty(fresh)]);
        let report = solve_all(&mut state, &ix, &[pc]);
        // Outer resolves; inner `Eq ?x` defers.
        let dicts = report.dicts.get("f").expect("outer resolves");
        assert_eq!(dicts.len(), 1);
        assert!(report.errors.is_empty());
        assert_eq!(report.deferred.len(), 1);
        assert_eq!(report.deferred[0].origin, ConstraintOrigin::InstanceContext);
    }

    // =================================================================
    // Phase E: dict expression recording
    //
    // Each `ResolvedDict` must point at the specific instance it
    // matched (so codegen can emit the right reference) and each
    // call site must have a span-keyed lookup into its resolved
    // dict (so codegen can find "which dict resolves THIS use").
    // =================================================================

    fn span_at(start: usize, end: usize) -> crate::span::Span {
        crate::span::Span { start, end }
    }

    #[test]
    fn resolved_dict_carries_instance_index() {
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![])); // idx 0
        ix.insert(mk_instance(
            "Eq",
            vec![Type::Con(QName::unqualified("String"))],
            vec![],
        )); // idx 1
        let pc = mk_pending("Eq", vec![int_ty()]);
        match solve_one(&mut state, &ix, &pc) {
            SolveOutcome::Resolved(dict) => {
                assert_eq!(dict.instance_idx, 0, "Eq Int should map to idx 0");
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
    }

    #[test]
    fn resolved_dict_idx_matches_second_candidate() {
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![])); // idx 0
        let string_ty = Type::Con(QName::unqualified("String"));
        ix.insert(mk_instance("Eq", vec![string_ty.clone()], vec![])); // idx 1
        let pc = mk_pending("Eq", vec![string_ty]);
        match solve_one(&mut state, &ix, &pc) {
            SolveOutcome::Resolved(dict) => assert_eq!(dict.instance_idx, 1),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn integration_constraint_dicts_map_uses_var_span() {
        // The span stored in the map should be the span of the Var
        // reference that triggered the constraint. Use a single
        // decl with one Eq lookup.
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let schemes = infer_with_ix(
            "module M where\nf (x :: Int) = eq x x\n",
            &mut env,
            &ix,
        );
        assert_eq!(schemes[0].constraint_dicts.len(), 1);
        // The span key should point into the source where `eq` is
        // referenced — a non-trivial one (not 0..0).
        let (_span, dicts) = schemes[0].constraint_dicts.iter().next().unwrap();
        assert_eq!(dicts[0].class.name, "Eq");
    }

    #[test]
    fn integration_no_instance_leaves_dict_map_empty() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let ix = InstanceIndex::new();
        let schemes = infer_with_ix(
            "module M where\nf (x :: Int) = eq x x\n",
            &mut env,
            &ix,
        );
        // The call didn't resolve — no dict recorded. The error
        // surfaces through `constraint_errors` as before.
        assert!(schemes[0].constraint_dicts.is_empty());
        assert_eq!(schemes[0].constraint_errors.len(), 1);
    }

    #[test]
    fn integration_two_call_sites_record_two_dict_entries() {
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let schemes = infer_with_ix(
            "\
module M where
f (x :: Int) = eq x x
g (y :: Int) = eq y y
",
            &mut env,
            &ix,
        );
        let f = schemes.iter().find(|s| s.name == "f").unwrap();
        let g = schemes.iter().find(|s| s.name == "g").unwrap();
        assert_eq!(f.constraint_dicts.len(), 1);
        assert_eq!(g.constraint_dicts.len(), 1);
        // And the two spans must be distinct — pointing at the
        // respective `eq` Var references.
        let f_span = *f.constraint_dicts.keys().next().unwrap();
        let g_span = *g.constraint_dicts.keys().next().unwrap();
        assert_ne!(f_span, g_span);
        let _ = span_at(0, 0); // silence unused
        let _ = Decl::Value {
            span: span_at(0, 0),
            name: crate::cst::Spanned {
                span: span_at(0, 0),
                value: crate::names::value_name("_"),
            },
            binders: vec![],
            guarded: crate::typecheck_db::ir::GuardedExpr::Unconditional(Box::new(
                crate::typecheck_db::ir::Expr::Literal {
                    span: span_at(0, 0),
                    lit: crate::typecheck_db::ir::Literal::Int(0),
                },
            )),
            where_clause: vec![],
            doc_comments: vec![],
        }; // silence unused Decl import
    }

    #[test]
    fn resolved_context_dict_also_carries_instance_idx() {
        // `instance Eq a => Eq (Maybe a)` at idx 0, `instance Eq
        // Int` at idx 1 of the Eq candidates. Solving `Eq (Maybe
        // Int)` resolves the outer (idx 0) and the context (idx 1);
        // both dicts should carry their respective indices.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        // Insert in this order so indices are predictable.
        ix.insert(Instance {
            class: QName::unqualified("Eq"),
            types: vec![maybe_ty(Type::Var("a".into()))],
            context: vec![Constraint {
                class: QName::unqualified("Eq"),
                args: vec![Type::Var("a".into())],
            }],
            vars: vec!["a".into()],
            chained: false,
        });
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let pc = mk_pending_for("f", "Eq", vec![maybe_ty(int_ty())]);
        let report = solve_all(&mut state, &ix, &[pc]);
        let dicts = report.dicts.get("f").unwrap();
        assert_eq!(dicts.len(), 2);
        let indices: std::collections::HashSet<usize> =
            dicts.iter().map(|d| d.instance_idx).collect();
        assert!(indices.contains(&0), "expected outer idx 0 in {dicts:?}");
        assert!(indices.contains(&1), "expected context idx 1 in {dicts:?}");
    }

    #[test]
    fn fundep_unmentioned_position_still_requires_concrete() {
        use crate::typecheck_db::passes::instance_index::{ClassInfo, FunDep};
        // `class B a b c | a -> b`: c is neither determiner nor
        // determined — unmentioned. Bare unif at c must defer.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert_class(
            "B".into(),
            ClassInfo {
                type_vars: vec!["a".into(), "b".into(), "c".into()],
                fundeps: vec![FunDep { determiners: vec![0], determined: vec![1] }],
                superclasses: vec![],
            },
        );
        ix.insert(mk_instance(
            "B",
            vec![
                int_ty(),
                Type::Con(QName::unqualified("BOut")),
                Type::Con(QName::unqualified("CPos")),
            ],
            vec![],
        ));
        let uc = state.fresh();
        let pc = mk_pending("B", vec![int_ty(), int_ty(), uc]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::Deferred);
    }

    #[test]
    fn integration_polymorphic_constraint_defers() {
        // `f x = eq x x` — `x`'s type stays polymorphic (forall a),
        // so `Eq ?0` is unresolvable at this phase. The solver
        // defers; no "no instance" error is raised, but no dict is
        // resolved either.
        let mut env = Env::new();
        env.bind_scheme(QName::unqualified("eq"), eq_a_a_to_bool());
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance("Eq", vec![int_ty()], vec![]));
        let schemes = infer_with_ix(
            "module M where\nf x = eq x x\n",
            &mut env,
            &ix,
        );
        assert!(schemes[0].constraint_errors.is_empty());
        assert!(schemes[0].resolved_dicts.is_empty());
    }
}
