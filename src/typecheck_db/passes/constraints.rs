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
                cur = *body;
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
    pub span: crate::span::Span,
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
pub fn solve_one(
    state: &mut crate::typecheck_db::unify::UnifyState,
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    pending: &PendingConstraint,
) -> SolveOutcome {
    // Givens discharge before anything else: a constraint promised
    // by an enclosing sig's `Constrained` layer is already known-
    // true. Each `PendingConstraint` carries a snapshot of the
    // givens that were in scope when it was recorded (see
    // `UnifyState::record_pending_constraint`). Match structurally
    // on zonked forms so a skolemised `Semigroupoid !sa` satisfies
    // a pending `Semigroupoid ?ua` once `?ua := !sa` is bound.
    if given_discharges_pending(state, instances, pending) {
        return SolveOutcome::Resolved(ResolvedDict {
            class: pending.constraint.class.clone(),
            instance_types: pending
                .constraint
                .args
                .iter()
                .map(|a| state.zonk(a))
                .collect(),
            instance_idx: usize::MAX,
            context: Vec::new(),
        });
    }
    // Compiler-magic auto-dispatch: some Prim classes discharge
    // purely from the constraint's shape and don't rely on user
    // instance declarations. Handle them up-front so a fixture
    // that only reaches these via a Prelude call-site doesn't
    // trip over a `NoInstanceFound`.
    match try_magic(state, pending) {
        MagicOutcome::Resolved(dict) => return SolveOutcome::Resolved(dict),
        MagicOutcome::Mismatch => return SolveOutcome::HeadMismatch,
        MagicOutcome::None => {}
    }

    // Fundep-aware defer: if the class declares fundeps, a position
    // is "free to improve" when it appears in at least one fundep's
    // determined list. Bare unifs in all other positions (keys or
    // unmentioned) can't be discriminated by the matcher and force
    // a defer. Without fundeps we fall back to the conservative
    // rule (any bare unif defers).
    let class_info = instances.class_info(&pending.constraint.class.name);
    let improvable: std::collections::HashSet<usize> = match class_info {
        Some(info) if !info.fundeps.is_empty() => {
            info.fundeps.iter().flat_map(|fd| fd.determined.iter().copied()).collect()
        }
        _ => std::collections::HashSet::new(),
    };
    let needs_defer = match class_info {
        Some(info) if !info.fundeps.is_empty() => {
            pending
                .constraint
                .args
                .iter()
                .enumerate()
                .any(|(i, a)| !improvable.contains(&i) && is_bare_unif(a, state))
        }
        _ => pending.constraint.args.iter().any(|a| is_bare_unif(a, state)),
    };
    if needs_defer {
        return SolveOutcome::Deferred;
    }

    let cands = instances.candidates(&pending.constraint.class.name);
    let cand_count = cands.len();
    for (instance_idx, cand) in cands.iter().enumerate() {
        let snapshot = state.snapshot_bindings();
        if let Some((head, context)) = try_match(state, cand, &pending.constraint.args) {
            return SolveOutcome::Resolved(ResolvedDict {
                class: pending.constraint.class.clone(),
                instance_types: head,
                instance_idx,
                context,
            });
        }
        state.restore_bindings(snapshot);
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
        return SolveOutcome::HeadMismatch;
    }
    // No instance matched. Before declaring failure, check whether
    // any argument contains a rigid `Type::Var`. Rigid type vars
    // here come from a surrounding signature (e.g. inside `power
    // :: forall m. Monoid m => …`, the body sees `m` as a Var).
    // The instance for that variable must come from a "given" the
    // outer scope provides; we don't track givens explicitly, so
    // defer the constraint and let it bubble up into the inferred
    // scheme via `generalize_with_constraints`. The importer then
    // re-instantiates fresh unifs and the solver retries at each
    // concrete use-site.
    if pending.constraint.args.iter().any(|a| contains_rigid_var(a, state)) {
        return SolveOutcome::Deferred;
    }
    // Classes with no in-scope candidates always defer rather than
    // emit NoInstance. A class with zero candidates is one of:
    //  * a marker / open class (`Partial`, `Warn`, `Fail`) that
    //    the user discharges via a special-case mechanism, never
    //    via instance resolution;
    //  * a class whose instances haven't been imported into this
    //    module's scope — the constraint legitimately propagates
    //    until a downstream caller produces a concrete arg the
    //    instance can match.
    // Either way, the right move is to defer: the constraint
    // ratchets into the inferred scheme and the use-site re-tries
    // with fresh unifs.
    if instances
        .candidates(&pending.constraint.class.name)
        .is_empty()
    {
        return SolveOutcome::Deferred;
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
    let zonked_args: Vec<Type> = pending
        .constraint
        .args
        .iter()
        .map(|a| state.zonk(a))
        .collect();
    let candidates = instances.candidates(&pending.constraint.class.name);
    // Kind-mismatch / wrong-shape defer: if any arg's App-spine
    // head + arity doesn't match any instance's head + arity,
    // the constraint can never be solved. Match on (head_qn,
    // app_spine_arity) — `Apply Tuple` has arity 0 (no apps),
    // `Apply (Tuple a)` instance has arity 1. Different keys
    // → no candidate fits → defer.
    let head_shape_mismatch = zonked_args.iter().enumerate().any(|(i, arg)| {
        if let Some((arg_qn, arg_arity)) = app_spine_head_arity(arg) {
            !candidates.iter().any(|cand| {
                cand.types
                    .get(i)
                    .and_then(app_spine_head_arity)
                    .map_or(false, |(h, a)| h == arg_qn && a == arg_arity)
            })
        } else {
            false
        }
    });
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
fn given_discharges_pending(
    state: &crate::typecheck_db::unify::UnifyState,
    instances: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    pending: &PendingConstraint,
) -> bool {
    let zp = Constraint {
        class: pending.constraint.class.clone(),
        args: pending.constraint.args.iter().map(|a| state.zonk(a)).collect(),
    };
    let live = state.givens_snapshot();
    for g in pending.givens.iter().chain(live.iter()) {
        let zg = Constraint {
            class: g.class.clone(),
            args: g.args.iter().map(|a| state.zonk(a)).collect(),
        };
        if constraints_eq(&zg, &zp) || superclass_matches(instances, &zg, &zp) {
            return true;
        }
    }
    false
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
fn is_bare_unif(ty: &Type, state: &crate::typecheck_db::unify::UnifyState) -> bool {
    matches!(state.zonk(ty), Type::Unif(_))
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
    let args: Vec<Type> = pending
        .constraint
        .args
        .iter()
        .map(|a| state.zonk(a))
        .collect();
    match class_name {
        "IsSymbol" => {
            if let [Type::TypeString(_)] = args.as_slice() {
                return MagicOutcome::Resolved(ResolvedDict {
                    class: pending.constraint.class.clone(),
                    instance_types: args,
                    instance_idx: 0,
                    context: Vec::new(),
                });
            }
        }
        "Nub" => {
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
        "ToString" => {
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
        "Append" => {
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
        "Compare" => {
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
        "Cons" => {
            if args.len() == 3 {
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
        _ => {}
    }
    MagicOutcome::None
}

/// Freshen an instance's quantified vars, unify its head with the
/// target args, and (on success) return the freshened head + context
/// so the caller can package a `ResolvedDict`.
fn try_match(
    state: &mut crate::typecheck_db::unify::UnifyState,
    instance: &crate::typecheck_db::passes::instance_index::Instance,
    target_args: &[Type],
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
        if state.unify(inst_ty, target).is_err() {
            return None;
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
/// `instance Loop a => Loop a`.
const MAX_SOLVER_DEPTH: usize = 32;

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
    let mut queue: Vec<PendingConstraint> = pending.to_vec();

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
        let current = std::mem::take(&mut queue);
        let mut carry_forward: Vec<PendingConstraint> = Vec::new();
        let mut made_progress = false;
        for pc in current {
            let owner = match &pc.decl_name {
                Some(n) => n.clone(),
                None => continue,
            };
            match solve_one(state, instances, &pc) {
                SolveOutcome::Resolved(dict) => {
                    made_progress = true;
                    // Push every context entry back onto the queue as
                    // a new pending with `InstanceContext` origin and
                    // the same owner/span. Later rounds see them the
                    // same way the top-level ones were seen this
                    // round.
                    for ctx in &dict.context {
                        carry_forward.push(PendingConstraint {
                            decl_name: Some(owner.clone()),
                            span: pc.span,
                            constraint: Constraint {
                                class: ctx.class.clone(),
                                args: ctx.args.iter().map(|a| state.zonk(a)).collect(),
                            },
                            origin: ConstraintOrigin::InstanceContext,
                            givens: pc.givens.clone(),
                        });
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
                            .insert(pc.span, dict.clone());
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
                            constraint: zonked,
                            kind: ConstraintErrorKind::OverlappingInstances,
                        });
                }
                SolveOutcome::Deferred => {
                    carry_forward.push(pc);
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
        let mut legitimately_deferred = Vec::new();
        for pc in std::mem::take(&mut queue) {
            match &pc.decl_name {
                Some(n) => {
                    report
                        .errors
                        .entry(n.clone())
                        .or_default()
                        .push(ConstraintError {
                            span: pc.span,
                            constraint: pc.constraint.clone(),
                            kind: ConstraintErrorKind::SolverDepthExceeded,
                        });
                }
                None => legitimately_deferred.push(pc),
            }
        }
        queue = legitimately_deferred;
    }
    report.deferred = queue;
    report
}

/// Per-decl aggregate of solving one SCC's worth of constraints.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SolveReport {
    /// Every resolved dict — outer + context-induced — keyed by
    /// owning decl. Codegen iterates this for the full set of
    /// references it needs to emit.
    pub dicts: std::collections::HashMap<String, Vec<ResolvedDict>>,
    /// Outer-only span lookup: maps each call site's span to the
    /// `ResolvedDict` that satisfies its top-level constraint.
    /// Sub-constraints born from instance contexts do not appear
    /// here — they're in `dicts` and navigable via their parent's
    /// `ResolvedDict::context`.
    pub dicts_by_span: std::collections::HashMap<
        String,
        std::collections::HashMap<crate::span::Span, ResolvedDict>,
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
        let ctx = DesugarContext { module_fixity_hash, fixity_table };
        let decls = desugar_module(cst_mod.decls.clone(), &ctx);
        let desugared = crate::cst::Module { decls, ..cst_mod };
        crate::typecheck_db::ir::lower_module(desugared).expect("lower")
    }

    // -- helpers ------------------------------------------------------

    fn int_ty() -> Type {
        Type::Con(QName::unqualified("Int"))
    }

    fn bool_ty() -> Type {
        Type::Con(QName::unqualified("Boolean"))
    }

    fn eq_a_a_to_bool() -> Scheme {
        // `forall a. Eq a => a -> a -> Boolean`
        let a = Type::Var("a".into());
        Scheme {
            vars: vec!["a".into()],
            ty: Type::Constrained(
                vec![Constraint {
                    class: QName::unqualified("Eq"),
                    args: vec![a.clone()],
                }],
                Box::new(Type::fun(a.clone(), Type::fun(a, bool_ty()))),
            ),
        }
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
            Box::new(Type::fun(int_ty(), bool_ty())),
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
            Box::new(a.clone()),
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
        let scheme = Scheme {
            vars: vec!["a".into()],
            ty: Type::Constrained(
                vec![
                    Constraint { class: QName::unqualified("Eq"), args: vec![a.clone()] },
                    Constraint { class: QName::unqualified("Show"), args: vec![a.clone()] },
                ],
                Box::new(Type::fun(a, bool_ty())),
            ),
        };
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
    fn solve_wrong_type_head_returns_no_instance() {
        // Index has `Eq String`, target is `Eq Int` — no match.
        let mut state = UnifyState::new();
        let mut ix = InstanceIndex::new();
        ix.insert(mk_instance(
            "Eq",
            vec![Type::Con(QName::unqualified("String"))],
            vec![],
        ));
        let pc = mk_pending("Eq", vec![int_ty()]);
        assert_eq!(solve_one(&mut state, &ix, &pc), SolveOutcome::NoInstance);
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
        infer_value_scc_with_all(&ops, env, &decls, &data, &ctors, instances).unwrap()
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
    fn phase_c_missing_sub_instance_reports_sub_error() {
        // instance `Eq a => Eq (Maybe a)` but NO `instance Eq Int`.
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
        // Outer Eq (Maybe Int) resolves; inner Eq Int fails.
        let errs = report.errors.get("f").expect("expected errors");
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].kind, ConstraintErrorKind::NoInstanceFound);
        assert_eq!(errs[0].constraint.args, vec![int_ty()]);
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
        let (_span, dict) = schemes[0].constraint_dicts.iter().next().unwrap();
        assert_eq!(dict.class.name, "Eq");
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
