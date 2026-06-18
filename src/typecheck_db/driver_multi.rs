//! Multi-module driver: `check_many_modules`.
//!
//! Given a set of parsed modules, sort them by their import
//! graph, check each in order while threading through a shared
//! [`ModuleRegistry`], and return the per-module results.
//!
//! Scope today:
//! * Topological ordering + cycle detection (SCCs with more than
//!   one module are reported as `CycleInModules`).
//! * Per-module import resolution via [`build_env_from_imports`].
//! * Per-module desugar + inference + exhaustiveness + constraints
//!   solving (delegating to the existing single-module pipeline).
//! * `distill_exports` on the result so downstream modules can
//!   import what was just checked.
//!
//! Not yet covered: fine-grained SCC breakdown *within* a module
//! (we pass all value decls to one `infer_value_scc_with_all`
//! call), per-decl cache invalidation across module boundaries,
//! and re-export (`module N` in an export clause).

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cst;
use crate::typecheck_db::desugar::{desugar_module, DesugarContext};
use crate::typecheck_db::driver::{CacheOutcome, TypecheckDb};
use crate::typecheck_db::env::Env;
use crate::typecheck_db::key::{hash_bytes, OutputHash};
use crate::typecheck_db::module_registry::{distill_exports, FixityDecl, ModuleExports, ModuleRegistry};
use crate::typecheck_db::passes::constraints::{ConstraintError, PendingConstraint, ResolvedDict};
use crate::typecheck_db::passes::exhaustiveness::{CtorInfo, CtorRegistry, DataConstructors, NonExhaustive};
use crate::typecheck_db::passes::check_nonvalue::{
    self, check_class, check_data, check_fixity, check_foreign, check_foreign_data,
    check_instance, check_type_alias, class_info_from_class_shape, ctor_info_from_data_shape,
    decl_key_for_nonvalue, decl_source_hash as nonvalue_source_hash, instance_from_shape,
    is_nonvalue_kind,
};
use crate::typecheck_db::passes::imports::{build_env_from_imports, ImportError};
use crate::typecheck_db::passes::infer_value::{
    infer_value_scc_with_all, put_cached, scheme_only_output_hash, try_get_cached,
    InferError, InferredScheme,
};
use crate::typecheck_db::passes::instance_index::{ClassInfo, Instance, InstanceIndex};
use crate::typecheck_db::passes::names::{free_names, NameKind};
use crate::typecheck_db::types::TypeOpMap;

// ---------------------------------------------------------------------------
// Result + error types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct ModuleCheckResult {
    pub name: String,
    pub schemes: Vec<InferredScheme>,
    pub import_errors: Vec<ImportError>,
    /// Aggregated across every decl in the module.
    pub exhaustiveness_errors: Vec<NonExhaustive>,
    pub constraint_errors: Vec<ConstraintError>,
    pub deferred_constraints: Vec<PendingConstraint>,
    pub resolved_dicts: Vec<ResolvedDict>,
    /// Inference bailed out early. When set, `schemes` contains
    /// whatever was inferred before the error.
    pub inference_error: Option<InferError>,
    /// Per-value-decl cache outcome from `infer_value_scc`. Decls in
    /// the same SCC share one outcome. Populated when the driver is
    /// invoked through [`check_many_modules_with_db`]; on a fresh
    /// in-memory DB every decl is a [`CacheOutcome::Miss`].
    pub decl_outcomes: HashMap<String, CacheOutcome>,
    /// Typed-hole diagnostics encountered anywhere in this module,
    /// aggregated across every decl's `hole_diagnostics`.
    pub hole_diagnostics:
        Vec<crate::typecheck_db::passes::infer_value::HoleDiagnostic>,
    /// Structural validation errors (duplicates, orphans, fixity conflicts,
    /// etc.) emitted before any type inference runs.
    pub validation_errors:
        Vec<crate::typecheck_db::passes::validate_decls::ValidationError>,
    /// Kind-arity errors. Currently catches over-application of type
    /// constructors and arity mismatches in class constraints. Pure
    /// CST walk; no kind unification.
    pub kind_errors:
        Vec<crate::typecheck_db::passes::kind_check::KindError>,
    /// Coercible-related structural errors: RoleMismatch on `type
    /// role` decls that are more permissive than inferred roles,
    /// plus InvalidCoercibleInstanceDeclaration for user-written
    /// Coercible instances (forbidden).
    pub coercible_errors:
        Vec<crate::typecheck_db::passes::coercible_check::CoercibleError>,
    /// Generated JavaScript for the whole module, produced by the
    /// per-declaration codegen (`DeclDb` engine). `None` unless codegen
    /// was enabled on the `TypecheckDb` via `set_codegen(true)`.
    pub js_module_text: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MultiModuleError {
    /// An SCC of size >1 — modules mutually import each other.
    CycleInModules(Vec<String>),
    /// Module M imports N, but N is neither in the input nor in
    /// the registry (and isn't a Prim module).
    UnknownImport { from: String, missing: String },
    /// The same module name was declared in two source files of
    /// the same build unit. Reference compiler reports as
    /// `DuplicateModule`.
    DuplicateModule(String),
    /// A user module declared a name in the `Prim` namespace
    /// (`module Prim where` or `module Prim.X where`). Reserved
    /// for compiler-defined terms.
    CannotDefinePrimModules(String),
}

/// Aggregate return of a multi-module check.
#[derive(Debug, Clone)]
pub struct ModuleCheckReport {
    pub registry: ModuleRegistry,
    pub results: Vec<ModuleCheckResult>,
    pub errors: Vec<MultiModuleError>,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// One module's input to the driver: canonical name, full source
/// text (needed for per-decl source-slice hashing), and the parsed
/// CST.
pub struct ModuleInput {
    pub name: String,
    pub source: String,
    pub module: cst::Module,
}

impl ModuleInput {
    pub fn new(
        name: impl Into<String>,
        source: impl Into<String>,
        module: cst::Module,
    ) -> Self {
        Self { name: name.into(), source: source.into(), module }
    }
}

/// Check every module in `modules` against a fresh in-memory
/// [`TypecheckDb`]. Convenience wrapper: nothing persists across calls.
pub fn check_many_modules(modules: Vec<ModuleInput>) -> ModuleCheckReport {
    let mut db = TypecheckDb::open_in_memory().expect("in-memory TypecheckDb");
    check_many_modules_with_db(&mut db, modules)
}

/// Check every module against a caller-owned [`TypecheckDb`]. Call
/// this twice with the same `db` to observe incremental behavior:
/// unchanged decls return [`CacheOutcome::Hit`] on the second run.
pub fn check_many_modules_with_db(
    db: &mut TypecheckDb,
    modules: Vec<ModuleInput>,
) -> ModuleCheckReport {
    let mut registry = ModuleRegistry::new();
    let mut results: Vec<ModuleCheckResult> = Vec::new();
    let errors =
        check_many_modules_inner(db, &mut registry, modules, |r| results.push(r));
    ModuleCheckReport { registry, results, errors }
}

/// Streaming variant: process each module's result via `on_result` as
/// soon as it's produced, then drop it. Memory stays bounded by one
/// in-flight `ModuleCheckResult` plus the internal `ModuleRegistry`
/// (whose size is bounded by exported names, not body details).
///
/// Use this for sweeps over many thousand modules where retaining
/// every `ModuleCheckResult` would cost 100s of GB — the standard
/// `check_many_modules` returns a `Vec<ModuleCheckResult>` that
/// duplicates every resolved dict and every InferredScheme.
pub fn check_many_modules_streaming(
    modules: Vec<ModuleInput>,
    on_result: impl FnMut(ModuleCheckResult),
) -> Vec<MultiModuleError> {
    let mut db = TypecheckDb::open_in_memory().expect("in-memory TypecheckDb");
    let mut registry = ModuleRegistry::new();
    check_many_modules_inner(&mut db, &mut registry, modules, on_result)
}

/// Streaming + caller-owned `db` for incremental scenarios.
pub fn check_many_modules_streaming_with_db(
    db: &mut TypecheckDb,
    modules: Vec<ModuleInput>,
    on_result: impl FnMut(ModuleCheckResult),
) -> Vec<MultiModuleError> {
    let mut registry = ModuleRegistry::new();
    check_many_modules_inner(db, &mut registry, modules, on_result)
}

/// Shared core: drives the topo-sorted check loop, forwarding each
/// module's result through `on_result` so the caller decides whether
/// to collect them all or drop after consuming. Returns driver-level
/// errors (cycles, dup module names, Prim namespace abuse).
fn check_many_modules_inner(
    db: &mut TypecheckDb,
    registry: &mut ModuleRegistry,
    modules: Vec<ModuleInput>,
    mut on_result: impl FnMut(ModuleCheckResult),
) -> Vec<MultiModuleError> {
    let name_index: HashMap<String, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, m)| (m.name.clone(), i))
        .collect();

    let mut errors: Vec<MultiModuleError> = Vec::new();

    // Reject build units that declare the same module name in two
    // different source files. The HashMap above silently dedupes by
    // last-write so we re-scan the original list to catch the dup.
    let mut seen_names: std::collections::HashSet<&str> =
        std::collections::HashSet::new();
    let mut duplicate_names: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for m in &modules {
        if !seen_names.insert(m.name.as_str()) {
            duplicate_names.insert(m.name.clone());
        }
    }
    for name in &duplicate_names {
        errors.push(MultiModuleError::DuplicateModule(name.clone()));
    }

    // User modules may not declare a name in the `Prim` namespace —
    // `Prim` and its sub-modules are reserved for compiler-defined
    // terms. The reference compiler's `CannotDefinePrimModules`.
    for m in &modules {
        if m.name == "Prim" || m.name.starts_with("Prim.") {
            errors.push(MultiModuleError::CannotDefinePrimModules(m.name.clone()));
        }
    }

    let (order, cycles) = topo_sort_modules(&modules, &name_index);
    for cycle in cycles {
        errors.push(MultiModuleError::CycleInModules(cycle));
    }

    let trace = std::env::var_os("TYPECHECK_DB_TRACE").is_some();
    // Timing trace prints each module's elapsed time. Useful for
    // finding hot/slow modules in big package sweeps. Cheap when
    // unset (one Instant::now per module).
    let timing_trace = std::env::var_os("TYPECHECK_DB_PER_MODULE_TIMING").is_some();
    let slow_threshold_ms: u128 = std::env::var("TYPECHECK_DB_SLOW_MS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(500);
    for (i, idx) in order.iter().enumerate() {
        let input = &modules[*idx];
        if trace {
            eprintln!(
                "[typecheck_db] [{i}/{}] checking {}",
                order.len(),
                input.name,
            );
        }
        let started = std::time::Instant::now();
        crate::memstats::checkpoint(&format!("module:{}:start", input.name));
        let result = check_one_module(db, input, registry);
        crate::memstats::checkpoint(&format!("module:{}:end", input.name));
        let elapsed_ms = started.elapsed().as_millis();
        if timing_trace || elapsed_ms >= slow_threshold_ms {
            eprintln!(
                "[typecheck_db] [{i}/{}] {} {} ms",
                order.len(),
                input.name,
                elapsed_ms,
            );
        }
        on_result(result);
    }

    if std::env::var_os("TYPECHECK_DB_TIMING").is_some() {
        phase_timing::dump();
    }

    errors
}

// ---------------------------------------------------------------------------
// Per-phase timing.
//
// Opt-in (`TYPECHECK_DB_TIMING=1`). Wrap each pass inside `check_one_module`
// with a `phase_timing::Scope`; the scope accumulates per-pass totals into a
// process-wide table. After the multi-module run finishes the totals are
// printed sorted descending so the dominant phase is obvious without
// per-iteration noise. Zero-overhead when the env var is unset (no
// `Instant::now()` and no env-var lookup, both cached behind a `OnceLock`).
// ---------------------------------------------------------------------------

pub mod phase_timing {
    use std::collections::HashMap;
    use std::sync::Mutex;
    use std::sync::OnceLock;
    use std::time::{Duration, Instant};

    fn enabled() -> bool {
        // Cache the env-var lookup in a `OnceLock<bool>` so the
        // per-phase `Scope::new` call doesn't syscall through
        // `std::env::var_os` on every entry.
        static E: OnceLock<bool> = OnceLock::new();
        *E.get_or_init(|| std::env::var_os("TYPECHECK_DB_TIMING").is_some())
    }

    fn table() -> &'static Mutex<HashMap<&'static str, Duration>> {
        static T: OnceLock<Mutex<HashMap<&'static str, Duration>>> = OnceLock::new();
        T.get_or_init(|| Mutex::new(HashMap::new()))
    }

    pub fn record(name: &'static str, dur: Duration) {
        let mut t = table().lock().expect("phase_timing table");
        *t.entry(name).or_default() += dur;
    }

    pub fn dump() {
        let t = table().lock().expect("phase_timing table");
        let mut entries: Vec<_> = t.iter().collect();
        entries.sort_by(|a, b| b.1.cmp(a.1));
        let total: Duration = entries.iter().map(|(_, d)| **d).sum();
        eprintln!("[typecheck_db] phase totals (across all modules):");
        for (name, dur) in &entries {
            let pct = if total.is_zero() {
                0.0
            } else {
                100.0 * dur.as_secs_f64() / total.as_secs_f64()
            };
            eprintln!("  {:>7.2?}  {:>5.1}%  {}", dur, pct, name);
        }
        eprintln!("  {:>7.2?}  100.0%  TOTAL", total);
    }

    pub struct Scope {
        name: &'static str,
        start: Option<Instant>,
    }

    impl Scope {
        pub fn new(name: &'static str) -> Self {
            Self {
                name,
                start: enabled().then(Instant::now),
            }
        }
    }

    impl Drop for Scope {
        fn drop(&mut self) {
            if let Some(start) = self.start {
                record(self.name, start.elapsed());
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Single-module orchestration
// ---------------------------------------------------------------------------

fn check_one_module(
    db: &mut TypecheckDb,
    input: &ModuleInput,
    registry: &mut ModuleRegistry,
) -> ModuleCheckResult {
    let name = input.name.clone();
    let module = &input.module;
    // Codegen consumes each decl's `constraint_dicts`, which must be zonked to
    // concrete types; gate that extra work on codegen being enabled.
    crate::typecheck_db::passes::infer_value::set_zonk_constraint_dicts(db.codegen_enabled());
    // Slow-module phase trace: when a module exceeds 5s overall,
    // dump a per-phase breakdown of where the time went. Off by
    // default; set TYPECHECK_DB_PROFILE_SLOW=1 to enable.
    let profile_slow = std::env::var_os("TYPECHECK_DB_PROFILE_SLOW").is_some();
    let phase_total = std::time::Instant::now();
    let mut phase_log: Vec<(String, std::time::Duration)> = Vec::new();
    macro_rules! phase {
        ($label:expr, $body:expr) => {{
            let _t = std::time::Instant::now();
            let _r = $body;
            if profile_slow {
                phase_log.push(($label.to_string(), _t.elapsed()));
            }
            _r
        }};
    }

    // 1) Pull imports into an Env + InstanceIndex.
    let (mut env, mut instance_index, mut import_errors) =
        phase!("1.build_env_from_imports", build_env_from_imports(module, registry));
    env.self_module = name.clone();

    // 1b) Structural validation (duplicates, orphans, fixity conflicts,
    //     duplicate type arguments). Pure traversal over the CST plus
    //     a small map of imported alias arities so the
    //     PartiallyAppliedSynonym detector can recognise imported
    //     synonyms used via type-operator syntax (e.g. `(~>)` from a
    //     `infixr type NaturalTransformation as ~>` in Prelude).
    let imported_alias_arity =
        build_imported_alias_arity(module, registry);
    let imported_poly_kind_set =
        build_imported_poly_kind_set(module, registry);
    let imported_class_arity =
        build_imported_class_arity(module, registry);
    let imported_class_fundeps =
        build_imported_class_fundeps(module, registry);
    let mut validation_errors =
        crate::typecheck_db::passes::validate_decls::validate_module_with_class_fundeps(
            module,
            &imported_alias_arity,
            &imported_poly_kind_set,
            &imported_class_arity,
            &imported_class_fundeps,
        );

    // Registry-aware UnknownExport check: walk the module's export
    // list and emit when a name isn't locally declared AND isn't
    // brought into scope by any of the module's imports. The
    // CST-only detector inside validate_decls bails on open imports
    // because it can't enumerate them — this is the precise
    // counterpart that runs once we have the registry.
    detect_unknown_exports_registry(module, registry, &mut validation_errors);

    // Registry-aware UnknownName check for type-constructor refs in
    // top-level signatures. The self-re-export `module M (module M)`
    // case is now handled by `expand_module_reexports`, so the
    // full type-position check is safe.
    detect_unknown_kind_refs_registry(module, registry, &mut validation_errors);
    detect_unknown_type_refs_registry(module, registry, &mut validation_errors);

    // Use-site ScopeConflict (open + open). Re-export chains
    // through Prelude are deduped via value_origins, so importing
    // both Prelude and Data.Function doesn't false-positive on
    // shared re-exports. Only fires when a referenced name has
    // distinct ORIGIN modules in scope through open imports.
    detect_use_site_scope_conflict(module, registry, &mut import_errors);

    // NonAssociativeError on imported operators: the in-pass
    // detector inside validate_decls only knows local fixities.
    // Build imported value/type fixities → associativity from the
    // registry and re-run the chain check.
    let (imp_val_op_assoc, imp_type_op_assoc) =
        build_imported_op_associativity(module, registry);
    crate::typecheck_db::passes::validate_decls::detect_non_associative_chain_with_imports(
        &module.decls,
        &imp_val_op_assoc,
        &imp_type_op_assoc,
        &mut validation_errors,
    );

    // MixedAssociativityError on imported operators (precedence +
    // assoc together).
    let (imp_val_fix, imp_type_fix) = build_imported_op_fixity(module, registry);
    crate::typecheck_db::passes::validate_decls::detect_mixed_associativity(
        &module.decls,
        &imp_val_fix,
        &imp_type_fix,
        &mut validation_errors,
    );

    // 1c) Kind-arity check. Catches over-application of type
    //     constructors and arity mismatches in class constraints.
    //     Reads the registry for imported types/classes.
    let kind_errors = phase!("1c.kind_check",
        crate::typecheck_db::passes::kind_check::check_module(module, registry));

    // 1d) Coercible-related checks: role validation + forbidden
    //     user-written Coercible instances. CST-only — doesn't need
    //     the registry.
    let coercible_errors = phase!("1d.coercible_check",
        crate::typecheck_db::passes::coercible_check::check_module(module));

    // 2) Desugar the module as a whole, then lower cst → ir so
    //    every downstream pass consumes an `ir::Decl` that has no
    //    residual operator nodes (Op / OpParens / BacktickApp).
    let ctx = phase!("2.build_desugar_context",
        build_desugar_context(module, registry));
    let desugared_cst: Vec<cst::Decl> = phase!("2.desugar_module",
        desugar_module(module.decls.clone(), &ctx));
    let desugared: Vec<crate::typecheck_db::ir::Decl> = phase!("2.lower_decl", {
        desugared_cst
            .into_iter()
            .map(crate::typecheck_db::ir::lower_decl)
            .collect::<Result<_, _>>()
            .unwrap_or_else(|e| {
                panic!("cst → ir lowering failed in {}: {e:?}", name)
            })
    });

    // 2b) Resolve every qualified name in the IR to its DEFINING
    //     module. After this pass every `Qualified<N>::module` is
    //     `Some(origin_module)`. Downstream consumers can lookup via
    //     env's qualified path; the existing unqualified fallback
    //     in `lookup_qualified` covers locally-pre-inserted recursive
    //     values until Step C lands.
    let desugared: Vec<crate::typecheck_db::ir::Decl> = phase!("2b.resolve_pass", {
        let prims = crate::typecheck_db::prim::prim_exports();
        let synthetic = crate::typecheck_db::ir::Module {
            span: module.span,
            name: module.name.clone(),
            exports: module.exports.clone(),
            imports: module.imports.clone(),
            decls: desugared,
            comments: module.comments.clone(),
            doc_comments: module.doc_comments.clone(),
        };
        let resolved = crate::typecheck_db::passes::resolve_pass::resolve_module(
            synthetic,
            &name,
            registry,
            &prims,
        );
        resolved.decls
    });

    // Type-level operator map: every `infixr N type Target as op`
    // decl in this module (and every imported module) becomes an
    // entry mapping `(module, op)` → `Target`'s QName so
    // `convert_type_expr` can rewrite `a /\ b` to `App(App(Tuple,
    // a), b)` at conversion time. Without this, instance heads
    // declared as `Test (a /\ b)` end up keyed on `Type::Con("/\")`
    // and never match a use-site `Test (Tuple Int Int)`.
    let mut type_ops: TypeOpMap = TypeOpMap::default();
    for d in &module.decls {
        if let cst::Decl::Fixity { operator, target, is_type, .. } = d {
            if !*is_type {
                continue;
            }
            // Local fixity decls are unqualified at the site of
            // declaration — no module prefix on the op.
            let op_name = crate::typecheck_db::util::resolve_symbol(
                operator.value.symbol(),
            );
            let target_module = target
                .module
                .map(crate::typecheck_db::util::resolve_symbol);
            let target_name = crate::typecheck_db::util::resolve_symbol(target.name);
            type_ops.insert(
                (None, op_name),
                crate::typecheck_db::types::QName {
                    module: target_module,
                    name: target_name,
                },
            );
        }
    }
    // Populate type_ops from imported modules' type fixities.
    // Type operators MUST always desugar at convert_type_expr time
    // (otherwise alias bodies and call-site annotations stay
    // `App(Con(None, "+"), …)` and never unify against fully-
    // resolved instances or expansions). The earlier "cross-module
    // only" filter was a no-op when `distill_exports` left local-
    // type targets as `target_module = None` (every entry passed
    // the unwrap_or fallback). Now that `distill_exports` pins
    // local-type targets to `Some(self_module)`, the filter would
    // start dropping entries like Type.Row's `+` → RowApply and
    // Type.Function's `$` → Apply, so we no longer apply it here.
    for imp in &module.imports {
        let mod_name = imp
            .module
            .parts
            .iter()
            .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
            .collect::<Vec<_>>()
            .join(".");
        // Qualified-only imports (`import M as Q`) make type
        // operators available ONLY under `Q.<op>`, not bare `<op>`.
        // Register every imported type fixity under the
        // (Some(qualifier), op) key so `convert_type_expr`'s
        // qualified-op lookup finds it. Without this, `H.<>`
        // (where `H` aliases Halogen.Hooks) stays as
        // `Con(Some("H"), "<>")` and mismatches against the
        // qualified target reached via a different code path.
        // Closes the HookAppend cluster (OaVirtual.Hooks.DOM.{Keypress,
        // Click}, Review.Hooks.DOM.Keypress).
        if let Some(qualifier) = &imp.qualified {
            if let Some(exports) = registry.get(&mod_name) {
                if exports.type_fixities.is_empty() {
                    continue;
                }
                let qualifier_str = qualifier
                    .parts
                    .iter()
                    .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                    .collect::<Vec<_>>()
                    .join(".");
                for (op_name, decl) in &exports.type_fixities {
                    let imported = match &imp.imports {
                        None => true,
                        Some(cst::ImportList::Hiding(list)) => {
                            !list.iter().any(|item| matches!(item,
                                cst::Import::TypeOp(n)
                                if crate::typecheck_db::util::resolve_symbol(n.value.symbol()) == *op_name))
                        }
                        Some(cst::ImportList::Explicit(list)) => {
                            list.iter().any(|item| matches!(item,
                                cst::Import::TypeOp(n)
                                if crate::typecheck_db::util::resolve_symbol(n.value.symbol()) == *op_name))
                        }
                    };
                    if imported {
                        let target = crate::typecheck_db::types::QName {
                            module: decl.target_module.clone(),
                            name: decl.target_name.clone(),
                        };
                        type_ops
                            .entry((Some(qualifier_str.clone()), op_name.clone()))
                            .or_insert(target);
                    }
                }
            }
            continue;
        }
        if let Some(exports) = registry.get(&mod_name) {
            if exports.type_fixities.is_empty() {
                continue;
            }
            for (op_name, decl) in &exports.type_fixities {
                let imported = match &imp.imports {
                    None => true,
                    Some(cst::ImportList::Hiding(list)) => {
                        !list.iter().any(|item| matches!(item,
                            cst::Import::TypeOp(n)
                            if crate::typecheck_db::util::resolve_symbol(n.value.symbol()) == *op_name))
                    }
                    Some(cst::ImportList::Explicit(list)) => {
                        list.iter().any(|item| matches!(item,
                            cst::Import::TypeOp(n)
                            if crate::typecheck_db::util::resolve_symbol(n.value.symbol()) == *op_name))
                    }
                };
                if imported {
                    let target = crate::typecheck_db::types::QName {
                        module: decl.target_module.clone(),
                        name: decl.target_name.clone(),
                    };
                    type_ops.entry((None, op_name.clone())).or_insert(target);
                }
            }
        }
    }
    // Build a consolidated alias map: local `type Foo = …` decls
    // plus every imported module's exported aliases. Passed into
    // inference / class-method binding so aliases like
    // `type SynString = String` expand to `String` before we try
    // to unify — otherwise `newtype NT = NT SynString` fields
    // refuse to unify with `String`.
    let alias_map: crate::typecheck_db::types::AliasMap = {
        let mut m: crate::typecheck_db::types::AliasMap = HashMap::new();
        // Local aliases from the CST. Walk a *resolved* copy of
        // the decls so the alias body's `Type::Con` qualifiers
        // name defining modules. Without this, an alias like
        // `type Foo = Q.Bar` (where `Q` is an import alias)
        // would expand to `Some("Q").Bar` and fail to unify with
        // user-side references that resolve to the defining
        // module's qualifier.
        let mut resolved_for_aliases = module.clone();
        let prims = crate::typecheck_db::prim::prim_exports();
        crate::typecheck_db::passes::resolve_pass::resolve_cst_types_in_place(
            &mut resolved_for_aliases,
            &name,
            registry,
            &prims,
        );
        let self_module_str: String = name.clone();
        for d in &resolved_for_aliases.decls {
            if let cst::Decl::TypeAlias { name: alias_name, type_vars, ty, .. } = d {
                let n = crate::typecheck_db::util::resolve_symbol(alias_name.value.symbol());
                let vars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let body = crate::typecheck_db::types::convert_type_expr(ty, &type_ops);
                // Local aliases: register under both the qualified
                // form (Some(self_module), name) and the bare
                // (None, name) — local aliases are always in scope
                // unqualified within their defining module.
                m.insert(
                    (Some(self_module_str.clone()), n.clone()),
                    (vars.clone(), body.clone()),
                );
                m.insert((None, n), (vars, body));
            }
        }
        // Names of locally-declared data/newtype/class/foreign-data
        // declarations. Imported type aliases with the same name must
        // NOT be added to alias_map — the local concrete type wins and
        // alias-expanding an `Eq Phylogeny` instance to `Eq Record(…)`
        // would produce spurious OverlappingInstances false positives.
        let local_concrete_names: std::collections::HashSet<String> = module
            .decls
            .iter()
            .filter_map(|d| match d {
                cst::Decl::Data { name, .. }
                | cst::Decl::Newtype { name, .. }
                | cst::Decl::ForeignData { name, .. } => Some(
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol()),
                ),
                _ => None,
            })
            .collect();

        // Every directly-imported module's aliases. Deeper
        // transitive aliases already land here because
        // `expand_module_reexports` merges them into each
        // module's exports, so `import Prelude` pulls in the
        // whole chain.
        for imp in &module.imports {
            let imp_name = join_module_name(&imp.module);
            let target = match registry.get(&imp_name) {
                Some(e) => e,
                None => continue,
            };
            for (k, a) in &target.type_aliases {
                // Defining-module key — populate ALWAYS so a
                // resolver-qualified `Type::Con(Some(M), name)` from
                // an alias body (e.g. transitive `type N3 = Succ N2`
                // where `N2` isn't directly imported) still
                // expands.
                let origin = target
                    .type_origins
                    .get(k)
                    .cloned()
                    .unwrap_or_else(|| imp_name.clone());
                m.entry((Some(origin), k.clone()))
                    .or_insert_with(|| (a.type_vars.clone(), a.body.clone()));
                // Unqualified key — skip when the name collides
                // with a locally-defined concrete type (the local
                // newtype/data wins). Otherwise register so a
                // call-site `Type::Con(None, name)` that survived
                // the resolver (legacy or transitive operator
                // desugar) still expands.
                if local_concrete_names.contains(k.as_str()) {
                    continue;
                }
                m.entry((None, k.clone()))
                    .or_insert_with(|| (a.type_vars.clone(), a.body.clone()));
            }
        }
        // Transitive aliases: an imported alias body may reference
        // OTHER modules' aliases (e.g.
        // `type SimulationNode r = Record (D3_ID + D3_XY + r)` where
        // `+` desugars to `Type.Row.RowApply`). Walk every alias body
        // we've registered so far, collect `Type::Con` references with
        // `Some(module)` qualifiers, and pull in those modules'
        // aliases too. Iterate to fixed point so multi-step
        // transitive chains all land.
        let mut frontier: std::collections::HashSet<String> =
            m.values()
                .flat_map(|(_, body)| collect_referenced_modules(body))
                .collect();
        let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
        while let Some(mod_name) = frontier.iter().next().cloned() {
            frontier.remove(&mod_name);
            if !visited.insert(mod_name.clone()) {
                continue;
            }
            let target = match registry.get(&mod_name) {
                Some(e) => e,
                None => continue,
            };
            for (k, a) in &target.type_aliases {
                let origin = target
                    .type_origins
                    .get(k)
                    .cloned()
                    .unwrap_or(mod_name.clone());
                if !m.contains_key(&(Some(origin.clone()), k.clone())) {
                    m.insert((Some(origin), k.clone()), (a.type_vars.clone(), a.body.clone()));
                    for referenced in collect_referenced_modules(&a.body) {
                        if !visited.contains(&referenced) {
                            frontier.insert(referenced);
                        }
                    }
                }
            }
        }
        m
    };

    // Pre-resolve the module's imports once. The per-reference
    // dep-resolver helpers used to walk and re-resolve
    // `module.imports` on every reference hit, which on a 90-module
    // bench was visibly hot (each call allocated a fresh
    // `Vec<String>` + `String::join`). Built before phase 3 so
    // every dep collector that follows can read the cached vectors.
    let imports_lookup = ImportLookup::build(module);

    // 3) Run per-decl cached check passes for every non-value decl.
    //    Each pass produces a structural `Shape` + an `output_hash`.
    //    The hashes feed into the value-SCC dep tracking below, so
    //    changing one non-value decl only invalidates the value SCCs
    //    that actually reference it.
    let mut data_constructors: DataConstructors = HashMap::new();
    let mut ctor_details: CtorRegistry = HashMap::new();
    let mut local_classes: HashMap<String, ClassInfo> = HashMap::new();
    let mut local_instances: Vec<Instance> = Vec::new();
    let mut decl_outcomes: HashMap<String, CacheOutcome> = HashMap::new();

    // Per-name lookup maps so the value-SCC dep resolver can
    // translate a free-names reference into the matching shape hash.
    let mut local_type_hashes: HashMap<String, OutputHash> = HashMap::new();
    let mut local_ctor_parent_hash: HashMap<String, OutputHash> = HashMap::new();
    let mut local_class_hashes: HashMap<String, OutputHash> = HashMap::new();
    let mut local_fixity_hashes: HashMap<String, OutputHash> = HashMap::new();
    let mut local_foreign_value_hashes: HashMap<String, OutputHash> = HashMap::new();
    // For instance-dispatch deps: class name → list of this module's
    // instance output hashes (with their decl keys, for graph edges).
    let mut local_instance_hashes_by_class: HashMap<String, Vec<(String, OutputHash)>> =
        HashMap::new();

    // Method→class index, assembled from local class shapes + every
    // imported class. A class method referenced from a value body is
    // a Value-kind reference, but its dep set must include the
    // defining class's shape hash + every in-scope instance of that
    // class. Lookup: method simple name → (class_module, class_name).
    let mut method_index: HashMap<String, (String, String)> = HashMap::new();

    let nonvalue_loop_started = if profile_slow {
        Some(std::time::Instant::now())
    } else {
        None
    };
    for d in &desugared {
        if !is_nonvalue_kind(d) {
            continue;
        }
        let (decl_key, decl_debug) = decl_key_for_nonvalue(d);
        let source_hash = nonvalue_source_hash(&input.source, d);
        // Collect dep hashes from this decl's free_names. "Deps" for
        // a non-value decl are: type refs → Data/Newtype/Alias/
        // ForeignData hashes; class refs → Class + instance hashes;
        // ctor refs → parent data hashes. We walk free_names in
        // source order — decls earlier in the file get registered in
        // local_*_hashes first, so self-references within the
        // module resolve.
        let dep_hashes = collect_nonvalue_dep_hashes(
            d,
            &name,
            &imports_lookup,
            registry,
            &local_type_hashes,
            &local_class_hashes,
            &local_ctor_parent_hash,
            &local_fixity_hashes,
            &local_foreign_value_hashes,
        );
        match d {
            crate::typecheck_db::ir::Decl::Data { .. } | crate::typecheck_db::ir::Decl::Newtype { .. } => {
                let (shape, oh, outcome) = check_data::run(
                    db,
                    &name,
                    &decl_key,
                    &decl_debug,
                    source_hash,
                    &dep_hashes,
                    d,
                    &type_ops,
                )
                .expect("check_data");
                let ctor_map = ctor_info_from_data_shape(&shape);
                for (cname, mut info) in ctor_map {
                    // `check_data` stores field types via a bare
                    // `convert_type_expr` — aliases are left
                    // unexpanded. Expand them here so downstream
                    // constructor-use sites (pattern matches,
                    // `synth_ctor_scheme` for imports) see the
                    // canonical form. Unblocks cases like
                    // `newtype StateL s a = StateL (s -> Accum s a)`
                    // where `Accum` must be the record row before
                    // the call site can unify a record literal
                    // against the constructor's arg.
                    info.fields = info
                        .fields
                        .into_iter()
                        .map(|f| crate::typecheck_db::types::expand_aliases(f, &alias_map))
                        .collect();
                    info.parent_module = Some(name.clone());
                    ctor_details.insert(cname.clone(), info);
                    local_ctor_parent_hash.insert(cname, oh);
                }
                data_constructors.insert(
                    shape.name.clone(),
                    shape.ctors.iter().map(|(n, _)| n.clone()).collect(),
                );
                let kp = if shape.is_newtype { "n" } else { "d" };
                registry.set_nonvalue_hash(&name, kp, &shape.name, oh);
                local_type_hashes.insert(shape.name.clone(), oh);
                decl_outcomes.insert(decl_key.clone(), outcome);
            }
            crate::typecheck_db::ir::Decl::TypeAlias { .. } => {
                let (shape, oh, outcome) = check_type_alias::run(
                    db,
                    &name,
                    &decl_key,
                    &decl_debug,
                    source_hash,
                    &dep_hashes,
                    d,
                    &type_ops,
                )
                .expect("check_type_alias");
                registry.set_nonvalue_hash(&name, "ta", &shape.name, oh);
                local_type_hashes.insert(shape.name.clone(), oh);
                decl_outcomes.insert(decl_key.clone(), outcome);
            }
            crate::typecheck_db::ir::Decl::Class { .. } => {
                let (shape, oh, outcome) = check_class::run(
                    db,
                    &name,
                    &decl_key,
                    &decl_debug,
                    source_hash,
                    &dep_hashes,
                    d,
                    &type_ops,
                )
                .expect("check_class");
                let ci = class_info_from_class_shape(&shape);
                local_classes.insert(shape.name.clone(), ci);
                registry.set_nonvalue_hash(&name, "c", &shape.name, oh);
                local_class_hashes.insert(shape.name.clone(), oh);
                // Method index: each method resolves back to its
                // defining class so Value-kind references can pick
                // up class + instance deps.
                for (method_name, _) in &shape.methods {
                    method_index
                        .insert(method_name.clone(), (name.clone(), shape.name.clone()));
                }
                decl_outcomes.insert(decl_key.clone(), outcome);
            }
            crate::typecheck_db::ir::Decl::Instance { .. } | crate::typecheck_db::ir::Decl::Derive { .. } => {
                let (shape, oh, outcome) = check_instance::run(
                    db,
                    &name,
                    &decl_key,
                    &decl_debug,
                    source_hash,
                    &dep_hashes,
                    d,
                    &type_ops,
                )
                .expect("check_instance");
                let mut inst = instance_from_shape(&shape);
                // Expand any type aliases in the instance head
                // (e.g. `instance Foo SynString` → `instance
                // Foo String`). The solver matches on concrete
                // head shapes; without expansion a user's
                // `SynString` vs. the call-site's `String` is a
                // spurious mismatch.
                inst.types = inst
                    .types
                    .into_iter()
                    .map(|t| crate::typecheck_db::types::expand_aliases(t, &alias_map))
                    .collect();
                for c in &mut inst.context {
                    c.args = c
                        .args
                        .iter()
                        .cloned()
                        .map(|t| crate::typecheck_db::types::expand_aliases(t, &alias_map))
                        .collect();
                }
                local_instances.push(inst);
                registry.set_nonvalue_hash(&name, "i", &decl_key, oh);
                registry.push_module_instance(&name, &shape.class.name, decl_key.clone());
                local_instance_hashes_by_class
                    .entry(shape.class.name.clone())
                    .or_default()
                    .push((decl_key.clone(), oh));
                decl_outcomes.insert(decl_key.clone(), outcome);
            }
            crate::typecheck_db::ir::Decl::Fixity { operator, .. } => {
                let (_shape, oh, outcome) = check_fixity::run(
                    db,
                    &name,
                    &decl_key,
                    &decl_debug,
                    source_hash,
                    &dep_hashes,
                    d,
                )
                .expect("check_fixity");
                let op_name =
                    crate::typecheck_db::util::resolve_symbol(operator.value.symbol());
                registry.set_nonvalue_hash(&name, "f", &op_name, oh);
                local_fixity_hashes.insert(op_name, oh);
                decl_outcomes.insert(decl_key.clone(), outcome);
            }
            crate::typecheck_db::ir::Decl::Foreign { .. } => {
                let (_shape, oh, outcome) = check_foreign::run(
                    db,
                    &name,
                    &decl_key,
                    &decl_debug,
                    source_hash,
                    &dep_hashes,
                    d,
                    &type_ops,
                )
                .expect("check_foreign");
                let fname = match d {
                    crate::typecheck_db::ir::Decl::Foreign { name, .. } => {
                        crate::typecheck_db::util::resolve_symbol(name.value.symbol())
                    }
                    _ => unreachable!(),
                };
                registry.set_scheme_hash(&name, &fname, oh);
                local_foreign_value_hashes.insert(fname, oh);
                decl_outcomes.insert(decl_key.clone(), outcome);
            }
            crate::typecheck_db::ir::Decl::ForeignData { .. } => {
                let (shape, oh, outcome) = check_foreign_data::run(
                    db,
                    &name,
                    &decl_key,
                    &decl_debug,
                    source_hash,
                    &dep_hashes,
                    d,
                    &type_ops,
                )
                .expect("check_foreign_data");
                registry.set_nonvalue_hash(&name, "ft", &shape.name, oh);
                local_type_hashes.insert(shape.name.clone(), oh);
                decl_outcomes.insert(decl_key.clone(), outcome);
            }
            _ => {}
        }
    }

    if let Some(t) = nonvalue_loop_started {
        let dur = t.elapsed();
        if profile_slow && dur >= std::time::Duration::from_millis(50) {
            phase_log.push(("3.nonvalue_decl_loop".to_string(), dur));
        }
    }

    // Fold every imported module's class methods into method_index
    // too, so users of `show` / `map` / etc. from imports pick up
    // class + instance deps.
    //
    // Walk values once per import — look at the first constraint
    // (the class context the method is bound under) and resolve it
    // against `exports.classes`. The earlier shape iterated classes
    // ⨯ values per import, which on Deku.DOM (~170 instances ⨯ 170
    // imports ⨯ Prelude-sized class/value lists) reached millions of
    // iterations and dominated wall time.
    let nonvalue_started = if profile_slow {
        Some(std::time::Instant::now())
    } else {
        None
    };
    for imp in &module.imports {
        let dep_mod = join_module_name(&imp.module);
        if let Some(exports) = registry.get(&dep_mod) {
            for (val_name, scheme) in exports.values.iter() {
                if let crate::typecheck_db::types::Type::Constrained(cs, _) =
                    &scheme.ty
                {
                    if let Some(first) = cs.first() {
                        if exports.classes.contains_key(&first.class.name) {
                            method_index.insert(
                                val_name.clone(),
                                (dep_mod.clone(), first.class.name.clone()),
                            );
                        }
                    }
                }
            }
        }
    }
    if let Some(t) = nonvalue_started {
        let dur = t.elapsed();
        if profile_slow && dur >= std::time::Duration::from_millis(50) {
            phase_log.push(("3.method_index_build".to_string(), dur));
        }
    }

    // Merge local instances + classes into the import-seeded index.
    for inst in &local_instances {
        instance_index.insert(inst.clone());
    }
    for (class_name, info) in &local_classes {
        instance_index.insert_class(class_name.clone(), info.clone());
    }
    // Expand aliases across every instance in the index using
    // the current module's alias map. Imported instances come
    // in with source-module type names (which may be aliases);
    // unification on the call site uses the *expanded* form,
    // so `instance Foo SynString` should match a `String` call.
    let alias_expand_started = if profile_slow {
        Some(std::time::Instant::now())
    } else {
        None
    };
    instance_index.expand_aliases_in_place(&alias_map);
    if let Some(t) = alias_expand_started {
        let dur = t.elapsed();
        if profile_slow && dur >= std::time::Duration::from_millis(50) {
            phase_log.push(("3.instance_alias_expand".to_string(), dur));
        }
    }

    // Cross-module overlap detection: walk the post-import,
    // post-alias-expansion instance index. Two instances overlap
    // when their heads can unify (so any concrete call could match
    // either). The local-only validate_decls detector covers
    // both-local pairs; we emit ScopeConflict-style
    // `OverlappingInstances` only for pairs where AT LEAST ONE
    // side comes from outside this module's local CST. Chain
    // members are deliberately ordered overlap and are skipped.
    let overlap_started = if profile_slow {
        Some(std::time::Instant::now())
    } else {
        None
    };
    // Names defined locally in this module as data types, newtypes, type
    // aliases, or foreign data. A local instance `Show (Product a b)` where
    // `Product` is locally defined must NOT be treated as overlapping with an
    // imported `Show (Product f g)` from a different module, even though both
    // use the same unqualified name. We pass this set so the detector can
    // tighten the unifier for local-type heads.
    let local_defined_type_names: std::collections::HashSet<String> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            cst::Decl::Data { name, kind_sig: cst::KindSigSource::None, .. }
            | cst::Decl::Newtype { name, .. }
            | cst::Decl::ForeignData { name, .. }
            | cst::Decl::TypeAlias { name, .. } => {
                Some(crate::typecheck_db::util::resolve_symbol(name.value.symbol()))
            }
            _ => None,
        })
        .collect();
    detect_cross_module_instance_overlaps(
        &instance_index,
        &local_instances,
        &local_defined_type_names,
        &mut validation_errors,
    );
    if let Some(t) = overlap_started {
        let dur = t.elapsed();
        if profile_slow && dur >= std::time::Duration::from_millis(50) {
            phase_log.push(("3.cross_mod_overlap".to_string(), dur));
        }
    }

    // Make the alias map available to every inference-side
    // `convert_type_expr` caller (type annotations, let-sigs,
    // `check_value` sigs) via the env.
    env.aliases = alias_map.clone();

    bind_local_ctors(&desugared, &name, &mut env, &alias_map, &type_ops);

    // 4) Value decls: split into SCCs + cached per-SCC inference.
    //    `module_context_hash` is now zero — all context dependencies
    //    are tracked explicitly via per-decl `dep_output_hashes` below.
    let module_context_hash: [u8; 32] = [0u8; 32];

    // Partition the desugared decls: value decls go through SCC
    // inference; everything else (data, class, instance, fixity)
    // contributes to env / registry but isn't a cacheable SCC unit.
    let mut value_idxs: Vec<usize> = Vec::new();
    let mut non_value_decls: Vec<&crate::typecheck_db::ir::Decl> = Vec::new();
    for (i, d) in desugared.iter().enumerate() {
        match d {
            crate::typecheck_db::ir::Decl::Value { .. } => value_idxs.push(i),
            _ => non_value_decls.push(d),
        }
    }

    // free_names for each value decl so we can build intra-module
    // dep edges.
    let mut value_free: Vec<Vec<String>> = Vec::with_capacity(value_idxs.len());
    let mut value_names: Vec<String> = Vec::with_capacity(value_idxs.len());
    let mut value_spans: Vec<(usize, usize)> = Vec::with_capacity(value_idxs.len());
    for &i in &value_idxs {
        let d = &desugared[i];
        let (n, span) = match d {
            crate::typecheck_db::ir::Decl::Value { name, span, .. } => (
                crate::typecheck_db::util::resolve_symbol(name.value.symbol()),
                (span.start, span.end),
            ),
            _ => unreachable!(),
        };
        value_names.push(n);
        value_spans.push(span);
        let free = free_names::compute(d);
        // Intra-module dep edges include refs that are EITHER
        // unqualified OR qualified with this module's name. After
        // resolve_pass runs, self-references to top-level values
        // carry `Some(self_module)` — without accepting them here the
        // SCC builder splits mutual-recursion groups (`f` calling `g`
        // and vice versa) into singletons and the pre-insert
        // mechanism breaks.
        let refs: Vec<String> = free
            .refs
            .iter()
            .filter(|r| {
                if r.kind != crate::typecheck_db::passes::names::NameKind::Value {
                    return false;
                }
                match &r.module {
                    None => true,
                    Some(m) => m == &name,
                }
            })
            .map(|r| r.name.clone())
            .collect();
        value_free.push(refs);
    }

    // Map local names → index for dep-graph building.
    let name_to_idx: HashMap<String, usize> = value_names
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), i))
        .collect();

    // Forward dep edges: for each value decl, which other value
    // decls in this module does it reference?
    let sccs = compute_sccs(&value_free, &name_to_idx);

    // Collect the union of **external** references for each SCC —
    // values, types, ctors, classes (plus their in-scope instances),
    // fixities. Every dep edge carries that node's structural output
    // hash, so the SCC's input_hash captures exactly the shape of
    // what it consumes.
    let mut all_schemes: Vec<InferredScheme> = Vec::new();
    let mut inference_error: Option<InferError> = None;
    // In-module scheme output hashes so later SCCs can resolve
    // intra-module deps.
    let mut local_scheme_hashes: HashMap<String, OutputHash> = HashMap::new();

    // Per-value-decl free_names, augmented with the references from
    // any associated `TypeSignature` decl (e.g. `fn :: Alias ->
    // Alias` is a separate Decl kind but its type refs belong to
    // `fn`'s dep set).
    let mut sig_free_by_name: HashMap<String, Vec<crate::typecheck_db::passes::names::Reference>> =
        HashMap::new();
    for d in &desugared {
        if let crate::typecheck_db::ir::Decl::TypeSignature { name, .. } = d {
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            let free = free_names::compute(d);
            sig_free_by_name.entry(n).or_default().extend(free.refs);
        }
    }
    let full_free: Vec<crate::typecheck_db::passes::names::FreeNames> = value_idxs
        .iter()
        .enumerate()
        .map(|(slot, &i)| {
            let mut free = free_names::compute(&desugared[i]);
            let vn = &value_names[slot];
            if let Some(sig_refs) = sig_free_by_name.get(vn) {
                free.refs.extend(sig_refs.iter().cloned());
            }
            free
        })
        .collect();

    let scc_loop_started = std::time::Instant::now();
    let mut scc_dep_resolve_total: std::time::Duration = std::time::Duration::ZERO;
    let mut scc_post_total: std::time::Duration = std::time::Duration::ZERO;
    let mut scc_full_iter_total: std::time::Duration = std::time::Duration::ZERO;
    let mut scc_iter_count: usize = 0;
    for scc in &sccs {
        let scc_iter_started = std::time::Instant::now();
        scc_iter_count += 1;
        // SCC decl source = concatenated source-slices in sorted
        // name order, so adding / removing / reordering decls inside
        // the SCC produces a deterministic hash.
        let mut scc_names: Vec<String> =
            scc.iter().map(|&i| value_names[i].clone()).collect();
        scc_names.sort();
        let scc_key = format!("scc__{}", scc_names.join("_"));

        let mut source_hasher = blake3::Hasher::new();
        source_hasher.update(b"scc_decl_sources_v1");
        // Sort the decls within the SCC by name for a stable hash.
        let mut by_name: Vec<(&str, (usize, usize))> = scc
            .iter()
            .map(|&i| (value_names[i].as_str(), value_spans[i]))
            .collect();
        by_name.sort_by(|a, b| a.0.cmp(b.0));
        for (_, (start, end)) in by_name {
            let slice = input.source.get(start..end).unwrap_or("");
            source_hasher.update(&(slice.len() as u32).to_le_bytes());
            source_hasher.update(slice.as_bytes());
        }
        let scc_source_hash = *source_hasher.finalize().as_bytes();

        let scc_member_set: HashSet<usize> = scc.iter().copied().collect();
        let mut dep_output_hashes: Vec<(String, String, OutputHash)> = Vec::new();
        let mut dep_seen: HashSet<(String, String)> = HashSet::new();

        let mut add_dep =
            |dep_mod: String, dep_decl: String, oh: OutputHash,
             dep_output_hashes: &mut Vec<(String, String, OutputHash)>,
             dep_seen: &mut HashSet<(String, String)>| {
                let pair = (dep_mod, dep_decl);
                if dep_seen.insert(pair.clone()) {
                    dep_output_hashes.push((pair.0, pair.1, oh));
                }
            };

        for &i in scc {
            let fn_i = &full_free[i];
            for r in &fn_i.refs {
                match r.kind {
                    NameKind::Value => {
                        resolve_value_dep(
                            r,
                            &name,
                            &imports_lookup,
                            registry,
                            &name_to_idx,
                            &scc_member_set,
                            &local_scheme_hashes,
                            &local_foreign_value_hashes,
                            &mut dep_output_hashes,
                            &mut dep_seen,
                        );
                        // If this Value ref is actually a class
                        // method, add class + in-scope-instance
                        // deps. A method's user is invalidated when
                        // the class changes OR when a new instance
                        // of the class is in scope. Post-resolve_pass
                        // refs may have a defining-module qualifier;
                        // method_index keys on the simple name so
                        // the check fires regardless.
                        if let Some((class_mod, class_name)) =
                            method_index.get(&r.name)
                        {
                            add_class_method_deps(
                                class_mod,
                                class_name,
                                &name,
                                &imports_lookup,
                                registry,
                                &local_class_hashes,
                                &local_instance_hashes_by_class,
                                &mut dep_output_hashes,
                                &mut dep_seen,
                            );
                        }
                    }
                    NameKind::Type => resolve_type_dep(
                        r,
                        &name,
                        &imports_lookup,
                        registry,
                        &local_type_hashes,
                        &mut dep_output_hashes,
                        &mut dep_seen,
                    ),
                    NameKind::Constructor => resolve_ctor_dep(
                        r,
                        &name,
                        &imports_lookup,
                        registry,
                        &local_ctor_parent_hash,
                        &mut dep_output_hashes,
                        &mut dep_seen,
                    ),
                    NameKind::Class => {
                        resolve_class_dep(
                            r,
                            &name,
                            &imports_lookup,
                            registry,
                            &local_class_hashes,
                            &local_instance_hashes_by_class,
                            &mut dep_output_hashes,
                            &mut dep_seen,
                        );
                    }
                    NameKind::Op | NameKind::TypeOp => resolve_fixity_dep(
                        r,
                        &name,
                        &imports_lookup,
                        registry,
                        &local_fixity_hashes,
                        &mut dep_output_hashes,
                        &mut dep_seen,
                    ),
                }
            }
        }
        let _ = add_dep; // closure kept for potential future use

        let scc_decl_refs: Vec<&crate::typecheck_db::ir::Decl> = scc
            .iter()
            .map(|&i| &desugared[value_idxs[i]])
            .collect();

        scc_dep_resolve_total += scc_iter_started.elapsed();
        let cache_t = std::time::Instant::now();
        // Try the cache first.
        let cached = try_get_cached(
            db,
            &name,
            &scc_key,
            scc_source_hash,
            &dep_output_hashes,
            module_context_hash,
            &mut env,
        )
        .expect("typecheck_db get_cached");
        scc_post_total += cache_t.elapsed();

        let (schemes, outcome, scheme_oh) = match cached {
            Some((schemes, scheme_oh)) => (schemes, CacheOutcome::Hit, Some(scheme_oh)),
            None => {
                // Run fresh inference for this SCC.
                let scc_started = std::time::Instant::now();
                let scc_label = scc_decl_refs.iter().find_map(|d| {
                    if let crate::typecheck_db::ir::Decl::Value { name, .. } = d {
                        Some(crate::typecheck_db::util::resolve_symbol(name.value.symbol()))
                    } else {
                        None
                    }
                }).unwrap_or_else(|| "?".to_string());
                let result = match infer_value_scc_with_all(
                    &type_ops,
                    &mut env,
                    &scc_decl_refs,
                    &data_constructors,
                    &ctor_details,
                    &instance_index,
                ) {
                    Ok(schemes) => {
                        // Cache write is best-effort: a pathological
                        // scheme (constraint-leak blowup in a decl
                        // that ran long under a generous deadline)
                        // can exceed SQLite's max blob size
                        // (SQLITE_TOOBIG). Treat any store failure
                        // as a cache skip — the schemes are still
                        // valid for THIS run; only re-use is lost.
                        let scheme_oh = match put_cached(
                            db,
                            &name,
                            &scc_key,
                            scc_source_hash,
                            &dep_output_hashes,
                            module_context_hash,
                            &schemes,
                        ) {
                            Ok(oh) => Some(oh),
                            Err(e) => {
                                eprintln!(
                                    "[typecheck_db] cache write skipped for {name}::{scc_label}: {e:?}",
                                );
                                None
                            }
                        };
                        (schemes, CacheOutcome::Miss, scheme_oh)
                    }
                    Err(e) => {
                        inference_error.get_or_insert(e);
                        (Vec::new(), CacheOutcome::Miss, None)
                    }
                };
                let scc_elapsed = scc_started.elapsed();
                if profile_slow {
                    phase_log.push((
                        format!("4.scc:{} ({}m)", scc_label, scc_decl_refs.len()),
                        scc_elapsed,
                    ));
                }
                result
            }
        };

        // Bind every inferred scheme back into `env` so the next SCC
        // in topo order sees these decls under their generalized
        // schemes. The cached-hit path already binds via
        // `try_get_cached`; this is the symmetric fix on the miss
        // path.
        //
        // `infer_value_scc_with_all` restores the SCC's local slots
        // before returning (its caller-reusable design). Those slots
        // would shadow our scheme bindings — locals are checked
        // first by `Env::lookup_unqualified`. Drop the stale slots
        // so the schemes are what subsequent SCCs see.
        if let Some(scope) = env.locals.last_mut() {
            for s in &schemes {
                scope.remove(&s.name);
            }
        }
        for s in &schemes {
            env.bind_scheme(
                crate::typecheck_db::types::QName::unqualified(&s.name),
                s.scheme.clone(),
            );
            env.bind_scheme(
                crate::typecheck_db::types::QName::qualified(&name, &s.name),
                s.scheme.clone(),
            );
        }

        for nm in &scc_names {
            decl_outcomes.insert(nm.clone(), outcome);
        }
        if let Some(oh) = scheme_oh {
            for s in &schemes {
                local_scheme_hashes.insert(s.name.clone(), oh);
                registry.set_scheme_hash(&name, &s.name, oh);
            }
        }
        all_schemes.extend(schemes);
        scc_full_iter_total += scc_iter_started.elapsed();
    }

    // Type-check instance method bodies. The class method's full
    // scheme already lives in `env.top_level` keyed by method name
    // (`forall (class+method vars). C <class vars> => <body>`). For
    // each instance method we:
    //   1. Look up that scheme.
    //   2. Substitute class type-vars with the instance's head types.
    //   3. Strip the leading `Constrained` layer (the class
    //      constraint is satisfied *by* this instance).
    //   4. Re-quantify the remaining method-only forall vars.
    //   5. Run a singleton SCC inference over the member's
    //      `Decl::Value` against the synthesised sig, swapping the
    //      class-method scheme out of `env.top_level` for the
    //      duration so the F2 sig-pin uses the instance-specialised
    //      sig instead of the polymorphic class one.
    //
    // The HoleDiagnostics + InferredScheme produced flow into
    // `all_schemes` so the rest of the pipeline (constraint
    // surfacing, hole reporting, validation) treats them the same as
    // ordinary value decls.
    let mut instance_method_schemes: Vec<InferredScheme> = Vec::new();
    let inst_method_started = std::time::Instant::now();
    // Per-class cache so a module that declares N instances for the
    // same class (e.g. Deku.DOM.Attr.Tabindex with 170 `Attr X_
    // Tabindex String` instances) doesn't re-walk
    // `module.imports × registry` for each instance. The lookup is
    // identical for every instance with the same class name.
    let mut class_info_cache: HashMap<String, Option<ClassInfo>> = HashMap::new();
    let mut method_scheme_cache: HashMap<
        String,
        Option<crate::typecheck_db::types::Scheme>,
    > = HashMap::new();
    for d in non_value_decls.iter() {
        if let crate::typecheck_db::ir::Decl::Instance {
            class_name,
            constraints: inst_constraints,
            types,
            members,
            ..
        } = d
        {
            let class_name_str =
                crate::typecheck_db::util::resolve_symbol(class_name.name.symbol());
            // Convert instance head context to typecheck_db
            // Constraints. We'll wrap the synthesized method sig with
            // these so the SCC's bidirectional check-mode skolemizes
            // the instance head vars and pushes the context as
            // givens (matching the original PureScript compiler's
            // semantics for instance method body checking).
            let inst_context_constraints: Vec<crate::typecheck_db::types::Constraint> =
                inst_constraints
                    .iter()
                    .map(|c| {
                        let qi = c.class.to_qi();
                        crate::typecheck_db::types::Constraint {
                            class: crate::typecheck_db::types::QName {
                                module: qi.module.map(|m| {
                                    crate::typecheck_db::util::resolve_symbol(m)
                                }),
                                name: crate::typecheck_db::util::resolve_symbol(qi.name),
                            },
                            args: c.args.iter().map(|a| {
                                crate::typecheck_db::types::convert_type_expr(a, &type_ops)
                            }).collect(),
                        }
                    })
                    .collect();
            // Class info: prefer the local declaration; otherwise
            // walk the importer's direct imports to find the class
            // in another module's exported `ClassInfo`. We only
            // need `type_vars` from it (to build the
            // class-var → instance-head subst).
            let class_info = if let Some(cached) =
                class_info_cache.get(&class_name_str)
            {
                cached.clone()
            } else {
                let resolved = local_classes
                    .get(&class_name_str)
                    .cloned()
                    .or_else(|| {
                        for imp in &module.imports {
                            let imp_name = join_module_name(&imp.module);
                            if let Some(exports) = registry.get(&imp_name) {
                                if let Some(ci) = exports.classes.get(&class_name_str)
                                {
                                    return Some(ci.clone());
                                }
                            }
                        }
                        None
                    });
                class_info_cache.insert(class_name_str.clone(), resolved.clone());
                resolved
            };
            let class_info = match class_info {
                Some(ci) => ci,
                None => continue,
            };
            let head_tys: Vec<crate::typecheck_db::types::Type> = types
                .iter()
                .map(|t| crate::typecheck_db::types::convert_type_expr(t, &type_ops))
                .collect();
            if head_tys.len() != class_info.type_vars.len() {
                continue; // Arity mismatch is reported elsewhere.
            }
            let mut subst: std::collections::HashMap<
                String,
                crate::typecheck_db::types::Type,
            > = std::collections::HashMap::new();
            for (v, t) in class_info.type_vars.iter().zip(head_tys.iter()) {
                subst.insert(v.clone(), t.clone());
            }
            // Member-level type signatures (`foo :: ?test` inside an
            // instance) — keyed by method name. When a method has its
            // own sig we prefer it over the class-derived one for
            // body inference; the user's holes are recorded against
            // the member sig's spans.
            let mut member_sigs: std::collections::HashMap<
                String,
                &crate::cst::TypeExpr,
            > = std::collections::HashMap::new();
            for m in members {
                if let crate::typecheck_db::ir::Decl::TypeSignature {
                    name: sig_name,
                    ty: sig_ty,
                    ..
                } = m
                {
                    let n = crate::typecheck_db::util::resolve_symbol(
                        sig_name.value.symbol(),
                    );
                    member_sigs.insert(n, sig_ty);
                }
            }
            for member in members {
                let crate::typecheck_db::ir::Decl::Value { name: member_name, .. } = member
                else {
                    continue;
                };
                let method_name =
                    crate::typecheck_db::util::resolve_symbol(member_name.value.symbol());
                // Class methods of locally declared classes are in
                // `env.top_level` (driver_multi binds them around
                // line 1953). For imported classes, `import M
                // (class C)` doesn't pull methods in — explicit
                // imports list each method separately. Fall back
                // to a direct registry lookup so an instance for
                // an imported class can still drive its method
                // body inference even when the method isn't in
                // env.top_level.
                let class_method_scheme = env
                    .top_level
                    .get(&crate::typecheck_db::types::QName::unqualified(&method_name))
                    .map(|arc| arc.as_ref().clone())
                    .or_else(|| {
                        if let Some(cached) =
                            method_scheme_cache.get(&method_name)
                        {
                            return cached.clone();
                        }
                        let resolved = (|| {
                            for imp in &module.imports {
                                let imp_name = join_module_name(&imp.module);
                                if let Some(exports) = registry.get(&imp_name) {
                                    if let Some(s) =
                                        exports.values.get(&method_name)
                                    {
                                        return Some(s.as_ref().clone());
                                    }
                                }
                            }
                            None
                        })();
                        method_scheme_cache
                            .insert(method_name.clone(), resolved.clone());
                        resolved
                    });
                let Some(full_scheme) = class_method_scheme else {
                    continue;
                };
                // Substitute the class type-vars in the method
                // scheme's body. `apply_var_subst` is capture-
                // avoiding for the inner `Forall` (so the method
                // can have its own quantifiers without colliding).
                let body_substed =
                    crate::typecheck_db::generalize::apply_var_subst(
                        &full_scheme.ty,
                        &subst,
                    );
                // Peel any number of leading Constrained layers (the
                // class constraint we're providing).
                let mut peeled = body_substed;
                while let crate::typecheck_db::types::Type::Constrained(_, body) =
                    peeled
                {
                    peeled = std::sync::Arc::unwrap_or_clone(body);
                }
                // Re-quantify any method-only vars from full_scheme.vars
                // that aren't class vars.
                let method_vars: Vec<String> = full_scheme
                    .vars
                    .iter()
                    .filter(|v| !subst.contains_key(*v))
                    .cloned()
                    .collect();
                // Collect free instance-head vars (e.g. `inner` in
                // `instance C inner => D Foo inner`). These must be
                // quantified by an INNER Forall in the synthesized
                // sig (NOT outer scheme.vars) so the SCC's check-
                // mode trigger (`scheme_has_inner_forall`) fires and
                // peels them into fresh skolems — letting the body's
                // pending constraints discharge against the
                // instance-context givens that check-mode pushes.
                let instance_head_vars =
                    crate::typecheck_db::passes::instance_index::collect_instance_vars(
                        &head_tys,
                        &inst_context_constraints,
                    );
                let with_ctx = if inst_context_constraints.is_empty() {
                    peeled
                } else {
                    crate::typecheck_db::types::Type::Constrained(
                        inst_context_constraints.clone(),
                        std::sync::Arc::new(peeled),
                    )
                };
                let with_inner_forall = if instance_head_vars.is_empty() {
                    with_ctx
                } else {
                    crate::typecheck_db::types::Type::Forall(
                        instance_head_vars
                            .into_iter()
                            .map(|n| (n, false, None))
                            .collect(),
                        std::sync::Arc::new(with_ctx),
                    )
                };
                let class_synthesized_sig =
                    crate::typecheck_db::types::Scheme::new(method_vars, with_inner_forall);
                // If the user wrote a member-level type signature for
                // this method (e.g. `foo :: ?test` inside an instance),
                // prefer it: convert the sig and record any type-level
                // holes so the SCC's F2 sig-pin path can rewrite them
                // to fresh unifs and emit `HoleDiagnostic`s. The class-
                // synthesized sig is the fallback shape; it should be
                // at least as specific as the member sig (the original
                // compiler enforces that elsewhere — we trust it here).
                let mut new_hole_sites: Option<Vec<(crate::span::Span, String)>> =
                    None;
                let synthesized_sig = if let Some(sig_te) =
                    member_sigs.get(&method_name)
                {
                    let mut hs: Vec<(crate::span::Span, String)> = Vec::new();
                    crate::typecheck_db::types::collect_type_holes(sig_te, &mut hs);
                    let sig_ty =
                        crate::typecheck_db::types::convert_type_expr(sig_te, &type_ops);
                    let (vars, vars_kinds, body) = match sig_ty {
                        crate::typecheck_db::types::Type::Forall(qs, body) => {
                            let (names, kinds): (
                                Vec<String>,
                                Vec<Option<crate::typecheck_db::types::Type>>,
                            ) = qs
                                .into_iter()
                                .map(|(n, _, k)| (n, k.map(|arc| (*arc).clone())))
                                .unzip();
                            (names, kinds, std::sync::Arc::unwrap_or_clone(body))
                        }
                        other => (Vec::new(), Vec::new(), other),
                    };
                    if !hs.is_empty() {
                        new_hole_sites = Some(hs);
                    }
                    // Wrap with instance context + inner Forall over
                    // instance head vars so the SCC's check-mode peels
                    // them as skolems/givens (same treatment as the
                    // class-derived synthesized sig — without this, a
                    // user-written member sig like
                    // `fromOutHtml :: forall msg. CtxT ctx html (These msg out) -> CtxT ctx html msg`
                    // would leave `ctx`/`html`/`out` as free
                    // Type::Vars in the body, and the method body's
                    // pending constraints couldn't discharge against
                    // the instance context.
                    let head_vars =
                        crate::typecheck_db::passes::instance_index::collect_instance_vars(
                            &head_tys,
                            &inst_context_constraints,
                        );
                    let body_with_ctx = if inst_context_constraints.is_empty() {
                        body
                    } else {
                        crate::typecheck_db::types::Type::Constrained(
                            inst_context_constraints.clone(),
                            std::sync::Arc::new(body),
                        )
                    };
                    let body_with_inner_forall = if head_vars.is_empty() {
                        body_with_ctx
                    } else {
                        crate::typecheck_db::types::Type::Forall(
                            head_vars.into_iter().map(|n| (n, false, None)).collect(),
                            std::sync::Arc::new(body_with_ctx),
                        )
                    };
                    crate::typecheck_db::types::Scheme::with_kinds(
                        vars,
                        vars_kinds,
                        body_with_inner_forall,
                    )
                } else {
                    class_synthesized_sig
                };
                // Swap the class-method scheme for the synthesized
                // instance-specialised one for the duration of body
                // inference.
                let key = crate::typecheck_db::types::QName::unqualified(&method_name);
                let saved_scheme = env
                    .top_level
                    .insert(key.clone(), std::sync::Arc::new(synthesized_sig));
                let was_signed = env.local_signed.insert(method_name.clone());
                let saved_hole_sites =
                    env.local_signed_hole_sites.remove(&method_name);
                if let Some(hs) = new_hole_sites {
                    env.local_signed_hole_sites
                        .insert(method_name.clone(), hs);
                }
                // Drop any stale local slot binding for this method
                // name from earlier value SCCs so lookup hits the
                // synthesised top-level scheme.
                let saved_local = env
                    .locals
                    .last_mut()
                    .and_then(|s| s.remove(&method_name));
                let inst_t = std::time::Instant::now();
                let solve_calls_before = if profile_slow {
                    crate::typecheck_db::passes::constraints::SOLVE_ONE_CALLS
                        .load(std::sync::atomic::Ordering::Relaxed)
                } else {
                    0
                };
                let try_match_before = if profile_slow {
                    crate::typecheck_db::passes::constraints::TRY_MATCH_ATTEMPTS
                        .load(std::sync::atomic::Ordering::Relaxed)
                } else {
                    0
                };
                let inference = infer_value_scc_with_all(
                    &type_ops,
                    &mut env,
                    &[member],
                    &data_constructors,
                    &ctor_details,
                    &instance_index,
                );
                let inst_elapsed = inst_t.elapsed();
                if profile_slow && inst_elapsed >= std::time::Duration::from_millis(50) {
                    let class_str = crate::typecheck_db::util::resolve_symbol(class_name.name.symbol());
                    let solve_calls = crate::typecheck_db::passes::constraints
                        ::SOLVE_ONE_CALLS
                        .load(std::sync::atomic::Ordering::Relaxed)
                        - solve_calls_before;
                    let try_match = crate::typecheck_db::passes::constraints
                        ::TRY_MATCH_ATTEMPTS
                        .load(std::sync::atomic::Ordering::Relaxed)
                        - try_match_before;
                    phase_log.push((
                        format!(
                            "4b.inst:{}.{} solve={} try={}",
                            class_str, method_name, solve_calls, try_match
                        ),
                        inst_elapsed,
                    ));
                }
                // Restore env state regardless of inference outcome.
                if let Some(s) = saved_scheme {
                    env.top_level.insert(key.clone(), s);
                } else {
                    env.top_level.remove(&key);
                }
                if !was_signed {
                    env.local_signed.remove(&method_name);
                }
                if let Some(s) = saved_hole_sites {
                    env.local_signed_hole_sites.insert(method_name.clone(), s);
                }
                if let Some(slot) = saved_local {
                    if let Some(scope) = env.locals.last_mut() {
                        scope.insert(method_name.clone(), slot);
                    }
                }
                if let Ok(schemes) = inference {
                    instance_method_schemes.extend(schemes);
                }
            }
        }
    }
    let _ = non_value_decls;
    if profile_slow {
        let dur = inst_method_started.elapsed();
        if dur >= std::time::Duration::from_millis(50) {
            phase_log.push(("4b.instance_method_bodies".to_string(), dur));
        }
    }

    // 5) Aggregate per-decl diagnostics. Instance-method-body
    // schemes flow through the same channel as value-decl schemes
    // so their hole diagnostics + constraint errors land in the
    // module's report.
    let mut exhaustiveness_errors = Vec::new();
    let mut constraint_errors = Vec::new();
    let mut deferred_constraints = Vec::new();
    let mut resolved_dicts = Vec::new();
    let mut hole_diagnostics = Vec::new();
    for s in all_schemes.iter().chain(instance_method_schemes.iter()) {
        exhaustiveness_errors.extend(s.exhaustiveness_errors.iter().cloned());
        constraint_errors.extend(s.constraint_errors.iter().cloned());
        deferred_constraints.extend(s.pending_constraints.iter().cloned());
        resolved_dicts.extend(s.resolved_dicts.iter().cloned());
        hole_diagnostics.extend(s.hole_diagnostics.iter().cloned());
    }

    // 6) Distill exports + register. `module X` re-export clauses
    // need a second pass because their expansion requires a
    // `ModuleRegistry` reference, which `distill_exports` doesn't
    // hold.
    //
    // distill_exports reads cst::Decl directly. To preserve the
    // resolved-qualifier invariant on exported schemes / instance
    // heads, we apply the CST-side type-position rewriter to a
    // clone before distillation. Validation passes (above) still
    // see the un-rewritten module so their `module.is_none()`
    // local-detection logic continues to fire correctly.
    let mut resolved_for_distill = module.clone();
    let prims = crate::typecheck_db::prim::prim_exports();
    crate::typecheck_db::passes::resolve_pass::resolve_cst_types_in_place(
        &mut resolved_for_distill,
        &name,
        registry,
        &prims,
    );
    let mut exports = distill_exports(
        &resolved_for_distill,
        &all_schemes,
        &local_instances,
        &local_classes,
        &ctor_details,
        &alias_map,
        &type_ops,
    );
    crate::typecheck_db::module_registry::expand_module_reexports(
        &mut exports,
        module,
        registry,
    );
    // ExportConflict: `module C (module A, module B)` clauses where
    // A and B both export the same name (value, ctor, type, class,
    // or operator alias) collide at C's surface.
    //
    // The reference rule is: `module N` re-exports the names that the
    // current module brought into scope FROM N (via its import list).
    // It does NOT re-export every name N happens to export. So for
    // Prelude — which `import Control.Apply (apply, ...)` and
    // `import Data.Function (const, flip, ...)` (no `apply`) — its
    // `module Data.Function` re-export carries only the four names it
    // imported, and there is no `apply` clash with `module Control.Apply`.
    //
    // We compute the per-clause imported-name set per namespace,
    // walk the intersection between every clause pair, and report a
    // conflict when the underlying definitions genuinely differ.
    if let Some(spanned_exports) = &module.exports {
        let module_clauses: Vec<(String, crate::span::Span)> = spanned_exports
            .value
            .exports
            .iter()
            .filter_map(|e| {
                if let crate::cst::Export::Module(mn) = e {
                    let name: String = mn
                        .parts
                        .iter()
                        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                        .collect::<Vec<_>>()
                        .join(".");
                    Some((name, spanned_exports.span))
                } else {
                    None
                }
            })
            .collect();
        // For each `module N` clause, build the per-namespace name
        // sets brought in by EVERY matching import (a single clause
        // can be fed by multiple imports — open + alias of the same
        // target are unioned).
        struct ClauseSets {
            target_module: String,
            values: std::collections::HashSet<String>,
            classes: std::collections::HashSet<String>,
            types: std::collections::HashSet<String>,
            ctors: std::collections::HashSet<String>,
            value_ops: std::collections::HashSet<String>,
            type_ops: std::collections::HashSet<String>,
        }
        let build_clause_sets = |clause_name: &str| -> Option<ClauseSets> {
            let mut sets = ClauseSets {
                target_module: String::new(),
                values: Default::default(),
                classes: Default::default(),
                types: Default::default(),
                ctors: Default::default(),
                value_ops: Default::default(),
                type_ops: Default::default(),
            };
            let mut matched_any = false;
            for imp in &module.imports {
                let imp_target = join_module_name(&imp.module);
                let alias_str = imp
                    .qualified
                    .as_ref()
                    .map(|q| join_module_name(q));
                // `import M as Q` is qualified-only: it doesn't bring M's
                // names into unqualified scope, so it cannot contribute to
                // a `module M` re-export clause. Only match when the alias
                // name itself IS the clause name (meaning the export clause
                // is `module Q`).
                let matches_clause = if imp.qualified.is_some() {
                    alias_str.as_deref() == Some(clause_name)
                } else {
                    imp_target == clause_name
                };
                if !matches_clause {
                    continue;
                }
                let Some(target) = registry.get(&imp_target) else {
                    continue;
                };
                matched_any = true;
                sets.target_module = imp_target.clone();
                match &imp.imports {
                    None => {
                        // Open import — every export of the target.
                        sets.values
                            .extend(target.values.keys().cloned());
                        sets.classes
                            .extend(target.classes.keys().cloned());
                        sets.types
                            .extend(target.type_arities.keys().cloned());
                        sets.ctors
                            .extend(target.ctors.keys().cloned());
                        sets.value_ops
                            .extend(target.value_fixities.keys().cloned());
                        sets.type_ops
                            .extend(target.type_fixities.keys().cloned());
                    }
                    Some(crate::cst::ImportList::Hiding(items)) => {
                        let mut hide_v: std::collections::HashSet<String> =
                            Default::default();
                        let mut hide_c: std::collections::HashSet<String> =
                            Default::default();
                        let mut hide_t: std::collections::HashSet<String> =
                            Default::default();
                        let mut hide_top: std::collections::HashSet<String> =
                            Default::default();
                        for item in items {
                            let name = crate::typecheck_db::util::resolve_symbol(
                                item.name(),
                            );
                            match item {
                                crate::cst::Import::Value(_) => { hide_v.insert(name); }
                                crate::cst::Import::Class(_) => { hide_c.insert(name); }
                                crate::cst::Import::Type(_, _) => { hide_t.insert(name); }
                                crate::cst::Import::TypeOp(_) => { hide_top.insert(name); }
                            }
                        }
                        for n in target.values.keys() {
                            if !hide_v.contains(n) {
                                sets.values.insert(n.clone());
                            }
                        }
                        for n in target.classes.keys() {
                            if !hide_c.contains(n) {
                                sets.classes.insert(n.clone());
                            }
                        }
                        for n in target.type_arities.keys() {
                            if !hide_t.contains(n) {
                                sets.types.insert(n.clone());
                            }
                        }
                        for n in target.ctors.keys() {
                            sets.ctors.insert(n.clone());
                        }
                        for n in target.value_fixities.keys() {
                            if !hide_v.contains(n) {
                                sets.value_ops.insert(n.clone());
                            }
                        }
                        for n in target.type_fixities.keys() {
                            if !hide_top.contains(n) {
                                sets.type_ops.insert(n.clone());
                            }
                        }
                    }
                    Some(crate::cst::ImportList::Explicit(items)) => {
                        for item in items {
                            let name = crate::typecheck_db::util::resolve_symbol(
                                item.name(),
                            );
                            match item {
                                crate::cst::Import::Value(_) => {
                                    // Value-import items can reference
                                    // either a regular value or a value
                                    // operator (parens form).
                                    sets.values.insert(name.clone());
                                    sets.value_ops.insert(name);
                                }
                                crate::cst::Import::Class(_) => {
                                    sets.classes.insert(name);
                                }
                                crate::cst::Import::Type(_, members) => {
                                    sets.types.insert(name.clone());
                                    match members {
                                        None => {}
                                        Some(crate::cst::DataMembers::All) => {
                                            if let Some(ctors) =
                                                target.data_constructors.get(&name)
                                            {
                                                for c in ctors {
                                                    sets.ctors.insert(c.clone());
                                                }
                                            }
                                        }
                                        Some(crate::cst::DataMembers::Explicit(cs)) => {
                                            for c in cs {
                                                sets.ctors.insert(
                                                    crate::typecheck_db::util::resolve_symbol(
                                                        c.value.symbol(),
                                                    ),
                                                );
                                            }
                                        }
                                    }
                                }
                                crate::cst::Import::TypeOp(_) => {
                                    sets.type_ops.insert(name);
                                }
                            }
                        }
                    }
                }
            }
            if matched_any { Some(sets) } else { None }
        };
        let clause_sets: Vec<(ClauseSets, crate::span::Span)> = module_clauses
            .iter()
            .filter_map(|(name, span)| {
                build_clause_sets(name).map(|s| (s, *span))
            })
            .collect();
        let mut reported: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        for i in 0..clause_sets.len() {
            for j in (i + 1)..clause_sets.len() {
                let (a_sets, _) = &clause_sets[i];
                let (b_sets, span) = &clause_sets[j];
                let Some(a) = registry.get(&a_sets.target_module) else { continue };
                let Some(b) = registry.get(&b_sets.target_module) else { continue };
                let mut report_conflict = |kind: &str, n: &str| {
                    let key = format!("{}:{}", kind, n);
                    if reported.insert(key) {
                        validation_errors.push(
                            crate::typecheck_db::passes::validate_decls::ValidationError {
                                span: *span,
                                kind: crate::typecheck_db::passes::validate_decls::ValidationErrorKind::ExportConflict(
                                    n.to_string(),
                                ),
                            },
                        );
                    }
                };
                // Walk the intersection of names imported into THIS
                // module from each side. For each namespace we
                // compare origin modules — re-exports through
                // different paths share an upstream origin and so
                // don't conflict, while two locally-declared `class
                // X` (or `data T`, etc.) in different modules have
                // distinct origins and produce a real conflict.
                for n in &a_sets.values {
                    if !b_sets.values.contains(n) { continue; }
                    if a.values.contains_key(n) && b.values.contains_key(n) {
                        let oa = a
                            .value_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| a_sets.target_module.clone());
                        let ob = b
                            .value_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| b_sets.target_module.clone());
                        if oa != ob {
                            report_conflict("value", n);
                        }
                    }
                }
                for n in &a_sets.classes {
                    if !b_sets.classes.contains(n) { continue; }
                    if a.classes.contains_key(n) && b.classes.contains_key(n) {
                        let oa = a
                            .class_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| a_sets.target_module.clone());
                        let ob = b
                            .class_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| b_sets.target_module.clone());
                        if oa != ob {
                            report_conflict("class", n);
                        }
                    }
                }
                for n in &a_sets.types {
                    if !b_sets.types.contains(n) { continue; }
                    if a.type_arities.contains_key(n) && b.type_arities.contains_key(n) {
                        let oa = a
                            .type_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| a_sets.target_module.clone());
                        let ob = b
                            .type_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| b_sets.target_module.clone());
                        if oa != ob {
                            report_conflict("type", n);
                        }
                    }
                }
                for n in &a_sets.ctors {
                    if !b_sets.ctors.contains(n) { continue; }
                    if a.ctors.contains_key(n) && b.ctors.contains_key(n) {
                        let oa = a
                            .ctor_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| a_sets.target_module.clone());
                        let ob = b
                            .ctor_origins
                            .get(n)
                            .cloned()
                            .unwrap_or_else(|| b_sets.target_module.clone());
                        if oa != ob {
                            report_conflict("ctor", n);
                        }
                    }
                }
                for n in &a_sets.value_ops {
                    if !b_sets.value_ops.contains(n) { continue; }
                    if let (Some(a_fix), Some(b_fix)) =
                        (a.value_fixities.get(n), b.value_fixities.get(n))
                    {
                        if a_fix != b_fix {
                            report_conflict("valueOp", n);
                        }
                    }
                }
                for n in &a_sets.type_ops {
                    if !b_sets.type_ops.contains(n) { continue; }
                    if let (Some(a_fix), Some(b_fix)) =
                        (a.type_fixities.get(n), b.type_fixities.get(n))
                    {
                        if a_fix != b_fix {
                            report_conflict("typeOp", n);
                        }
                    }
                }
            }
        }
    }
    // Post-distill: resolve fixity targets that weren't local
    // against our imports. `infixr 6 Tuple as /\` in a module
    // that imports `Tuple` from `Data.Tuple` needs the fixity's
    // `target_module` filled in with `Data.Tuple` so downstream
    // importers of the operator alias find the ctor. We also
    // surface the target's value scheme under the alias name
    // so `import M ((/\))` brings it into scope.
    {
        let prim_map_rs = crate::typecheck_db::prim::prim_exports();
        let import_targets: Vec<String> = module
            .imports
            .iter()
            .map(|imp| join_module_name(&imp.module))
            .collect();
        // Build alias → real-module map from this module's imports,
        // e.g. `import Control.Semigroupoid as S` → `"S" → "Control.Semigroupoid"`.
        let alias_to_real: std::collections::HashMap<String, String> = module
            .imports
            .iter()
            .filter_map(|imp| {
                let alias = imp.qualified.as_ref()?;
                let alias_str: String = alias
                    .parts
                    .iter()
                    .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                    .collect::<Vec<_>>()
                    .join(".");
                Some((alias_str, join_module_name(&imp.module)))
            })
            .collect();
        let mut inserts: Vec<(String, String, FixityDecl)> = Vec::new();
        // Each entry: (op_alias, target_name, origin_module, scheme).
        let mut value_inserts: Vec<(
            String,
            String,
            String,
            std::sync::Arc<crate::typecheck_db::types::Scheme>,
        )> = Vec::new();
        for (op, fx) in &exports.value_fixities {
            // Skip fixities whose target_module is already a real
            // module name (resolved in the local-target branch above).
            // Allow fixities where target_module is a module alias
            // (e.g. `S` for `Control.Semigroupoid`) — those need
            // resolution below.
            if let Some(ref tm) = fx.target_module {
                let is_alias = alias_to_real.contains_key(tm);
                let is_real = registry.contains(tm)
                    || prim_map_rs.contains_key(tm.as_str());
                if is_real && !is_alias {
                    continue;
                }
                if !is_alias {
                    // Unknown module — skip.
                    continue;
                }
            }
            // If the fixity target has a module alias (e.g. `S.compose`
            // where `S` is `Control.Semigroupoid`), search only the
            // resolved alias target; otherwise search all imports.
            let resolved_target_mod: Option<String> = fx
                .target_module
                .as_ref()
                .and_then(|tm| alias_to_real.get(tm))
                .cloned();
            let search_targets: Box<dyn Iterator<Item = &String>> =
                if let Some(ref rt) = resolved_target_mod {
                    Box::new(std::iter::once(rt))
                } else {
                    Box::new(import_targets.iter())
                };
            for imp_name in search_targets {
                let source = match registry.get(imp_name) {
                    Some(s) => Some(s),
                    None => prim_map_rs.get(imp_name),
                };
                let Some(source) = source else { continue };
                if source.values.contains_key(&fx.target_name)
                    || source.ctors.contains_key(&fx.target_name)
                {
                    let origin = source
                        .value_origins
                        .get(&fx.target_name)
                        .cloned()
                        .unwrap_or_else(|| imp_name.clone());
                    let mut new_fx = fx.clone();
                    new_fx.target_module = Some(origin.clone());
                    inserts.push((op.clone(), origin.clone(), new_fx));
                    // Surface the target's scheme so `import M
                    // ((/\))` fills `exports.values` with an
                    // entry for `/\` AND for the target
                    // constructor under its origin module —
                    // downstream `Expr::Constructor(origin.Tuple)`
                    // then resolves.
                    let scheme: Option<std::sync::Arc<crate::typecheck_db::types::Scheme>> = source
                        .values
                        .get(&fx.target_name)
                        .cloned()
                        .or_else(|| {
                            source
                                .ctors
                                .get(&fx.target_name)
                                .map(|info| std::sync::Arc::new(
                                    crate::typecheck_db::passes::imports::synth_ctor_scheme(info)
                                ))
                        });
                    if let Some(s) = scheme {
                        value_inserts.push((
                            op.clone(),
                            fx.target_name.clone(),
                            origin.clone(),
                            s,
                        ));
                    }
                    break;
                }
            }
        }
        for (op, _origin, new_fx) in inserts {
            exports.value_fixities.insert(op, new_fx);
        }
        for (op, target_name, origin, scheme) in value_inserts {
            exports.values.entry(op.clone()).or_insert_with(|| scheme.clone());
            exports
                .value_origins
                .entry(op.clone())
                .or_insert(origin.clone());
            // Also thread the target name through as a
            // qualified binding. `import M ((/\))` then brings
            // the target's scheme into the importer's env via
            // `qualified_values` under `(origin, target_name)`.
            exports
                .qualified_values
                .entry((origin.clone(), op.clone()))
                .or_insert_with(|| scheme.clone());
            exports
                .qualified_values
                .entry((origin, target_name))
                .or_insert(scheme);
        }
    }
    // PureScript instances are globally visible — they must flow
    // through the import chain, not just through `module X`
    // re-exports. Merge every directly-imported module's
    // `instances` into ours so downstream consumers that only
    // `import` this module still see the whole transitively
    // reachable instance set (e.g. `main = do …` in a fixture
    // that only imports `Effect.Console` still needs
    // `instance bindEffect` from `Effect`).
    let prim_map = crate::typecheck_db::prim::prim_exports();
    // Build a fingerprint set of instances we already have so the
    // dedup check is O(1) per candidate instead of O(n). On
    // import-heavy modules (Deku.DOM aggregates ~6800 instances
    // across 40 Attr.* re-exports) the prior `iter().any(|i| i ==
    // inst)` was visibly quadratic and dominated wall time after
    // the cross-module overlap detector got fixed.
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let inst_fingerprint = |inst: &crate::typecheck_db::passes::instance_index::Instance| -> u64 {
        let mut h = DefaultHasher::new();
        inst.class.name.hash(&mut h);
        if let Some(ref m) = inst.class.module {
            m.hash(&mut h);
        }
        inst.types.hash(&mut h);
        inst.context.len().hash(&mut h);
        for c in &inst.context {
            c.class.name.hash(&mut h);
            c.args.hash(&mut h);
        }
        inst.vars.hash(&mut h);
        inst.chained.hash(&mut h);
        h.finish()
    };
    let mut existing: std::collections::HashSet<u64> = exports
        .instances
        .iter()
        .map(|arc| inst_fingerprint(arc.as_ref()))
        .collect();
    for imp in &module.imports {
        let imp_name = join_module_name(&imp.module);
        let source = match registry.get(&imp_name) {
            Some(s) => s,
            None => match prim_map.get(&imp_name) {
                Some(s) => s,
                None => continue,
            },
        };
        for inst in &source.instances {
            let fp = inst_fingerprint(inst.as_ref());
            if existing.insert(fp) {
                // Arc::clone is a refcount bump — no deep copy.
                exports.instances.push(std::sync::Arc::clone(inst));
            }
        }
    }
    registry.insert(name.clone(), exports);

    if profile_slow {
        let scc_total = scc_loop_started.elapsed();
        if scc_total >= std::time::Duration::from_millis(50) {
            phase_log.push((
                format!("4.scc_loop_TOTAL ({}sccs)", scc_iter_count),
                scc_total,
            ));
            phase_log.push(("4.scc_dep_resolve_TOTAL".to_string(), scc_dep_resolve_total));
            phase_log.push(("4.scc_cache_lookup_TOTAL".to_string(), scc_post_total));
            phase_log.push(("4.scc_full_iter_TOTAL".to_string(), scc_full_iter_total));
            // Anything between scc_full_iter end and scc_loop end is
            // outside this loop — but more importantly, what's
            // missing within the loop is captured here.
        }
    }
    let dump_threshold_ms: u64 = std::env::var("TYPECHECK_DB_DUMP_MS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5000);
    if profile_slow
        && phase_total.elapsed() >= std::time::Duration::from_millis(dump_threshold_ms)
    {
        let total_ms = phase_total.elapsed().as_millis();
        eprintln!("=== profile [{}] total {}ms ===", name, total_ms);
        let mut entries = phase_log.clone();
        entries.sort_by(|a, b| b.1.cmp(&a.1));
        for (label, dur) in entries.iter().take(40) {
            let pct = (dur.as_millis() as f64 / total_ms as f64) * 100.0;
            eprintln!("  {:>6}ms  {:>5.1}%  {}", dur.as_millis(), pct, label);
        }
    }
    // Per-declaration JS codegen (DeclDb engine). Only when explicitly
    // enabled, so plain typechecking pays no codegen cost.
    let js_module_text = if db.codegen_enabled() {
        Some(generate_module_js(
            db,
            &name,
            &desugared,
            &input.source,
            &local_scheme_hashes,
            module_context_hash,
            &all_schemes,
            &instance_method_schemes,
            &instance_index,
            registry,
            &ctor_details,
            &data_constructors,
        ))
    } else {
        None
    };

    ModuleCheckResult {
        name,
        schemes: all_schemes,
        import_errors,
        exhaustiveness_errors,
        constraint_errors,
        deferred_constraints,
        resolved_dicts,
        inference_error,
        decl_outcomes,
        hole_diagnostics,
        validation_errors,
        kind_errors,
        coercible_errors,
        js_module_text,
    }
}

/// Generate the full ES-module JS for a checked module via the per-decl
/// `codegen_decl` pass + trivial assembler. Phase 1: value declarations only.
#[allow(clippy::too_many_arguments)]
fn generate_module_js(
    db: &mut TypecheckDb,
    module: &str,
    desugared: &[crate::typecheck_db::ir::Decl],
    source: &str,
    local_scheme_hashes: &HashMap<String, OutputHash>,
    module_context_hash: [u8; 32],
    all_schemes: &[InferredScheme],
    instance_method_schemes: &[InferredScheme],
    instance_index: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    registry: &ModuleRegistry,
    ctor_details: &CtorRegistry,
    data_constructors: &DataConstructors,
) -> String {
    use crate::codegen::common::ident_to_js;
    use crate::codegen::decl::{instance_js_name, type_head_name, DeclCgCtx};
    use crate::typecheck_db::ir::Decl;
    use crate::typecheck_db::passes::codegen_decl;
    use crate::typecheck_db::util::resolve_symbol;
    use std::collections::HashSet;

    // Instance dictionary JS name → DEFINING module, for emitting imported
    // instance references as `Module.name`. Instances are forwarded to every
    // re-exporter, so we can't just read the first module that exports one;
    // instead we correlate each instance's content key (`i__hex`) with the
    // module that DECLARED it (tracked in `registry.module_instances`).
    let mut instance_modules: HashMap<String, String> = HashMap::new();
    {
        use crate::typecheck_db::passes::check_nonvalue::instance_key_hex;
        // key (`i__hex`) → instance JS name, across every instance in scope.
        let mut key_to_name: HashMap<String, String> = HashMap::new();
        for (class_str, inst) in instance_index.all_instances() {
            let heads: Vec<String> = inst.types.iter().map(type_head_name).collect();
            if heads.iter().all(|h| h.is_empty()) {
                continue;
            }
            let class_debug = match &inst.class.module {
                Some(m) => format!("{m}.{}", inst.class.name),
                None => inst.class.name.clone(),
            };
            let key = instance_key_hex(&class_debug, &inst.types);
            key_to_name.insert(key, instance_js_name(class_str, &heads));
        }
        for (mod_name, _) in registry.iter() {
            for key in registry.module_instances(mod_name) {
                if let Some(name) = key_to_name.get(key) {
                    instance_modules.insert(name.clone(), mod_name.clone());
                }
            }
        }
    }

    // Per-decl resolved-dict maps, keyed by decl/method name.
    let mut cd_by_name: HashMap<String, std::collections::HashMap<crate::span::Span, _>> =
        HashMap::new();
    let mut leading_by_name: HashMap<String, Vec<crate::typecheck_db::types::Constraint>> =
        HashMap::new();
    for s in all_schemes {
        cd_by_name.insert(s.name.clone(), s.constraint_dicts.clone());
        leading_by_name.insert(
            s.name.clone(),
            crate::codegen::decl::leading_constraints(&s.scheme.ty),
        );
    }
    let mut method_dicts_by_name: HashMap<
        String,
        std::collections::HashMap<crate::span::Span, _>,
    > = HashMap::new();
    for s in instance_method_schemes {
        method_dicts_by_name.insert(s.name.clone(), s.constraint_dicts.clone());
    }

    // Module-global info needed for expression translation.
    let mut ctor_arity: HashMap<String, usize> = HashMap::new();
    let mut newtype_ctors: HashSet<String> = HashSet::new();
    let mut foreign_names: HashSet<String> = HashSet::new();
    for d in desugared {
        match d {
            Decl::Data { constructors, .. } => {
                for ctor in constructors {
                    ctor_arity
                        .insert(ident_to_js(ctor.name.value.symbol()), ctor.fields.len());
                }
            }
            Decl::Newtype { constructor, .. } => {
                newtype_ctors.insert(ident_to_js(constructor.value.symbol()));
            }
            Decl::Foreign { name, .. } => {
                foreign_names.insert(resolve_symbol(name.value.symbol()));
            }
            _ => {}
        }
    }
    // Imported constructors: arities + newtype-ness so cross-module ctor refs
    // pick `.value`/`.create`/identity correctly. Local entries win (`or_insert`).
    for (_, exports) in registry.iter() {
        for (ctor_name, info) in &exports.ctors {
            let cjs = crate::codegen::common::any_name_to_js(ctor_name);
            ctor_arity.entry(cjs.clone()).or_insert(info.fields.len());
            if exports.newtypes.contains(&info.parent_type) {
                newtype_ctors.insert(cjs);
            }
        }
    }
    // Map each class method (raw PS name) to its class simple name, and to the
    // classes of its own (method-level) constraints — the latter become leading
    // dict params on instance method bodies (e.g. `eq1 :: Eq a => …`).
    let mut class_methods: HashMap<String, String> = HashMap::new();
    let mut method_leading: HashMap<String, Vec<String>> = HashMap::new();
    for d in desugared {
        if let Decl::Class { name, members, .. } = d {
            let class_simple = resolve_symbol(name.value.symbol());
            for m in members {
                let method = resolve_symbol(m.name.value.symbol());
                class_methods.insert(method.clone(), class_simple.clone());
                method_leading.insert(method, crate::codegen::decl::method_dict_classes(&m.ty));
            }
        }
    }
    // Imported class methods: their own constraints (beyond the class itself)
    // also become leading dict params on instance method bodies. The method's
    // exported scheme is `forall. Class a => MethodCtx => …`, so we strip the
    // class constraint and keep the rest. Needed for e.g. `instance Eq1 Maybe`
    // whose `eq1 :: Eq a => …` comes from the imported `Eq1` class.
    for d in desugared {
        let (class_name, members) = match d {
            Decl::Instance { class_name, members, .. } => (class_name, members),
            _ => continue,
        };
        let class_simple = resolve_symbol(class_name.name.symbol());
        let class_mod = resolve_symbol(class_name.module.symbol());
        let Some(exports) = registry.get(&class_mod) else { continue };
        for member in members {
            if let Decl::Value { name: mname, .. } = member {
                let method = resolve_symbol(mname.value.symbol());
                if method_leading.contains_key(&method) {
                    continue;
                }
                if let Some(scheme) = exports.values.get(&method) {
                    let classes: Vec<String> =
                        crate::codegen::decl::leading_constraints(&scheme.ty)
                            .iter()
                            .map(|c| c.class.name.clone())
                            .filter(|c| *c != class_simple)
                            .collect();
                    method_leading.insert(method, classes);
                }
            }
        }
    }
    let ctx = DeclCgCtx {
        module,
        ctor_arity: &ctor_arity,
        newtype_ctors: &newtype_ctors,
        foreign_names: &foreign_names,
        class_methods: &class_methods,
        instances: instance_index,
        instance_modules: &instance_modules,
    };

    let mut outputs: Vec<codegen_decl::CodegenOutput> = Vec::new();

    // Constructor layout per local type, for the deriver.
    let mut derived_info: HashMap<String, crate::codegen::decl::DerivedTypeInfo> = HashMap::new();
    for (ty, ctor_names) in data_constructors {
        let ctors: Vec<_> = ctor_names
            .iter()
            .map(|cn| crate::codegen::decl::DerivedCtor {
                js_name: crate::codegen::common::any_name_to_js(cn),
                fields: ctor_details.get(cn).map(|ci| ci.fields.clone()).unwrap_or_default(),
            })
            .collect();
        let type_vars = ctor_names
            .first()
            .and_then(|cn| ctor_details.get(cn))
            .map(|ci| ci.type_vars.clone())
            .unwrap_or_default();
        derived_info.insert(
            ty.clone(),
            crate::codegen::decl::DerivedTypeInfo { ctors, type_vars },
        );
    }

    // Group value-decl equations by name; emit the whole group at the first
    // equation's source position.
    let mut value_groups: HashMap<String, Vec<&Decl>> = HashMap::new();
    let mut value_spans: HashMap<String, Vec<(usize, usize)>> = HashMap::new();
    for d in desugared {
        if let Decl::Value { name, span, .. } = d {
            let n = resolve_symbol(name.value.symbol());
            value_groups.entry(n.clone()).or_default().push(d);
            value_spans.entry(n).or_default().push((span.start, span.end));
        }
    }

    // Emit in SOURCE ORDER. Top-level value initializers and instance dict
    // objects are eagerly evaluated at module load and may reference each other
    // (a value uses an instance dict; an instance method calls a value); neither
    // a values-first nor instances-first phase order is correct. PureScript
    // modules are written so eager bindings are dependency-ordered in source, so
    // emitting in source order is correct for the common case (matching the
    // reference compiler's effective behavior).
    let empty_cd = std::collections::HashMap::new();
    let empty_leading: Vec<crate::typecheck_db::types::Constraint> = Vec::new();
    let mut emitted_value: HashSet<String> = HashSet::new();
    for d in desugared {
        match d {
            Decl::Data { name, span, .. } => {
                let decl_key = format!("data__{}", resolve_symbol(name.value.symbol()));
                let src_hash = codegen_decl::source_slice_hash(source, &[(span.start, span.end)]);
                if let Ok((out, _, _)) = codegen_decl::run_nonvalue_decl(
                    db, module, &decl_key, src_hash, module_context_hash, d,
                ) {
                    outputs.push(out);
                }
            }
            Decl::Newtype { name, span, .. } => {
                let decl_key = format!("newtype__{}", resolve_symbol(name.value.symbol()));
                let src_hash = codegen_decl::source_slice_hash(source, &[(span.start, span.end)]);
                if let Ok((out, _, _)) = codegen_decl::run_nonvalue_decl(
                    db, module, &decl_key, src_hash, module_context_hash, d,
                ) {
                    outputs.push(out);
                }
            }
            Decl::Foreign { name, span, .. } => {
                let decl_key = format!("foreign__{}", resolve_symbol(name.value.symbol()));
                let src_hash = codegen_decl::source_slice_hash(source, &[(span.start, span.end)]);
                if let Ok((out, _, _)) = codegen_decl::run_nonvalue_decl(
                    db, module, &decl_key, src_hash, module_context_hash, d,
                ) {
                    outputs.push(out);
                }
            }
            Decl::Class { name, span, .. } => {
                let decl_key = format!("class__{}", resolve_symbol(name.value.symbol()));
                let src_hash = codegen_decl::source_slice_hash(source, &[(span.start, span.end)]);
                if let Ok((out, _, _)) = codegen_decl::run_class_decl(
                    db, module, &decl_key, src_hash, module_context_hash, d,
                ) {
                    outputs.push(out);
                }
            }
            Decl::Instance { .. } => {
                outputs.push(codegen_decl::run_instance_decl(
                    d, &ctx, &method_dicts_by_name, &method_leading,
                ));
            }
            Decl::Derive { types, .. } => {
                let head = types
                    .last()
                    .map(crate::codegen::decl::type_expr_head_name)
                    .unwrap_or_default();
                outputs.push(codegen_decl::run_derive_decl(d, &ctx, derived_info.get(&head)));
            }
            Decl::Value { name, .. } => {
                let n = resolve_symbol(name.value.symbol());
                if emitted_value.insert(n.clone()) {
                    let eqs = &value_groups[&n];
                    let sp = &value_spans[&n];
                    let src_hash = codegen_decl::source_slice_hash(source, sp);
                    let scheme_dep = local_scheme_hashes.get(&n).copied();
                    let decl_key = format!("value__{n}");
                    let cd = cd_by_name.get(&n).unwrap_or(&empty_cd);
                    let leading = leading_by_name.get(&n).unwrap_or(&empty_leading);
                    if let Ok((out, _, _)) = codegen_decl::run_value_group(
                        db, &decl_key, src_hash, module_context_hash, scheme_dep, eqs, &ctx, cd,
                        leading,
                    ) {
                        outputs.push(out);
                    }
                }
            }
            _ => {}
        }
    }

    codegen_decl::assemble_module(&outputs)
}

// ---------------------------------------------------------------------------
// SCC extraction + dep resolution helpers
// ---------------------------------------------------------------------------

/// Tarjan's SCC algorithm over the intra-module value-decl dep graph.
/// Each returned SCC is a list of indices into `value_free`; SCCs are
/// emitted in reverse-topological order (Tarjan's natural output),
/// which is exactly what we want — a dependency's SCC appears before
/// any SCC that references it.
fn compute_sccs(
    value_free: &[Vec<String>],
    name_to_idx: &HashMap<String, usize>,
) -> Vec<Vec<usize>> {
    let n = value_free.len();
    let mut index = 0usize;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![usize::MAX; n];
    let mut lowlink = vec![0usize; n];
    let mut sccs: Vec<Vec<usize>> = Vec::new();

    fn strongconnect(
        v: usize,
        index: &mut usize,
        indices: &mut [usize],
        lowlink: &mut [usize],
        stack: &mut Vec<usize>,
        on_stack: &mut [bool],
        sccs: &mut Vec<Vec<usize>>,
        value_free: &[Vec<String>],
        name_to_idx: &HashMap<String, usize>,
    ) {
        indices[v] = *index;
        lowlink[v] = *index;
        *index += 1;
        stack.push(v);
        on_stack[v] = true;

        for dep_name in &value_free[v] {
            if let Some(&w) = name_to_idx.get(dep_name) {
                if indices[w] == usize::MAX {
                    strongconnect(
                        w, index, indices, lowlink, stack, on_stack, sccs,
                        value_free, name_to_idx,
                    );
                    lowlink[v] = lowlink[v].min(lowlink[w]);
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(indices[w]);
                }
            }
        }

        if lowlink[v] == indices[v] {
            let mut scc = Vec::new();
            loop {
                let w = stack.pop().expect("scc stack");
                on_stack[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            sccs.push(scc);
        }
    }

    for v in 0..n {
        if indices[v] == usize::MAX {
            strongconnect(
                v, &mut index, &mut indices, &mut lowlink, &mut stack,
                &mut on_stack, &mut sccs, value_free, name_to_idx,
            );
        }
    }

    sccs
}

/// For an unqualified name referenced from a module's body, find
/// which imported module it was brought in from (if any) and look up
/// that module's scheme output hash in the registry.
/// Build a map of imported alias names → arity, used by
/// `validate_module_with_imports` for the PartiallyAppliedSynonym
/// detector. Includes both:
/// - direct type-alias imports (alias name → arity), and
/// - type-fixity-operator imports whose target is a type alias
///   (operator name → target alias's arity).
///
/// Only unqualified imports contribute (qualified `import M as Q`
/// keeps the alias under `Q.Foo`, which bare `Constructor("Foo")`
/// references in the importer don't shadow). Module-aliased uses
/// hit a different code path that the detector doesn't probe.
/// Walk every (class_name, instance) pair in `ix` and emit an
/// `OverlappingInstances` validation error for any pair whose
/// heads can unify (after fresh-renaming each side's vars), unless
/// both instances come from the current module's local CST (those
/// pairs are caught by the local validate_decls detector).
///
/// Chain members (`chained == true`) are explicitly ordered
/// overlap and skipped.
fn detect_cross_module_instance_overlaps(
    ix: &crate::typecheck_db::passes::instance_index::InstanceIndex,
    local_instances: &[crate::typecheck_db::passes::instance_index::Instance],
    local_defined_type_names: &std::collections::HashSet<String>,
    validation_errors: &mut Vec<
        crate::typecheck_db::passes::validate_decls::ValidationError,
    >,
) {
    use crate::typecheck_db::passes::instance_index::Instance;
    use std::collections::HashMap;
    // Build a fingerprint set for local instances so we can ask
    // "is THIS instance from local CST?" without walking every
    // time.
    let local_keys: std::collections::HashSet<(String, usize, u64)> =
        local_instances
            .iter()
            .map(|i| (i.class.name.clone(), i.types.len(), instance_fingerprint(i)))
            .collect();
    // Group instances by class. The index already keys per-class;
    // we walk pairs WITHIN each group.
    let mut by_class: HashMap<String, Vec<&Instance>> = HashMap::new();
    for (cls, inst) in ix.all_instances() {
        if inst.chained {
            continue;
        }
        by_class.entry(cls.to_string()).or_default().push(inst);
    }
    // Drop any class that has at least one chain member — the
    // chain semantics make ordering deliberate.
    let chain_classes: std::collections::HashSet<String> = ix
        .all_instances()
        .filter_map(|(c, i)| if i.chained { Some(c.to_string()) } else { None })
        .collect();
    for cls in chain_classes {
        by_class.remove(&cls);
    }
    // Drop classes that declare fundeps. With fundeps, the
    // reference compiler accepts surface overlaps because fundep
    // resolution at use-site disambiguates. Examples that would
    // false-positive without this: `class Newtype t a | t -> a`
    // (one instance per newtype), `Row.Cons label ty rest row |
    // row -> ...`, `Row.Union r1 r2 r3 | r1 r2 -> r3, r1 r3 -> r2,
    // r2 r3 -> r1`. Source of truth: the class's declared `FunDep`
    // list, propagated from CST or `ModuleExports.classes` into the
    // instance index.
    let fundep_classes: std::collections::HashSet<String> = by_class
        .keys()
        .filter(|cls| {
            ix.class_info(cls.as_str())
                .map(|info| !info.fundeps.is_empty())
                .unwrap_or(false)
        })
        .cloned()
        .collect();
    for cls in fundep_classes {
        by_class.remove(&cls);
    }
    for (class_name, list) in by_class {
        let n = list.len();
        if n < 2 {
            continue;
        }
        // Pre-compute per-instance data once. Each prior version
        // recomputed `instance_fingerprint` (formerly a `Debug`-format
        // string) up to five times per pair — at O(n²) pairs that
        // turned this detector into ~50% of total typecheck time.
        // Fingerprint is a u64 structural hash now (collision
        // probability 1/2⁶⁴; a hypothetical collision would only
        // suppress a single overlap diagnostic — never a typechecker
        // correctness regression).
        let fingerprints: Vec<u64> =
            list.iter().map(|inst| instance_fingerprint(inst)).collect();
        let local_flags: Vec<bool> = list
            .iter()
            .zip(fingerprints.iter())
            .map(|(inst, fp)| {
                local_keys.contains(&(
                    inst.class.name.clone(),
                    inst.types.len(),
                    *fp,
                ))
            })
            .collect();
        // If this class has no local instances at all, every pair
        // would be cross-module-only — those are caught when the
        // owning modules are checked. Skip the whole class.
        if !local_flags.iter().any(|f| *f) {
            continue;
        }
        // Pre-compute the head-constructor key vector once per
        // instance. Comparing keys before calling
        // `instances_heads_unify` filters out the dominant case —
        // two instances at different concrete heads (e.g. `Show
        // Int` vs `Show String`) can't unify, so we skip the
        // allocation-heavy unification entirely.
        let head_keys: Vec<Vec<Option<String>>> =
            list.iter().map(|inst| instance_head_keys(inst)).collect();
        // Iterate `local × all` pairs only. The earlier shape
        // walked all O(n²) pairs and rejected local-local /
        // cross-cross inside the inner loop, which on
        // Deku.DOM-style aggregations (~6800 imported `Attr`
        // instances + 170 local) reached ~23M pair checks per
        // module. The reference compiler's diagnostic is
        // class-level (one per class), so we exit on the first
        // overlap found.
        let local_idxs: Vec<usize> = local_flags
            .iter()
            .enumerate()
            .filter_map(|(i, f)| if *f { Some(i) } else { None })
            .collect();
        let mut emitted = false;
        'outer: for &i in &local_idxs {
            if emitted {
                break;
            }
            let a = list[i];
            let a_fp = fingerprints[i];
            let a_keys = &head_keys[i];
            for j in 0..n {
                if i == j {
                    continue;
                }
                // Skip local-local — those are handled by the
                // validate_decls detector at parse time.
                if local_flags[j] {
                    continue;
                }
                let b = list[j];
                if a.types.len() != b.types.len() {
                    continue;
                }
                // Skip identical-head pairs — those are usually
                // the same instance arriving twice through a
                // re-export chain.
                if a_fp == fingerprints[j] {
                    continue;
                }
                // Cheap head-key pre-filter (see comment on
                // `head_keys_could_match`). Skips the dominant
                // case before any allocation.
                if !head_keys_could_match(a_keys, &head_keys[j]) {
                    continue;
                }
                if instances_heads_unify(a, b, local_defined_type_names) {
                    validation_errors.push(
                        crate::typecheck_db::passes::validate_decls::ValidationError {
                            span: crate::span::Span { start: 0, end: 0 },
                            kind: crate::typecheck_db::passes::validate_decls
                                ::ValidationErrorKind::OverlappingInstances(
                                    class_name.clone(),
                                ),
                        },
                    );
                    emitted = true;
                    break 'outer;
                }
            }
        }
    }
}

fn instance_fingerprint(
    i: &crate::typecheck_db::passes::instance_index::Instance,
) -> u64 {
    // Structural u64 hash of the instance's head types. Replaced
    // an earlier `format!("{:?}", …)` Debug-string fingerprint
    // because that allocated per call and dominated the
    // `detect_cross_module_instance_overlaps` loop. Collision
    // risk is 1/2⁶⁴, and a hypothetical collision merely
    // suppresses one overlap diagnostic — never a typechecker
    // correctness regression.
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    i.types.hash(&mut h);
    h.finish()
}

/// Cheap pre-filter for `detect_cross_module_instance_overlaps`:
/// extract the head-constructor name of every type in the instance
/// head, defaulting to `None` for type-variable heads (which can
/// unify with anything). Two instances whose head-key vectors
/// disagree on any concrete position can't possibly unify, so we
/// skip the expensive `instances_heads_unify` call.
fn instance_head_keys(
    i: &crate::typecheck_db::passes::instance_index::Instance,
) -> Vec<Option<String>> {
    use crate::typecheck_db::types::Type;
    fn key_of(t: &Type) -> Option<String> {
        match t {
            Type::Con(qn) => Some(qn.name.clone()),
            Type::App(f, _) => key_of(f),
            Type::Fun(_, _) => Some("->".to_string()),
            // Var / Forall / Constrained / Record / Row / Hole /
            // Wildcard / TypeString / TypeInt / Kinded / Unif /
            // Skolem all unify (or might unify) with anything in
            // the head position. Treat as wildcard.
            _ => None,
        }
    }
    i.types.iter().map(key_of).collect()
}

/// Two instance heads can't possibly unify if their head-keys
/// disagree on any concrete position. Vars (`None`) are wildcards.
fn head_keys_could_match(
    a: &[Option<String>],
    b: &[Option<String>],
) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b.iter()).all(|(x, y)| match (x, y) {
        (Some(x), Some(y)) => x == y,
        _ => true,
    })
}

fn instances_heads_unify(
    a: &crate::typecheck_db::passes::instance_index::Instance,
    b: &crate::typecheck_db::passes::instance_index::Instance,
    local_defined_type_names: &std::collections::HashSet<String>,
) -> bool {
    use crate::typecheck_db::generalize::apply_var_subst;
    use crate::typecheck_db::types::Type;
    use crate::typecheck_db::unify::UnifyState;
    if a.types.len() != b.types.len() {
        return false;
    }
    // Before the full unification, check for type-constructor head mismatches
    // that the lenient unifier would otherwise accept. Specifically: if `a`
    // (the LOCAL instance) refers to a locally-defined type `Con(None, X)`
    // and `b` (the imported instance) refers to a different module's `X` via
    // `Con(Some(m), X)`, they are DIFFERENT types and cannot overlap.
    // Returns true when the LOCAL instance's type head uses a locally-defined
    // constructor `X` (Con(None, X) where X ∈ local_names) against the
    // IMPORTED instance's head. Since locally-defined types are unique to the
    // current module, the imported instance cannot legitimately refer to the
    // same type regardless of the imported instance's module qualifier.
    fn locally_defined_con_mismatch(
        ta: &Type,
        tb: &Type,
        local_names: &std::collections::HashSet<String>,
    ) -> bool {
        match (ta, tb) {
            (Type::Con(qa), Type::Con(qb)) => {
                // `ta` is from the LOCAL instance; `tb` from the IMPORTED.
                // If `ta`'s name is locally defined in the current module,
                // the two instances refer to different types — block overlap.
                qa.name == qb.name
                    && qa.module.is_none()
                    && local_names.contains(&qa.name)
            }
            (Type::App(fa, aa), Type::App(fb, ab)) => {
                locally_defined_con_mismatch(fa, fb, local_names)
                    || locally_defined_con_mismatch(aa, ab, local_names)
            }
            (Type::Fun(fa, ra), Type::Fun(fb, rb)) => {
                locally_defined_con_mismatch(fa, fb, local_names)
                    || locally_defined_con_mismatch(ra, rb, local_names)
            }
            _ => false,
        }
    }
    let mut state = UnifyState::new();
    let mut subst_a: std::collections::HashMap<String, Type> =
        std::collections::HashMap::new();
    for v in &a.vars {
        subst_a.insert(v.clone(), state.fresh());
    }
    let head_a: Vec<_> = a.types.iter().map(|t| apply_var_subst(t, &subst_a)).collect();
    let mut subst_b: std::collections::HashMap<String, Type> =
        std::collections::HashMap::new();
    for v in &b.vars {
        subst_b.insert(v.clone(), state.fresh());
    }
    let head_b: Vec<_> = b.types.iter().map(|t| apply_var_subst(t, &subst_b)).collect();
    for (ta, tb) in head_a.iter().zip(head_b.iter()) {
        if locally_defined_con_mismatch(ta, tb, local_defined_type_names) {
            return false;
        }
        if state.unify(ta, tb).is_err() {
            return false;
        }
    }
    true
}

fn build_imported_alias_arity(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> std::collections::HashMap<crate::interner::Symbol, usize> {
    use crate::interner::intern;
    let mut out: std::collections::HashMap<crate::interner::Symbol, usize> =
        std::collections::HashMap::new();
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target = join_module_name(&imp.module);
        let exports = match registry.get(&target) {
            Some(e) => e,
            None => continue,
        };
        match &imp.imports {
            Some(crate::cst::ImportList::Explicit(items)) => {
                // Only insert type aliases and type operators explicitly named.
                let named_types: std::collections::HashSet<String> = items
                    .iter()
                    .filter_map(|item| match item {
                        crate::cst::Import::Type(tn, _) => {
                            Some(crate::typecheck_db::util::resolve_symbol(tn.value.symbol()))
                        }
                        crate::cst::Import::TypeOp(tn) => {
                            Some(crate::typecheck_db::util::resolve_symbol(tn.value.symbol()))
                        }
                        _ => None,
                    })
                    .collect();
                for name in &named_types {
                    if let Some(alias) = exports.type_aliases.get(name) {
                        out.insert(intern(name), alias.type_vars.len());
                    }
                    // Type operator explicitly imported
                    if let Some(fix) = exports.type_fixities.get(name) {
                        if let Some(alias) = exports.type_aliases.get(&fix.target_name) {
                            out.insert(intern(name), alias.type_vars.len());
                        }
                    }
                }
            }
            Some(crate::cst::ImportList::Hiding(hidden)) => {
                let hidden_types: std::collections::HashSet<String> = hidden
                    .iter()
                    .filter_map(|item| match item {
                        crate::cst::Import::Type(tn, _) => {
                            Some(crate::typecheck_db::util::resolve_symbol(tn.value.symbol()))
                        }
                        crate::cst::Import::TypeOp(tn) => {
                            Some(crate::typecheck_db::util::resolve_symbol(tn.value.symbol()))
                        }
                        _ => None,
                    })
                    .collect();
                for (alias_name, alias) in &exports.type_aliases {
                    if !hidden_types.contains(alias_name) {
                        out.insert(intern(alias_name), alias.type_vars.len());
                    }
                }
                for (op_name, fix) in &exports.type_fixities {
                    if !hidden_types.contains(op_name) {
                        if let Some(alias) = exports.type_aliases.get(&fix.target_name) {
                            out.insert(intern(op_name), alias.type_vars.len());
                        }
                    }
                }
            }
            None => {
                for (alias_name, alias) in &exports.type_aliases {
                    out.insert(intern(alias_name), alias.type_vars.len());
                }
                for (op_name, fix) in &exports.type_fixities {
                    if let Some(alias) = exports.type_aliases.get(&fix.target_name) {
                        out.insert(intern(op_name), alias.type_vars.len());
                    }
                }
            }
        }
    }
    out
}

/// Builds the set of imported POLYKINDED alias names (interned symbols).
/// A polykinded alias has a standalone kind signature whose outermost form
/// is `forall …`.  Such aliases are valid to use with zero explicit type
/// args (the kind unifier instantiates the forall), so the
/// `PartiallyAppliedSynonym` bare-constructor check must skip them.
fn build_imported_poly_kind_set(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> std::collections::HashSet<crate::interner::Symbol> {
    use crate::interner::intern;
    let mut out: std::collections::HashSet<crate::interner::Symbol> =
        std::collections::HashSet::new();
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target = join_module_name(&imp.module);
        let exports = match registry.get(&target) {
            Some(e) => e,
            None => continue,
        };
        let insert_if_poly = |name: &str, out: &mut std::collections::HashSet<_>| {
            if let Some(alias) = exports.type_aliases.get(name) {
                if alias.has_poly_kind {
                    out.insert(intern(name));
                }
            }
        };
        match &imp.imports {
            Some(crate::cst::ImportList::Explicit(items)) => {
                for item in items {
                    match item {
                        crate::cst::Import::Type(tn, _) => {
                            let n =
                                crate::typecheck_db::util::resolve_symbol(tn.value.symbol());
                            insert_if_poly(&n, &mut out);
                        }
                        crate::cst::Import::TypeOp(tn) => {
                            let op =
                                crate::typecheck_db::util::resolve_symbol(tn.value.symbol());
                            if let Some(fix) = exports.type_fixities.get(&op) {
                                if let Some(alias) =
                                    exports.type_aliases.get(&fix.target_name)
                                {
                                    if alias.has_poly_kind {
                                        out.insert(intern(&op));
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            Some(crate::cst::ImportList::Hiding(hidden)) => {
                let hidden_types: std::collections::HashSet<String> = hidden
                    .iter()
                    .filter_map(|item| match item {
                        crate::cst::Import::Type(tn, _) => {
                            Some(crate::typecheck_db::util::resolve_symbol(tn.value.symbol()))
                        }
                        crate::cst::Import::TypeOp(tn) => {
                            Some(crate::typecheck_db::util::resolve_symbol(tn.value.symbol()))
                        }
                        _ => None,
                    })
                    .collect();
                for (alias_name, alias) in &exports.type_aliases {
                    if !hidden_types.contains(alias_name) && alias.has_poly_kind {
                        out.insert(intern(alias_name));
                    }
                }
                for (op_name, fix) in &exports.type_fixities {
                    if !hidden_types.contains(op_name) {
                        if let Some(alias) = exports.type_aliases.get(&fix.target_name) {
                            if alias.has_poly_kind {
                                out.insert(intern(op_name));
                            }
                        }
                    }
                }
            }
            None => {
                for (alias_name, alias) in &exports.type_aliases {
                    if alias.has_poly_kind {
                        out.insert(intern(alias_name));
                    }
                }
                for (op_name, fix) in &exports.type_fixities {
                    if let Some(alias) = exports.type_aliases.get(&fix.target_name) {
                        if alias.has_poly_kind {
                            out.insert(intern(op_name));
                        }
                    }
                }
            }
        }
    }
    out
}

/// Registry-aware UnknownExport check. Walks `module.exports` and
/// emits a `ValidationError::UnknownExport` (or
/// `UnknownExportDataConstructor`) whenever an export-list item
/// references a name that's neither locally declared nor brought
/// into scope through one of the module's imports.
fn detect_unknown_exports_registry(
    module: &cst::Module,
    registry: &ModuleRegistry,
    errors: &mut Vec<crate::typecheck_db::passes::validate_decls::ValidationError>,
) {
    use crate::typecheck_db::passes::validate_decls::{
        ValidationError, ValidationErrorKind,
    };
    let Some(spanned) = &module.exports else {
        return;
    };
    // Build per-namespace name sets from local decls + every import.
    let mut values: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut classes: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut types: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut value_ops: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut type_ops: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut data_ctors_of: std::collections::HashMap<
        String,
        std::collections::HashSet<String>,
    > = std::collections::HashMap::new();

    for d in &module.decls {
        match d {
            cst::Decl::Value { name, .. } | cst::Decl::Foreign { name, .. } => {
                values.insert(crate::typecheck_db::util::resolve_symbol(name.value.symbol()));
            }
            cst::Decl::Class { name, members, is_kind_sig: false, .. } => {
                classes.insert(crate::typecheck_db::util::resolve_symbol(name.value.symbol()));
                for m in members {
                    values.insert(crate::typecheck_db::util::resolve_symbol(m.name.value.symbol()));
                }
            }
            cst::Decl::Data { name, constructors, kind_sig: cst::KindSigSource::None, is_role_decl: false, .. } => {
                let tn = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                types.insert(tn.clone());
                let mut cs: std::collections::HashSet<String> = std::collections::HashSet::new();
                for c in constructors {
                    cs.insert(crate::typecheck_db::util::resolve_symbol(c.name.value.symbol()));
                }
                data_ctors_of.insert(tn, cs);
            }
            cst::Decl::Newtype { name, constructor, .. } => {
                let tn = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                types.insert(tn.clone());
                let mut cs: std::collections::HashSet<String> = std::collections::HashSet::new();
                cs.insert(crate::typecheck_db::util::resolve_symbol(constructor.value.symbol()));
                data_ctors_of.insert(tn, cs);
            }
            cst::Decl::TypeAlias { name, .. } | cst::Decl::ForeignData { name, .. } => {
                types.insert(crate::typecheck_db::util::resolve_symbol(name.value.symbol()));
            }
            cst::Decl::Fixity { operator, is_type, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(operator.value.symbol());
                if *is_type { type_ops.insert(n); } else { value_ops.insert(n); }
            }
            _ => {}
        }
    }
    // Imports: only unqualified imports introduce names into the
    // module's unqualified namespace. Walk each and add what they
    // surface, respecting open / explicit / hiding lists.
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target_name = join_module_name(&imp.module);
        let Some(target) = registry.get(&target_name) else { continue };
        match &imp.imports {
            None => {
                values.extend(target.values.keys().cloned());
                classes.extend(target.classes.keys().cloned());
                types.extend(target.type_arities.keys().cloned());
                value_ops.extend(target.value_fixities.keys().cloned());
                type_ops.extend(target.type_fixities.keys().cloned());
            }
            Some(crate::cst::ImportList::Hiding(items)) => {
                let mut hide_v: std::collections::HashSet<String> = std::collections::HashSet::new();
                let mut hide_c: std::collections::HashSet<String> = std::collections::HashSet::new();
                let mut hide_t: std::collections::HashSet<String> = std::collections::HashSet::new();
                let mut hide_top: std::collections::HashSet<String> = std::collections::HashSet::new();
                for item in items {
                    let n = crate::typecheck_db::util::resolve_symbol(item.name());
                    match item {
                        cst::Import::Value(_) => { hide_v.insert(n); }
                        cst::Import::Class(_) => { hide_c.insert(n); }
                        cst::Import::Type(_, _) => { hide_t.insert(n); }
                        cst::Import::TypeOp(_) => { hide_top.insert(n); }
                    }
                }
                for k in target.values.keys() { if !hide_v.contains(k) { values.insert(k.clone()); } }
                for k in target.classes.keys() { if !hide_c.contains(k) { classes.insert(k.clone()); } }
                for k in target.type_arities.keys() { if !hide_t.contains(k) { types.insert(k.clone()); } }
                for k in target.value_fixities.keys() { if !hide_v.contains(k) { value_ops.insert(k.clone()); } }
                for k in target.type_fixities.keys() { if !hide_top.contains(k) { type_ops.insert(k.clone()); } }
            }
            Some(crate::cst::ImportList::Explicit(items)) => {
                for item in items {
                    let n = crate::typecheck_db::util::resolve_symbol(item.name());
                    match item {
                        cst::Import::Value(_) => {
                            values.insert(n.clone());
                            value_ops.insert(n);
                        }
                        cst::Import::Class(_) => { classes.insert(n); }
                        cst::Import::Type(_, _) => { types.insert(n); }
                        cst::Import::TypeOp(_) => { type_ops.insert(n); }
                    }
                }
            }
        }
    }
    for e in &spanned.value.exports {
        match e {
            crate::cst::Export::Value(vn) => {
                let n = crate::typecheck_db::util::resolve_symbol(vn.symbol());
                if !values.contains(&n) && !value_ops.contains(&n) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(n),
                    });
                }
            }
            crate::cst::Export::Class(cn) => {
                let n = crate::typecheck_db::util::resolve_symbol(cn.symbol());
                if !classes.contains(&n) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(n),
                    });
                }
            }
            crate::cst::Export::TypeOp(on) => {
                let n = crate::typecheck_db::util::resolve_symbol(on.symbol());
                if !type_ops.contains(&n) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(n),
                    });
                }
            }
            crate::cst::Export::Type(tn, _members) => {
                let n = crate::typecheck_db::util::resolve_symbol(tn.symbol());
                if !types.contains(&n) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(n),
                    });
                }
            }
            crate::cst::Export::Module(_) => {}
        }
    }
}

/// Use-site ScopeConflict. Build a set of names that are
/// unqualified-open-imported from MULTIPLE distinct origin modules
/// without any explicit-list pin; then walk the module body for
/// `Var` references to those names. Emit ScopeConflict at the
/// use site.
fn detect_use_site_scope_conflict(
    module: &cst::Module,
    registry: &ModuleRegistry,
    errors: &mut Vec<crate::typecheck_db::passes::imports::ImportError>,
) {
    use crate::typecheck_db::passes::imports::{ImportError, ImportErrorKind};
    // For each name, collect (origin_module, target_module) pairs
    // where target = the imported module, origin = the module the
    // value was originally declared in (== target if directly
    // declared; != target if re-exported).
    // To avoid false positives on re-export chains where Prelude's
    // `module Data.Function` clause incorrectly leaks unfiltered
    // re-exports, we only flag a conflict when at least TWO
    // distinct DIRECT (target == origin) imports contribute the
    // same name.
    let mut open_direct: std::collections::HashMap<
        String,
        std::collections::HashSet<String>,
    > = std::collections::HashMap::new();
    let mut explicit_pinned: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let prims = crate::typecheck_db::prim::prim_exports();
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target_name = join_module_name(&imp.module);
        let exports: Option<&ModuleExports> = registry
            .get(&target_name)
            .or_else(|| prims.get(&target_name));
        let Some(exports) = exports else { continue };
        let mut walk_open = |hide: Option<&std::collections::HashSet<String>>,
                              open_direct: &mut std::collections::HashMap<
                                  String,
                                  std::collections::HashSet<String>,
                              >| {
            for (n, _) in &exports.values {
                if let Some(h) = hide {
                    if h.contains(n) {
                        continue;
                    }
                }
                let origin = exports
                    .value_origins
                    .get(n)
                    .cloned()
                    .unwrap_or_else(|| target_name.clone());
                if origin == target_name {
                    open_direct
                        .entry(n.clone())
                        .or_default()
                        .insert(origin);
                }
            }
        };
        match &imp.imports {
            None => {
                walk_open(None, &mut open_direct);
            }
            Some(crate::cst::ImportList::Hiding(items)) => {
                let mut hide_v: std::collections::HashSet<String> =
                    std::collections::HashSet::new();
                for item in items {
                    if let cst::Import::Value(_) = item {
                        hide_v.insert(crate::typecheck_db::util::resolve_symbol(
                            item.name(),
                        ));
                    }
                }
                walk_open(Some(&hide_v), &mut open_direct);
            }
            Some(crate::cst::ImportList::Explicit(items)) => {
                for item in items {
                    if let cst::Import::Value(_) = item {
                        let n =
                            crate::typecheck_db::util::resolve_symbol(item.name());
                        explicit_pinned.insert(n);
                    }
                }
            }
        }
    }
    // Names that remain ambiguous: 2+ DIRECT origins from open
    // imports, not pinned by any explicit list, and not locally
    // defined (a local definition shadows the imports).
    let mut local_value_names: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for d in &module.decls {
        match d {
            cst::Decl::Value { name, .. }
            | cst::Decl::Foreign { name, .. } => {
                local_value_names.insert(
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol()),
                );
            }
            _ => {}
        }
    }
    let ambiguous: std::collections::HashSet<String> = open_direct
        .into_iter()
        .filter_map(|(n, origins)| {
            if origins.len() >= 2
                && !explicit_pinned.contains(&n)
                && !local_value_names.contains(&n)
            {
                Some(n)
            } else {
                None
            }
        })
        .collect();
    if ambiguous.is_empty() {
        return;
    }
    // Walk module body for Var refs to ambiguous names.
    let mut emitted: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for d in &module.decls {
        if let cst::Decl::Value { guarded, where_clause, span, .. } = d {
            walk_guarded_for_ambig(
                guarded,
                &ambiguous,
                *span,
                &mut emitted,
                errors,
            );
            for b in where_clause {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_ambig(
                        expr,
                        &ambiguous,
                        *span,
                        &mut emitted,
                        errors,
                    );
                }
            }
        }
    }
    let _ = ImportError {
        span: crate::span::Span::new(0, 0),
        kind: ImportErrorKind::ScopeConflict {
            name: String::new(),
            first_module: String::new(),
            second_module: String::new(),
            first_import: crate::span::Span::new(0, 0),
            second_import: crate::span::Span::new(0, 0),
        },
    };
}

fn walk_guarded_for_ambig(
    g: &crate::cst::GuardedExpr,
    ambiguous: &std::collections::HashSet<String>,
    span: crate::span::Span,
    emitted: &mut std::collections::HashSet<String>,
    errors: &mut Vec<crate::typecheck_db::passes::imports::ImportError>,
) {
    match g {
        crate::cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_ambig(e, ambiguous, span, emitted, errors);
        }
        crate::cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        crate::cst::GuardPattern::Pattern(_, e)
                        | crate::cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_ambig(e, ambiguous, span, emitted, errors);
                        }
                    }
                }
                walk_expr_for_ambig(&gd.expr, ambiguous, span, emitted, errors);
            }
        }
    }
}

fn walk_expr_for_ambig(
    expr: &crate::cst::Expr,
    ambiguous: &std::collections::HashSet<String>,
    span: crate::span::Span,
    emitted: &mut std::collections::HashSet<String>,
    errors: &mut Vec<crate::typecheck_db::passes::imports::ImportError>,
) {
    use crate::typecheck_db::passes::imports::{ImportError, ImportErrorKind};
    match expr {
        cst::Expr::Var { name, .. } if name.module.is_none() => {
            let n = crate::typecheck_db::util::resolve_symbol(name.name.symbol());
            if ambiguous.contains(&n) && emitted.insert(n.clone()) {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::ScopeConflict {
                        name: n,
                        first_module: String::new(),
                        second_module: String::new(),
                        first_import: span,
                        second_import: span,
                    },
                });
            }
        }
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_ambig(func, ambiguous, span, emitted, errors);
            walk_expr_for_ambig(arg, ambiguous, span, emitted, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_ambig(func, ambiguous, span, emitted, errors);
        }
        cst::Expr::Lambda { body, .. } => {
            walk_expr_for_ambig(body, ambiguous, span, emitted, errors);
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_ambig(left, ambiguous, span, emitted, errors);
            walk_expr_for_ambig(right, ambiguous, span, emitted, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_ambig(cond, ambiguous, span, emitted, errors);
            walk_expr_for_ambig(then_expr, ambiguous, span, emitted, errors);
            walk_expr_for_ambig(else_expr, ambiguous, span, emitted, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_ambig(e, ambiguous, span, emitted, errors);
            }
            for alt in alts {
                walk_guarded_for_ambig(&alt.result, ambiguous, span, emitted, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_ambig(expr, ambiguous, span, emitted, errors);
                }
            }
            walk_expr_for_ambig(body, ambiguous, span, emitted, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_ambig(expr, ambiguous, span, emitted, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_ambig(
                                    expr, ambiguous, span, emitted, errors,
                                );
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_ambig(result, ambiguous, span, emitted, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_ambig(v, ambiguous, span, emitted, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_ambig(expr, ambiguous, span, emitted, errors);
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_ambig(expr, ambiguous, span, emitted, errors);
            for u in updates {
                walk_expr_for_ambig(&u.value, ambiguous, span, emitted, errors);
            }
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_for_ambig(expr, ambiguous, span, emitted, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_ambig(e, ambiguous, span, emitted, errors);
            }
        }
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_ambig(name, ambiguous, span, emitted, errors);
            walk_expr_for_ambig(pattern, ambiguous, span, emitted, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_ambig(func, ambiguous, span, emitted, errors);
            walk_expr_for_ambig(left, ambiguous, span, emitted, errors);
            walk_expr_for_ambig(right, ambiguous, span, emitted, errors);
        }
        _ => {}
    }
    let _ = ImportError {
        span: crate::span::Span::new(0, 0),
        kind: ImportErrorKind::ScopeConflict {
            name: String::new(),
            first_module: String::new(),
            second_module: String::new(),
            first_import: crate::span::Span::new(0, 0),
            second_import: crate::span::Span::new(0, 0),
        },
    };
}

/// Walks every kind-annotation position in `module.decls` (the
/// `K` in `forall (a :: K).`, in `data T :: K`, in `class C :: K`,
/// in `(x :: K)` annotations) for unqualified `Constructor`
/// references that aren't local and aren't brought in by any
/// unqualified import. Emits `UnknownName` for each.
fn detect_unknown_kind_refs_registry(
    module: &cst::Module,
    registry: &ModuleRegistry,
    errors: &mut Vec<crate::typecheck_db::passes::validate_decls::ValidationError>,
) {
    use crate::typecheck_db::passes::validate_decls::{
        ValidationError, ValidationErrorKind,
    };
    let mut known: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for d in &module.decls {
        match d {
            cst::Decl::Data { name, .. }
            | cst::Decl::Newtype { name, .. }
            | cst::Decl::TypeAlias { name, .. }
            | cst::Decl::ForeignData { name, .. } => {
                known.insert(crate::typecheck_db::util::resolve_symbol(
                    name.value.symbol(),
                ));
            }
            _ => {}
        }
    }
    let prims = crate::typecheck_db::prim::prim_exports();
    // Prim auto-import: skipped when the module explicitly writes
    // `import Prim` or `import Prim (...)` — the explicit form
    // restricts the visible Prim names to only those listed.
    let has_explicit_prim = module
        .imports
        .iter()
        .any(|imp| join_module_name(&imp.module) == "Prim");
    if !has_explicit_prim {
        if let Some(prim) = prims.get("Prim") {
            for k in prim.type_arities.keys() {
                known.insert(k.clone());
            }
        }
    }
    // `(->)` is the built-in function-type constructor; it's always valid.
    known.insert("->".to_string());
    for imp in &module.imports {
        let target = join_module_name(&imp.module);
        let exports: Option<&ModuleExports> = registry
            .get(&target)
            .or_else(|| prims.get(&target));
        let Some(exports) = exports else { continue };
        if imp.qualified.is_some() {
            continue;
        }
        match &imp.imports {
            None | Some(crate::cst::ImportList::Hiding(_)) => {
                for k in exports.type_arities.keys() {
                    known.insert(k.clone());
                }
                for k in exports.type_aliases.keys() {
                    known.insert(k.clone());
                }
            }
            Some(crate::cst::ImportList::Explicit(items)) => {
                for item in items {
                    if let cst::Import::Type(_, _) = item {
                        let n =
                            crate::typecheck_db::util::resolve_symbol(item.name());
                        known.insert(n);
                    }
                }
            }
        }
    }
    let mut seen: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for d in &module.decls {
        match d {
            cst::Decl::TypeSignature { ty, span, .. }
            | cst::Decl::Foreign { ty, span, .. } => {
                check_kind_anns(ty, *span, &known, &mut seen, errors);
            }
            cst::Decl::Class { members, kind_type, span, .. } => {
                if let Some(k) = kind_type {
                    check_kind_anns_in_kind(k, *span, &known, &mut seen, errors);
                }
                for m in members {
                    check_kind_anns(&m.ty, m.span, &known, &mut seen, errors);
                }
            }
            cst::Decl::Data { kind_type, span, .. } => {
                if let Some(k) = kind_type {
                    check_kind_anns_in_kind(k, *span, &known, &mut seen, errors);
                }
            }
            _ => {}
        }
    }
    let _ = ValidationErrorKind::UnknownName(String::new());
    let _ = ValidationError {
        span: crate::span::Span::new(0, 0),
        kind: ValidationErrorKind::UnknownName(String::new()),
    };
}

fn check_kind_anns(
    ty: &cst::TypeExpr,
    span: crate::span::Span,
    known: &std::collections::HashSet<String>,
    seen: &mut std::collections::HashSet<String>,
    errors: &mut Vec<crate::typecheck_db::passes::validate_decls::ValidationError>,
) {
    use crate::typecheck_db::passes::validate_decls::{
        ValidationError, ValidationErrorKind,
    };
    match ty {
        cst::TypeExpr::Forall { vars, ty: inner, .. } => {
            for (_, _, kind) in vars {
                if let Some(k) = kind {
                    check_kind_anns_in_kind(k, span, known, seen, errors);
                }
            }
            check_kind_anns(inner, span, known, seen, errors);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            check_kind_anns(from, span, known, seen, errors);
            check_kind_anns(to, span, known, seen, errors);
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            check_kind_anns(constructor, span, known, seen, errors);
            check_kind_anns(arg, span, known, seen, errors);
        }
        cst::TypeExpr::Constrained { constraints, ty: inner, .. } => {
            for c in constraints {
                for arg in &c.args {
                    check_kind_anns(arg, span, known, seen, errors);
                }
            }
            check_kind_anns(inner, span, known, seen, errors);
        }
        cst::TypeExpr::Parens { ty: inner, .. } => {
            check_kind_anns(inner, span, known, seen, errors);
        }
        cst::TypeExpr::Kinded { ty: inner, kind, .. } => {
            check_kind_anns(inner, span, known, seen, errors);
            check_kind_anns_in_kind(kind, span, known, seen, errors);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                check_kind_anns(&f.ty, span, known, seen, errors);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                check_kind_anns(&f.ty, span, known, seen, errors);
            }
            if let Some(t) = tail {
                check_kind_anns(t, span, known, seen, errors);
            }
        }
        _ => {}
    }
    let _ = ValidationError {
        span,
        kind: ValidationErrorKind::UnknownName(String::new()),
    };
}

fn check_kind_anns_in_kind(
    ty: &cst::TypeExpr,
    span: crate::span::Span,
    known: &std::collections::HashSet<String>,
    seen: &mut std::collections::HashSet<String>,
    errors: &mut Vec<crate::typecheck_db::passes::validate_decls::ValidationError>,
) {
    use crate::typecheck_db::passes::validate_decls::{
        ValidationError, ValidationErrorKind,
    };
    match ty {
        cst::TypeExpr::Constructor { name, .. } if name.module.is_none() => {
            let n = crate::typecheck_db::util::resolve_symbol(name.name.symbol());
            if !known.contains(&n) && seen.insert(n.clone()) {
                errors.push(ValidationError {
                    span,
                    kind: ValidationErrorKind::UnknownName(n),
                });
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            check_kind_anns_in_kind(constructor, span, known, seen, errors);
            check_kind_anns_in_kind(arg, span, known, seen, errors);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            check_kind_anns_in_kind(from, span, known, seen, errors);
            check_kind_anns_in_kind(to, span, known, seen, errors);
        }
        cst::TypeExpr::Parens { ty: inner, .. } => {
            check_kind_anns_in_kind(inner, span, known, seen, errors);
        }
        cst::TypeExpr::Forall { ty: inner, .. } => {
            check_kind_anns_in_kind(inner, span, known, seen, errors);
        }
        _ => {}
    }
}

/// Walks every TypeExpr in `module.decls` for unqualified
/// `Constructor` references (type ctors) that aren't local and
/// aren't brought in by any unqualified import. Emits `UnknownName`
/// for each such reference.
fn detect_unknown_type_refs_registry(
    module: &cst::Module,
    registry: &ModuleRegistry,
    errors: &mut Vec<crate::typecheck_db::passes::validate_decls::ValidationError>,
) {
    use crate::typecheck_db::passes::validate_decls::{
        ValidationError, ValidationErrorKind,
    };
    let mut known: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for d in &module.decls {
        match d {
            cst::Decl::Data { name, .. }
            | cst::Decl::Newtype { name, .. }
            | cst::Decl::TypeAlias { name, .. }
            | cst::Decl::ForeignData { name, .. } => {
                known.insert(crate::typecheck_db::util::resolve_symbol(
                    name.value.symbol(),
                ));
            }
            _ => {}
        }
    }
    let prims = crate::typecheck_db::prim::prim_exports();
    // Prim auto-import: skipped when the module explicitly writes
    // `import Prim` or `import Prim (...)` — the explicit form
    // restricts the visible Prim names to only those listed.
    let has_explicit_prim = module
        .imports
        .iter()
        .any(|imp| join_module_name(&imp.module) == "Prim");
    if !has_explicit_prim {
        if let Some(prim) = prims.get("Prim") {
            for k in prim.type_arities.keys() {
                known.insert(k.clone());
            }
        }
    }
    // `(->)` is the built-in function-type constructor; always valid.
    known.insert("->".to_string());
    // Collect type-level operator names too — some grammars emit
    // ops in Constructor position post-desugar, and even if not,
    // we don't want a use-site `(~>)` that's an operator-aliased
    // type to surface as UnknownName.
    for d in &module.decls {
        if let cst::Decl::Fixity { operator, is_type: true, .. } = d {
            known.insert(crate::typecheck_db::util::resolve_symbol(
                operator.value.symbol(),
            ));
        }
    }
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target = join_module_name(&imp.module);
        let exports: Option<&ModuleExports> = registry
            .get(&target)
            .or_else(|| prims.get(&target));
        let Some(exports) = exports else { continue };
        match &imp.imports {
            None | Some(crate::cst::ImportList::Hiding(_)) => {
                for k in exports.type_arities.keys() {
                    known.insert(k.clone());
                }
                for k in exports.type_fixities.keys() {
                    known.insert(k.clone());
                }
            }
            Some(crate::cst::ImportList::Explicit(items)) => {
                for item in items {
                    match item {
                        cst::Import::Type(_, _) | cst::Import::TypeOp(_) => {
                            let n =
                                crate::typecheck_db::util::resolve_symbol(item.name());
                            known.insert(n);
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    let mut seen: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut walk = |ty: &cst::TypeExpr,
                    span: crate::span::Span,
                    seen: &mut std::collections::HashSet<String>,
                    errors: &mut Vec<ValidationError>| {
        let mut refs: Vec<String> = Vec::new();
        collect_unqualified_type_constructors(ty, &mut refs);
        for r in refs {
            if !known.contains(&r) && seen.insert(r.clone()) {
                errors.push(ValidationError {
                    span,
                    kind: ValidationErrorKind::UnknownName(r),
                });
            }
        }
    };
    for d in &module.decls {
        match d {
            cst::Decl::TypeSignature { ty, span, .. }
            | cst::Decl::Foreign { ty, span, .. } => {
                walk(ty, *span, &mut seen, errors);
            }
            cst::Decl::Class { members, .. } => {
                for m in members {
                    walk(&m.ty, m.span, &mut seen, errors);
                }
            }
            _ => {}
        }
    }
}

fn collect_unqualified_type_constructors(te: &cst::TypeExpr, out: &mut Vec<String>) {
    match te {
        cst::TypeExpr::Constructor { name, .. } if name.module.is_none() => {
            out.push(crate::typecheck_db::util::resolve_symbol(name.name.symbol()));
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            collect_unqualified_type_constructors(constructor, out);
            collect_unqualified_type_constructors(arg, out);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            collect_unqualified_type_constructors(from, out);
            collect_unqualified_type_constructors(to, out);
        }
        cst::TypeExpr::Forall { vars, ty, .. } => {
            for (_, _, kind) in vars {
                if let Some(k) = kind {
                    collect_unqualified_type_constructors(k, out);
                }
            }
            collect_unqualified_type_constructors(ty, out);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for arg in &c.args {
                    collect_unqualified_type_constructors(arg, out);
                }
            }
            collect_unqualified_type_constructors(ty, out);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                collect_unqualified_type_constructors(&f.ty, out);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                collect_unqualified_type_constructors(&f.ty, out);
            }
            if let Some(t) = tail {
                collect_unqualified_type_constructors(t, out);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => {
            collect_unqualified_type_constructors(ty, out);
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            collect_unqualified_type_constructors(left, out);
            collect_unqualified_type_constructors(right, out);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            collect_unqualified_type_constructors(ty, out);
            collect_unqualified_type_constructors(kind, out);
        }
        _ => {}
    }
}

/// Imported value-operator and type-operator names → (precedence,
/// associativity). Used by the MixedAssociativityError detector.
fn build_imported_op_fixity(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> (
    std::collections::HashMap<crate::interner::Symbol, (u8, crate::cst::Associativity)>,
    std::collections::HashMap<crate::interner::Symbol, (u8, crate::cst::Associativity)>,
) {
    use crate::interner::intern;
    let mut val: std::collections::HashMap<
        crate::interner::Symbol,
        (u8, crate::cst::Associativity),
    > = std::collections::HashMap::new();
    let mut typ: std::collections::HashMap<
        crate::interner::Symbol,
        (u8, crate::cst::Associativity),
    > = std::collections::HashMap::new();
    let prims = crate::typecheck_db::prim::prim_exports();
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target = join_module_name(&imp.module);
        let exports: Option<&ModuleExports> = registry
            .get(&target)
            .or_else(|| prims.get(&target));
        let Some(exports) = exports else { continue };
        for (op, fix) in &exports.value_fixities {
            val.insert(intern(op), (fix.precedence, fix.associativity));
        }
        for (op, fix) in &exports.type_fixities {
            typ.insert(intern(op), (fix.precedence, fix.associativity));
        }
    }
    (val, typ)
}

/// Imported value-operator and type-operator names → associativity.
/// Used by the NonAssociativeError detector for chains involving
/// imported operators (e.g. `==` from Data.Eq).
fn build_imported_op_associativity(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> (
    std::collections::HashMap<crate::interner::Symbol, crate::cst::Associativity>,
    std::collections::HashMap<crate::interner::Symbol, crate::cst::Associativity>,
) {
    use crate::interner::intern;
    let mut val: std::collections::HashMap<
        crate::interner::Symbol,
        crate::cst::Associativity,
    > = std::collections::HashMap::new();
    let mut typ: std::collections::HashMap<
        crate::interner::Symbol,
        crate::cst::Associativity,
    > = std::collections::HashMap::new();
    let prims = crate::typecheck_db::prim::prim_exports();
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target = join_module_name(&imp.module);
        let exports: Option<&ModuleExports> = registry
            .get(&target)
            .or_else(|| prims.get(&target));
        let Some(exports) = exports else { continue };
        for (op, fix) in &exports.value_fixities {
            val.insert(intern(op), fix.associativity);
        }
        for (op, fix) in &exports.type_fixities {
            typ.insert(intern(op), fix.associativity);
        }
    }
    (val, typ)
}

/// Imported class name → positional fundeps. Each
/// `(determiners, determined)` is a pair of `Vec<usize>` indexing
/// into the class's `type_vars`. Used by the fundep-aware
/// orphan-instance detector.
fn build_imported_class_fundeps(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> std::collections::HashMap<crate::interner::Symbol, Vec<(Vec<usize>, Vec<usize>)>>
{
    use crate::interner::intern;
    let mut out: std::collections::HashMap<
        crate::interner::Symbol,
        Vec<(Vec<usize>, Vec<usize>)>,
    > = std::collections::HashMap::new();
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target = join_module_name(&imp.module);
        let exports = match registry.get(&target) {
            Some(e) => e,
            None => continue,
        };
        for (class_name, class_info) in &exports.classes {
            let var_names: Vec<&str> =
                class_info.type_vars.iter().map(|s| s.as_str()).collect();
            let fds: Vec<(Vec<usize>, Vec<usize>)> = class_info
                .fundeps
                .iter()
                .map(|fd| (fd.determiners.clone(), fd.determined.clone()))
                .collect();
            let _ = var_names;
            out.insert(intern(class_name), fds);
        }
    }
    out
}

/// Imported class name → arity (number of class type-vars). Used by
/// the `ClassInstanceArityMismatch` detector. Mirrors
/// [`build_imported_alias_arity`] for type aliases — same scoping
/// rule (only unqualified imports). Also covers Prim sub-modules,
/// which import_all auto-binds for the `Prim` namespace.
fn build_imported_class_arity(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> std::collections::HashMap<crate::interner::Symbol, usize> {
    use crate::interner::intern;
    let mut out: std::collections::HashMap<crate::interner::Symbol, usize> =
        std::collections::HashMap::new();
    let prims = crate::typecheck_db::prim::prim_exports();
    // Auto-imported Prim module classes (those bare `Prim.X` names
    // become available unqualified in every user module).
    if let Some(prim) = prims.get("Prim") {
        for (class_name, class_info) in &prim.classes {
            out.insert(intern(class_name), class_info.type_vars.len());
        }
    }
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target = join_module_name(&imp.module);
        let exports: Option<&ModuleExports> = registry
            .get(&target)
            .or_else(|| prims.get(&target));
        let Some(exports) = exports else { continue };
        match &imp.imports {
            Some(crate::cst::ImportList::Explicit(items)) => {
                // Only insert classes that are explicitly named.
                for item in items {
                    if let crate::cst::Import::Class(cn) = item {
                        let name = crate::typecheck_db::util::resolve_symbol(cn.value.symbol());
                        if let Some(ci) = exports.classes.get(&name) {
                            out.insert(intern(&name), ci.type_vars.len());
                        }
                    }
                }
            }
            Some(crate::cst::ImportList::Hiding(hidden)) => {
                let hidden_set: std::collections::HashSet<String> = hidden
                    .iter()
                    .filter_map(|item| {
                        if let crate::cst::Import::Class(cn) = item {
                            Some(crate::typecheck_db::util::resolve_symbol(cn.value.symbol()))
                        } else {
                            None
                        }
                    })
                    .collect();
                for (class_name, class_info) in &exports.classes {
                    if !hidden_set.contains(class_name) {
                        out.insert(intern(class_name), class_info.type_vars.len());
                    }
                }
            }
            None => {
                for (class_name, class_info) in &exports.classes {
                    out.insert(intern(class_name), class_info.type_vars.len());
                }
            }
        }
    }
    out
}

/// Pre-computed import view for one module. Built once per
/// `check_one_module` call and passed through `resolve_*_dep`
/// helpers so per-reference lookups don't re-resolve every
/// import's `Symbol` parts on every call. The original walk
/// allocated a fresh `Vec<String>` and `String::join(".")` per
/// import per reference, which on a 90-module bench was visibly
/// hot.
struct ImportLookup {
    /// Target module names of every unqualified `import M`. Order
    /// preserved so first-match-wins semantics match the prior
    /// behaviour.
    unqualified_targets: Vec<String>,
    /// Target module names of every import (qualified or not), in
    /// source order. Used by edges that need to enumerate every
    /// in-scope import (e.g. instance dispatch).
    all_targets: Vec<String>,
    /// `import M as Q` → `Q` → `M`. First-import-wins on
    /// duplicate aliases (matching prior fold-then-find loop).
    alias_to_target: std::collections::HashMap<String, String>,
}

impl ImportLookup {
    fn build(module: &cst::Module) -> Self {
        let mut unqualified_targets: Vec<String> = Vec::with_capacity(module.imports.len());
        let mut all_targets: Vec<String> = Vec::with_capacity(module.imports.len());
        let mut alias_to_target: std::collections::HashMap<String, String> =
            std::collections::HashMap::with_capacity(module.imports.len());
        for imp in &module.imports {
            let target = join_module_name(&imp.module);
            all_targets.push(target.clone());
            match &imp.qualified {
                None => unqualified_targets.push(target),
                Some(q) => {
                    let alias = join_module_name(q);
                    alias_to_target.entry(alias).or_insert(target);
                }
            }
        }
        Self { unqualified_targets, all_targets, alias_to_target }
    }
}

fn lookup_unqualified_import(
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    name: &str,
) -> Option<(String, OutputHash)> {
    for target in &imports.unqualified_targets {
        if let Some(oh) = registry.scheme_hash(target, name) {
            return Some((target.clone(), oh));
        }
    }
    None
}

/// Map a qualified-import alias (`Q` from `import M as Q`) to its
/// canonical module name. Also accepts canonical module names that
/// match an import target or that the resolver attributed via
/// re-exports (e.g. `Some("Control.Apply")` reached through an
/// `import Prelude`). Downstream lookups consult the registry and
/// fail naturally for non-existent modules.
fn canonical_module_for_alias(imports: &ImportLookup, alias: &str) -> Option<String> {
    if let Some(m) = imports.alias_to_target.get(alias) {
        return Some(m.clone());
    }
    Some(alias.to_string())
}

// ---------------------------------------------------------------------------
// Per-ref dep resolution for value SCCs
// ---------------------------------------------------------------------------
//
// Each helper below takes one reference from a value SCC's free_names
// and, if it matches a known decl (local or cross-module), pushes the
// decl's output hash into the SCC's dep list. A reference that can't
// be resolved (e.g. Prim types, wildcards) is silently skipped —
// inference either handles it on its own or surfaces an unbound error.

#[allow(clippy::too_many_arguments)]
fn resolve_value_dep(
    r: &crate::typecheck_db::passes::names::Reference,
    self_module: &str,
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    name_to_idx: &HashMap<String, usize>,
    scc_member_set: &HashSet<usize>,
    local_scheme_hashes: &HashMap<String, OutputHash>,
    local_foreign_value_hashes: &HashMap<String, OutputHash>,
    out: &mut Vec<(String, String, OutputHash)>,
    seen: &mut HashSet<(String, String)>,
) {
    match (&r.module, &r.name) {
        (None, nm) => {
            if let Some(&dep_idx) = name_to_idx.get(nm) {
                if scc_member_set.contains(&dep_idx) {
                    return;
                }
                if let Some(oh) = local_scheme_hashes.get(nm) {
                    push_dep(out, seen, self_module, nm, *oh);
                }
                return;
            }
            if let Some(oh) = local_foreign_value_hashes.get(nm) {
                push_dep(out, seen, self_module, nm, *oh);
                return;
            }
            if let Some((dep_mod, oh)) =
                lookup_unqualified_import(imports, registry, nm)
            {
                push_dep(out, seen, &dep_mod, nm, oh);
            }
        }
        (Some(alias), nm) if alias == self_module => {
            // Self-module qualified ref (post-resolve_pass). Same
            // dep-edge semantics as the unqualified local-name path.
            if let Some(&dep_idx) = name_to_idx.get(nm) {
                if scc_member_set.contains(&dep_idx) {
                    return;
                }
                if let Some(oh) = local_scheme_hashes.get(nm) {
                    push_dep(out, seen, self_module, nm, *oh);
                }
                return;
            }
            if let Some(oh) = local_foreign_value_hashes.get(nm) {
                push_dep(out, seen, self_module, nm, *oh);
            }
        }
        (Some(alias), nm) => {
            if let Some(dep_mod) = canonical_module_for_alias(imports, alias) {
                if let Some(oh) = registry.scheme_hash(&dep_mod, nm) {
                    push_dep(out, seen, &dep_mod, nm, oh);
                }
            }
        }
    }
}

/// Invoked when a Value-kind reference matches a known class
/// method. Adds the defining class's shape hash plus every in-scope
/// instance of that class to the dep set.
#[allow(clippy::too_many_arguments)]
fn add_class_method_deps(
    class_mod: &str,
    class_name: &str,
    self_module: &str,
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    local_class_hashes: &HashMap<String, OutputHash>,
    local_instance_hashes_by_class: &HashMap<String, Vec<(String, OutputHash)>>,
    out: &mut Vec<(String, String, OutputHash)>,
    seen: &mut HashSet<(String, String)>,
) {
    // Class shape hash.
    let class_hash = if class_mod == self_module {
        local_class_hashes.get(class_name).copied()
    } else {
        registry.nonvalue_hash(class_mod, "c", class_name)
    };
    if let Some(oh) = class_hash {
        push_dep(out, seen, class_mod, &format!("class:{class_name}"), oh);
    }

    // Every in-scope instance: local + every imported module.
    if let Some(list) = local_instance_hashes_by_class.get(class_name) {
        for (decl_key, oh) in list {
            push_dep(out, seen, self_module, decl_key, *oh);
        }
    }
    for dep_mod in &imports.all_targets {
        for inst_key in registry.instances_of_class(dep_mod, class_name) {
            if let Some(oh) = registry.nonvalue_hash(dep_mod, "i", inst_key) {
                push_dep(out, seen, dep_mod, inst_key, oh);
            }
        }
    }
}

/// Gather dep hashes for one non-value decl by walking its
/// `free_names` references. Any ref that resolves to a known local
/// or imported hash is folded in; unresolvable refs (e.g. Prim
/// types) are skipped silently. Deduplication is done by the caller
/// treating the returned slice as unordered.
#[allow(clippy::too_many_arguments)]
fn collect_nonvalue_dep_hashes(
    decl: &crate::typecheck_db::ir::Decl,
    self_module: &str,
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    local_type_hashes: &HashMap<String, OutputHash>,
    local_class_hashes: &HashMap<String, OutputHash>,
    local_ctor_parent_hash: &HashMap<String, OutputHash>,
    local_fixity_hashes: &HashMap<String, OutputHash>,
    local_foreign_value_hashes: &HashMap<String, OutputHash>,
) -> Vec<OutputHash> {
    let free = free_names::compute(decl);
    let mut out: Vec<(String, String, OutputHash)> = Vec::new();
    let mut seen: HashSet<(String, String)> = HashSet::new();
    let empty_name_to_idx: HashMap<String, usize> = HashMap::new();
    let empty_scc: HashSet<usize> = HashSet::new();
    let empty_scheme_hashes: HashMap<String, OutputHash> = HashMap::new();
    let empty_instance_by_class: HashMap<String, Vec<(String, OutputHash)>> = HashMap::new();
    for r in &free.refs {
        match r.kind {
            NameKind::Value => resolve_value_dep(
                r,
                self_module,
                imports,
                registry,
                &empty_name_to_idx,
                &empty_scc,
                &empty_scheme_hashes,
                local_foreign_value_hashes,
                &mut out,
                &mut seen,
            ),
            NameKind::Type => resolve_type_dep(
                r,
                self_module,
                imports,
                registry,
                local_type_hashes,
                &mut out,
                &mut seen,
            ),
            NameKind::Constructor => resolve_ctor_dep(
                r,
                self_module,
                imports,
                registry,
                local_ctor_parent_hash,
                &mut out,
                &mut seen,
            ),
            NameKind::Class => resolve_class_dep(
                r,
                self_module,
                imports,
                registry,
                local_class_hashes,
                &empty_instance_by_class,
                &mut out,
                &mut seen,
            ),
            NameKind::Op | NameKind::TypeOp => resolve_fixity_dep(
                r,
                self_module,
                imports,
                registry,
                local_fixity_hashes,
                &mut out,
                &mut seen,
            ),
        }
    }
    out.into_iter().map(|(_, _, h)| h).collect()
}

fn resolve_type_dep(
    r: &crate::typecheck_db::passes::names::Reference,
    self_module: &str,
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    local_type_hashes: &HashMap<String, OutputHash>,
    out: &mut Vec<(String, String, OutputHash)>,
    seen: &mut HashSet<(String, String)>,
) {
    // A type reference may land in any of four kinds: Data (d),
    // Newtype (n), TypeAlias (ta), ForeignData (ft). We probe all
    // four prefixes on both local and imported sides.
    let type_prefixes = ["d", "n", "ta", "ft"];
    match (&r.module, &r.name) {
        (None, nm) => {
            if let Some(oh) = local_type_hashes.get(nm) {
                push_dep(out, seen, self_module, &format!("type:{nm}"), *oh);
                return;
            }
            for dep_mod in &imports.unqualified_targets {
                for kp in &type_prefixes {
                    if let Some(oh) = registry.nonvalue_hash(dep_mod, kp, nm) {
                        push_dep(
                            out,
                            seen,
                            dep_mod,
                            &format!("type:{nm}"),
                            oh,
                        );
                        return;
                    }
                }
            }
        }
        (Some(alias), nm) if alias == self_module => {
            // Self-module qualified type ref (post-resolve_pass).
            if let Some(oh) = local_type_hashes.get(nm) {
                push_dep(out, seen, self_module, &format!("type:{nm}"), *oh);
            }
        }
        (Some(alias), nm) => {
            if let Some(dep_mod) = canonical_module_for_alias(imports, alias) {
                for kp in &type_prefixes {
                    if let Some(oh) = registry.nonvalue_hash(&dep_mod, kp, nm) {
                        push_dep(
                            out,
                            seen,
                            &dep_mod,
                            &format!("type:{nm}"),
                            oh,
                        );
                        return;
                    }
                }
            }
        }
    }
}

fn resolve_ctor_dep(
    r: &crate::typecheck_db::passes::names::Reference,
    self_module: &str,
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    local_ctor_parent_hash: &HashMap<String, OutputHash>,
    out: &mut Vec<(String, String, OutputHash)>,
    seen: &mut HashSet<(String, String)>,
) {
    // Constructor refs depend on their parent data/newtype's shape.
    // Locally we already have that map; cross-module, we have to
    // walk the imported module's `data_constructors` to find which
    // type owns this ctor, then look up that type's nonvalue_hash.
    match (&r.module, &r.name) {
        (None, nm) => {
            if let Some(oh) = local_ctor_parent_hash.get(nm) {
                push_dep(out, seen, self_module, &format!("ctor:{nm}"), *oh);
                return;
            }
            for dep_mod in &imports.unqualified_targets {
                if let Some(oh) = cross_module_ctor_hash(dep_mod, nm, registry) {
                    push_dep(out, seen, dep_mod, &format!("ctor:{nm}"), oh);
                    return;
                }
            }
        }
        (Some(alias), nm) if alias == self_module => {
            // Self-module qualified ctor ref (post-resolve_pass).
            if let Some(oh) = local_ctor_parent_hash.get(nm) {
                push_dep(out, seen, self_module, &format!("ctor:{nm}"), *oh);
            }
        }
        (Some(alias), nm) => {
            if let Some(dep_mod) = canonical_module_for_alias(imports, alias) {
                if let Some(oh) = cross_module_ctor_hash(&dep_mod, nm, registry) {
                    push_dep(out, seen, &dep_mod, &format!("ctor:{nm}"), oh);
                }
            }
        }
    }
}

/// Look up a ctor in an imported module: walk its `ModuleExports.ctors`
/// to find the parent type, then the parent's `nonvalue_hash`.
fn cross_module_ctor_hash(
    dep_mod: &str,
    ctor_name: &str,
    registry: &ModuleRegistry,
) -> Option<OutputHash> {
    let exports = registry.get(dep_mod)?;
    let parent = &exports.ctors.get(ctor_name)?.parent_type;
    for kp in &["d", "n"] {
        if let Some(oh) = registry.nonvalue_hash(dep_mod, kp, parent) {
            return Some(oh);
        }
    }
    None
}

fn resolve_class_dep(
    r: &crate::typecheck_db::passes::names::Reference,
    self_module: &str,
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    local_class_hashes: &HashMap<String, OutputHash>,
    local_instance_hashes_by_class: &HashMap<String, Vec<(String, OutputHash)>>,
    out: &mut Vec<(String, String, OutputHash)>,
    seen: &mut HashSet<(String, String)>,
) {
    let (class_mod, class_name) = match (&r.module, &r.name) {
        (None, nm) => {
            if local_class_hashes.contains_key(nm) {
                (self_module.to_string(), nm.clone())
            } else {
                // Walk imports to find which module exports this class.
                let mut found: Option<String> = None;
                for dep_mod in &imports.unqualified_targets {
                    if registry.nonvalue_hash(dep_mod, "c", nm).is_some() {
                        found = Some(dep_mod.clone());
                        break;
                    }
                }
                match found {
                    Some(m) => (m, nm.clone()),
                    None => return,
                }
            }
        }
        (Some(alias), nm) => match canonical_module_for_alias(imports, alias) {
            Some(dep_mod) => (dep_mod, nm.clone()),
            None => return,
        },
    };

    // Edge 1: the Class node's shape hash.
    let class_hash = if class_mod == self_module {
        local_class_hashes.get(&class_name).copied()
    } else {
        registry.nonvalue_hash(&class_mod, "c", &class_name)
    };
    if let Some(oh) = class_hash {
        push_dep(out, seen, &class_mod, &format!("class:{class_name}"), oh);
    }

    // Edge 2: every in-scope Instance of this class. Collect from
    // local + every imported module, narrowed by class via
    // `instances_of_class`.
    if let Some(list) = local_instance_hashes_by_class.get(&class_name) {
        for (decl_key, oh) in list {
            push_dep(out, seen, self_module, decl_key, *oh);
        }
    }
    for dep_mod in &imports.all_targets {
        for inst_key in registry.instances_of_class(dep_mod, &class_name) {
            if let Some(oh) = registry.nonvalue_hash(dep_mod, "i", inst_key) {
                push_dep(out, seen, dep_mod, inst_key, oh);
            }
        }
    }
}

fn resolve_fixity_dep(
    r: &crate::typecheck_db::passes::names::Reference,
    self_module: &str,
    imports: &ImportLookup,
    registry: &ModuleRegistry,
    local_fixity_hashes: &HashMap<String, OutputHash>,
    out: &mut Vec<(String, String, OutputHash)>,
    seen: &mut HashSet<(String, String)>,
) {
    match (&r.module, &r.name) {
        (None, op) => {
            if let Some(oh) = local_fixity_hashes.get(op) {
                push_dep(out, seen, self_module, &format!("fixity:{op}"), *oh);
                return;
            }
            for dep_mod in &imports.unqualified_targets {
                if let Some(oh) = registry.nonvalue_hash(dep_mod, "f", op) {
                    push_dep(
                        out,
                        seen,
                        dep_mod,
                        &format!("fixity:{op}"),
                        oh,
                    );
                    return;
                }
            }
        }
        (Some(alias), op) if alias == self_module => {
            if let Some(oh) = local_fixity_hashes.get(op) {
                push_dep(out, seen, self_module, &format!("fixity:{op}"), *oh);
            }
        }
        (Some(alias), op) => {
            if let Some(dep_mod) = canonical_module_for_alias(imports, alias) {
                if let Some(oh) = registry.nonvalue_hash(&dep_mod, "f", op) {
                    push_dep(
                        out,
                        seen,
                        &dep_mod,
                        &format!("fixity:{op}"),
                        oh,
                    );
                }
            }
        }
    }
}

fn push_dep(
    out: &mut Vec<(String, String, OutputHash)>,
    seen: &mut HashSet<(String, String)>,
    dep_mod: &str,
    dep_decl: &str,
    oh: OutputHash,
) {
    let pair = (dep_mod.to_string(), dep_decl.to_string());
    if seen.insert(pair.clone()) {
        out.push((pair.0, pair.1, oh));
    }
}

fn join_module_name(mn: &cst::ModuleName) -> String {
    mn.parts
        .iter()
        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
        .collect::<Vec<_>>()
        .join(".")
}

/// Walk a `Type` and collect every defining module mentioned in
/// `Type::Con(Some(module), _)`. Used by the alias_map builder to
/// pull in transitive alias dependencies (e.g.
/// `type SimulationNode r = Record (Type.Row.RowApply ...)` —
/// importing SimulationNode should also pull `Type.Row`'s aliases
/// so `RowApply` expands at use-sites).
fn collect_referenced_modules(ty: &crate::typecheck_db::types::Type) -> Vec<String> {
    use crate::typecheck_db::types::Type;
    let mut out: Vec<String> = Vec::new();
    fn walk(t: &Type, out: &mut Vec<String>) {
        match t {
            Type::Con(qn) => {
                if let Some(m) = &qn.module {
                    if !out.contains(m) {
                        out.push(m.clone());
                    }
                }
            }
            Type::App(f, a) | Type::Fun(f, a) => {
                walk(f, out);
                walk(a, out);
            }
            Type::Forall(_, b) => walk(b, out),
            Type::Constrained(cs, b) => {
                for c in cs {
                    if let Some(m) = &c.class.module {
                        if !out.contains(m) {
                            out.push(m.clone());
                        }
                    }
                    for arg in &c.args {
                        walk(arg, out);
                    }
                }
                walk(b, out);
            }
            Type::Record(fs, tail) | Type::Row(fs, tail) => {
                for (_, v) in fs {
                    walk(v, out);
                }
                if let Some(t) = tail {
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
    walk(ty, &mut out);
    out
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Collect local data / newtype / class / instance info from a
/// module's decls. Returns the exhaustiveness-shaped maps plus
/// local class + instance records.
fn collect_decl_scope(
    decls: &[crate::typecheck_db::ir::Decl],
) -> (
    DataConstructors,
    CtorRegistry,
    HashMap<String, ClassInfo>,
    Vec<Instance>,
) {
    let mut data_constructors: DataConstructors = HashMap::new();
    let mut ctor_details: CtorRegistry = HashMap::new();

    let type_ops = TypeOpMap::default();
    for d in decls {
        match d {
            crate::typecheck_db::ir::Decl::Data { name, type_vars, constructors, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let ctor_names: Vec<String> = constructors
                    .iter()
                    .map(|c| {
                        crate::typecheck_db::util::resolve_symbol(c.name.value.symbol())
                    })
                    .collect();
                data_constructors.insert(type_name.clone(), ctor_names.clone());
                for c in constructors {
                    let ctor_name =
                        crate::typecheck_db::util::resolve_symbol(c.name.value.symbol());
                    let fields: Vec<_> = c
                        .fields
                        .iter()
                        .map(|f| {
                            crate::typecheck_db::types::convert_type_expr(f, &type_ops)
                        })
                        .collect();
                    ctor_details.insert(
                        ctor_name,
                        CtorInfo {
                            parent_type: type_name.clone(),
                            parent_module: None,
                            type_vars: tvars.clone(),
                            fields,
                        },
                    );
                }
            }
            crate::typecheck_db::ir::Decl::Newtype { name, type_vars, constructor, ty, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let ctor_name =
                    crate::typecheck_db::util::resolve_symbol(constructor.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                data_constructors.insert(type_name.clone(), vec![ctor_name.clone()]);
                ctor_details.insert(
                    ctor_name,
                    CtorInfo {
                        parent_type: type_name,
                        parent_module: None,
                        type_vars: tvars,
                        fields: vec![crate::typecheck_db::types::convert_type_expr(
                            ty, &type_ops,
                        )],
                    },
                );
            }
            _ => {}
        }
    }

    // Reuse the existing instance-index scanner for classes and
    // instances.
    let local_ix = crate::typecheck_db::passes::instance_index::from_decls(decls, &type_ops);
    let mut local_classes: HashMap<String, ClassInfo> = HashMap::new();
    for d in decls {
        if let crate::typecheck_db::ir::Decl::Class { name, .. } = d {
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            if let Some(info) = local_ix.class_info(&n) {
                local_classes.insert(n, info.clone());
            }
        }
    }
    let local_instances: Vec<Instance> = local_ix
        .all_instances()
        .map(|(_, i)| i.clone())
        .collect();

    (data_constructors, ctor_details, local_classes, local_instances)
}

/// For every local data / newtype constructor, synthesize its
/// value scheme (`forall a. f1 -> ... -> fn -> T a b ...`) and
/// bind it under its simple name in the env.
/// Assemble the desugar context for one module: merges fixity
/// entries from every import (and the module's own `Decl::Fixity`
/// decls) into a single `FixityTable` so MDe can rebracket
/// operator chains using real precedence info.
fn build_desugar_context(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> DesugarContext {
    use crate::typecheck_db::desugar::{fixity_table_from_decls, FixityInfo, FixityTable};

    // Start with a local fixity table built from the module's
    // own `Decl::Fixity`. `fixity_table_from_decls` already does
    // the work; it also stamps the module_fixity_hash for us via
    // `DesugarContext::module_fixity_hash` below.
    let (mut table, _local_hash) =
        fixity_table_from_decls(&module.decls);

    // Qualified-only operator fixities (`import M as Q` brings
    // `Q.(:)` into scope but not bare `(:)`). Keyed by
    // `(qualifier_symbol, op_symbol)`; consulted as a fallback
    // by the rebracketer when the bare-op lookup misses, so
    // `Q.(:)` picks up `infixr N` from M.
    let mut qualified_table: crate::typecheck_db::desugar::QualifiedFixityTable =
        std::collections::HashMap::new();

    // Merge every imported module's value_fixities. We look up
    // each import's target in the registry rather than walking
    // Prim submodules (Prim defines no operators).
    for imp in &module.imports {
        // Qualified-only imports (`import M as Q`) put operators
        // under `Q.(:)` only — they don't make the operator
        // available as bare `(:)`. Capture those into the
        // qualified_table so `Q.op` still gets its declared
        // fixity; skip them from the unqualified merge so an
        // open `import Data.Array as A` doesn't pre-empt a
        // later `import Data.List (List(..), (:))` from
        // claiming the unqualified slot.
        if let Some(qualifier) = &imp.qualified {
            let target_name = imp
                .module
                .parts
                .iter()
                .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                .collect::<Vec<_>>()
                .join(".");
            let target = match registry.get(&target_name) {
                Some(t) => t,
                None => continue,
            };
            let qualifier_str: String = qualifier
                .parts
                .iter()
                .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                .collect::<Vec<_>>()
                .join(".");
            let qualifier_sym = crate::interner::intern(&qualifier_str);
            for (op_name, fx) in &target.value_fixities {
                // Respect the import's explicit/hiding list,
                // same rules as the unqualified path below.
                let op_in_scope = match &imp.imports {
                    None => true,
                    Some(crate::cst::ImportList::Explicit(items)) => {
                        let op_sym_raw = crate::interner::intern(op_name.as_str());
                        items.iter().any(|item| {
                            matches!(item, crate::cst::Import::Value(_))
                                && item.name() == op_sym_raw
                        })
                    }
                    Some(crate::cst::ImportList::Hiding(items)) => {
                        let op_sym_raw = crate::interner::intern(op_name.as_str());
                        !items.iter().any(|item| {
                            matches!(item, crate::cst::Import::Value(_))
                                && item.name() == op_sym_raw
                        })
                    }
                };
                if !op_in_scope {
                    continue;
                }
                let op_sym = crate::interner::intern(op_name);
                let target_module_sym =
                    fx.target_module.as_deref().map(crate::interner::intern);
                let target_name_sym = crate::interner::intern(&fx.target_name);
                qualified_table.insert(
                    (qualifier_sym, op_sym),
                    FixityInfo {
                        associativity: fx.associativity,
                        precedence: fx.precedence,
                        target_module: target_module_sym,
                        target_name: target_name_sym,
                    },
                );
            }
            continue;
        }
        let target_name = imp
            .module
            .parts
            .iter()
            .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
            .collect::<Vec<_>>()
            .join(".");
        let target = match registry.get(&target_name) {
            Some(t) => t,
            None => continue,
        };
        for (op_name, fx) in &target.value_fixities {
            // Respect the import's explicit/hiding list. An operator is
            // only in scope if:
            //   - open import (`import M`) → all fixities visible
            //   - explicit list containing the operator name (`import M ((:))`) → visible
            //   - hiding list NOT containing the operator name → visible
            // `import M (valueTarget)` does NOT implicitly bring the
            // operator into scope — the operator must be explicitly
            // listed. (PureScript's own compiler enforces the same rule.)
            let op_in_scope = match &imp.imports {
                None => true, // open import
                Some(crate::cst::ImportList::Explicit(items)) => {
                    let op_sym_raw = crate::interner::intern(op_name.as_str());
                    items.iter().any(|item| {
                        matches!(item, crate::cst::Import::Value(_))
                            && item.name() == op_sym_raw
                    })
                }
                Some(crate::cst::ImportList::Hiding(items)) => {
                    let op_sym_raw = crate::interner::intern(op_name.as_str());
                    !items.iter().any(|item| {
                        matches!(item, crate::cst::Import::Value(_))
                            && item.name() == op_sym_raw
                    })
                }
            };
            if !op_in_scope {
                continue;
            }
            let op_sym = crate::interner::intern(op_name);
            // Local fixities take precedence — don't let an
            // imported `infixl 6 sub as -` overwrite a module's
            // own `infixl 6 Tuple as -`. This matches PureScript's
            // ambiguity-free local-wins rule.
            if table.contains_key(&op_sym) {
                continue;
            }
            let target_module_sym =
                fx.target_module.as_deref().map(crate::interner::intern);
            let target_name_sym = crate::interner::intern(&fx.target_name);
            table.insert(
                op_sym,
                FixityInfo {
                    associativity: fx.associativity,
                    precedence: fx.precedence,
                    target_module: target_module_sym,
                    target_name: target_name_sym,
                },
            );
        }
    }

    // Re-hash after the imported fixities land so the module's
    // module_fixity_hash reflects the full visible set.
    let combined_hash = hash_fixity_table(&table);
    DesugarContext {
        module_fixity_hash: combined_hash,
        fixity_table: table,
        qualified_fixity_table: qualified_table,
    }
}

fn hash_fixity_table(
    table: &crate::typecheck_db::desugar::FixityTable,
) -> [u8; 32] {
    use string_interner::Symbol as _;
    let mut h = blake3::Hasher::new();
    h.update(b"driver_multi::fixity_hash_v1");
    let mut entries: Vec<_> = table.iter().collect();
    entries.sort_by_key(|(k, _)| k.to_usize() as u32);
    h.update(&(entries.len() as u32).to_le_bytes());
    for (k, v) in entries {
        h.update(&(k.to_usize() as u32).to_le_bytes());
        h.update(&[v.associativity as u8, v.precedence]);
        match v.target_module {
            None => {
                h.update(&[0u8]);
            }
            Some(m) => {
                h.update(&[1u8]);
                h.update(&(m.to_usize() as u32).to_le_bytes());
            }
        }
        h.update(&(v.target_name.to_usize() as u32).to_le_bytes());
    }
    *h.finalize().as_bytes()
}

fn bind_local_ctors(
    decls: &[crate::typecheck_db::ir::Decl],
    self_module: &str,
    env: &mut Env,
    aliases: &crate::typecheck_db::types::AliasMap,
    type_ops: &TypeOpMap,
) {
    use crate::typecheck_db::types::{expand_aliases, QName, Scheme, Type};
    let conv = |ty: &crate::cst::TypeExpr| -> Type {
        expand_aliases(crate::typecheck_db::types::convert_type_expr(ty, type_ops), aliases)
    };
    for d in decls {
        match d {
            crate::typecheck_db::ir::Decl::Foreign { name, ty, .. } => {
                // `foreign import foo :: Type` — FFI value binding.
                // Put its declared type into the env so downstream
                // references resolve.
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let declared = conv(ty);
                // Strip a leading Forall into the scheme's vars
                // field so generalization / instantiation treats
                // quantifiers the standard way.
                let (vars, vars_kinds, body) = match declared {
                    Type::Forall(qs, body) => {
                        let (names, kinds): (Vec<String>, Vec<Option<Type>>) = qs
                            .into_iter()
                            .map(|(n, _, k)| (n, k.map(|arc| (*arc).clone())))
                            .unzip();
                        (names, kinds, std::sync::Arc::unwrap_or_clone(body))
                    }
                    other => (Vec::new(), Vec::new(), other),
                };
                let scheme = Scheme::with_kinds(vars, vars_kinds, body);
                // Dual-bind during transition: legacy consumers look up under
                // `QName::unqualified(name)`, post-resolve consumers under
                // `QName::qualified(self_module, name)`. Once every consumer
                // is migrated to the qualified form, drop the unqualified
                // binding here.
                env.bind_scheme(QName::unqualified(&n), scheme.clone());
                env.bind_scheme(QName::qualified(self_module, &n), scheme);
            }
            crate::typecheck_db::ir::Decl::TypeSignature { name, ty, .. } => {
                // A top-level `foo :: T` before `foo = …` — bind
                // the declared scheme so mutual references pick
                // up the annotated shape.
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                // Mark the decl as user-signed so the SCC can opt
                // into bidirectional check-mode for it.
                env.local_signed.insert(n.clone());
                // Capture type-level holes (`?h`) in the sig: spans
                // are needed for `HoleDiagnostic` emission, but
                // `convert_type_expr` lowers `TE::Hole` to a
                // span-less `Type::Hole(name)`. Stash the per-decl
                // (span, name) list now so the SCC inference can
                // reattach spans when it allocates unifs for the
                // holes.
                let mut hole_sites: Vec<(crate::span::Span, String)> = Vec::new();
                crate::typecheck_db::types::collect_type_holes(ty, &mut hole_sites);
                let has_holes = !hole_sites.is_empty();
                if has_holes {
                    env.local_signed_hole_sites.insert(n.clone(), hole_sites);
                }
                let declared = conv(ty);
                let (vars, vars_kinds, body) = match declared {
                    Type::Forall(qs, body) => {
                        let (names, kinds): (Vec<String>, Vec<Option<Type>>) = qs
                            .into_iter()
                            .map(|(n, _, k)| (n, k.map(|arc| (*arc).clone())))
                            .unzip();
                        (names, kinds, std::sync::Arc::unwrap_or_clone(body))
                    }
                    other => (Vec::new(), Vec::new(), other),
                };
                let scheme = Scheme::with_kinds(vars, vars_kinds, body);
                env.bind_scheme(QName::unqualified(&n), scheme.clone());
                // Sigs with `?h` (type-level holes) MUST NOT be bound
                // under the qualified key. `infer_var`'s qualified-first
                // lookup would otherwise route recursive references
                // (`loop x = loop (x + 1.0)` with `loop :: ?h -> a`)
                // through this Hole-bearing scheme. Leaving the
                // qualified slot empty makes the qualified lookup
                // miss, and the unqualified fallback finds the SCC
                // pre-insert's fresh unif slot in `env.locals` — the
                // right behavior for hole rewrite + body inference.
                if !has_holes {
                    env.bind_scheme(QName::qualified(self_module, &n), scheme);
                }
            }
            crate::typecheck_db::ir::Decl::Data { name, type_vars, constructors, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let result_ty =
                    apply_type_vars(&Type::Con(QName::unqualified(&type_name)), &tvars);
                for c in constructors {
                    let ctor_name =
                        crate::typecheck_db::util::resolve_symbol(c.name.value.symbol());
                    let fields: Vec<Type> = c.fields.iter().map(|f| conv(f)).collect();
                    let scheme_ty = build_fn_chain(&fields, &result_ty);
                    let scheme = Scheme::new(tvars.clone(), scheme_ty);
                    env.bind_scheme(QName::unqualified(&ctor_name), scheme.clone());
                    env.bind_scheme(QName::qualified(self_module, &ctor_name), scheme);
                }
            }
            crate::typecheck_db::ir::Decl::Newtype { name, type_vars, constructor, ty, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let result_ty =
                    apply_type_vars(&Type::Con(QName::unqualified(&type_name)), &tvars);
                let field_ty = conv(ty);
                let ctor_name =
                    crate::typecheck_db::util::resolve_symbol(constructor.value.symbol());
                let scheme_ty = Type::fun(field_ty, result_ty);
                let scheme = Scheme::new(tvars.clone(), scheme_ty);
                env.bind_scheme(QName::unqualified(&ctor_name), scheme.clone());
                env.bind_scheme(QName::qualified(self_module, &ctor_name), scheme);
            }
            crate::typecheck_db::ir::Decl::Class {
                name,
                type_vars,
                type_var_kind_anns,
                members,
                ..
            } => {
                // Expose each class method as a constrained scheme:
                // `forall (class vars + method vars). C <class vars>
                //  => <method type>`. The `Type::Constrained` layer
                // is what `infer_var`'s
                // `instantiate_and_record_constraints` peels at
                // each call site to register a pending
                // constraint.
                let class_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let class_vars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                // Per-class-var kinds propagate so `instantiate`
                // creates fresh unifs whose kind matches the class's
                // declared kind for that var. Without this, parallel's
                // `f :: Type -> Type` is unconstrained and can be
                // (incorrectly) bound to a Type-kind value at a use
                // site.
                // Compute class-var kinds:
                //  1. If the source has an explicit `(f :: K)` annotation, use that.
                //  2. Else, scan every method's body type for `App(Var(v), _)`
                //     patterns and infer kind `Type -> Type` (or higher arity)
                //     for each var seen as App head. This is what makes
                //     parallel's `f` / `g` get a `Type -> Type` kind even
                //     when the class declaration didn't annotate them.
                //  3. Else, None — kind unknown, bind_var skips its check.
                let mut class_var_kinds: Vec<Option<Type>> = type_vars
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        type_var_kind_anns
                            .get(i)
                            .and_then(|o| o.as_ref())
                            .map(|k| conv(k))
                    })
                    .collect();
                // Inference pass: for each unannotated class var, walk all
                // method bodies and count the maximum number of App args it
                // appears under as head. n args ↦ kind `Type -> ... -> Type`
                // (n arrows + final Type).
                for (i, var_name) in class_vars.iter().enumerate() {
                    if class_var_kinds[i].is_some() {
                        continue;
                    }
                    let mut max_args: usize = 0;
                    for m in members {
                        let mty = conv(&m.ty);
                        max_app_args_for_var(&mty, var_name, &mut max_args);
                    }
                    if max_args > 0 {
                        let mut k = crate::typecheck_db::types::prim_kind_type();
                        for _ in 0..max_args {
                            k = Type::Fun(
                                std::sync::Arc::new(
                                    crate::typecheck_db::types::prim_kind_type(),
                                ),
                                std::sync::Arc::new(k),
                            );
                        }
                        class_var_kinds[i] = Some(k);
                    }
                }
                for m in members {
                    let method_name =
                        crate::typecheck_db::util::resolve_symbol(m.name.value.symbol());
                    let method_ty = conv(&m.ty);
                    let (method_vars, method_var_kinds, method_body) = match method_ty {
                        Type::Forall(qs, body) => {
                            let (ns, ks): (Vec<String>, Vec<Option<Type>>) = qs
                                .into_iter()
                                .map(|(n, _, k)| (n, k.map(|arc| (*arc).clone())))
                                .unzip();
                            (ns, ks, std::sync::Arc::unwrap_or_clone(body))
                        }
                        other => (Vec::new(), Vec::new(), other),
                    };
                    let constraint = crate::typecheck_db::types::Constraint {
                        // Class methods carry a constraint whose class
                        // qualifier names the DEFINING module — same
                        // form the resolver emits for user references
                        // to the class. Without this the solver sees
                        // a Some(M).C constraint at the call site
                        // and a None.C in the method's scheme and
                        // can't discharge.
                        class: QName::qualified(self_module, &class_name),
                        args: class_vars
                            .iter()
                            .map(|v| Type::Var(v.clone()))
                            .collect(),
                    };
                    let constrained_body =
                        Type::Constrained(vec![constraint], std::sync::Arc::new(method_body));
                    let mut all_vars = class_vars.clone();
                    all_vars.extend(method_vars);
                    let mut all_kinds = class_var_kinds.clone();
                    all_kinds.extend(method_var_kinds);
                    let scheme = Scheme::with_kinds(all_vars, all_kinds, constrained_body);
                    env.bind_scheme(QName::unqualified(&method_name), scheme.clone());
                    env.bind_scheme(
                        QName::qualified(self_module, &method_name),
                        scheme,
                    );
                }
            }
            _ => {}
        }
    }
}

/// Walk `ty` looking for `App(...App(Var(var_name), _)..._)` chains
/// and update `max_args` with the longest App-spine count whose head
/// is `Var(var_name)`. Used by the class-method scheme builder to
/// infer a kind shape (`Type -> ... -> Type`) for class-quantified
/// vars that the source didn't annotate. e.g. for
/// `class Parallel f g where parallel :: g a -> f a`, walking the
/// method body finds `App(Var("f"), Var("a"))` and `App(Var("g"),
/// Var("a"))` — both vars come back with arity 1, hence kind
/// `Type -> Type`.
fn max_app_args_for_var(
    ty: &crate::typecheck_db::types::Type,
    var_name: &str,
    max_args: &mut usize,
) {
    use crate::typecheck_db::types::Type;
    // Local: detect a spine whose head is Var(var_name) and return
    // the spine arity. Returns None when the spine head isn't this
    // var (in which case we continue recursing into subterms).
    fn spine_args(t: &Type, var_name: &str, args_seen: usize) -> Option<usize> {
        match t {
            Type::App(f, _) => spine_args(f, var_name, args_seen + 1),
            Type::Var(n) if n == var_name => Some(args_seen),
            _ => None,
        }
    }
    if let Some(args) = spine_args(ty, var_name, 0) {
        if args > *max_args {
            *max_args = args;
        }
    }
    match ty {
        Type::App(f, a) => {
            max_app_args_for_var(f, var_name, max_args);
            max_app_args_for_var(a, var_name, max_args);
        }
        Type::Fun(a, b) => {
            max_app_args_for_var(a, var_name, max_args);
            max_app_args_for_var(b, var_name, max_args);
        }
        Type::Forall(_, body) => max_app_args_for_var(body, var_name, max_args),
        Type::Constrained(cs, body) => {
            for c in cs {
                for a in &c.args {
                    max_app_args_for_var(a, var_name, max_args);
                }
            }
            max_app_args_for_var(body, var_name, max_args);
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            for (_, t) in fs {
                max_app_args_for_var(t, var_name, max_args);
            }
            if let Some(t) = tail {
                max_app_args_for_var(t, var_name, max_args);
            }
        }
        Type::Kinded(t, k) => {
            max_app_args_for_var(t, var_name, max_args);
            max_app_args_for_var(k, var_name, max_args);
        }
        _ => {}
    }
}

/// Build `T a b c …` from a head type and the parent's type-var names.
fn apply_type_vars(
    head: &crate::typecheck_db::types::Type,
    tvars: &[String],
) -> crate::typecheck_db::types::Type {
    use crate::typecheck_db::types::Type;
    let mut ty = head.clone();
    for v in tvars {
        ty = Type::app(ty, Type::Var(v.clone()));
    }
    ty
}

/// `[f1, f2, …, fn] + result` → `f1 -> f2 -> … -> fn -> result`.
fn build_fn_chain(
    fields: &[crate::typecheck_db::types::Type],
    result: &crate::typecheck_db::types::Type,
) -> crate::typecheck_db::types::Type {
    use crate::typecheck_db::types::Type;
    let mut acc = result.clone();
    for f in fields.iter().rev() {
        acc = Type::fun(f.clone(), acc);
    }
    acc
}

fn topo_sort_modules(
    modules: &[ModuleInput],
    name_index: &HashMap<String, usize>,
) -> (Vec<usize>, Vec<Vec<String>>) {
    // Edges: for each module i, list of js it depends on
    // (i imports j). Kahn's algorithm.
    let n = modules.len();
    let mut deps: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    let mut rev_deps: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (i, input) in modules.iter().enumerate() {
        let m = &input.module;
        for imp in &m.imports {
            let imported = imp
                .module
                .parts
                .iter()
                .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                .collect::<Vec<_>>()
                .join(".");
            // Skip Prim imports and imports we don't have source
            // for; those are either built in or (legitimately)
            // missing — that's a build-level concern, not a
            // topo-sort concern.
            if crate::typecheck_db::prim::is_prim_module_name(&imported) {
                continue;
            }
            if let Some(&j) = name_index.get(&imported) {
                deps[i].insert(j);
                rev_deps[j].insert(i);
            }
        }
    }

    // Kahn: push all modules with no deps, pop one at a time.
    let mut in_degree: Vec<usize> = deps.iter().map(|s| s.len()).collect();
    let mut queue: VecDeque<usize> =
        (0..n).filter(|i| in_degree[*i] == 0).collect();
    let mut order: Vec<usize> = Vec::with_capacity(n);
    while let Some(i) = queue.pop_front() {
        order.push(i);
        for &j in &rev_deps[i] {
            in_degree[j] -= 1;
            if in_degree[j] == 0 {
                queue.push_back(j);
            }
        }
    }

    // Anything remaining is part of a cycle. Group by
    // connectedness and report as `CycleInModules`.
    let mut cycles: Vec<Vec<String>> = Vec::new();
    if order.len() < n {
        let remaining: Vec<usize> = (0..n).filter(|i| !order.contains(i)).collect();
        // Simple: one cycle per connected component among the
        // remaining set. Good enough for a first pass.
        let mut visited: HashSet<usize> = HashSet::new();
        for &start in &remaining {
            if visited.contains(&start) {
                continue;
            }
            let mut stack = vec![start];
            let mut component: Vec<usize> = Vec::new();
            while let Some(i) = stack.pop() {
                if !visited.insert(i) {
                    continue;
                }
                component.push(i);
                for &j in &deps[i] {
                    if remaining.contains(&j) {
                        stack.push(j);
                    }
                }
                for &j in &rev_deps[i] {
                    if remaining.contains(&j) {
                        stack.push(j);
                    }
                }
            }
            cycles.push(
                component
                    .iter()
                    .map(|i| modules[*i].name.clone())
                    .collect(),
            );
        }
    }

    (order, cycles)
}

// Silence unused-import complaints when ModuleExports isn't
// directly constructed in this file (it's only built via
// distill_exports).
#[allow(dead_code)]
fn _touch_exports(_: &ModuleExports) {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn input(name: &str, src: &str) -> ModuleInput {
        let m = parse(src).unwrap();
        ModuleInput::new(name, src, m)
    }

    // =================================================================
    // Topological ordering + cycle detection
    // =================================================================

    #[test]
    fn single_module_no_imports_processes_successfully() {
        let report = check_many_modules(vec![input("M", "module M where\nfoo = 1\n")]);
        assert!(report.errors.is_empty(), "got: {:?}", report.errors);
        assert_eq!(report.results.len(), 1);
        assert_eq!(report.results[0].name, "M");
    }

    #[test]
    fn importer_checked_after_importee() {
        let report = check_many_modules(vec![
            input("B", "module B where\nimport A\nbar = foo\n"),
            input("A", "module A where\nfoo = 1\n"),
        ]);
        assert!(report.errors.is_empty());
        let names: Vec<&str> = report.results.iter().map(|r| r.name.as_str()).collect();
        assert_eq!(names, vec!["A", "B"]);
    }

    #[test]
    fn cycle_between_two_modules_is_reported() {
        let report = check_many_modules(vec![
            input("A", "module A where\nimport B\nfoo = 1\n"),
            input("B", "module B where\nimport A\nbar = 2\n"),
        ]);
        let cycle_reported = report.errors.iter().any(|e| {
            matches!(e, MultiModuleError::CycleInModules(names)
                if names.iter().any(|n| n == "A")
                    && names.iter().any(|n| n == "B"))
        });
        assert!(cycle_reported, "got: {:?}", report.errors);
    }

    #[test]
    fn chain_a_then_b_then_c_all_process() {
        let report = check_many_modules(vec![
            input("C", "module C where\nimport B\ncx = bx\n"),
            input("A", "module A where\nax = 1\n"),
            input("B", "module B where\nimport A\nbx = ax\n"),
        ]);
        assert!(report.errors.is_empty());
        let names: Vec<&str> = report.results.iter().map(|r| r.name.as_str()).collect();
        assert_eq!(names, vec!["A", "B", "C"]);
    }

    // =================================================================
    // Cross-module lookup produces the right scheme
    // =================================================================

    #[test]
    fn import_brings_value_into_scope() {
        let report = check_many_modules(vec![
            input("A", "module A where\nfoo = 1\n"),
            input("B", "module B where\nimport A\nbar = foo\n"),
        ]);
        assert!(report.errors.is_empty());
        let b_result = report.results.iter().find(|r| r.name == "B").unwrap();
        assert!(b_result.inference_error.is_none(), "{:?}", b_result.inference_error);
        assert!(b_result.schemes.iter().any(|s| s.name == "bar"));
    }

    #[test]
    fn import_as_qualified_requires_prefix_to_lookup() {
        let report = check_many_modules(vec![
            input("A", "module A where\nfoo = 1\n"),
            input("B", "module B where\nimport A as Q\nbar = Q.foo\n"),
        ]);
        let b_result = report.results.iter().find(|r| r.name == "B").unwrap();
        assert!(
            b_result.inference_error.is_none(),
            "{:?}",
            b_result.inference_error,
        );
    }

    #[test]
    fn unqualified_ref_fails_under_import_as() {
        let report = check_many_modules(vec![
            input("A", "module A where\nfoo = 1\n"),
            input("B", "module B where\nimport A as Q\nbar = foo\n"),
        ]);
        let b_result = report.results.iter().find(|r| r.name == "B").unwrap();
        assert!(
            matches!(
                &b_result.inference_error,
                Some(InferError::UnboundVar(n)) if n == "foo"
            ),
            "expected UnboundVar(\"foo\"); got {:?}",
            b_result.inference_error,
        );
    }

    // =================================================================
    // Import errors surface per-module
    // =================================================================

    #[test]
    fn import_of_unknown_module_reports_import_error() {
        let report = check_many_modules(vec![input(
            "M",
            "module M where\nimport Data.DoesNotExist\n",
        )]);
        let r = &report.results[0];
        assert_eq!(r.import_errors.len(), 1);
    }

    // =================================================================
    // Diagnostics aggregate across decls
    // =================================================================

    #[test]
    fn exhaustiveness_errors_surface_on_result() {
        let src = "\
module M where
data X = A | B
f x = case x of A -> 0
";
        let report = check_many_modules(vec![input("M", src)]);
        let r = &report.results[0];
        assert!(!r.exhaustiveness_errors.is_empty(), "expected non-exhaustive error");
    }

    #[test]
    fn inference_error_is_reported_not_panic() {
        let report = check_many_modules(vec![input(
            "M",
            "module M where\nfoo = undefinedNameHere\n",
        )]);
        let r = &report.results[0];
        assert!(matches!(r.inference_error, Some(InferError::UnboundVar(_))));
    }
}
