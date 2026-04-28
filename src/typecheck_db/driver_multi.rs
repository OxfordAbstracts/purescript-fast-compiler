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
    let name_index: HashMap<String, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, m)| (m.name.clone(), i))
        .collect();

    let mut report = ModuleCheckReport {
        registry: ModuleRegistry::new(),
        results: Vec::new(),
        errors: Vec::new(),
    };

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
        report
            .errors
            .push(MultiModuleError::DuplicateModule(name.clone()));
    }

    // User modules may not declare a name in the `Prim` namespace —
    // `Prim` and its sub-modules are reserved for compiler-defined
    // terms. The reference compiler's `CannotDefinePrimModules`.
    for m in &modules {
        if m.name == "Prim" || m.name.starts_with("Prim.") {
            report
                .errors
                .push(MultiModuleError::CannotDefinePrimModules(m.name.clone()));
        }
    }

    let (order, cycles) = topo_sort_modules(&modules, &name_index);
    for cycle in cycles {
        report.errors.push(MultiModuleError::CycleInModules(cycle));
    }

    for idx in order {
        let input = &modules[idx];
        let result = check_one_module(db, input, &mut report.registry);
        report.results.push(result);
    }

    report
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

    // 1) Pull imports into an Env + InstanceIndex.
    let (mut env, mut instance_index, import_errors) =
        build_env_from_imports(module, registry);

    // 1b) Structural validation (duplicates, orphans, fixity conflicts,
    //     duplicate type arguments). Pure traversal over the CST plus
    //     a small map of imported alias arities so the
    //     PartiallyAppliedSynonym detector can recognise imported
    //     synonyms used via type-operator syntax (e.g. `(~>)` from a
    //     `infixr type NaturalTransformation as ~>` in Prelude).
    let imported_alias_arity =
        build_imported_alias_arity(module, registry);
    let imported_class_arity =
        build_imported_class_arity(module, registry);
    let imported_class_fundeps =
        build_imported_class_fundeps(module, registry);
    let mut validation_errors =
        crate::typecheck_db::passes::validate_decls::validate_module_with_class_fundeps(
            module,
            &imported_alias_arity,
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
    // top-level signatures. Restricted to kind-annotation positions
    // (`forall (a :: K).` and `data T :: K`) — bare type-position
    // refs are skipped because of `module M (module M, …)`
    // self-re-export interactions that aren't reflected in
    // `type_arities`. Kind-annotation positions are narrower and
    // safer.
    detect_unknown_kind_refs_registry(module, registry, &mut validation_errors);
    let _ = detect_unknown_type_refs_registry;

    // 1c) Kind-arity check. Catches over-application of type
    //     constructors and arity mismatches in class constraints.
    //     Reads the registry for imported types/classes.
    let kind_errors =
        crate::typecheck_db::passes::kind_check::check_module(module, registry);

    // 1d) Coercible-related checks: role validation + forbidden
    //     user-written Coercible instances. CST-only — doesn't need
    //     the registry.
    let coercible_errors =
        crate::typecheck_db::passes::coercible_check::check_module(module);

    // 2) Desugar the module as a whole, then lower cst → ir so
    //    every downstream pass consumes an `ir::Decl` that has no
    //    residual operator nodes (Op / OpParens / BacktickApp).
    let ctx = build_desugar_context(module, registry);
    let desugared_cst: Vec<cst::Decl> = desugar_module(module.decls.clone(), &ctx);
    let desugared: Vec<crate::typecheck_db::ir::Decl> = desugared_cst
        .into_iter()
        .map(crate::typecheck_db::ir::lower_decl)
        .collect::<Result<_, _>>()
        .unwrap_or_else(|e| {
            panic!("cst → ir lowering failed in {}: {e:?}", name)
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

    // Build a consolidated alias map: local `type Foo = …` decls
    // plus every imported module's exported aliases. Passed into
    // inference / class-method binding so aliases like
    // `type SynString = String` expand to `String` before we try
    // to unify — otherwise `newtype NT = NT SynString` fields
    // refuse to unify with `String`.
    let alias_map: crate::typecheck_db::types::AliasMap = {
        let mut m: crate::typecheck_db::types::AliasMap = HashMap::new();
        // Local aliases from the (raw) CST so forward references
        // don't need the registry.
        for d in &module.decls {
            if let cst::Decl::TypeAlias { name, type_vars, ty, .. } = d {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let vars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let body = crate::typecheck_db::types::convert_type_expr(ty, &type_ops);
                m.insert(n, (vars, body));
            }
        }
        // Every directly-imported module's aliases. Deeper
        // transitive aliases already land here because
        // `expand_module_reexports` merges them into each
        // module's exports, so `import Prelude` pulls in the
        // whole chain.
        for imp in &module.imports {
            let imp_name = join_module_name(&imp.module);
            if let Some(e) = registry.get(&imp_name) {
                for (k, a) in &e.type_aliases {
                    m.entry(k.clone())
                        .or_insert_with(|| (a.type_vars.clone(), a.body.clone()));
                }
            }
        }
        m
    };

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
            module,
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

    // Fold every imported module's class methods into method_index
    // too, so users of `show` / `map` / etc. from imports pick up
    // class + instance deps.
    for imp in &module.imports {
        let dep_mod = join_module_name(&imp.module);
        if let Some(exports) = registry.get(&dep_mod) {
            for (class_name, _) in exports.classes.iter() {
                // Every method sits under `exports.values` with its
                // class name; we find them by consulting the class
                // shape stored in the registry's nonvalue_hashes is
                // not enough, so we walk exports.classes via the
                // shape. A simpler path: we just iterate ALL
                // exports.values and check if each entry's scheme
                // is Constrained on this class. Cheaper: also store
                // method names on `ClassInfo`? For now, use the
                // shape available under `exports.classes`, which
                // doesn't carry method names. Fallback: inspect
                // exports.values bodies for leading Constrained
                // layers.
                for (val_name, scheme) in exports.values.iter() {
                    if let crate::typecheck_db::types::Type::Constrained(cs, _) =
                        &scheme.ty
                    {
                        if cs.iter().any(|c| &c.class.name == class_name) {
                            method_index.insert(
                                val_name.clone(),
                                (dep_mod.clone(), class_name.clone()),
                            );
                        }
                    }
                }
            }
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
    instance_index.expand_aliases_in_place(&alias_map);

    // Make the alias map available to every inference-side
    // `convert_type_expr` caller (type annotations, let-sigs,
    // `check_value` sigs) via the env.
    env.aliases = alias_map.clone();

    bind_local_ctors(&desugared, &mut env, &alias_map);

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
        let refs: Vec<String> = free
            .refs
            .iter()
            .filter(|r| r.kind == crate::typecheck_db::passes::names::NameKind::Value
                && r.module.is_none())
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

    for scc in &sccs {
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
                            module,
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
                        // of the class is in scope.
                        if r.module.is_none() {
                            if let Some((class_mod, class_name)) =
                                method_index.get(&r.name)
                            {
                                add_class_method_deps(
                                    class_mod,
                                    class_name,
                                    &name,
                                    module,
                                    registry,
                                    &local_class_hashes,
                                    &local_instance_hashes_by_class,
                                    &mut dep_output_hashes,
                                    &mut dep_seen,
                                );
                            }
                        }
                    }
                    NameKind::Type => resolve_type_dep(
                        r,
                        &name,
                        module,
                        registry,
                        &local_type_hashes,
                        &mut dep_output_hashes,
                        &mut dep_seen,
                    ),
                    NameKind::Constructor => resolve_ctor_dep(
                        r,
                        &name,
                        module,
                        registry,
                        &local_ctor_parent_hash,
                        &mut dep_output_hashes,
                        &mut dep_seen,
                    ),
                    NameKind::Class => {
                        resolve_class_dep(
                            r,
                            &name,
                            module,
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
                        module,
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

        let (schemes, outcome, scheme_oh) = match cached {
            Some((schemes, scheme_oh)) => (schemes, CacheOutcome::Hit, Some(scheme_oh)),
            None => {
                // Run fresh inference for this SCC.
                match infer_value_scc_with_all(
                    &type_ops,
                    &mut env,
                    &scc_decl_refs,
                    &data_constructors,
                    &ctor_details,
                    &instance_index,
                ) {
                    Ok(schemes) => {
                        let scheme_oh = put_cached(
                            db,
                            &name,
                            &scc_key,
                            scc_source_hash,
                            &dep_output_hashes,
                            module_context_hash,
                            &schemes,
                        )
                        .expect("typecheck_db put_cached");
                        (schemes, CacheOutcome::Miss, Some(scheme_oh))
                    }
                    Err(e) => {
                        inference_error.get_or_insert(e);
                        (Vec::new(), CacheOutcome::Miss, None)
                    }
                }
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
    for d in non_value_decls.iter() {
        if let crate::typecheck_db::ir::Decl::Instance {
            class_name,
            types,
            members,
            ..
        } = d
        {
            let class_qi = class_name.to_qi();
            let class_name_str =
                crate::typecheck_db::util::resolve_symbol(class_qi.name);
            // Class info: prefer the local declaration; otherwise
            // walk the importer's direct imports to find the class
            // in another module's exported `ClassInfo`. We only
            // need `type_vars` from it (to build the
            // class-var → instance-head subst).
            let class_info = local_classes
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
                    .cloned()
                    .or_else(|| {
                        for imp in &module.imports {
                            let imp_name = join_module_name(&imp.module);
                            if let Some(exports) = registry.get(&imp_name) {
                                if let Some(s) = exports.values.get(&method_name) {
                                    return Some(s.clone());
                                }
                            }
                        }
                        None
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
                    peeled = *body;
                }
                // Re-quantify any method-only vars from full_scheme.vars
                // that aren't class vars.
                let method_vars: Vec<String> = full_scheme
                    .vars
                    .iter()
                    .filter(|v| !subst.contains_key(*v))
                    .cloned()
                    .collect();
                let class_synthesized_sig = if method_vars.is_empty() {
                    crate::typecheck_db::types::Scheme {
                        vars: Vec::new(),
                        ty: peeled,
                    }
                } else {
                    crate::typecheck_db::types::Scheme {
                        vars: method_vars,
                        ty: peeled,
                    }
                };
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
                    let (vars, body) = match sig_ty {
                        crate::typecheck_db::types::Type::Forall(qs, body) => {
                            let names: Vec<String> =
                                qs.into_iter().map(|(n, _, _)| n).collect();
                            (names, *body)
                        }
                        other => (Vec::new(), other),
                    };
                    if !hs.is_empty() {
                        new_hole_sites = Some(hs);
                    }
                    crate::typecheck_db::types::Scheme { vars, ty: body }
                } else {
                    class_synthesized_sig
                };
                // Swap the class-method scheme for the synthesized
                // instance-specialised one for the duration of body
                // inference.
                let key = crate::typecheck_db::types::QName::unqualified(&method_name);
                let saved_scheme = env.top_level.insert(key.clone(), synthesized_sig);
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
                let inference = infer_value_scc_with_all(
                    &type_ops,
                    &mut env,
                    &[member],
                    &data_constructors,
                    &ctor_details,
                    &instance_index,
                );
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
    let mut exports = distill_exports(
        module,
        &all_schemes,
        &local_instances,
        &local_classes,
        &ctor_details,
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
                let matches_clause = imp_target == clause_name
                    || alias_str.as_deref() == Some(clause_name);
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
        let mut inserts: Vec<(String, String, FixityDecl)> = Vec::new();
        // Each entry: (op_alias, target_name, origin_module, scheme).
        let mut value_inserts: Vec<(
            String,
            String,
            String,
            crate::typecheck_db::types::Scheme,
        )> = Vec::new();
        for (op, fx) in &exports.value_fixities {
            if fx.target_module.is_some() {
                continue;
            }
            for imp_name in &import_targets {
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
                    let scheme = source
                        .values
                        .get(&fx.target_name)
                        .cloned()
                        .or_else(|| {
                            source
                                .ctors
                                .get(&fx.target_name)
                                .map(|info| crate::typecheck_db::passes::imports::synth_ctor_scheme(info))
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
            if !exports.instances.iter().any(|i| i == inst) {
                exports.instances.push(inst.clone());
            }
        }
    }
    registry.insert(name.clone(), exports);

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
    }
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
        for (alias_name, alias) in &exports.type_aliases {
            out.insert(intern(alias_name), alias.type_vars.len());
        }
        for (op_name, fix) in &exports.type_fixities {
            if let Some(alias) = exports.type_aliases.get(&fix.target_name) {
                out.insert(intern(op_name), alias.type_vars.len());
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
    if let Some(prim) = prims.get("Prim") {
        for k in prim.type_arities.keys() {
            known.insert(k.clone());
        }
    }
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
    if let Some(prim) = prims.get("Prim") {
        for k in prim.type_arities.keys() {
            known.insert(k.clone());
        }
    }
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
        for (class_name, class_info) in &exports.classes {
            out.insert(intern(class_name), class_info.type_vars.len());
        }
    }
    out
}

fn lookup_unqualified_import(
    module: &cst::Module,
    registry: &ModuleRegistry,
    name: &str,
) -> Option<(String, OutputHash)> {
    for imp in &module.imports {
        // Only unqualified imports (no `as Q`) contribute unqualified
        // names to the importer's env.
        if imp.qualified.is_some() {
            continue;
        }
        let target = imp
            .module
            .parts
            .iter()
            .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
            .collect::<Vec<_>>()
            .join(".");
        if let Some(oh) = registry.scheme_hash(&target, name) {
            return Some((target, oh));
        }
    }
    None
}

/// Map a qualified-import alias (`Q` from `import M as Q`) to its
/// canonical module name.
fn canonical_module_for_alias(module: &cst::Module, alias: &str) -> Option<String> {
    for imp in &module.imports {
        if let Some(q) = &imp.qualified {
            let alias_str = q
                .parts
                .iter()
                .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                .collect::<Vec<_>>()
                .join(".");
            if alias_str == alias {
                return Some(
                    imp.module
                        .parts
                        .iter()
                        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                        .collect::<Vec<_>>()
                        .join("."),
                );
            }
        }
    }
    None
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

fn resolve_value_dep(
    r: &crate::typecheck_db::passes::names::Reference,
    self_module: &str,
    module: &cst::Module,
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
                lookup_unqualified_import(module, registry, nm)
            {
                push_dep(out, seen, &dep_mod, nm, oh);
            }
        }
        (Some(alias), nm) => {
            if let Some(dep_mod) = canonical_module_for_alias(module, alias) {
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
    module: &cst::Module,
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
    for imp in &module.imports {
        let dep_mod = join_module_name(&imp.module);
        for inst_key in registry.instances_of_class(&dep_mod, class_name) {
            if let Some(oh) = registry.nonvalue_hash(&dep_mod, "i", inst_key) {
                push_dep(out, seen, &dep_mod, inst_key, oh);
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
    module: &cst::Module,
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
                module,
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
                module,
                registry,
                local_type_hashes,
                &mut out,
                &mut seen,
            ),
            NameKind::Constructor => resolve_ctor_dep(
                r,
                self_module,
                module,
                registry,
                local_ctor_parent_hash,
                &mut out,
                &mut seen,
            ),
            NameKind::Class => resolve_class_dep(
                r,
                self_module,
                module,
                registry,
                local_class_hashes,
                &empty_instance_by_class,
                &mut out,
                &mut seen,
            ),
            NameKind::Op | NameKind::TypeOp => resolve_fixity_dep(
                r,
                self_module,
                module,
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
    module: &cst::Module,
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
            for imp in &module.imports {
                if imp.qualified.is_some() {
                    continue;
                }
                let dep_mod = join_module_name(&imp.module);
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
        (Some(alias), nm) => {
            if let Some(dep_mod) = canonical_module_for_alias(module, alias) {
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
    module: &cst::Module,
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
            for imp in &module.imports {
                if imp.qualified.is_some() {
                    continue;
                }
                let dep_mod = join_module_name(&imp.module);
                if let Some(oh) = cross_module_ctor_hash(&dep_mod, nm, registry) {
                    push_dep(out, seen, &dep_mod, &format!("ctor:{nm}"), oh);
                    return;
                }
            }
        }
        (Some(alias), nm) => {
            if let Some(dep_mod) = canonical_module_for_alias(module, alias) {
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
    module: &cst::Module,
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
                for imp in &module.imports {
                    if imp.qualified.is_some() {
                        continue;
                    }
                    let dep_mod = join_module_name(&imp.module);
                    if registry.nonvalue_hash(&dep_mod, "c", nm).is_some() {
                        found = Some(dep_mod);
                        break;
                    }
                }
                match found {
                    Some(m) => (m, nm.clone()),
                    None => return,
                }
            }
        }
        (Some(alias), nm) => match canonical_module_for_alias(module, alias) {
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
    for imp in &module.imports {
        let dep_mod = join_module_name(&imp.module);
        for inst_key in registry.instances_of_class(&dep_mod, &class_name) {
            if let Some(oh) = registry.nonvalue_hash(&dep_mod, "i", inst_key) {
                push_dep(out, seen, &dep_mod, inst_key, oh);
            }
        }
    }
}

fn resolve_fixity_dep(
    r: &crate::typecheck_db::passes::names::Reference,
    self_module: &str,
    module: &cst::Module,
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
            for imp in &module.imports {
                if imp.qualified.is_some() {
                    continue;
                }
                let dep_mod = join_module_name(&imp.module);
                if let Some(oh) = registry.nonvalue_hash(&dep_mod, "f", op) {
                    push_dep(
                        out,
                        seen,
                        &dep_mod,
                        &format!("fixity:{op}"),
                        oh,
                    );
                    return;
                }
            }
        }
        (Some(alias), op) => {
            if let Some(dep_mod) = canonical_module_for_alias(module, alias) {
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

    // Merge every imported module's value_fixities. We look up
    // each import's target in the registry rather than walking
    // Prim submodules (Prim defines no operators).
    for imp in &module.imports {
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
    DesugarContext { module_fixity_hash: combined_hash, fixity_table: table }
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
    env: &mut Env,
    aliases: &crate::typecheck_db::types::AliasMap,
) {
    use crate::typecheck_db::types::{expand_aliases, QName, Scheme, Type};
    let type_ops = TypeOpMap::default();
    let conv = |ty: &crate::cst::TypeExpr| -> Type {
        expand_aliases(crate::typecheck_db::types::convert_type_expr(ty, &type_ops), aliases)
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
                let (vars, body) = match declared {
                    Type::Forall(qs, body) => {
                        let names: Vec<String> = qs.into_iter().map(|(n, _, _)| n).collect();
                        (names, *body)
                    }
                    other => (Vec::new(), other),
                };
                env.bind_scheme(QName::unqualified(&n), Scheme { vars, ty: body });
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
                if !hole_sites.is_empty() {
                    env.local_signed_hole_sites.insert(n.clone(), hole_sites);
                }
                let declared = conv(ty);
                let (vars, body) = match declared {
                    Type::Forall(qs, body) => {
                        let names: Vec<String> = qs.into_iter().map(|(n, _, _)| n).collect();
                        (names, *body)
                    }
                    other => (Vec::new(), other),
                };
                env.bind_scheme(QName::unqualified(&n), Scheme { vars, ty: body });
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
                    let scheme = Scheme { vars: tvars.clone(), ty: scheme_ty };
                    env.bind_scheme(QName::unqualified(&ctor_name), scheme);
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
                let scheme = Scheme { vars: tvars.clone(), ty: scheme_ty };
                env.bind_scheme(QName::unqualified(&ctor_name), scheme);
            }
            crate::typecheck_db::ir::Decl::Class { name, type_vars, members, .. } => {
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
                for m in members {
                    let method_name =
                        crate::typecheck_db::util::resolve_symbol(m.name.value.symbol());
                    let method_ty = conv(&m.ty);
                    let (method_vars, method_body) = match method_ty {
                        Type::Forall(qs, body) => {
                            let ns: Vec<String> =
                                qs.into_iter().map(|(n, _, _)| n).collect();
                            (ns, *body)
                        }
                        other => (Vec::new(), other),
                    };
                    let constraint = crate::typecheck_db::types::Constraint {
                        class: QName::unqualified(&class_name),
                        args: class_vars
                            .iter()
                            .map(|v| Type::Var(v.clone()))
                            .collect(),
                    };
                    let constrained_body =
                        Type::Constrained(vec![constraint], Box::new(method_body));
                    let mut all_vars = class_vars.clone();
                    all_vars.extend(method_vars);
                    env.bind_scheme(
                        QName::unqualified(&method_name),
                        Scheme { vars: all_vars, ty: constrained_body },
                    );
                }
            }
            _ => {}
        }
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
