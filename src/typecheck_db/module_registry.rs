//! Multi-module surface types.
//!
//! `ModuleExports` is the distilled, cross-module view of one compiled
//! module — what other modules see when they `import` from it.
//! `ModuleRegistry` is a simple in-process cache of those surfaces,
//! keyed by canonical module name (e.g. `"Data.Maybe"`).
//!
//! The goals here are:
//! * Store values, types, constructors, classes, instances, and
//!   fixities the same way the new typechecker already tracks them
//!   internally — reusing `Scheme`, `CtorInfo`, `ClassInfo`, `Instance`
//!   from their existing homes rather than redefining.
//! * Key everything inside `ModuleExports` by the **local** name
//!   (the bare identifier the defining module uses). Importers
//!   wrap those names into `QName`s with their own qualifier when
//!   they populate the consumer's `Env`.
//! * `distill_exports` filters the module's full decl list by its
//!   export-list clause (`module M (foo, Bar(..), class C) where`).
//!   When no export clause is present, everything declared at the
//!   top level ships.

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::cst::{Associativity, Decl};
use crate::typecheck_db::passes::exhaustiveness::CtorInfo;
use crate::typecheck_db::passes::infer_value::InferredScheme;
use crate::typecheck_db::passes::instance_index::{ClassInfo, Instance};
use crate::typecheck_db::types::{Scheme, Type};

// ---------------------------------------------------------------------------
// Supporting types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeAlias {
    pub type_vars: Vec<String>,
    pub body: Type,
    /// True when the type alias has a polykinded standalone kind signature
    /// (`type Foo :: forall k. ...`). Polykinded aliases can be used with
    /// fewer explicit type args than their arity (the kind unifier handles
    /// instantiation), so they're exempt from the `PartiallyAppliedSynonym`
    /// check.
    pub has_poly_kind: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixityDecl {
    pub associativity: Associativity,
    pub precedence: u8,
    /// Fully-qualified target this operator aliases. For
    /// `infixl 6 add as +`, target is the `QName` for `add` with
    /// the defining module's prefix.
    pub target_module: Option<String>,
    pub target_name: String,
}

// ---------------------------------------------------------------------------
// ModuleExports + ModuleRegistry
// ---------------------------------------------------------------------------

/// The surface another module sees when it imports this one.
/// Internal names only — no module prefix, since each entry is
/// already scoped by the outer module key in `ModuleRegistry`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleExports {
    /// Top-level values (functions + non-method constants) plus
    /// class methods. Keyed by the local value name.
    /// `Arc`-shared so importers can `Arc::clone` into their `Env`
    /// instead of doing a deep `Scheme::clone` per imported name.
    /// Each importer of, say, Prelude binds 200+ values under two
    /// keys; before this the whole `Type` tree was being cloned
    /// twice per scheme per importer.
    pub values: HashMap<String, std::sync::Arc<Scheme>>,

    /// Every constructor declared in this module, keyed by the
    /// constructor's local name. Includes newtype constructors.
    pub ctors: HashMap<String, CtorInfo>,

    /// Type name → list of its constructor names. Mirrors legacy
    /// `data_constructors` and is what exhaustiveness + import
    /// machinery both consult.
    pub data_constructors: HashMap<String, Vec<String>>,

    /// Type aliases: alias name → (vars, body).
    pub type_aliases: HashMap<String, TypeAlias>,

    /// Classes declared in this module. Value for each entry is
    /// the same `ClassInfo` the instance index carries plus any
    /// methods — method names themselves are looked up through
    /// `values`, so this struct only adds metadata not covered
    /// there.
    pub classes: HashMap<String, ClassInfo>,

    /// Every instance declared in this module. PureScript
    /// instances are globally visible, so import resolution
    /// forwards this whole list regardless of export clauses.
    ///
    /// `Arc`-shared so transitive re-exports clone an Arc handle
    /// (8 bytes + atomic refcount bump) instead of deep-cloning
    /// the whole `Instance` struct. For modules that re-export
    /// through long Prelude/library chains, this is the dominant
    /// per-module-exports memory cost — without Arc-sharing,
    /// each level in the chain duplicates the full Instance.
    #[serde(default)]
    pub instances: Vec<std::sync::Arc<Instance>>,

    /// Value-level operator fixities: op name → declaration.
    pub value_fixities: HashMap<String, FixityDecl>,

    /// Type-level operator fixities.
    pub type_fixities: HashMap<String, FixityDecl>,

    /// Newtype names (used by the Coercible solver).
    pub newtypes: HashSet<String>,

    /// Type constructor arities (Int=0, Array=1, Function=2, …).
    pub type_arities: HashMap<String, usize>,

    /// Renderable kind per exported type constructor and class, for LSP
    /// hover — e.g. `Type`, `Type -> Type`, `Type -> Constraint`,
    /// `(Type -> Type) -> Constraint`. Types default to all-`Type` params
    /// from their arity; classes carry their real param kinds (inferred from
    /// method usage), so higher-kinded params render correctly. Not consumed
    /// by the type checker — purely IDE metadata.
    #[serde(default)]
    pub type_kinds: HashMap<String, Type>,

    /// For each exported value, the *defining* module. When a
    /// module only re-exports a name (via `module Other` re-export
    /// clauses), the origin here is the module that actually
    /// declared it — not the re-exporter. Used by import
    /// resolution to bind each scheme under its origin-qualified
    /// key so downstream code compiled against a canonicalized
    /// fixity target (e.g. `$` → `Data.Function.apply`) still
    /// resolves even when the importer only saw the
    /// re-exporter's name.
    #[serde(default)]
    pub value_origins: HashMap<String, String>,

    /// Extra origin-qualified value bindings. Needed when a
    /// module re-exports multiple distinct values under the same
    /// simple name (e.g. Prelude re-exports both
    /// `Data.Function.apply` and `Control.Apply.apply`). The
    /// primary `values` entry holds one of them; this map holds
    /// any additional `(origin, name) → scheme` pair so the
    /// importer can still bind all distinct origin keys.
    #[serde(default)]
    pub qualified_values: HashMap<(String, String), std::sync::Arc<Scheme>>,

    /// Defining module for each exported class — same shape and
    /// semantics as `value_origins`, used by ExportConflict to
    /// distinguish two locally-declared classes with colliding
    /// names from a single class re-exported through two paths.
    #[serde(default)]
    pub class_origins: HashMap<String, String>,

    /// Defining module for each exported type (data/newtype/alias).
    #[serde(default)]
    pub type_origins: HashMap<String, String>,

    /// Defining module for each exported data constructor.
    #[serde(default)]
    pub ctor_origins: HashMap<String, String>,

    /// For each `foreign import data X :: K` (and `data X` with no
    /// constructors used as a kind), the QUALIFIED name of K's
    /// "head" type when K is a Constructor. Stored as
    /// `(module, name)` so the importer can compare across modules
    /// even when the kind constructor was unqualified at the
    /// declaration site (in which case `module` is the declaring
    /// module). Used to detect kind mismatches like
    /// `LibA.DemoKind` vs `LibB.DemoKind`.
    #[serde(default)]
    pub foreign_data_kinds: HashMap<String, (String, String)>,
}

/// In-process cache of every compiled module's export surface,
/// keyed by canonical module name ("Data.Maybe", "Prim.Row", …).
///
/// Also carries the scheme-only `output_hash` of each top-level value
/// decl (populated by the multi-module driver during a cached run). The
/// hash is the cross-module cache's version stamp: an importer's
/// `infer_value_scc` `input_hash` folds in the relevant
/// `scheme_hashes[decl]`, so body-only edits in an exporter — which
/// preserve the schemes and thus their hashes — don't invalidate
/// importers, while signature changes do.
#[derive(Debug, Clone, Default)]
pub struct ModuleRegistry {
    modules: HashMap<String, ModuleExports>,
    scheme_hashes: HashMap<String, HashMap<String, [u8; 32]>>,
    /// Per-module cached output hashes for every non-value decl
    /// kind. Keyed by `(module, kind_prefix, simple_name)` — e.g.
    /// `("Data.Maybe", "d", "Maybe")` for `data Maybe`. Instances
    /// (keyed by content-hash) also land here under prefix `"i"`.
    /// Downstream value SCCs pull these hashes into their
    /// `dep_output_hashes` for precise invalidation.
    nonvalue_hashes: HashMap<String, HashMap<(String, String), [u8; 32]>>,
    /// Per-module: every instance decl key in that module. The
    /// value-SCC dep resolver walks this list to find in-scope
    /// instances for each class reference.
    module_instances: HashMap<String, Vec<String>>,
    /// Per-module, per-class: instance decl keys. Lets callers look
    /// up exactly the instances of a given class without scanning
    /// every instance in the module.
    instances_by_class: HashMap<(String, String), Vec<String>>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: impl Into<String>, exports: ModuleExports) {
        self.modules.insert(name.into(), exports);
    }

    /// Record the scheme-only output hash of one value decl in `module`.
    /// Overwrites any prior entry for the same `(module, decl)` pair.
    pub fn set_scheme_hash(
        &mut self,
        module: impl Into<String>,
        decl: impl Into<String>,
        hash: [u8; 32],
    ) {
        self.scheme_hashes
            .entry(module.into())
            .or_default()
            .insert(decl.into(), hash);
    }

    /// Look up the scheme-only output hash for a specific decl, if one
    /// was recorded.
    pub fn scheme_hash(&self, module: &str, decl: &str) -> Option<[u8; 32]> {
        self.scheme_hashes
            .get(module)
            .and_then(|m| m.get(decl))
            .copied()
    }

    /// Record a non-value decl's check output hash. `kind_prefix` is
    /// one of `"d"` / `"n"` / `"ta"` / `"c"` / `"i"` / `"f"` / `"fv"`
    /// / `"ft"` (matching `decl_key_for_nonvalue`).
    pub fn set_nonvalue_hash(
        &mut self,
        module: impl Into<String>,
        kind_prefix: impl Into<String>,
        name: impl Into<String>,
        hash: [u8; 32],
    ) {
        let m = module.into();
        self.nonvalue_hashes
            .entry(m)
            .or_default()
            .insert((kind_prefix.into(), name.into()), hash);
    }

    pub fn nonvalue_hash(
        &self,
        module: &str,
        kind_prefix: &str,
        name: &str,
    ) -> Option<[u8; 32]> {
        self.nonvalue_hashes
            .get(module)
            .and_then(|m| m.get(&(kind_prefix.to_string(), name.to_string())))
            .copied()
    }

    /// Record one instance decl key (content-hashed) for a module,
    /// along with the class it implements. The class entry enables
    /// fine-grained dep tracking: callers pulling in "every in-scope
    /// instance of class C" walk only the `instances_by_class` slice.
    pub fn push_module_instance(
        &mut self,
        module: impl Into<String>,
        class_name: impl Into<String>,
        decl_key: impl Into<String>,
    ) {
        let m = module.into();
        let cn = class_name.into();
        let dk = decl_key.into();
        self.module_instances
            .entry(m.clone())
            .or_default()
            .push(dk.clone());
        self.instances_by_class
            .entry((m, cn))
            .or_default()
            .push(dk);
    }

    /// All instance decl keys recorded for a module.
    pub fn module_instances(&self, module: &str) -> &[String] {
        self.module_instances
            .get(module)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Instance decl keys in `module` that implement `class_name`.
    pub fn instances_of_class(&self, module: &str, class_name: &str) -> &[String] {
        self.instances_by_class
            .get(&(module.to_string(), class_name.to_string()))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    // ===== Bulk per-module accessors for the build-plan module memo =====

    /// All recorded scheme-only output hashes for `module`, as owned pairs.
    pub fn scheme_hashes_for(&self, module: &str) -> Vec<(String, [u8; 32])> {
        self.scheme_hashes
            .get(module)
            .map(|m| m.iter().map(|(k, v)| (k.clone(), *v)).collect())
            .unwrap_or_default()
    }

    /// All recorded non-value output hashes for `module`, as owned
    /// `((kind_prefix, name), hash)` pairs.
    pub fn nonvalue_hashes_for(&self, module: &str) -> Vec<((String, String), [u8; 32])> {
        self.nonvalue_hashes
            .get(module)
            .map(|m| m.iter().map(|(k, v)| (k.clone(), *v)).collect())
            .unwrap_or_default()
    }

    /// Every `(class_name, instance_decl_key)` recorded for `module`,
    /// recovered from the per-class index so a memo restore can rebuild
    /// both `module_instances` and `instances_by_class` via
    /// `push_module_instance`.
    pub fn instances_with_class_for(&self, module: &str) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for ((m, class), keys) in &self.instances_by_class {
            if m == module {
                for k in keys {
                    out.push((class.clone(), k.clone()));
                }
            }
        }
        out
    }

    /// Repopulate every per-module structure for a clean module restored
    /// from its memo: exports, per-decl scheme / non-value hashes, and
    /// instances. Used by the build plan to skip `check_one_module` while
    /// keeping the registry identical to what a fresh check would produce.
    pub fn restore_module(
        &mut self,
        module: &str,
        exports: ModuleExports,
        scheme_hashes: Vec<(String, [u8; 32])>,
        nonvalue_hashes: Vec<((String, String), [u8; 32])>,
        instances: Vec<(String, String)>,
    ) {
        self.insert(module.to_string(), exports);
        for (decl, h) in scheme_hashes {
            self.set_scheme_hash(module.to_string(), decl, h);
        }
        for ((kind, name), h) in nonvalue_hashes {
            self.set_nonvalue_hash(module.to_string(), kind, name, h);
        }
        for (class, key) in instances {
            self.push_module_instance(module.to_string(), class, key);
        }
    }

    pub fn get(&self, name: &str) -> Option<&ModuleExports> {
        self.modules.get(name)
    }

    pub fn contains(&self, name: &str) -> bool {
        self.modules.contains_key(name)
    }

    pub fn len(&self) -> usize {
        self.modules.len()
    }

    pub fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }

    /// Iterate every `(module_name, exports)` entry.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &ModuleExports)> {
        self.modules.iter()
    }
}

// ---------------------------------------------------------------------------
// distill_exports
// ---------------------------------------------------------------------------

/// Build a `ModuleExports` surface from a module's decls + its
/// inferred schemes. Applies the module's export-list filter when
/// one is present; exports everything declared at the top level
/// otherwise.
///
/// `schemes` carries one entry per `Decl::Value` the checker saw
/// (produced by `infer_value_scc_with_all`). Other decl kinds —
/// data, newtype, class, instance, type alias, fixity — are
/// derived from the CST directly.
pub fn distill_exports(
    module: &crate::cst::Module,
    schemes: &[InferredScheme],
    instances: &[Instance],
    class_info: &HashMap<String, ClassInfo>,
    ctor_info: &HashMap<String, CtorInfo>,
    alias_map: &crate::typecheck_db::types::AliasMap,
    type_ops: &crate::typecheck_db::types::TypeOpMap,
) -> ModuleExports {
    use crate::cst::{DataMembers, Export};

    // Full pool of exportable items, sourced from the CST + the
    // checker's per-decl outputs. We'll prune this down by the
    // export clause.
    //
    // Start with every inferred value scheme, then layer on the
    // CST-declared types of foreign imports and any top-level
    // type signatures (the checker doesn't run inference on
    // signatures-without-bodies, so their schemes only live in
    // the CST). Signature entries lose to inferred schemes when
    // both exist, since a `foo :: T` + `foo = body` pair should
    // export the inferred type, not the raw annotation.
    let conv = |ty: &crate::cst::TypeExpr| -> Type {
        crate::typecheck_db::types::expand_aliases(
            crate::typecheck_db::types::convert_type_expr(ty, type_ops),
            alias_map,
        )
    };

    let distill_self_module: String = module
        .name
        .value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".");
    let mut scheme_by_name: HashMap<String, std::sync::Arc<Scheme>> = HashMap::new();
    // Renderable class kinds (e.g. `(Type -> Type) -> Constraint`), keyed by
    // class name, folded from the per-var kinds computed below. Merged into
    // `out.type_kinds` before return (classes override the arity-based default).
    let mut class_kinds_by_name: HashMap<String, Type> = HashMap::new();
    for d in &module.decls {
        match d {
            Decl::Class { name, type_vars, type_var_kind_anns, members, .. } => {
                // Class methods get a constrained scheme:
                // `forall (class + method vars). C <class vars>
                //  => <method type>`. Without this they never
                // appear in ModuleExports.values and downstream
                // imports fail with UnknownValue.
                let class_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let class_vars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                // Class-quantified vars' kinds, parallel to `class_vars`.
                // Empty annotation → None (kind defaults to Type at
                // use sites that need a default; the unifier just
                // skips the check for None-kinded unifs).
                let mut class_var_kinds: Vec<Option<Type>> = type_vars
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        type_var_kind_anns
                            .get(i)
                            .and_then(|o| o.as_ref())
                            .map(|k| {
                                crate::typecheck_db::types::expand_aliases(
                                    crate::typecheck_db::types::convert_type_expr(k, type_ops),
                                    alias_map,
                                )
                            })
                    })
                    .collect();
                // Infer higher-kindedness from method bodies for vars
                // the source didn't annotate. e.g. `class Parallel f g`
                // doesn't annotate `f`/`g`, but `parallel :: g a -> f a`
                // applies them — so they must be at least `Type -> Type`.
                // Without this, `instantiate` would call `fresh()` (not
                // `fresh_with_kind`) on those vars, and `bind_var`
                // wouldn't refuse a `Type`-kind binding.
                for (i, var_name) in class_vars.iter().enumerate() {
                    if class_var_kinds[i].is_some() {
                        continue;
                    }
                    let mut max_args: usize = 0;
                    for m in members {
                        let mty = conv(&m.ty);
                        infer_max_app_args(&mty, var_name, &mut max_args);
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
                // Renderable class kind for hover: fold each param's kind
                // (defaulting unannotated/un-inferred params to `Type`) into a
                // right-nested arrow ending in `Constraint`. A no-param class
                // is just `Constraint`.
                {
                    let kind = class_var_kinds.iter().rev().fold(
                        crate::typecheck_db::types::prim_constraint(),
                        |acc, k| {
                            let param = k
                                .clone()
                                .unwrap_or_else(crate::typecheck_db::types::prim_kind_type);
                            Type::Fun(std::sync::Arc::new(param), std::sync::Arc::new(acc))
                        },
                    );
                    class_kinds_by_name.insert(class_name.clone(), kind);
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
                        // Use the DEFINING module's qualifier (this is
                        // distill_exports for `module`, so its decls
                        // define the class here). Matches
                        // `bind_local_ctors`'s qualified-class form
                        // so cross-module constraint discharge
                        // compares apples to apples.
                        class: crate::typecheck_db::types::QName::qualified(
                            &distill_self_module,
                            &class_name,
                        ),
                        args: class_vars
                            .iter()
                            .map(|v| Type::Var(v.clone()))
                            .collect(),
                    };
                    let constrained =
                        Type::Constrained(vec![constraint], std::sync::Arc::new(method_body));
                    let mut all_vars = class_vars.clone();
                    all_vars.extend(method_vars);
                    let mut all_kinds = class_var_kinds.clone();
                    all_kinds.extend(method_var_kinds);
                    scheme_by_name.insert(
                        method_name,
                        std::sync::Arc::new(Scheme::with_kinds(all_vars, all_kinds, constrained)),
                    );
                }
            }
            Decl::Foreign { name, ty, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let declared = conv(ty);
                let (vars, vars_kinds, body) = match declared {
                    Type::Forall(qs, body) => {
                        let (ns, ks): (Vec<String>, Vec<Option<Type>>) = qs
                            .into_iter()
                            .map(|(n, _, k)| (n, k.map(|arc| (*arc).clone())))
                            .unzip();
                        (ns, ks, std::sync::Arc::unwrap_or_clone(body))
                    }
                    other => (Vec::new(), Vec::new(), other),
                };
                scheme_by_name.insert(
                    n,
                    std::sync::Arc::new(Scheme::with_kinds(vars, vars_kinds, body)),
                );
            }
            Decl::TypeSignature { name, ty, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let declared = conv(ty);
                let (vars, vars_kinds, body) = match declared {
                    Type::Forall(qs, body) => {
                        let (ns, ks): (Vec<String>, Vec<Option<Type>>) = qs
                            .into_iter()
                            .map(|(n, _, k)| (n, k.map(|arc| (*arc).clone())))
                            .unzip();
                        (ns, ks, std::sync::Arc::unwrap_or_clone(body))
                    }
                    other => (Vec::new(), Vec::new(), other),
                };
                scheme_by_name
                    .entry(n)
                    .or_insert_with(|| {
                        std::sync::Arc::new(Scheme::with_kinds(vars, vars_kinds, body))
                    });
            }
            _ => {}
        }
    }
    for s in schemes {
        scheme_by_name.insert(s.name.clone(), std::sync::Arc::new(s.scheme.clone()));
    }

    // Walk decls once to extract everything the checker doesn't
    // already hand us (data/newtype ctor membership, type aliases,
    // class method sets, fixities, newtype names, type arities).
    let mut data_ctors_all: HashMap<String, Vec<String>> = HashMap::new();
    let mut type_arities_all: HashMap<String, usize> = HashMap::new();
    let mut type_aliases_all: HashMap<String, TypeAlias> = HashMap::new();
    let mut newtypes_all: HashSet<String> = HashSet::new();
    let mut value_fixities_all: HashMap<String, FixityDecl> = HashMap::new();
    let mut type_fixities_all: HashMap<String, FixityDecl> = HashMap::new();
    let mut class_methods: HashMap<String, Vec<String>> = HashMap::new();
    let mut foreign_data_kinds_all: HashMap<String, (String, String)> = HashMap::new();

    // Pre-collect locally-declared type-like names so we can
    // canonicalize unqualified Constructor refs in foreign-data
    // kind annotations to (this_module, name).
    let self_module: String = module
        .name
        .value
        .parts
        .iter()
        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
        .collect::<Vec<_>>()
        .join(".");
    let mut local_type_names: HashSet<String> = HashSet::new();
    for d in &module.decls {
        match d {
            Decl::Data { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::TypeAlias { name, .. }
            | Decl::ForeignData { name, .. } => {
                local_type_names.insert(
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol()),
                );
            }
            Decl::Class { name, .. } => {
                local_type_names.insert(
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol()),
                );
            }
            _ => {}
        }
    }

    // Pre-collect which type aliases have a standalone kind signature
    // Pre-collect which type aliases have a POLYKINDED standalone kind signature
    // (`type Foo :: forall k. ...`).  These are represented in the CST as
    // Decl::Data { kind_sig: KindSigSource::Type, kind_type: Some(Forall{…}), … }.
    // Polykinded aliases can be used with fewer explicit type args than their
    // syntactic arity (the kind unifier instantiates the forall), so they are
    // exempt from the PartiallyAppliedSynonym check.  Monokinded aliases like
    // `type NaturalTransformation :: (Type->Type) -> (Type->Type) -> Type` are
    // NOT exempt and must still be checked.
    let mut poly_kind_alias_names: HashSet<String> = HashSet::new();
    for d in &module.decls {
        if let Decl::Data {
            name,
            kind_sig: crate::cst::KindSigSource::Type,
            kind_type: Some(kt),
            ..
        } = d
        {
            if matches!(kt.as_ref(), crate::cst::TypeExpr::Forall { .. }) {
                poly_kind_alias_names
                    .insert(crate::typecheck_db::util::resolve_symbol(name.value.symbol()));
            }
        }
    }

    for d in &module.decls {
        match d {
            Decl::Data { name, type_vars, constructors, is_role_decl, kind_sig, .. } => {
                // Skip role declarations and standalone kind signatures —
                // they share the type name but have empty type_vars/ctors
                // and would overwrite the real declaration's arity and
                // constructor list if processed.
                if *is_role_decl || !matches!(kind_sig, crate::cst::KindSigSource::None) {
                    continue;
                }
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let ctor_names: Vec<String> = constructors
                    .iter()
                    .map(|c| crate::typecheck_db::util::resolve_symbol(c.name.value.symbol()))
                    .collect();
                data_ctors_all.insert(n.clone(), ctor_names);
                type_arities_all.insert(n, type_vars.len());
            }
            Decl::Newtype { name, type_vars, constructor, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let ctor_name =
                    crate::typecheck_db::util::resolve_symbol(constructor.value.symbol());
                data_ctors_all.insert(n.clone(), vec![ctor_name]);
                type_arities_all.insert(n.clone(), type_vars.len());
                newtypes_all.insert(n);
            }
            Decl::TypeAlias { name, type_vars, ty, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let vars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let body = crate::typecheck_db::types::convert_type_expr(ty, type_ops);
                let has_poly_kind = poly_kind_alias_names.contains(&n);
                type_arities_all.insert(n.clone(), vars.len());
                type_aliases_all.insert(n, TypeAlias { type_vars: vars, body, has_poly_kind });
            }
            Decl::Class { name, type_vars, members, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                type_arities_all.insert(n.clone(), type_vars.len());
                let method_names: Vec<String> = members
                    .iter()
                    .map(|m| {
                        crate::typecheck_db::util::resolve_symbol(m.name.value.symbol())
                    })
                    .collect();
                class_methods.insert(n, method_names);
            }
            Decl::ForeignData { name, kind, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                // Derive arity from the kind annotation (arrow count).
                type_arities_all.insert(n.clone(), count_kind_arrows(kind));
                // Track the qualified head of the kind annotation
                // when it's a single Constructor reference. Used by
                // cross-module kind comparison to detect
                // `LibA.DemoKind` vs `LibB.DemoKind` mismatches.
                if let Some((m, k)) = qualified_kind_head(kind, &self_module, &local_type_names) {
                    foreign_data_kinds_all.insert(n, (m, k));
                }
            }
            Decl::Fixity { associativity, precedence, target, operator, is_type, .. } => {
                let op = crate::typecheck_db::util::resolve_symbol(operator.value.symbol());
                let user_target_module = target
                    .module
                    .map(|m| crate::typecheck_db::util::resolve_symbol(m));
                let target_name = crate::typecheck_db::util::resolve_symbol(target.name);
                // Canonicalization:
                // * If the user wrote an explicit module qualifier
                //   (`infixl 6 MyMod.add as +`), keep it.
                // * If the target is defined *in this module*
                //   (value scheme or data ctor), pin it to this
                //   module — lets Prelude distinguish
                //   `Data.Function.apply` from
                //   `Control.Apply.apply`.
                // * If the target is an *imported* name (e.g.
                //   `Data.Tuple.Nested`'s `infixr 6 Tuple as /\`
                //   where `Tuple` came from `Data.Tuple`), pin it
                //   to the origin module so downstream importers
                //   of the operator alias find `Data.Tuple.Tuple`
                //   even without a direct `import Data.Tuple`.
                //   Otherwise leave as `None`.
                let target_is_local_value = scheme_by_name.contains_key(&target_name);
                let target_is_local_ctor = ctor_info.contains_key(&target_name);
                // Type fixities (`infixr 4 type RowApply as +`)
                // target a TYPE — check local_type_names.
                // Without this, a locally-defined-type target
                // leaves `target_module = None`, so importers
                // build `type_ops[+] = QName(None, "RowApply")`
                // and their distilled alias bodies that mention
                // `+` keep the unqualified `RowApply`.
                let target_is_local_type =
                    local_type_names.contains(&target_name);
                let self_module_name_str: String = module
                    .name
                    .value
                    .parts
                    .iter()
                    .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                    .collect::<Vec<_>>()
                    .join(".");
                let target_module = match user_target_module {
                    Some(m) => Some(m),
                    None if target_is_local_value
                        || target_is_local_ctor
                        || target_is_local_type =>
                    {
                        Some(self_module_name_str.clone())
                    }
                    // Non-local target (e.g. `infixr 6 Tuple as
                    // /\` where `Tuple` came from an import).
                    // Left as `None` here; a post-distill pass
                    // in `driver_multi` re-resolves against the
                    // `ModuleRegistry` and fills in the origin.
                    None => None,
                };
                let decl = FixityDecl {
                    associativity: *associativity,
                    precedence: *precedence,
                    target_module,
                    target_name,
                };
                if *is_type {
                    type_fixities_all.insert(op, decl);
                } else {
                    value_fixities_all.insert(op, decl);
                }
            }
            _ => {}
        }
    }

    // Now decide what to include. No export clause → everything;
    // otherwise walk the list and promote matching items.
    let mut out = ModuleExports::default();

    // Always: instances are globally visible in PureScript.
    // Wrap each local instance in `Arc` so transitively-re-exporting
    // modules clone the handle (8 bytes) instead of the whole struct.
    out.instances = instances
        .iter()
        .map(|i| std::sync::Arc::new(i.clone()))
        .collect();

    // Origin for every value this module defines — used by import
    // resolution to bind the scheme under its origin-qualified key
    // (`Data.Function.apply`) so canonicalized fixity targets
    // resolve across re-exports.
    let self_module_name: String = module
        .name
        .value
        .parts
        .iter()
        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
        .collect::<Vec<_>>()
        .join(".");

    match &module.exports {
        None => {
            // Export everything.
            out.values = scheme_by_name.clone();
            for name in scheme_by_name.keys() {
                out.value_origins.insert(name.clone(), self_module_name.clone());
            }
            for (name, info) in ctor_info {
                out.ctors.insert(name.clone(), info.clone());
                out.ctor_origins
                    .insert(name.clone(), self_module_name.clone());
            }
            out.data_constructors = data_ctors_all;
            out.type_aliases = type_aliases_all;
            for (name, info) in class_info {
                out.classes.insert(name.clone(), info.clone());
                out.class_origins
                    .insert(name.clone(), self_module_name.clone());
            }
            out.value_fixities = value_fixities_all.clone();
            out.type_fixities = type_fixities_all;
            out.newtypes = newtypes_all;
            out.type_arities = type_arities_all;
            for name in out.type_arities.keys().cloned().collect::<Vec<_>>() {
                out.type_origins
                    .entry(name)
                    .or_insert_with(|| self_module_name.clone());
            }
            out.foreign_data_kinds = foreign_data_kinds_all.clone();
            // Make operators importable under their own name by
            // cross-referencing their fixity's target's scheme.
            // `import M (<<<)` parses as `Import::Value("<<<")`;
            // without this alias the importer can't find `<<<` in
            // `values`.
            for (op, fx) in &value_fixities_all {
                if let Some(scheme) = scheme_by_name.get(&fx.target_name) {
                    out.values.insert(op.clone(), scheme.clone());
                    out.value_origins.insert(op.clone(), self_module_name.clone());
                } else if let Some(info) = ctor_info.get(&fx.target_name) {
                    // Constructor-operator alias (`infixl 6
                    // Tuple as /\`): the target is a ctor, not a
                    // value. Synthesize its ctor scheme so the
                    // operator is importable as a value too.
                    out.values.insert(
                        op.clone(),
                        std::sync::Arc::new(crate::typecheck_db::passes::imports::synth_ctor_scheme(info)),
                    );
                    out.value_origins.insert(op.clone(), self_module_name.clone());
                }
            }
        }
        Some(spanned) => {
            for item in &spanned.value.exports {
                match item {
                    Export::Value(vn) => {
                        let name = crate::typecheck_db::util::resolve_symbol(vn.symbol());
                        if let Some(s) = scheme_by_name.get(&name) {
                            out.values.insert(name.clone(), s.clone());
                            out.value_origins.insert(name.clone(), self_module_name.clone());
                        } else if let Some(fx) = value_fixities_all.get(&name) {
                            // Operator alias: `(&&)` → fixity decl
                            // names `&&` with `conj` as target.
                            // Expose `&&` in `values` with the
                            // target's scheme plus copy the fixity
                            // itself so importers can use both.
                            if let Some(s) = scheme_by_name.get(&fx.target_name) {
                                out.values.insert(name.clone(), s.clone());
                                out.value_origins.insert(name.clone(), self_module_name.clone());
                            } else if let Some(info) = ctor_info.get(&fx.target_name) {
                                out.values.insert(
                                    name.clone(),
                                    std::sync::Arc::new(crate::typecheck_db::passes::imports::synth_ctor_scheme(info)),
                                );
                                out.value_origins
                                    .insert(name.clone(), self_module_name.clone());
                            }
                            out.value_fixities.insert(name, fx.clone());
                        }
                    }
                    Export::Type(tn, members) => {
                        let name = crate::typecheck_db::util::resolve_symbol(tn.symbol());
                        // Always export the type itself — register
                        // as a known type even if members are
                        // filtered.
                        if let Some(arity) = type_arities_all.get(&name) {
                            out.type_arities.insert(name.clone(), *arity);
                            out.type_origins
                                .insert(name.clone(), self_module_name.clone());
                        }
                        if let Some(alias) = type_aliases_all.get(&name) {
                            out.type_aliases.insert(name.clone(), alias.clone());
                            out.type_origins
                                .insert(name.clone(), self_module_name.clone());
                        }
                        if let Some(kind_q) = foreign_data_kinds_all.get(&name) {
                            out.foreign_data_kinds
                                .insert(name.clone(), kind_q.clone());
                        }
                        if newtypes_all.contains(&name) {
                            out.newtypes.insert(name.clone());
                        }
                        if let Some(all_ctors) = data_ctors_all.get(&name) {
                            // Decide which ctors travel with the
                            // type.
                            let wanted: Vec<String> = match members {
                                None => Vec::new(),
                                Some(DataMembers::All) => all_ctors.clone(),
                                Some(DataMembers::Explicit(list)) => list
                                    .iter()
                                    .map(|c| {
                                        crate::typecheck_db::util::resolve_symbol(
                                            c.value.symbol(),
                                        )
                                    })
                                    .collect(),
                            };
                            // When the same type is exported more than
                            // once (e.g. `module M (A(..), A) where`)
                            // prefer the richer ctor list. A later
                            // `A` (no ctors) shouldn't shadow a prior
                            // `A(..)` (full list).
                            out.data_constructors
                                .entry(name.clone())
                                .and_modify(|existing| {
                                    if wanted.len() > existing.len() {
                                        *existing = wanted.clone();
                                    }
                                })
                                .or_insert_with(|| wanted.clone());
                            for ctor in wanted {
                                if let Some(info) = ctor_info.get(&ctor) {
                                    out.ctors.insert(ctor.clone(), info.clone());
                                    out.ctor_origins
                                        .insert(ctor, self_module_name.clone());
                                }
                            }
                        } else {
                            // Type alias or foreign data —
                            // data_constructors gets no entry.
                        }
                    }
                    Export::Class(cn) => {
                        let name = crate::typecheck_db::util::resolve_symbol(cn.symbol());
                        if let Some(info) = class_info.get(&name) {
                            out.classes.insert(name.clone(), info.clone());
                            out.class_origins
                                .insert(name.clone(), self_module_name.clone());
                        }
                        // Class methods travel with the class.
                        if let Some(methods) = class_methods.get(&name) {
                            for m in methods {
                                if let Some(s) = scheme_by_name.get(m) {
                                    out.values.insert(m.clone(), s.clone());
                                    out.value_origins.insert(m.clone(), self_module_name.clone());
                                }
                            }
                        }
                    }
                    Export::TypeOp(on) => {
                        let name = crate::typecheck_db::util::resolve_symbol(on.symbol());
                        if let Some(f) = type_fixities_all.get(&name) {
                            out.type_fixities.insert(name, f.clone());
                        }
                    }
                    Export::Module(mn) => {
                        let re_export_name: String = mn
                            .parts
                            .iter()
                            .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                            .collect::<Vec<_>>()
                            .join(".");
                        if re_export_name == self_module_name {
                            // Self-export: `module M (module M)` exports
                            // all locally-defined items. Equivalent to
                            // the None-export branch for local items.
                            for (name, s) in &scheme_by_name {
                                out.values.entry(name.clone()).or_insert_with(|| s.clone());
                                out.value_origins.entry(name.clone()).or_insert_with(|| self_module_name.clone());
                            }
                            for (name, info) in ctor_info.iter() {
                                out.ctors.entry(name.clone()).or_insert_with(|| info.clone());
                                out.ctor_origins.entry(name.clone()).or_insert_with(|| self_module_name.clone());
                            }
                            for (name, cls) in class_info.iter() {
                                out.classes.entry(name.clone()).or_insert_with(|| cls.clone());
                                out.class_origins.entry(name.clone()).or_insert_with(|| self_module_name.clone());
                            }
                            for (name, arity) in &type_arities_all {
                                out.type_arities.entry(name.clone()).or_insert(*arity);
                                out.type_origins.entry(name.clone()).or_insert_with(|| self_module_name.clone());
                            }
                            for (name, alias) in &type_aliases_all {
                                out.type_aliases.entry(name.clone()).or_insert_with(|| alias.clone());
                            }
                            for (name, ctors) in &data_ctors_all {
                                out.data_constructors.entry(name.clone()).or_insert_with(|| ctors.clone());
                            }
                            for (k, v) in &type_fixities_all {
                                out.type_fixities.entry(k.clone()).or_insert_with(|| v.clone());
                            }
                            for name in &newtypes_all {
                                out.newtypes.insert(name.clone());
                            }
                            for (name, kind) in &foreign_data_kinds_all {
                                out.foreign_data_kinds.entry(name.clone()).or_insert_with(|| kind.clone());
                            }
                            // Make operators importable under their own name.
                            for (op, fx) in &value_fixities_all {
                                if let Some(scheme) = scheme_by_name.get(&fx.target_name) {
                                    out.values.entry(op.clone()).or_insert_with(|| scheme.clone());
                                    out.value_origins.entry(op.clone()).or_insert_with(|| self_module_name.clone());
                                } else if let Some(info) = ctor_info.get(&fx.target_name) {
                                    out.values.entry(op.clone()).or_insert_with(|| {
                                        std::sync::Arc::new(crate::typecheck_db::passes::imports::synth_ctor_scheme(info))
                                    });
                                    out.value_origins.entry(op.clone()).or_insert_with(|| self_module_name.clone());
                                }
                            }
                        }
                        // Non-self Export::Module handled in second pass
                        // outside this function — see `expand_module_reexports`,
                        // which has access to the `ModuleRegistry`.
                    }
                }
            }
            // Operator exports: `module M (+) where` lists `+` as a
            // Value(OpName) or similar. PureScript lists exported
            // operators alongside values, and the fixity decl
            // travels too.
            for (op, fx) in &value_fixities_all {
                if out.values.contains_key(&fx.target_name)
                    || is_operator_in_export_list(&spanned.value.exports, op)
                {
                    out.value_fixities.insert(op.clone(), fx.clone());
                }
            }
        }
    }

    // Renderable kinds for hover. Types default to all-`Type` params from
    // their arity; classes then override with their real (possibly
    // higher-kinded) param kinds. Only emit kinds for names actually exported.
    for (n, arity) in &out.type_arities {
        let kind = (0..*arity).fold(crate::typecheck_db::types::prim_kind_type(), |acc, _| {
            Type::Fun(
                std::sync::Arc::new(crate::typecheck_db::types::prim_kind_type()),
                std::sync::Arc::new(acc),
            )
        });
        out.type_kinds.insert(n.clone(), kind);
    }
    for (n, kind) in &class_kinds_by_name {
        if out.classes.contains_key(n) {
            out.type_kinds.insert(n.clone(), kind.clone());
        }
    }

    out
}

/// Second pass over `out` to handle `module N` re-export clauses.
/// For every `module X` in the export list, find the matching
/// import (by alias or raw target name), look up the imported
/// module's `ModuleExports` in the registry, and merge those
/// items into `out`. `distill_exports` itself can't do this
/// because it doesn't hold a registry reference — so this lives
/// Per-import filter restricting which CONSTRUCTORS a `module M`
/// re-export forwards. Mirrors the reference compiler's rule that
/// `module M` re-exports only the slice of M the importing module
/// actually pulled in. We narrow this to ctors specifically because
/// ctor collisions across modules with different arities are the
/// motivating bug (Halogen's `Input.Action` vs `HalogenQ.Action`).
/// Other namespaces (values / types / classes / fixities) use the
/// existing unfiltered merge — many fixtures depend on transitive
/// re-export behaviour for those.
#[derive(Clone, Debug)]
enum CtorReexportFilter {
    /// `import M` (open) or no list — every ctor / value passes.
    Open,
    /// `import M hiding (xs)` — every ctor / value passes unless
    /// the corresponding name is hidden. `hidden_types` covers
    /// ctors whose parent type is hidden; `values` lists hidden
    /// values (and value operators).
    Hiding {
        hidden_types: std::collections::HashSet<String>,
        values: std::collections::HashSet<String>,
    },
    /// `import M (xs)` — only ctors whose parent type was imported
    /// with `(..)` (or whose name was listed individually) pass,
    /// and only values explicitly listed pass.
    Explicit {
        types_with_all_ctors: std::collections::HashSet<String>,
        ctors: std::collections::HashSet<String>,
        values: std::collections::HashSet<String>,
    },
}

impl CtorReexportFilter {
    fn includes_ctor(&self, ctor_name: &str, target: &ModuleExports) -> bool {
        match self {
            CtorReexportFilter::Open => true,
            CtorReexportFilter::Hiding { hidden_types, .. } => {
                // Hide the ctor only when EVERY parent type is
                // hidden. A name like `Action` can appear as a ctor
                // of both `Input` (hidden in some hiding lists) and
                // `HalogenQ` (not hidden); the ctor survives if any
                // parent is visible.
                let mut had_match = false;
                for (parent, ctor_list) in &target.data_constructors {
                    if ctor_list.iter().any(|c| c == ctor_name) {
                        had_match = true;
                        if !hidden_types.contains(parent) {
                            return true;
                        }
                    }
                }
                !had_match
            }
            CtorReexportFilter::Explicit { types_with_all_ctors, ctors, .. } => {
                if ctors.contains(ctor_name) {
                    return true;
                }
                // Iterate ALL parent types for `ctor_name` —
                // `target.data_constructors` may carry multiple
                // entries that share a constructor name (e.g.
                // `Action` is a ctor of both `Input` and `HalogenQ`
                // in Halogen.Query after both are merged). The
                // re-export includes the ctor if ANY parent was
                // imported with `(..)`.
                for (parent, ctor_list) in &target.data_constructors {
                    if ctor_list.iter().any(|c| c == ctor_name) {
                        if types_with_all_ctors.contains(parent) {
                            return true;
                        }
                    }
                }
                false
            }
        }
    }

    /// True if this re-export should surface `value_name` from
    /// the target. Used to filter values when a `module M`
    /// re-export collides with another `module N` re-export —
    /// e.g. Halogen.HTML re-exports `module Halogen.HTML.Core`
    /// and `module Halogen.HTML.Properties`, both defining `attr`
    /// with different arities. Only the import list that
    /// explicitly listed `attr` should surface it.
    fn includes_value(&self, value_name: &str) -> bool {
        match self {
            CtorReexportFilter::Open => true,
            CtorReexportFilter::Hiding { values, .. } => !values.contains(value_name),
            CtorReexportFilter::Explicit { values, .. } => values.contains(value_name),
        }
    }
}

fn build_ctor_reexport_filter(
    list: &Option<crate::cst::ImportList>,
) -> CtorReexportFilter {
    use crate::cst::Import;
    use crate::cst::ImportList;
    let resolve = |s: crate::interner::Symbol| -> String {
        crate::typecheck_db::util::resolve_symbol(s)
    };
    match list {
        None => CtorReexportFilter::Open,
        Some(ImportList::Hiding(items)) => {
            let mut hidden_types: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            let mut values: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            for item in items {
                match item {
                    Import::Type(n, _) => {
                        hidden_types.insert(resolve(n.value.symbol()));
                    }
                    Import::Value(n) => {
                        values.insert(resolve(n.value.symbol()));
                    }
                    _ => {}
                }
            }
            CtorReexportFilter::Hiding { hidden_types, values }
        }
        Some(ImportList::Explicit(items)) => {
            let mut types_with_all_ctors: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            let mut ctors: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            let mut values: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            for item in items {
                match item {
                    Import::Type(n, members) => match members {
                        Some(crate::cst::DataMembers::All) => {
                            types_with_all_ctors.insert(resolve(n.value.symbol()));
                        }
                        Some(crate::cst::DataMembers::Explicit(names)) => {
                            for cn in names {
                                ctors.insert(resolve(cn.value.symbol()));
                            }
                        }
                        None => {}
                    },
                    Import::Value(n) => {
                        values.insert(resolve(n.value.symbol()));
                    }
                    _ => {}
                }
            }
            CtorReexportFilter::Explicit {
                types_with_all_ctors,
                ctors,
                values,
            }
        }
    }
}

/// here and is called from the driver after the primary distill.
pub fn expand_module_reexports(
    out: &mut ModuleExports,
    module: &crate::cst::Module,
    registry: &ModuleRegistry,
) {
    use crate::cst::Export;
    let spanned = match &module.exports {
        Some(s) => s,
        None => return,
    };
    let self_module_name: String = module
        .name
        .value
        .parts
        .iter()
        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
        .collect::<Vec<_>>()
        .join(".");
    for item in &spanned.value.exports {
        if let Export::Module(mn) = item {
            let re_exported_name: String = mn
                .parts
                .iter()
                .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                .collect::<Vec<_>>()
                .join(".");

            // Self re-export: `module M (module M)` — surface all
            // local declarations as if they'd been listed
            // explicitly. We scan `module.decls` directly since
            // `out`'s explicit-export logic only added items
            // listed in the export list; local-only types like
            // a `type Foo = Boolean` referenced via `module M`
            // wouldn't otherwise reach `out`.
            if re_exported_name == self_module_name {
                for d in &module.decls {
                    match d {
                        crate::cst::Decl::Data {
                            name,
                            type_vars,
                            kind_sig: crate::cst::KindSigSource::None,
                            is_role_decl: false,
                            ..
                        } => {
                            let n = crate::typecheck_db::util::resolve_symbol(
                                name.value.symbol(),
                            );
                            out.type_arities
                                .entry(n)
                                .or_insert(type_vars.len());
                        }
                        crate::cst::Decl::Newtype { name, type_vars, .. } => {
                            let n = crate::typecheck_db::util::resolve_symbol(
                                name.value.symbol(),
                            );
                            out.type_arities
                                .entry(n)
                                .or_insert(type_vars.len());
                        }
                        crate::cst::Decl::TypeAlias {
                            name, type_vars, ..
                        } => {
                            let n = crate::typecheck_db::util::resolve_symbol(
                                name.value.symbol(),
                            );
                            out.type_arities
                                .entry(n)
                                .or_insert(type_vars.len());
                        }
                        crate::cst::Decl::ForeignData { name, .. } => {
                            let n = crate::typecheck_db::util::resolve_symbol(
                                name.value.symbol(),
                            );
                            out.type_arities.entry(n).or_insert(0);
                        }
                        crate::cst::Decl::Fixity {
                            is_type,
                            operator,
                            target,
                            associativity,
                            precedence,
                            ..
                        } => {
                            let op = crate::typecheck_db::util::resolve_symbol(
                                operator.value.symbol(),
                            );
                            let target_name = crate::typecheck_db::util::resolve_symbol(target.name);
                            let target_module = target
                                .module
                                .map(|m| crate::typecheck_db::util::resolve_symbol(m));
                            let decl = FixityDecl {
                                associativity: *associativity,
                                precedence: *precedence,
                                target_module,
                                target_name,
                            };
                            if *is_type {
                                out.type_fixities.entry(op).or_insert(decl);
                            } else {
                                out.value_fixities.entry(op).or_insert(decl);
                            }
                        }
                        _ => {}
                    }
                }
                continue;
            }

            // Find which import targets this `module X` clause
            // refers to. Multiple imports may share the same alias
            // (e.g. `import A.Foo (Foo) as Exports` + `import A.Bar
            // (Bar) as Exports`), so collect ALL matching targets.
            // We track the per-import CTOR filter so the re-export
            // surfaces only constructors the importing module
            // actually pulled in. Without this, `import M (T(..))`
            // re-exports every ctor M happens to define — letting
            // an unrelated `Action` from one module shadow another
            // module's `Action` of different arity (the Halogen
            // `Input.Action` / `HalogenQ.Action` ambiguity).
            //
            // The filter intentionally only restricts CTORS. Other
            // fields (values, types, classes, fixities) propagate
            // unchanged: many tests rely on the existing transitive
            // re-export behaviour for those namespaces and they
            // don't share the ctor-collision pattern (values have
            // `qualified_values` for multi-origin disambiguation;
            // types/classes don't typically collide cross-module).
            let mut target_modules: Vec<(String, CtorReexportFilter)> = Vec::new();
            for imp in &module.imports {
                let imp_target: String = imp
                    .module
                    .parts
                    .iter()
                    .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                    .collect::<Vec<_>>()
                    .join(".");
                let ctor_filter = build_ctor_reexport_filter(&imp.imports);
                // `module M` re-export sources from `import M`
                // (UNQUALIFIED only). `import M as Q` brings
                // names in only under `Q.foo`; their bare names
                // are accessible via `module Q` re-exports
                // instead (handled below). Without this guard a
                // single module imported BOTH `import M (foo)`
                // and `import M as Q` would have `module M`
                // surface every name from M (via the qualified
                // branch's wider implicit filter), defeating the
                // explicit-list filter on the unqualified arm.
                if imp_target == re_exported_name && imp.qualified.is_none() {
                    target_modules.push((imp_target, ctor_filter));
                    continue;
                }
                if let Some(alias) = &imp.qualified {
                    let alias_str: String = alias
                        .parts
                        .iter()
                        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                        .collect::<Vec<_>>()
                        .join(".");
                    if alias_str == re_exported_name {
                        target_modules.push((imp_target, ctor_filter));
                    }
                }
            }
            if target_modules.is_empty() {
                continue;
            }
            let prim_map = crate::typecheck_db::prim::prim_exports();
            for (target_name, ctor_filter) in &target_modules {
                // Re-export target may be a user module (in the
                // registry) OR a Prim submodule (not in the registry,
                // built from `prim::prim_exports`). Safe.Coerce relies
                // on the latter when it writes `module Prim.Coerce`.
                let target_exports = match registry.get(target_name) {
                    Some(t) => t,
                    None => match prim_map.get(target_name.as_str()) {
                        Some(t) => t,
                        None => continue,
                    },
                };

                // Merge everything from the target.
                for (k, v) in &target_exports.values {
                    let origin = target_exports
                        .value_origins
                        .get(k)
                        .cloned()
                        .unwrap_or_else(|| target_name.clone());
                    // `qualified_values` always carries the
                    // multi-origin map so consumers needing the
                    // ORIGIN-keyed scheme (e.g. the per-import
                    // post-distill fixity resolver) still find
                    // it even when the unqualified slot loses to
                    // a sibling re-export.
                    out.qualified_values
                        .entry((origin.clone(), k.clone()))
                        .or_insert_with(|| v.clone());
                    // The UNQUALIFIED slot is filtered by the
                    // importing module's per-import list: a
                    // `module M` clause only surfaces names the
                    // current module pulled in from M. Without
                    // this, `Halogen.HTML` re-exporting
                    // `module Halogen.HTML.Core` AND
                    // `module Halogen.HTML.Properties` collides
                    // on `attr` (Core's 3-arg variant vs
                    // Properties's 2-arg variant) and the first
                    // merge wins regardless of which one the
                    // user explicitly imported.
                    if !ctor_filter.includes_value(k) {
                        continue;
                    }
                    out.values.entry(k.clone()).or_insert_with(|| v.clone());
                    out.value_origins.entry(k.clone()).or_insert(origin);
                }
                for (key, scheme) in &target_exports.qualified_values {
                    out.qualified_values
                        .entry(key.clone())
                        .or_insert_with(|| scheme.clone());
                }
                for (k, v) in &target_exports.ctors {
                    if !ctor_filter.includes_ctor(k, target_exports) {
                        continue;
                    }
                    out.ctors.entry(k.clone()).or_insert_with(|| v.clone());
                    let origin = target_exports
                        .ctor_origins
                        .get(k)
                        .cloned()
                        .unwrap_or_else(|| target_name.clone());
                    out.ctor_origins.entry(k.clone()).or_insert(origin);
                }
                for (k, v) in &target_exports.data_constructors {
                    out.data_constructors.entry(k.clone()).or_insert_with(|| v.clone());
                }
                for (k, v) in &target_exports.type_aliases {
                    out.type_aliases.entry(k.clone()).or_insert_with(|| v.clone());
                }
                for (k, v) in &target_exports.classes {
                    out.classes.entry(k.clone()).or_insert_with(|| v.clone());
                    let origin = target_exports
                        .class_origins
                        .get(k)
                        .cloned()
                        .unwrap_or_else(|| target_name.clone());
                    out.class_origins.entry(k.clone()).or_insert(origin);
                }
                for inst in &target_exports.instances {
                    // Fast path: Arc pointer equality — most
                    // transitively-shared instances will alias the
                    // same Arc. Slow path: structural equality for
                    // local-vs-imported instances that share
                    // structure but not Arc identity.
                    let already = out.instances.iter().any(|i| {
                        std::sync::Arc::ptr_eq(i, inst) || **i == **inst
                    });
                    if !already {
                        out.instances.push(std::sync::Arc::clone(inst));
                    }
                }
                for (k, v) in &target_exports.value_fixities {
                    out.value_fixities.entry(k.clone()).or_insert_with(|| v.clone());
                }
                for (k, v) in &target_exports.type_fixities {
                    out.type_fixities.entry(k.clone()).or_insert_with(|| v.clone());
                }
                for n in &target_exports.newtypes {
                    out.newtypes.insert(n.clone());
                }
                for (k, v) in &target_exports.type_arities {
                    out.type_arities.entry(k.clone()).or_insert(*v);
                    let origin = target_exports
                        .type_origins
                        .get(k)
                        .cloned()
                        .unwrap_or_else(|| target_name.clone());
                    out.type_origins.entry(k.clone()).or_insert(origin);
                }
            }
        }
    }
}

/// Walk a kind type expression's "head" Constructor (after stripping
/// Forall/Function/Parens) and return its qualified module + name.
/// If the constructor was unqualified at declaration site AND the
/// name is locally declared, qualify with `self_module`.
fn count_kind_arrows(te: &crate::cst::TypeExpr) -> usize {
    match te {
        crate::cst::TypeExpr::Function { to, .. } => 1 + count_kind_arrows(to),
        crate::cst::TypeExpr::Parens { ty, .. } => count_kind_arrows(ty),
        crate::cst::TypeExpr::Forall { ty, .. } => count_kind_arrows(ty),
        _ => 0,
    }
}

fn qualified_kind_head(
    kind: &crate::cst::TypeExpr,
    self_module: &str,
    local_type_names: &HashSet<String>,
) -> Option<(String, String)> {
    let mut cur = kind;
    loop {
        match cur {
            crate::cst::TypeExpr::Forall { ty, .. }
            | crate::cst::TypeExpr::Parens { ty, .. } => cur = ty,
            crate::cst::TypeExpr::Function { to, .. } => cur = to,
            crate::cst::TypeExpr::Constructor { name, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.name.symbol());
                let m = match name.module {
                    Some(m) => crate::typecheck_db::util::resolve_symbol(m.symbol()),
                    None => {
                        if local_type_names.contains(&n) {
                            self_module.to_string()
                        } else {
                            // Imported reference: we can't canonicalize
                            // without the import alias map; bail.
                            return None;
                        }
                    }
                };
                return Some((m, n));
            }
            _ => return None,
        }
    }
}

/// Walk `ty` and update `max_args` with the longest App-spine count
/// whose head is `Type::Var(var_name)`. Used by the class-method
/// scheme builder to infer a kind shape (`Type -> ... -> Type`) for
/// class-quantified vars the source didn't annotate.
fn infer_max_app_args(ty: &Type, var_name: &str, max_args: &mut usize) {
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
            infer_max_app_args(f, var_name, max_args);
            infer_max_app_args(a, var_name, max_args);
        }
        Type::Fun(a, b) => {
            infer_max_app_args(a, var_name, max_args);
            infer_max_app_args(b, var_name, max_args);
        }
        Type::Forall(_, body) => infer_max_app_args(body, var_name, max_args),
        Type::Constrained(cs, body) => {
            for c in cs {
                for a in &c.args {
                    infer_max_app_args(a, var_name, max_args);
                }
            }
            infer_max_app_args(body, var_name, max_args);
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            for (_, t) in fs {
                infer_max_app_args(t, var_name, max_args);
            }
            if let Some(t) = tail {
                infer_max_app_args(t, var_name, max_args);
            }
        }
        Type::Kinded(t, k) => {
            infer_max_app_args(t, var_name, max_args);
            infer_max_app_args(k, var_name, max_args);
        }
        _ => {}
    }
}

fn is_operator_in_export_list(exports: &[crate::cst::Export], op: &str) -> bool {
    exports.iter().any(|e| match e {
        crate::cst::Export::Value(v) => {
            crate::typecheck_db::util::resolve_symbol(v.symbol()) == op
        }
        _ => false,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::passes::exhaustiveness::CtorInfo;
    use crate::typecheck_db::passes::infer_value::InferredScheme;
    use crate::typecheck_db::passes::instance_index::{ClassInfo, Instance};
    use crate::typecheck_db::types::{QName, Scheme, Type};
    use std::collections::HashMap;

    fn int_ty() -> Type {
        crate::typecheck_db::types::prim_int()
    }

    fn parse_module(src: &str) -> crate::cst::Module {
        parse(src).unwrap()
    }

    fn mono_scheme(name: &str, ty: Type) -> InferredScheme {
        InferredScheme {
            name: name.into(),
            scheme: Scheme::mono(ty),
            exhaustiveness_errors: vec![],
            pending_constraints: vec![],
            resolved_dicts: vec![],
            constraint_errors: vec![],
            constraint_dicts: HashMap::new(),
            hole_diagnostics: vec![],
        }
    }

    // =================================================================
    // ModuleRegistry basics
    // =================================================================

    #[test]
    fn registry_round_trips_one_entry() {
        let mut r = ModuleRegistry::new();
        assert!(r.is_empty());
        r.insert("Data.Maybe", ModuleExports::default());
        assert_eq!(r.len(), 1);
        assert!(r.contains("Data.Maybe"));
        assert!(r.get("Data.Maybe").is_some());
    }

    #[test]
    fn registry_lookup_missing_returns_none() {
        let r = ModuleRegistry::new();
        assert!(r.get("Nope").is_none());
    }

    #[test]
    fn registry_iter_yields_all_entries() {
        let mut r = ModuleRegistry::new();
        r.insert("A", ModuleExports::default());
        r.insert("B", ModuleExports::default());
        let names: Vec<&String> = r.iter().map(|(n, _)| n).collect();
        assert_eq!(names.len(), 2);
    }

    // =================================================================
    // distill_exports — no export clause (export everything)
    // =================================================================

    #[test]
    fn distill_no_export_clause_exports_every_value() {
        let m = parse_module("module M where\nfoo = 1\nbar = 2\n");
        let schemes = vec![
            mono_scheme("foo", int_ty()),
            mono_scheme("bar", int_ty()),
        ];
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), &Default::default());
        assert!(exports.values.contains_key("foo"));
        assert!(exports.values.contains_key("bar"));
    }

    #[test]
    fn distill_no_export_clause_exports_data_ctors() {
        let m = parse_module("module M where\ndata Maybe a = Nothing | Just a\n");
        let mut ctors: HashMap<String, CtorInfo> = HashMap::new();
        ctors.insert(
            "Nothing".into(),
            CtorInfo { parent_type: "Maybe".into(), parent_module: None, type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                parent_module: None,
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors, &HashMap::new(), &Default::default());
        assert!(exports.ctors.contains_key("Nothing"));
        assert!(exports.ctors.contains_key("Just"));
        assert_eq!(
            exports.data_constructors.get("Maybe").unwrap(),
            &vec!["Nothing".to_string(), "Just".into()],
        );
    }

    #[test]
    fn distill_no_export_clause_exports_classes_and_instances() {
        let m = parse_module(
            "\
module M where
class Eq a where
  eq :: a -> a -> Boolean
instance Eq Int where
  eq _ _ = true
",
        );
        let mut classes: HashMap<String, ClassInfo> = HashMap::new();
        classes.insert(
            "Eq".into(),
            ClassInfo { type_vars: vec!["a".into()], fundeps: vec![], superclasses: vec![] },
        );
        let instance = Instance {
            class: QName::unqualified("Eq"),
            types: vec![int_ty()],
            context: vec![],
            vars: vec![],
            chained: false,
        };
        let exports =
            distill_exports(&m, &[], std::slice::from_ref(&instance), &classes, &HashMap::new(), &HashMap::new(), &Default::default());
        assert!(exports.classes.contains_key("Eq"));
        assert_eq!(exports.instances.len(), 1);
    }

    // =================================================================
    // distill_exports — honours the export clause
    // =================================================================

    #[test]
    fn distill_export_clause_filters_values() {
        let m = parse_module(
            "\
module M (foo) where
foo = 1
bar = 2
",
        );
        let schemes = vec![
            mono_scheme("foo", int_ty()),
            mono_scheme("bar", int_ty()),
        ];
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), &Default::default());
        assert!(exports.values.contains_key("foo"));
        assert!(
            !exports.values.contains_key("bar"),
            "bar should not be exported"
        );
    }

    #[test]
    fn distill_type_export_without_members_hides_ctors() {
        // `module M (Maybe) where data Maybe = …` — the type is
        // exported but its constructors are private.
        let m = parse_module(
            "\
module M (Maybe) where
data Maybe a = Nothing | Just a
",
        );
        let mut ctors: HashMap<String, CtorInfo> = HashMap::new();
        ctors.insert(
            "Nothing".into(),
            CtorInfo { parent_type: "Maybe".into(), parent_module: None, type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                parent_module: None,
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors, &HashMap::new(), &Default::default());
        assert!(exports.data_constructors.contains_key("Maybe"));
        // No ctors exported since no (..)
        assert!(exports.ctors.is_empty(), "got: {:?}", exports.ctors);
    }

    #[test]
    fn distill_type_export_with_dot_dot_exports_all_ctors() {
        let m = parse_module(
            "\
module M (Maybe(..)) where
data Maybe a = Nothing | Just a
",
        );
        let mut ctors: HashMap<String, CtorInfo> = HashMap::new();
        ctors.insert(
            "Nothing".into(),
            CtorInfo { parent_type: "Maybe".into(), parent_module: None, type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                parent_module: None,
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors, &HashMap::new(), &Default::default());
        assert!(exports.ctors.contains_key("Nothing"));
        assert!(exports.ctors.contains_key("Just"));
    }

    #[test]
    fn distill_type_export_with_explicit_members_filters() {
        let m = parse_module(
            "\
module M (Maybe(Just)) where
data Maybe a = Nothing | Just a
",
        );
        let mut ctors: HashMap<String, CtorInfo> = HashMap::new();
        ctors.insert(
            "Nothing".into(),
            CtorInfo { parent_type: "Maybe".into(), parent_module: None, type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                parent_module: None,
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors, &HashMap::new(), &Default::default());
        assert!(exports.ctors.contains_key("Just"));
        assert!(!exports.ctors.contains_key("Nothing"));
    }

    #[test]
    fn distill_class_export_includes_class_methods() {
        // Legacy behavior: `module M (class Eq) where` exports the
        // class itself AND its methods (the methods become importable).
        let m = parse_module(
            "\
module M (class Eq) where
class Eq a where
  eq :: a -> a -> Boolean
",
        );
        let mut classes: HashMap<String, ClassInfo> = HashMap::new();
        classes.insert(
            "Eq".into(),
            ClassInfo { type_vars: vec!["a".into()], fundeps: vec![], superclasses: vec![] },
        );
        // Method scheme as it would appear after inference.
        let a = Type::Var("a".into());
        let method_scheme = Scheme::new(
            vec!["a".into()],
            Type::fun(
                a.clone(),
                Type::fun(a, Type::Con(QName::unqualified("Boolean"))),
            ),
        );
        let schemes = vec![InferredScheme {
            name: "eq".into(),
            scheme: method_scheme,
            exhaustiveness_errors: vec![],
            pending_constraints: vec![],
            resolved_dicts: vec![],
            constraint_errors: vec![],
            constraint_dicts: HashMap::new(),
            hole_diagnostics: vec![],
        }];
        let exports = distill_exports(&m, &schemes, &[], &classes, &HashMap::new(), &HashMap::new(), &Default::default());
        assert!(exports.classes.contains_key("Eq"));
        assert!(
            exports.values.contains_key("eq"),
            "class methods should travel with the class",
        );
    }

    #[test]
    fn distill_value_not_listed_is_hidden() {
        let m = parse_module("module M (foo) where\nfoo = 1\nprivate = 2\n");
        let schemes = vec![
            mono_scheme("foo", int_ty()),
            mono_scheme("private", int_ty()),
        ];
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), &Default::default());
        assert!(exports.values.contains_key("foo"));
        assert!(!exports.values.contains_key("private"));
    }

    #[test]
    fn distill_always_exports_instances_regardless_of_list() {
        // PureScript: instances are globally visible. An export
        // clause that omits instance names doesn't hide them.
        let m = parse_module(
            "\
module M (foo) where
foo = 1
instance Eq Int where
  eq _ _ = true
",
        );
        let schemes = vec![mono_scheme("foo", int_ty())];
        let instance = Instance {
            class: QName::unqualified("Eq"),
            types: vec![int_ty()],
            context: vec![],
            vars: vec![],
            chained: false,
        };
        let exports = distill_exports(
            &m,
            &schemes,
            std::slice::from_ref(&instance),
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &Default::default(),
        );
        assert_eq!(exports.instances.len(), 1);
    }

    #[test]
    fn distill_operator_export_and_fixity() {
        let m = parse_module(
            "\
module M ((+), add) where
add x y = x
infixl 6 add as +
",
        );
        let a = Type::Var("a".into());
        let add_scheme =
            Scheme::new(vec!["a".into()], Type::fun(a.clone(), Type::fun(a.clone(), a)));
        let schemes = vec![InferredScheme {
            name: "add".into(),
            scheme: add_scheme,
            exhaustiveness_errors: vec![],
            pending_constraints: vec![],
            resolved_dicts: vec![],
            constraint_errors: vec![],
            constraint_dicts: HashMap::new(),
            hole_diagnostics: vec![],
        }];
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), &Default::default());
        assert!(exports.values.contains_key("add"));
        assert!(exports.value_fixities.contains_key("+"));
    }
}
