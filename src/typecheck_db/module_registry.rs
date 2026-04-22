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
    pub values: HashMap<String, Scheme>,

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
    pub instances: Vec<Instance>,

    /// Value-level operator fixities: op name → declaration.
    pub value_fixities: HashMap<String, FixityDecl>,

    /// Type-level operator fixities.
    pub type_fixities: HashMap<String, FixityDecl>,

    /// Newtype names (used by the Coercible solver).
    pub newtypes: HashSet<String>,

    /// Type constructor arities (Int=0, Array=1, Function=2, …).
    pub type_arities: HashMap<String, usize>,

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
    pub qualified_values: HashMap<(String, String), Scheme>,
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
    let mut scheme_by_name: HashMap<String, Scheme> = HashMap::new();
    for d in &module.decls {
        match d {
            Decl::Class { name, type_vars, members, .. } => {
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
                for m in members {
                    let method_name =
                        crate::typecheck_db::util::resolve_symbol(m.name.value.symbol());
                    let method_ty = crate::typecheck_db::types::convert_type_expr(
                        &m.ty,
                        &crate::typecheck_db::types::TypeOpMap::default(),
                    );
                    let (method_vars, method_body) = match method_ty {
                        Type::Forall(qs, body) => {
                            let ns: Vec<String> =
                                qs.into_iter().map(|(n, _, _)| n).collect();
                            (ns, *body)
                        }
                        other => (Vec::new(), other),
                    };
                    let constraint = crate::typecheck_db::types::Constraint {
                        class: crate::typecheck_db::types::QName::unqualified(
                            &class_name,
                        ),
                        args: class_vars
                            .iter()
                            .map(|v| Type::Var(v.clone()))
                            .collect(),
                    };
                    let constrained =
                        Type::Constrained(vec![constraint], Box::new(method_body));
                    let mut all_vars = class_vars.clone();
                    all_vars.extend(method_vars);
                    scheme_by_name.insert(
                        method_name,
                        Scheme { vars: all_vars, ty: constrained },
                    );
                }
            }
            Decl::Foreign { name, ty, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let declared = crate::typecheck_db::types::convert_type_expr(
                    ty,
                    &crate::typecheck_db::types::TypeOpMap::default(),
                );
                let (vars, body) = match declared {
                    Type::Forall(qs, body) => {
                        let ns: Vec<String> =
                            qs.into_iter().map(|(n, _, _)| n).collect();
                        (ns, *body)
                    }
                    other => (Vec::new(), other),
                };
                scheme_by_name.insert(n, Scheme { vars, ty: body });
            }
            Decl::TypeSignature { name, ty, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let declared = crate::typecheck_db::types::convert_type_expr(
                    ty,
                    &crate::typecheck_db::types::TypeOpMap::default(),
                );
                let (vars, body) = match declared {
                    Type::Forall(qs, body) => {
                        let ns: Vec<String> =
                            qs.into_iter().map(|(n, _, _)| n).collect();
                        (ns, *body)
                    }
                    other => (Vec::new(), other),
                };
                scheme_by_name.entry(n).or_insert(Scheme { vars, ty: body });
            }
            _ => {}
        }
    }
    for s in schemes {
        scheme_by_name.insert(s.name.clone(), s.scheme.clone());
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

    for d in &module.decls {
        match d {
            Decl::Data { name, type_vars, constructors, .. } => {
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
                let body = crate::typecheck_db::types::convert_type_expr(
                    ty,
                    &crate::typecheck_db::types::TypeOpMap::default(),
                );
                type_arities_all.insert(n.clone(), vars.len());
                type_aliases_all.insert(n, TypeAlias { type_vars: vars, body });
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
            Decl::ForeignData { name, .. } => {
                let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                // Arity unknown without kind checking; 0 is a safe
                // default — the type_arities entry is primarily
                // used by importers as "this name is a type",
                // not for over-application detection.
                type_arities_all.insert(n, 0);
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
                    None if target_is_local_value || target_is_local_ctor => {
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
    out.instances = instances.to_vec();

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
            }
            out.data_constructors = data_ctors_all;
            out.type_aliases = type_aliases_all;
            for (name, info) in class_info {
                out.classes.insert(name.clone(), info.clone());
            }
            out.value_fixities = value_fixities_all.clone();
            out.type_fixities = type_fixities_all;
            out.newtypes = newtypes_all;
            out.type_arities = type_arities_all;
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
                    out.values.insert(op.clone(), crate::typecheck_db::passes::imports::synth_ctor_scheme(info));
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
                                out.values.insert(name.clone(), crate::typecheck_db::passes::imports::synth_ctor_scheme(info));
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
                        }
                        if let Some(alias) = type_aliases_all.get(&name) {
                            out.type_aliases.insert(name.clone(), alias.clone());
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
                            out.data_constructors.insert(name.clone(), wanted.clone());
                            for ctor in wanted {
                                if let Some(info) = ctor_info.get(&ctor) {
                                    out.ctors.insert(ctor, info.clone());
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
                    Export::Module(_) => {
                        // Handled in a second pass outside this
                        // function — see `expand_module_reexports`,
                        // which has access to the `ModuleRegistry`
                        // needed to look up the target's exports.
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

    out
}

/// Second pass over `out` to handle `module N` re-export clauses.
/// For every `module X` in the export list, find the matching
/// import (by alias or raw target name), look up the imported
/// module's `ModuleExports` in the registry, and merge those
/// items into `out`. `distill_exports` itself can't do this
/// because it doesn't hold a registry reference — so this lives
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
    for item in &spanned.value.exports {
        if let Export::Module(mn) = item {
            let re_exported_name: String = mn
                .parts
                .iter()
                .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                .collect::<Vec<_>>()
                .join(".");

            // Find which import target this `module X` clause
            // refers to: either an `import M as X` aliased as
            // `re_exported_name`, or the raw target `import
            // re_exported_name`.
            let mut target_module: Option<String> = None;
            for imp in &module.imports {
                let imp_target: String = imp
                    .module
                    .parts
                    .iter()
                    .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                    .collect::<Vec<_>>()
                    .join(".");
                if imp_target == re_exported_name {
                    target_module = Some(imp_target);
                    break;
                }
                if let Some(alias) = &imp.qualified {
                    let alias_str: String = alias
                        .parts
                        .iter()
                        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                        .collect::<Vec<_>>()
                        .join(".");
                    if alias_str == re_exported_name {
                        target_module = Some(imp_target);
                        break;
                    }
                }
            }
            let Some(target_name) = target_module else {
                continue;
            };
            // Re-export target may be a user module (in the
            // registry) OR a Prim submodule (not in the registry,
            // built from `prim::prim_exports`). Safe.Coerce relies
            // on the latter when it writes `module Prim.Coerce`.
            let prim_map = crate::typecheck_db::prim::prim_exports();
            let target_exports = match registry.get(&target_name) {
                Some(t) => t,
                None => match prim_map.get(&target_name) {
                    Some(t) => t,
                    None => continue,
                },
            };

            // Merge everything from the target. The target's items
            // become re-exported under this module — but the value
            // origin stays pointed at the *original* defining
            // module (follow the chain: if target has a recorded
            // origin, keep it; else fall back to the target itself).
            // When multiple re-exports contribute distinct
            // schemes under the same simple name, the primary
            // `values` map keeps the first (preserving existing
            // behavior) and the `qualified_values` map records
            // the rest so importers can still bind every origin
            // key.
            for (k, v) in &target_exports.values {
                let origin = target_exports
                    .value_origins
                    .get(k)
                    .cloned()
                    .unwrap_or_else(|| target_name.clone());
                out.qualified_values
                    .entry((origin.clone(), k.clone()))
                    .or_insert_with(|| v.clone());
                out.values.entry(k.clone()).or_insert_with(|| v.clone());
                out.value_origins.entry(k.clone()).or_insert(origin);
            }
            for (key, scheme) in &target_exports.qualified_values {
                out.qualified_values
                    .entry(key.clone())
                    .or_insert_with(|| scheme.clone());
            }
            for (k, v) in &target_exports.ctors {
                out.ctors.entry(k.clone()).or_insert_with(|| v.clone());
            }
            for (k, v) in &target_exports.data_constructors {
                out.data_constructors.entry(k.clone()).or_insert_with(|| v.clone());
            }
            for (k, v) in &target_exports.type_aliases {
                out.type_aliases.entry(k.clone()).or_insert_with(|| v.clone());
            }
            for (k, v) in &target_exports.classes {
                out.classes.entry(k.clone()).or_insert_with(|| v.clone());
            }
            // Instances are global — already carried via the
            // importer's own `instances` field, but re-exporting
            // them again is harmless and matches PureScript
            // semantics.
            for inst in &target_exports.instances {
                if !out.instances.iter().any(|i| i == inst) {
                    out.instances.push(inst.clone());
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
            }
        }
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
        Type::Con(QName::unqualified("Int"))
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
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new());
        assert!(exports.values.contains_key("foo"));
        assert!(exports.values.contains_key("bar"));
    }

    #[test]
    fn distill_no_export_clause_exports_data_ctors() {
        let m = parse_module("module M where\ndata Maybe a = Nothing | Just a\n");
        let mut ctors: HashMap<String, CtorInfo> = HashMap::new();
        ctors.insert(
            "Nothing".into(),
            CtorInfo { parent_type: "Maybe".into(), type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors);
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
            ClassInfo { type_vars: vec!["a".into()], fundeps: vec![] },
        );
        let instance = Instance {
            class: QName::unqualified("Eq"),
            types: vec![int_ty()],
            context: vec![],
            vars: vec![],
            chained: false,
        };
        let exports =
            distill_exports(&m, &[], std::slice::from_ref(&instance), &classes, &HashMap::new());
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
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new());
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
            CtorInfo { parent_type: "Maybe".into(), type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors);
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
            CtorInfo { parent_type: "Maybe".into(), type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors);
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
            CtorInfo { parent_type: "Maybe".into(), type_vars: vec!["a".into()], fields: vec![] },
        );
        ctors.insert(
            "Just".into(),
            CtorInfo {
                parent_type: "Maybe".into(),
                type_vars: vec!["a".into()],
                fields: vec![Type::Var("a".into())],
            },
        );
        let exports = distill_exports(&m, &[], &[], &HashMap::new(), &ctors);
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
            ClassInfo { type_vars: vec!["a".into()], fundeps: vec![] },
        );
        // Method scheme as it would appear after inference.
        let a = Type::Var("a".into());
        let method_scheme = Scheme {
            vars: vec!["a".into()],
            ty: Type::fun(
                a.clone(),
                Type::fun(a, Type::Con(QName::unqualified("Boolean"))),
            ),
        };
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
        let exports = distill_exports(&m, &schemes, &[], &classes, &HashMap::new());
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
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new());
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
        let add_scheme = Scheme {
            vars: vec!["a".into()],
            ty: Type::fun(a.clone(), Type::fun(a.clone(), a)),
        };
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
        let exports = distill_exports(&m, &schemes, &[], &HashMap::new(), &HashMap::new());
        assert!(exports.values.contains_key("add"));
        assert!(exports.value_fixities.contains_key("+"));
    }
}
