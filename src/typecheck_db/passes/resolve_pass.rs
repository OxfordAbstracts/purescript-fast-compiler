//! Single-pass name resolution.
//!
//! Exposes:
//! - [`build_module_scope`] — builds a `ModuleScope` used by the
//!   side-table resolver in `passes::names::resolve_names::compute`.
//! - [`resolve_module`] — walks an `ir::Module` and rewrites every
//!   `Qualified<N>::module` so it carries the DEFINING module's
//!   qualifier, never `None` and never an intermediate re-exporter.
//!
//! Both consume the registry's pre-computed origin maps
//! (`value_origins` / `type_origins` / `class_origins` /
//! `ctor_origins`) so re-exports through a wrapper module never
//! survive into downstream passes.

use std::collections::{HashMap, HashSet};

use crate::cst::{self, DataMembers, ImportList};
use crate::names::{
    module_qualifier, ClassName, ConstructorName, ModuleQualifier, Qualified, TypeName,
    TypeOpName, ValueName,
};
use crate::typecheck_db::ir;
use crate::typecheck_db::module_registry::{ModuleExports, ModuleRegistry};
use crate::typecheck_db::passes::names::{ModuleScope, NameKind};
use crate::typecheck_db::util::resolve_symbol;

/// Build a `ModuleScope` for `module` against `registry` + `prims`.
///
/// The returned scope's `imports` map every `(qualifier, name)` pair the
/// module brings into scope to the module that DEFINES that entity. If
/// `Prelude` re-exports `Data.Eq.Eq` and this module does
/// `import Prelude (class Eq)`, the resulting scope binds
/// `(None, "Eq")` → `ResolvedName { module: "Data.Eq", … }` — NOT
/// `"Prelude"`.
///
/// This is the heart of Phase 1: the resolver consumes the registry's
/// pre-computed origin maps so re-exports become invisible to downstream
/// passes.
pub fn build_module_scope(
    module: &cst::Module,
    registry: &ModuleRegistry,
    prims: &HashMap<String, ModuleExports>,
) -> ModuleScope {
    let self_module = module_name_string(&module.name.value);
    let mut scope = ModuleScope::new(self_module.clone());

    // Locally-defined names take precedence over any import.
    for decl in &module.decls {
        add_local_decl_names(&mut scope, decl);
    }

    // Prim is implicitly imported unqualified by every module.
    if let Some(prim) = prims.get("Prim") {
        add_module_imports(&mut scope, "Prim", prim, None, &None);
    }

    for imp in &module.imports {
        let target_name = module_name_string(&imp.module);
        let target = prims.get(&target_name).or_else(|| registry.get(&target_name));
        let Some(target) = target else { continue };

        let qualifier = imp.qualified.as_ref().map(module_name_string);
        add_module_imports(&mut scope, &target_name, target, qualifier, &imp.imports);
    }

    scope
}

// ---------------------------------------------------------------------------
// Local-decl name extraction
// ---------------------------------------------------------------------------

fn add_local_decl_names(scope: &mut ModuleScope, decl: &cst::Decl) {
    match decl {
        cst::Decl::Value { name, .. } | cst::Decl::TypeSignature { name, .. } => {
            scope.add_local(NameKind::Value, resolve_symbol(name.value.symbol()));
        }
        cst::Decl::Data { name, constructors, kind_sig, is_role_decl, .. } => {
            if *is_role_decl {
                return;
            }
            scope.add_local(NameKind::Type, resolve_symbol(name.value.symbol()));
            if matches!(*kind_sig, cst::KindSigSource::None) {
                for ctor in constructors {
                    scope.add_local(
                        NameKind::Constructor,
                        resolve_symbol(ctor.name.value.symbol()),
                    );
                }
            }
        }
        cst::Decl::TypeAlias { name, .. } => {
            scope.add_local(NameKind::Type, resolve_symbol(name.value.symbol()));
        }
        cst::Decl::Newtype { name, constructor, .. } => {
            scope.add_local(NameKind::Type, resolve_symbol(name.value.symbol()));
            scope.add_local(
                NameKind::Constructor,
                resolve_symbol(constructor.value.symbol()),
            );
        }
        cst::Decl::Class { name, members, is_kind_sig, .. } => {
            scope.add_local(NameKind::Class, resolve_symbol(name.value.symbol()));
            if !is_kind_sig {
                for m in members {
                    scope.add_local(NameKind::Value, resolve_symbol(m.name.value.symbol()));
                }
            }
        }
        cst::Decl::Instance { .. } | cst::Decl::Derive { .. } => {}
        cst::Decl::Fixity { operator, is_type, .. } => {
            let kind = if *is_type { NameKind::TypeOp } else { NameKind::Op };
            scope.add_local(kind, resolve_symbol(operator.value.symbol()));
        }
        cst::Decl::Foreign { name, .. } => {
            scope.add_local(NameKind::Value, resolve_symbol(name.value.symbol()));
        }
        cst::Decl::ForeignData { name, .. } => {
            scope.add_local(NameKind::Type, resolve_symbol(name.value.symbol()));
        }
    }
}

// ---------------------------------------------------------------------------
// Per-import resolution
// ---------------------------------------------------------------------------

fn add_module_imports(
    scope: &mut ModuleScope,
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<String>,
    list: &Option<ImportList>,
) {
    let filter = build_filter(list, target);

    add_values(scope, target_name, target, qualifier.as_deref(), &filter);
    add_types(scope, target_name, target, qualifier.as_deref(), &filter);
    add_classes(scope, target_name, target, qualifier.as_deref(), &filter);
    add_ctors(scope, target_name, target, qualifier.as_deref(), &filter);
    add_ops(scope, target_name, target, qualifier.as_deref(), &filter);
    add_type_ops(scope, target_name, target, qualifier.as_deref(), &filter);
}

fn add_values(
    scope: &mut ModuleScope,
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<&str>,
    filter: &ImportFilter,
) {
    for name in target.values.keys() {
        if !filter.allows(NameKind::Value, name) {
            continue;
        }
        let origin = origin_of(&target.value_origins, name, target_name);
        push_import(scope, NameKind::Value, qualifier, name, origin);
    }
}

fn add_types(
    scope: &mut ModuleScope,
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<&str>,
    filter: &ImportFilter,
) {
    // The set of type names a module exposes is the union of arities,
    // data-ctor map keys, and type-alias map keys. Iterate the union to
    // make sure aliases-without-arities aren't missed.
    let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for name in target
        .type_arities
        .keys()
        .chain(target.data_constructors.keys())
        .chain(target.type_aliases.keys())
    {
        if !seen.insert(name.as_str()) {
            continue;
        }
        if !filter.allows(NameKind::Type, name) {
            continue;
        }
        let origin = origin_of(&target.type_origins, name, target_name);
        push_import(scope, NameKind::Type, qualifier, name, origin);
    }
}

fn add_classes(
    scope: &mut ModuleScope,
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<&str>,
    filter: &ImportFilter,
) {
    for name in target.classes.keys() {
        if !filter.allows(NameKind::Class, name) {
            continue;
        }
        let origin = origin_of(&target.class_origins, name, target_name);
        push_import(scope, NameKind::Class, qualifier, name, origin);
    }
}

fn add_ctors(
    scope: &mut ModuleScope,
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<&str>,
    filter: &ImportFilter,
) {
    for name in target.ctors.keys() {
        if !filter.allows(NameKind::Constructor, name) {
            continue;
        }
        let origin = origin_of(&target.ctor_origins, name, target_name);
        push_import(scope, NameKind::Constructor, qualifier, name, origin);
    }
}

fn add_ops(
    scope: &mut ModuleScope,
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<&str>,
    filter: &ImportFilter,
) {
    for name in target.value_fixities.keys() {
        if !filter.allows(NameKind::Op, name) {
            continue;
        }
        // Operators are re-exported through `value_origins` (their
        // op-name lands in the value map alongside their fixity).
        // Defining module of the FIXITY is where its origin entry
        // points; fall back to the import target if absent.
        let origin = origin_of(&target.value_origins, name, target_name);
        push_import(scope, NameKind::Op, qualifier, name, origin);
    }
}

fn add_type_ops(
    scope: &mut ModuleScope,
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<&str>,
    filter: &ImportFilter,
) {
    for name in target.type_fixities.keys() {
        if !filter.allows(NameKind::TypeOp, name) {
            continue;
        }
        push_import(scope, NameKind::TypeOp, qualifier, name, target_name);
    }
}

fn push_import(
    scope: &mut ModuleScope,
    kind: NameKind,
    qualifier: Option<&str>,
    name: &str,
    origin_module: &str,
) {
    match qualifier {
        Some(q) => scope.add_qualified_import(kind, q, origin_module, name),
        None => scope.add_import(kind, name, origin_module, name),
    }
}

fn origin_of<'a>(
    origins: &'a HashMap<String, String>,
    name: &str,
    fallback: &'a str,
) -> &'a str {
    origins.get(name).map(String::as_str).unwrap_or(fallback)
}

// ---------------------------------------------------------------------------
// Import-list filter
// ---------------------------------------------------------------------------

#[derive(Debug, Default)]
struct ImportFilter {
    /// `None` = take everything (open import). `Some(true)` = explicit list (only listed pass).
    /// `Some(false)` = hiding list (everything except listed passes).
    mode: FilterMode,
    values: std::collections::HashSet<String>,
    types: std::collections::HashSet<String>,
    classes: std::collections::HashSet<String>,
    ctors: std::collections::HashSet<String>,
    ops: std::collections::HashSet<String>,
    type_ops: std::collections::HashSet<String>,
}

#[derive(Debug, Default, PartialEq, Eq)]
enum FilterMode {
    #[default]
    Open,
    Explicit,
    Hiding,
}

impl ImportFilter {
    fn allows(&self, kind: NameKind, name: &str) -> bool {
        let listed = match kind {
            NameKind::Value => self.values.contains(name),
            NameKind::Type => self.types.contains(name),
            NameKind::Class => self.classes.contains(name),
            NameKind::Constructor => self.ctors.contains(name),
            NameKind::Op => self.ops.contains(name),
            NameKind::TypeOp => self.type_ops.contains(name),
        };
        match self.mode {
            FilterMode::Open => true,
            FilterMode::Explicit => listed,
            FilterMode::Hiding => !listed,
        }
    }
}

fn build_filter(list: &Option<ImportList>, target: &ModuleExports) -> ImportFilter {
    let mut filter = ImportFilter::default();
    match list {
        None => filter.mode = FilterMode::Open,
        Some(ImportList::Explicit(items)) => {
            filter.mode = FilterMode::Explicit;
            for item in items {
                add_filter_item(&mut filter, item, target);
            }
        }
        Some(ImportList::Hiding(items)) => {
            filter.mode = FilterMode::Hiding;
            for item in items {
                add_filter_item(&mut filter, item, target);
            }
        }
    }
    filter
}

fn add_filter_item(filter: &mut ImportFilter, item: &cst::Import, target: &ModuleExports) {
    match item {
        cst::Import::Value(n) => {
            filter.values.insert(resolve_symbol(n.value.symbol()));
        }
        cst::Import::Type(n, members) => {
            let type_name = resolve_symbol(n.value.symbol());
            match members {
                None => {}
                Some(DataMembers::All) => {
                    // `T(..)` brings in every ctor of T. Look them up via
                    // the target module's data_constructors map.
                    if let Some(ctors) = target.data_constructors.get(&type_name) {
                        for ctor in ctors {
                            filter.ctors.insert(ctor.clone());
                        }
                    }
                }
                Some(DataMembers::Explicit(list)) => {
                    for c in list {
                        filter.ctors.insert(resolve_symbol(c.value.symbol()));
                    }
                }
            }
            filter.types.insert(type_name);
        }
        cst::Import::Class(n) => {
            filter.classes.insert(resolve_symbol(n.value.symbol()));
        }
        cst::Import::TypeOp(n) => {
            filter.type_ops.insert(resolve_symbol(n.value.symbol()));
        }
    }
}

fn module_name_string(m: &cst::ModuleName) -> String {
    m.parts.iter().map(|p| resolve_symbol(*p)).collect::<Vec<_>>().join(".")
}

// ===========================================================================
// resolve_module — tree-walking name normalizer
// ===========================================================================

/// Walk an `ir::Module` and rewrite every `Qualified<N>::module` so it
/// carries the DEFINING module's qualifier (never `None`, never an
/// intermediate re-exporter). Locally-defined names get the current
/// module's qualifier; imported names get their origin module from the
/// registry; locally-shadowed value names (lambda / let / case / do
/// binders) are left as-is (unqualified at the source position).
///
/// This is the load-bearing entry point: after this pass runs every
/// downstream consumer can treat `Qualified<N>::module` as if it were
/// non-optional (in Phase 5 we'll lock that in at the type level).
///
/// The pass preserves behavior: locally-shadowed names retain their
/// `None` qualifier so the existing local-binder lookup in `infer_var`
/// continues to fire. Top-level names that previously carried `None`
/// now carry `Some(origin)` — which the existing dual-key env binding
/// already accepts.
pub fn resolve_module(
    module: ir::Module,
    self_module: &str,
    registry: &ModuleRegistry,
    prims: &HashMap<String, ModuleExports>,
) -> ir::Module {
    let resolver = NameResolver::build(self_module, &module.imports, registry, prims);
    // Pre-scan local decls so locally-defined values / classes / types
    // route to the current module.
    let mut resolver = resolver;
    register_local_decls(&mut resolver, &module.decls, self_module);

    let mut new_decls = Vec::with_capacity(module.decls.len());
    for decl in module.decls {
        new_decls.push(rewrite_decl(&resolver, decl));
    }
    ir::Module { decls: new_decls, ..module }
}

/// Walk every `cst::TypeExpr` inside a `cst::Module`'s decls and
/// rewrite their qualifiers to point at the DEFINING module. Used by
/// `distill_exports` (which consumes cst::Module rather than ir::Module
/// so it can also access the export list and import declarations) to
/// ensure that exposed schemes / instance heads / class methods carry
/// resolved qualifiers in their `Type::Con` cells. Operates on the CST
/// in place — non-type CST nodes (Expr bodies, binders, etc.) are
/// untouched; only TypeExpr positions are rewritten.
pub fn resolve_cst_types_in_place(
    module: &mut cst::Module,
    self_module: &str,
    registry: &ModuleRegistry,
    prims: &HashMap<String, ModuleExports>,
) {
    let mut resolver = NameResolver::build(self_module, &module.imports, registry, prims);
    register_local_decls_cst(&mut resolver, &module.decls, self_module);
    for d in &mut module.decls {
        rewrite_cst_decl_types(&resolver, d);
    }
}

// ---------------------------------------------------------------------------
// NameResolver — fast lookup over imports + locals
// ---------------------------------------------------------------------------

/// Per-namespace resolver. Each map keys on `(qualifier, name)` —
/// qualifier `""` represents an unqualified reference. Lookup returns
/// the defining module's qualified string.
struct NameResolver {
    self_module: String,
    /// Imported / Prim'd values, keyed by (qualifier, name) → origin module.
    values: HashMap<(String, String), String>,
    types: HashMap<(String, String), String>,
    classes: HashMap<(String, String), String>,
    ctors: HashMap<(String, String), String>,
    /// Set of namespaces × name owned by this module's locals. Local
    /// definitions always take precedence over imports.
    local_values: HashSet<String>,
    local_types: HashSet<String>,
    local_classes: HashSet<String>,
    local_ctors: HashSet<String>,
}

impl NameResolver {
    fn build(
        self_module: &str,
        imports: &[cst::ImportDecl],
        registry: &ModuleRegistry,
        prims: &HashMap<String, ModuleExports>,
    ) -> Self {
        let mut r = NameResolver {
            self_module: self_module.to_string(),
            values: HashMap::new(),
            types: HashMap::new(),
            classes: HashMap::new(),
            ctors: HashMap::new(),
            local_values: HashSet::new(),
            local_types: HashSet::new(),
            local_classes: HashSet::new(),
            local_ctors: HashSet::new(),
        };

        // Prim is implicitly imported unqualified by every module.
        if let Some(prim) = prims.get("Prim") {
            r.add_module("Prim", prim, None, &None);
        }

        for imp in imports {
            let target_name = module_name_string(&imp.module);
            let target = prims.get(&target_name).or_else(|| registry.get(&target_name));
            let Some(target) = target else { continue };
            let qualifier = imp.qualified.as_ref().map(module_name_string);
            r.add_module(&target_name, target, qualifier, &imp.imports);
        }

        r
    }

    fn add_module(
        &mut self,
        target_name: &str,
        target: &ModuleExports,
        qualifier: Option<String>,
        list: &Option<ImportList>,
    ) {
        let filter = build_filter(list, target);
        let key_qual: &str = qualifier.as_deref().unwrap_or("");

        for name in target.values.keys() {
            if !filter.allows(NameKind::Value, name) {
                continue;
            }
            let origin = origin_of(&target.value_origins, name, target_name).to_string();
            self.values
                .insert((key_qual.to_string(), name.clone()), origin);
        }
        let mut seen: HashSet<&str> = HashSet::new();
        for name in target
            .type_arities
            .keys()
            .chain(target.data_constructors.keys())
            .chain(target.type_aliases.keys())
        {
            if !seen.insert(name.as_str()) {
                continue;
            }
            if !filter.allows(NameKind::Type, name) {
                continue;
            }
            let origin = origin_of(&target.type_origins, name, target_name).to_string();
            self.types
                .insert((key_qual.to_string(), name.clone()), origin);
        }
        for name in target.classes.keys() {
            if !filter.allows(NameKind::Class, name) {
                continue;
            }
            let origin = origin_of(&target.class_origins, name, target_name).to_string();
            self.classes
                .insert((key_qual.to_string(), name.clone()), origin);
        }
        for name in target.ctors.keys() {
            if !filter.allows(NameKind::Constructor, name) {
                continue;
            }
            let origin = origin_of(&target.ctor_origins, name, target_name).to_string();
            self.ctors
                .insert((key_qual.to_string(), name.clone()), origin);
        }
    }

    fn add_local_value(&mut self, name: &str) {
        self.local_values.insert(name.to_string());
    }
    fn add_local_type(&mut self, name: &str) {
        self.local_types.insert(name.to_string());
    }
    fn add_local_class(&mut self, name: &str) {
        self.local_classes.insert(name.to_string());
    }
    fn add_local_ctor(&mut self, name: &str) {
        self.local_ctors.insert(name.to_string());
    }

    fn resolve_value(&self, qualifier: Option<&str>, name: &str) -> Option<&str> {
        // Locally-defined module-level values resolve to
        // `Some(self_module)`. Lexical-scope refs (lambda / case /
        // let / where / do binders) are filtered upstream in
        // `rewrite_expr` by the `LocalScope` stack BEFORE this
        // function is consulted — so by the time we get here the
        // name is module-level and the resolved qualifier is the
        // defining module.
        if qualifier.is_none() && self.local_values.contains(name) {
            return Some(self.self_module.as_str());
        }
        self.values
            .get(&(qualifier.unwrap_or("").to_string(), name.to_string()))
            .map(String::as_str)
    }
    fn resolve_type(&self, qualifier: Option<&str>, name: &str) -> Option<&str> {
        if qualifier.is_none() && self.local_types.contains(name) {
            return Some(self.self_module.as_str());
        }
        self.types
            .get(&(qualifier.unwrap_or("").to_string(), name.to_string()))
            .map(String::as_str)
    }
    fn resolve_class(&self, qualifier: Option<&str>, name: &str) -> Option<&str> {
        if qualifier.is_none() && self.local_classes.contains(name) {
            return Some(self.self_module.as_str());
        }
        self.classes
            .get(&(qualifier.unwrap_or("").to_string(), name.to_string()))
            .map(String::as_str)
    }
    fn resolve_ctor(&self, qualifier: Option<&str>, name: &str) -> Option<&str> {
        if qualifier.is_none() && self.local_ctors.contains(name) {
            return Some(self.self_module.as_str());
        }
        self.ctors
            .get(&(qualifier.unwrap_or("").to_string(), name.to_string()))
            .map(String::as_str)
    }
}

fn register_local_decls(
    resolver: &mut NameResolver,
    decls: &[ir::Decl],
    _self_module: &str,
) {
    for d in decls {
        match d {
            ir::Decl::Value { name, .. } | ir::Decl::TypeSignature { name, .. } => {
                resolver.add_local_value(&resolve_symbol(name.value.symbol()));
            }
            ir::Decl::Data { name, constructors, kind_sig, is_role_decl, .. } => {
                if *is_role_decl {
                    continue;
                }
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
                if matches!(*kind_sig, crate::cst::KindSigSource::None) {
                    for ctor in constructors {
                        resolver.add_local_ctor(&resolve_symbol(ctor.name.value.symbol()));
                        // Constructors are also values (a ctor used in
                        // expr position).
                        resolver.add_local_value(&resolve_symbol(ctor.name.value.symbol()));
                    }
                }
            }
            ir::Decl::TypeAlias { name, .. } => {
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
            }
            ir::Decl::Newtype { name, constructor, .. } => {
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
                resolver.add_local_ctor(&resolve_symbol(constructor.value.symbol()));
                resolver.add_local_value(&resolve_symbol(constructor.value.symbol()));
            }
            ir::Decl::Class { name, members, is_kind_sig, .. } => {
                resolver.add_local_class(&resolve_symbol(name.value.symbol()));
                if !is_kind_sig {
                    for m in members {
                        resolver.add_local_value(&resolve_symbol(m.name.value.symbol()));
                    }
                }
            }
            ir::Decl::Foreign { name, .. } => {
                resolver.add_local_value(&resolve_symbol(name.value.symbol()));
            }
            ir::Decl::ForeignData { name, .. } => {
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
            }
            ir::Decl::Instance { .. }
            | ir::Decl::Derive { .. }
            | ir::Decl::Fixity { .. } => {}
        }
    }
}

/// Mirror of `register_local_decls` for the CST. Walks `cst::Decl`s
/// the same way the IR-side walker does but on the un-lowered form,
/// so the resolver can rewrite TypeExprs in cst::Module before
/// `distill_exports` reads them.
fn register_local_decls_cst(
    resolver: &mut NameResolver,
    decls: &[cst::Decl],
    _self_module: &str,
) {
    for d in decls {
        match d {
            cst::Decl::Value { name, .. } | cst::Decl::TypeSignature { name, .. } => {
                resolver.add_local_value(&resolve_symbol(name.value.symbol()));
            }
            cst::Decl::Data { name, constructors, kind_sig, is_role_decl, .. } => {
                if *is_role_decl {
                    continue;
                }
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
                if matches!(*kind_sig, cst::KindSigSource::None) {
                    for ctor in constructors {
                        resolver.add_local_ctor(&resolve_symbol(ctor.name.value.symbol()));
                        resolver.add_local_value(&resolve_symbol(ctor.name.value.symbol()));
                    }
                }
            }
            cst::Decl::TypeAlias { name, .. } => {
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
            }
            cst::Decl::Newtype { name, constructor, .. } => {
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
                resolver.add_local_ctor(&resolve_symbol(constructor.value.symbol()));
                resolver.add_local_value(&resolve_symbol(constructor.value.symbol()));
            }
            cst::Decl::Class { name, members, is_kind_sig, .. } => {
                resolver.add_local_class(&resolve_symbol(name.value.symbol()));
                if !is_kind_sig {
                    for m in members {
                        resolver.add_local_value(&resolve_symbol(m.name.value.symbol()));
                    }
                }
            }
            cst::Decl::Foreign { name, .. } => {
                resolver.add_local_value(&resolve_symbol(name.value.symbol()));
            }
            cst::Decl::ForeignData { name, .. } => {
                resolver.add_local_type(&resolve_symbol(name.value.symbol()));
            }
            cst::Decl::Instance { .. } | cst::Decl::Derive { .. } | cst::Decl::Fixity { .. } => {}
        }
    }
}

/// Rewrite every `cst::TypeExpr` reachable from a `cst::Decl` to
/// carry the resolved (defining-module) qualifier. Non-type fields
/// are left untouched; this is a TYPE-position rewrite only.
fn rewrite_cst_decl_types(r: &NameResolver, decl: &mut cst::Decl) {
    match decl {
        cst::Decl::TypeSignature { ty, .. } => {
            *ty = rewrite_type(r, std::mem::replace(ty, dummy_type()));
        }
        cst::Decl::Data { constructors, kind_type, type_var_kind_anns, .. } => {
            for c in constructors {
                let fields = std::mem::take(&mut c.fields);
                c.fields = fields.into_iter().map(|f| rewrite_type(r, f)).collect();
            }
            if let Some(k) = kind_type {
                let owned = std::mem::replace(k.as_mut(), dummy_type());
                **k = rewrite_type(r, owned);
            }
            for opt in type_var_kind_anns {
                if let Some(k) = opt {
                    let owned = std::mem::replace(k.as_mut(), dummy_type());
                    **k = rewrite_type(r, owned);
                }
            }
        }
        cst::Decl::TypeAlias { ty, type_var_kind_anns, .. } => {
            *ty = rewrite_type(r, std::mem::replace(ty, dummy_type()));
            for opt in type_var_kind_anns {
                if let Some(k) = opt {
                    let owned = std::mem::replace(k.as_mut(), dummy_type());
                    **k = rewrite_type(r, owned);
                }
            }
        }
        cst::Decl::Newtype { ty, type_var_kind_anns, .. } => {
            *ty = rewrite_type(r, std::mem::replace(ty, dummy_type()));
            for opt in type_var_kind_anns {
                if let Some(k) = opt {
                    let owned = std::mem::replace(k.as_mut(), dummy_type());
                    **k = rewrite_type(r, owned);
                }
            }
        }
        cst::Decl::Class { constraints, members, kind_type, type_var_kind_anns, .. } => {
            for c in constraints {
                rewrite_cst_constraint_in_place(r, c);
            }
            for m in members {
                m.ty = rewrite_type(r, std::mem::replace(&mut m.ty, dummy_type()));
            }
            if let Some(k) = kind_type {
                let owned = std::mem::replace(k.as_mut(), dummy_type());
                **k = rewrite_type(r, owned);
            }
            for opt in type_var_kind_anns {
                if let Some(k) = opt {
                    let owned = std::mem::replace(k.as_mut(), dummy_type());
                    **k = rewrite_type(r, owned);
                }
            }
        }
        cst::Decl::Instance { constraints, class_name, types, .. } => {
            *class_name = rewrite_class_name(r, *class_name);
            for c in constraints {
                rewrite_cst_constraint_in_place(r, c);
            }
            let owned = std::mem::take(types);
            *types = owned.into_iter().map(|t| rewrite_type(r, t)).collect();
            // Note: instance members carry expressions (Decl::Value)
            // whose types we'd rewrite via Type-position walking;
            // distill_exports doesn't recurse into instance method
            // bodies, so we skip them.
        }
        cst::Decl::Derive { constraints, class_name, types, .. } => {
            *class_name = rewrite_class_name(r, *class_name);
            for c in constraints {
                rewrite_cst_constraint_in_place(r, c);
            }
            let owned = std::mem::take(types);
            *types = owned.into_iter().map(|t| rewrite_type(r, t)).collect();
        }
        cst::Decl::Foreign { ty, .. } => {
            *ty = rewrite_type(r, std::mem::replace(ty, dummy_type()));
        }
        cst::Decl::ForeignData { kind, .. } => {
            *kind = rewrite_type(r, std::mem::replace(kind, dummy_type()));
        }
        cst::Decl::Value { .. } | cst::Decl::Fixity { .. } => {}
    }
}

fn rewrite_cst_constraint_in_place(r: &NameResolver, c: &mut cst::Constraint) {
    c.class = rewrite_class_name(r, c.class);
    let args = std::mem::take(&mut c.args);
    c.args = args.into_iter().map(|t| rewrite_type(r, t)).collect();
}

/// Cheap throwaway TypeExpr used as a placeholder during in-place
/// rewriting. Never observed by downstream code — the swap is
/// immediately replaced with the rewritten value.
fn dummy_type() -> cst::TypeExpr {
    cst::TypeExpr::Wildcard { span: crate::span::Span { start: 0, end: 0 } }
}

// ---------------------------------------------------------------------------
// Tree rewriting
// ---------------------------------------------------------------------------

fn rewrite_decl(r: &NameResolver, decl: ir::Decl) -> ir::Decl {
    match decl {
        ir::Decl::Value { span, name, binders, guarded, where_clause, doc_comments } => {
            let mut locals = LocalScope::default();
            // where-clause binders are mutually recursive — pre-collect.
            for wb in &where_clause {
                if let ir::LetBinding::Value { binder, .. } = wb {
                    collect_binder_locals(binder, &mut locals);
                }
            }
            for b in &binders {
                collect_binder_locals(b, &mut locals);
            }
            let binders = binders.into_iter().map(|b| rewrite_binder(r, &locals, b)).collect();
            let guarded = rewrite_guarded(r, &locals, guarded);
            let where_clause = where_clause
                .into_iter()
                .map(|wb| rewrite_let_binding(r, &locals, wb))
                .collect();
            ir::Decl::Value { span, name, binders, guarded, where_clause, doc_comments }
        }
        ir::Decl::TypeSignature { span, name, ty, doc_comments } => {
            ir::Decl::TypeSignature { span, name, ty: rewrite_type(r, ty), doc_comments }
        }
        ir::Decl::Data {
            span,
            name,
            type_vars,
            constructors,
            kind_sig,
            is_role_decl,
            kind_type,
            type_var_kind_anns,
            doc_comments,
        } => {
            let constructors = constructors
                .into_iter()
                .map(|mut c| {
                    c.fields = c.fields.into_iter().map(|f| rewrite_type(r, f)).collect();
                    c
                })
                .collect();
            let kind_type = kind_type.map(|k| Box::new(rewrite_type(r, *k)));
            let type_var_kind_anns = type_var_kind_anns
                .into_iter()
                .map(|opt| opt.map(|k| Box::new(rewrite_type(r, *k))))
                .collect();
            ir::Decl::Data {
                span,
                name,
                type_vars,
                constructors,
                kind_sig,
                is_role_decl,
                kind_type,
                type_var_kind_anns,
                doc_comments,
            }
        }
        ir::Decl::TypeAlias { span, name, type_vars, ty, type_var_kind_anns, doc_comments } => {
            let ty = rewrite_type(r, ty);
            let type_var_kind_anns = type_var_kind_anns
                .into_iter()
                .map(|opt| opt.map(|k| Box::new(rewrite_type(r, *k))))
                .collect();
            ir::Decl::TypeAlias { span, name, type_vars, ty, type_var_kind_anns, doc_comments }
        }
        ir::Decl::Newtype { span, name, type_vars, constructor, ty, type_var_kind_anns, doc_comments } => {
            let ty = rewrite_type(r, ty);
            let type_var_kind_anns = type_var_kind_anns
                .into_iter()
                .map(|opt| opt.map(|k| Box::new(rewrite_type(r, *k))))
                .collect();
            ir::Decl::Newtype { span, name, type_vars, constructor, ty, type_var_kind_anns, doc_comments }
        }
        ir::Decl::Class {
            span,
            constraints,
            name,
            type_vars,
            fundeps,
            members,
            is_kind_sig,
            kind_type,
            type_var_kind_anns,
            doc_comments,
        } => {
            let constraints = constraints.into_iter().map(|c| rewrite_constraint(r, c)).collect();
            let members = members
                .into_iter()
                .map(|mut m| {
                    m.ty = rewrite_type(r, m.ty);
                    m
                })
                .collect();
            let kind_type = kind_type.map(|k| Box::new(rewrite_type(r, *k)));
            let type_var_kind_anns = type_var_kind_anns
                .into_iter()
                .map(|opt| opt.map(|k| Box::new(rewrite_type(r, *k))))
                .collect();
            ir::Decl::Class {
                span,
                constraints,
                name,
                type_vars,
                fundeps,
                members,
                is_kind_sig,
                kind_type,
                type_var_kind_anns,
                doc_comments,
            }
        }
        ir::Decl::Instance { span, name, constraints, class_name, types, members, chain, doc_comments } => {
            let class_name = rewrite_class_name_resolved(r, class_name);
            let constraints = constraints.into_iter().map(|c| rewrite_constraint(r, c)).collect();
            let types = types.into_iter().map(|t| rewrite_type(r, t)).collect();
            let members = members.into_iter().map(|d| rewrite_decl(r, d)).collect();
            ir::Decl::Instance { span, name, constraints, class_name, types, members, chain, doc_comments }
        }
        ir::Decl::Derive { span, newtype, name, constraints, class_name, types, doc_comments } => {
            let class_name = rewrite_class_name_resolved(r, class_name);
            let constraints = constraints.into_iter().map(|c| rewrite_constraint(r, c)).collect();
            let types = types.into_iter().map(|t| rewrite_type(r, t)).collect();
            ir::Decl::Derive { span, newtype, name, constraints, class_name, types, doc_comments }
        }
        ir::Decl::Fixity { .. } | ir::Decl::Foreign { .. } | ir::Decl::ForeignData { .. } => {
            // Fixity targets are looked up downstream; leaving the
            // QualifiedIdent's optional module as-is here keeps the
            // existing fixity resolver behavior unchanged.
            // Foreign types' kinds are TypeExprs; rewrite them.
            match decl {
                ir::Decl::Foreign { span, name, ty, doc_comments } => {
                    ir::Decl::Foreign { span, name, ty: rewrite_type(r, ty), doc_comments }
                }
                ir::Decl::ForeignData { span, name, kind, doc_comments } => {
                    ir::Decl::ForeignData { span, name, kind: rewrite_type(r, kind), doc_comments }
                }
                ir::Decl::Fixity { .. } => decl,
                _ => unreachable!(),
            }
        }
    }
}

// LocalScope is a stack of HashSets so nested scopes can shadow outer ones.
#[derive(Debug, Default, Clone)]
struct LocalScope {
    /// Stack of frames. Each frame is the set of value names bound at
    /// that lexical depth. `is_local_value(n)` walks the stack for any
    /// match.
    frames: Vec<HashSet<String>>,
}

impl LocalScope {
    fn push(&mut self) {
        self.frames.push(HashSet::new());
    }
    fn pop(&mut self) {
        self.frames.pop();
    }
    fn bind(&mut self, name: &str) {
        if let Some(top) = self.frames.last_mut() {
            top.insert(name.to_string());
        } else {
            // No active frame — treat as the topmost (used for `Value`
            // decl's where-binders pre-scan).
            let mut s = HashSet::new();
            s.insert(name.to_string());
            self.frames.push(s);
        }
    }
    fn is_bound(&self, name: &str) -> bool {
        self.frames.iter().any(|f| f.contains(name))
    }
}

fn collect_binder_locals(b: &ir::Binder, locals: &mut LocalScope) {
    match b {
        ir::Binder::Wildcard { .. } | ir::Binder::Literal { .. } => {}
        ir::Binder::Var { name, .. } => locals.bind(&resolve_symbol(name.value.symbol())),
        ir::Binder::Constructor { args, .. } => {
            for a in args {
                collect_binder_locals(a, locals);
            }
        }
        ir::Binder::Record { fields, .. } => {
            for f in fields {
                match &f.binder {
                    Some(b) => collect_binder_locals(b, locals),
                    None => locals.bind(&resolve_symbol(f.label.value.symbol())),
                }
            }
        }
        ir::Binder::As { name, binder, .. } => {
            locals.bind(&resolve_symbol(name.value.symbol()));
            collect_binder_locals(binder, locals);
        }
        ir::Binder::Parens { binder, .. } => collect_binder_locals(binder, locals),
        ir::Binder::Array { elements, .. } => {
            for e in elements {
                collect_binder_locals(e, locals);
            }
        }
        ir::Binder::Typed { binder, .. } => collect_binder_locals(binder, locals),
    }
}

fn rewrite_expr(r: &NameResolver, locals: &LocalScope, e: ir::Expr) -> ir::Expr {
    use ir::Expr::*;
    match e {
        Var { span, name } => {
            // `name` is `Resolved<ValueName>` — module is always
            // present (sentinel for unresolved CST-side refs). If it
            // resolves to a locally-bound binder by unqualified name,
            // leave the sentinel in place so `infer_var` falls
            // through to the local-scope lookup.
            let q = if name.module.is_unresolved() {
                None
            } else {
                Some(resolve_symbol(name.module.symbol()))
            };
            let name_str = resolve_symbol(name.name.symbol());
            if q.is_none() && locals.is_bound(&name_str) {
                return Var { span, name };
            }
            let origin = r.resolve_value(q.as_deref(), &name_str);
            let new_name = match origin {
                Some(m) => crate::names::Resolved::new(module_qualifier(m), name.name),
                None => name,
            };
            Var { span, name: new_name }
        }
        Constructor { span, name } => {
            let q = if name.module.is_unresolved() {
                None
            } else {
                Some(resolve_symbol(name.module.symbol()))
            };
            let name_str = resolve_symbol(name.name.symbol());
            let origin = r.resolve_ctor(q.as_deref(), &name_str);
            let new_name = match origin {
                Some(m) => crate::names::Resolved::new(module_qualifier(m), name.name),
                None => name,
            };
            Constructor { span, name: new_name }
        }
        Literal { span, lit } => Literal { span, lit: rewrite_literal(r, locals, lit) },
        App { span, func, arg } => App {
            span,
            func: Box::new(rewrite_expr(r, locals, *func)),
            arg: Box::new(rewrite_expr(r, locals, *arg)),
        },
        VisibleTypeApp { span, func, ty } => VisibleTypeApp {
            span,
            func: Box::new(rewrite_expr(r, locals, *func)),
            ty: rewrite_type(r, ty),
        },
        Lambda { span, binders, body } => {
            let mut inner = locals.clone();
            inner.push();
            for b in &binders {
                collect_binder_locals(b, &mut inner);
            }
            let binders = binders.into_iter().map(|b| rewrite_binder(r, &inner, b)).collect();
            let body = Box::new(rewrite_expr(r, &inner, *body));
            Lambda { span, binders, body }
        }
        If { span, cond, then_expr, else_expr } => If {
            span,
            cond: Box::new(rewrite_expr(r, locals, *cond)),
            then_expr: Box::new(rewrite_expr(r, locals, *then_expr)),
            else_expr: Box::new(rewrite_expr(r, locals, *else_expr)),
        },
        Case { span, exprs, alts } => Case {
            span,
            exprs: exprs.into_iter().map(|e| rewrite_expr(r, locals, e)).collect(),
            alts: alts.into_iter().map(|a| rewrite_case_alt(r, locals, a)).collect(),
        },
        Let { span, bindings, body, is_where } => {
            let mut inner = locals.clone();
            inner.push();
            for b in &bindings {
                if let ir::LetBinding::Value { binder, .. } = b {
                    collect_binder_locals(binder, &mut inner);
                }
            }
            let bindings = bindings.into_iter().map(|b| rewrite_let_binding(r, &inner, b)).collect();
            let body = Box::new(rewrite_expr(r, &inner, *body));
            Let { span, bindings, body, is_where }
        }
        Do { span, module, statements } => {
            let mut inner = locals.clone();
            inner.push();
            let statements = statements
                .into_iter()
                .map(|s| rewrite_do_stmt(r, &mut inner, s))
                .collect();
            Do { span, module, statements }
        }
        Ado { span, module, statements, result } => {
            let mut inner = locals.clone();
            inner.push();
            let statements = statements
                .into_iter()
                .map(|s| rewrite_do_stmt(r, &mut inner, s))
                .collect();
            let result = Box::new(rewrite_expr(r, &inner, *result));
            Ado { span, module, statements, result }
        }
        Record { span, fields } => Record {
            span,
            fields: fields
                .into_iter()
                .map(|f| ir::RecordField {
                    value: f.value.map(|e| rewrite_expr(r, locals, e)),
                    type_ann: f.type_ann.map(|t| rewrite_type(r, t)),
                    ..f
                })
                .collect(),
        },
        RecordAccess { span, expr, field } => RecordAccess {
            span,
            expr: Box::new(rewrite_expr(r, locals, *expr)),
            field,
        },
        RecordUpdate { span, expr, updates } => RecordUpdate {
            span,
            expr: Box::new(rewrite_expr(r, locals, *expr)),
            updates: updates
                .into_iter()
                .map(|u| ir::RecordUpdate { value: rewrite_expr(r, locals, u.value), ..u })
                .collect(),
        },
        Parens { span, expr } => Parens { span, expr: Box::new(rewrite_expr(r, locals, *expr)) },
        TypeAnnotation { span, expr, ty } => TypeAnnotation {
            span,
            expr: Box::new(rewrite_expr(r, locals, *expr)),
            ty: rewrite_type(r, ty),
        },
        Array { span, elements } => Array {
            span,
            elements: elements.into_iter().map(|e| rewrite_expr(r, locals, e)).collect(),
        },
        Negate { span, expr } => Negate { span, expr: Box::new(rewrite_expr(r, locals, *expr)) },
        AsPattern { span, name, pattern } => AsPattern {
            span,
            name: Box::new(rewrite_expr(r, locals, *name)),
            pattern: Box::new(rewrite_expr(r, locals, *pattern)),
        },
        Wildcard { span } => Wildcard { span },
        Hole { span, name } => Hole { span, name },
    }
}

fn rewrite_literal(r: &NameResolver, locals: &LocalScope, lit: ir::Literal) -> ir::Literal {
    match lit {
        ir::Literal::Array(es) => {
            ir::Literal::Array(es.into_iter().map(|e| rewrite_expr(r, locals, e)).collect())
        }
        other => other,
    }
}

fn rewrite_binder(r: &NameResolver, locals: &LocalScope, b: ir::Binder) -> ir::Binder {
    match b {
        ir::Binder::Constructor { span, name, args } => {
            let q = if name.module.is_unresolved() {
                None
            } else {
                Some(resolve_symbol(name.module.symbol()))
            };
            let name_str = resolve_symbol(name.name.symbol());
            let origin = r.resolve_ctor(q.as_deref(), &name_str);
            let new_name = match origin {
                Some(m) => crate::names::Resolved::new(module_qualifier(m), name.name),
                None => name,
            };
            let args = args.into_iter().map(|a| rewrite_binder(r, locals, a)).collect();
            ir::Binder::Constructor { span, name: new_name, args }
        }
        ir::Binder::Record { span, fields } => ir::Binder::Record {
            span,
            fields: fields
                .into_iter()
                .map(|f| ir::RecordBinderField {
                    binder: f.binder.map(|b| rewrite_binder(r, locals, b)),
                    ..f
                })
                .collect(),
        },
        ir::Binder::As { span, name, binder } => ir::Binder::As {
            span,
            name,
            binder: Box::new(rewrite_binder(r, locals, *binder)),
        },
        ir::Binder::Parens { span, binder } => ir::Binder::Parens {
            span,
            binder: Box::new(rewrite_binder(r, locals, *binder)),
        },
        ir::Binder::Array { span, elements } => ir::Binder::Array {
            span,
            elements: elements.into_iter().map(|e| rewrite_binder(r, locals, e)).collect(),
        },
        ir::Binder::Typed { span, binder, ty } => ir::Binder::Typed {
            span,
            binder: Box::new(rewrite_binder(r, locals, *binder)),
            ty: rewrite_type(r, ty),
        },
        other => other,
    }
}

fn rewrite_guarded(r: &NameResolver, locals: &LocalScope, g: ir::GuardedExpr) -> ir::GuardedExpr {
    match g {
        ir::GuardedExpr::Unconditional(e) => {
            ir::GuardedExpr::Unconditional(Box::new(rewrite_expr(r, locals, *e)))
        }
        ir::GuardedExpr::Guarded(guards) => ir::GuardedExpr::Guarded(
            guards
                .into_iter()
                .map(|g| {
                    let mut inner = locals.clone();
                    inner.push();
                    let patterns = g
                        .patterns
                        .into_iter()
                        .map(|p| rewrite_guard_pat(r, &mut inner, p))
                        .collect();
                    let expr = Box::new(rewrite_expr(r, &inner, *g.expr));
                    ir::Guard { span: g.span, patterns, expr }
                })
                .collect(),
        ),
    }
}

fn rewrite_guard_pat(
    r: &NameResolver,
    locals: &mut LocalScope,
    p: ir::GuardPattern,
) -> ir::GuardPattern {
    match p {
        ir::GuardPattern::Boolean(e) => ir::GuardPattern::Boolean(Box::new(rewrite_expr(r, locals, *e))),
        ir::GuardPattern::Pattern(binder, e) => {
            collect_binder_locals(&binder, locals);
            let binder = rewrite_binder(r, locals, binder);
            ir::GuardPattern::Pattern(binder, Box::new(rewrite_expr(r, locals, *e)))
        }
    }
}

fn rewrite_case_alt(r: &NameResolver, locals: &LocalScope, alt: ir::CaseAlternative) -> ir::CaseAlternative {
    let mut inner = locals.clone();
    inner.push();
    for b in &alt.binders {
        collect_binder_locals(b, &mut inner);
    }
    let binders = alt.binders.into_iter().map(|b| rewrite_binder(r, &inner, b)).collect();
    let result = rewrite_guarded(r, &inner, alt.result);
    ir::CaseAlternative { span: alt.span, binders, result }
}

fn rewrite_let_binding(r: &NameResolver, locals: &LocalScope, b: ir::LetBinding) -> ir::LetBinding {
    match b {
        ir::LetBinding::Value { span, binder, expr } => {
            let binder = rewrite_binder(r, locals, binder);
            let expr = rewrite_expr(r, locals, expr);
            ir::LetBinding::Value { span, binder, expr }
        }
        ir::LetBinding::Signature { span, name, ty } => ir::LetBinding::Signature {
            span,
            name,
            ty: rewrite_type(r, ty),
        },
    }
}

fn rewrite_do_stmt(
    r: &NameResolver,
    locals: &mut LocalScope,
    s: ir::DoStatement,
) -> ir::DoStatement {
    match s {
        ir::DoStatement::Bind { span, binder, expr } => {
            // The expr is evaluated in the enclosing scope, then the
            // binder's names are added for subsequent statements.
            let expr = rewrite_expr(r, locals, expr);
            collect_binder_locals(&binder, locals);
            let binder = rewrite_binder(r, locals, binder);
            ir::DoStatement::Bind { span, binder, expr }
        }
        ir::DoStatement::Let { span, bindings } => {
            for b in &bindings {
                if let ir::LetBinding::Value { binder, .. } = b {
                    collect_binder_locals(binder, locals);
                }
            }
            let bindings = bindings.into_iter().map(|b| rewrite_let_binding(r, locals, b)).collect();
            ir::DoStatement::Let { span, bindings }
        }
        ir::DoStatement::Discard { span, expr } => {
            ir::DoStatement::Discard { span, expr: rewrite_expr(r, locals, expr) }
        }
    }
}

fn rewrite_constraint(r: &NameResolver, c: cst::Constraint) -> cst::Constraint {
    let class = rewrite_class_name(r, c.class);
    let args = c.args.into_iter().map(|a| rewrite_type(r, a)).collect();
    cst::Constraint { class, args, ..c }
}

fn rewrite_class_name(r: &NameResolver, q: Qualified<ClassName>) -> Qualified<ClassName> {
    let qual = q.module.map(|m| resolve_symbol(m.symbol()));
    let name_str = resolve_symbol(q.name.symbol());
    let origin = r.resolve_class(qual.as_deref(), &name_str);
    match origin {
        Some(m) => Qualified {
            module: Some(module_qualifier(m)),
            name: q.name,
        },
        None => q,
    }
}

/// `rewrite_class_name` variant for the IR's `Resolved<ClassName>`
/// positions. Same lookup, different wrapper.
fn rewrite_class_name_resolved(
    r: &NameResolver,
    q: crate::names::Resolved<ClassName>,
) -> crate::names::Resolved<ClassName> {
    let qual = if q.module.is_unresolved() {
        None
    } else {
        Some(resolve_symbol(q.module.symbol()))
    };
    let name_str = resolve_symbol(q.name.symbol());
    let origin = r.resolve_class(qual.as_deref(), &name_str);
    match origin {
        Some(m) => crate::names::Resolved::new(module_qualifier(m), q.name),
        None => q,
    }
}

fn rewrite_type(r: &NameResolver, ty: cst::TypeExpr) -> cst::TypeExpr {
    use cst::TypeExpr::*;
    match ty {
        Constructor { span, name } => {
            let qual = name.module.map(|m| resolve_symbol(m.symbol()));
            let name_str = resolve_symbol(name.name.symbol());
            let origin = r.resolve_type(qual.as_deref(), &name_str);
            let new_name = match origin {
                Some(m) => Qualified {
                    module: Some(module_qualifier(m)),
                    name: name.name,
                },
                None => name,
            };
            Constructor { span, name: new_name }
        }
        App { span, constructor, arg } => App {
            span,
            constructor: Box::new(rewrite_type(r, *constructor)),
            arg: Box::new(rewrite_type(r, *arg)),
        },
        Function { span, from, to } => Function {
            span,
            from: Box::new(rewrite_type(r, *from)),
            to: Box::new(rewrite_type(r, *to)),
        },
        Forall { span, vars, ty } => {
            let vars = vars
                .into_iter()
                .map(|(s, v, k)| (s, v, k.map(|kk| Box::new(rewrite_type(r, *kk)))))
                .collect();
            Forall { span, vars, ty: Box::new(rewrite_type(r, *ty)) }
        }
        Constrained { span, constraints, ty } => Constrained {
            span,
            constraints: constraints.into_iter().map(|c| rewrite_constraint(r, c)).collect(),
            ty: Box::new(rewrite_type(r, *ty)),
        },
        Record { span, fields } => Record {
            span,
            fields: fields
                .into_iter()
                .map(|f| cst::TypeField { ty: rewrite_type(r, f.ty), ..f })
                .collect(),
        },
        Row { span, fields, tail, is_record } => Row {
            span,
            fields: fields
                .into_iter()
                .map(|f| cst::TypeField { ty: rewrite_type(r, f.ty), ..f })
                .collect(),
            tail: tail.map(|t| Box::new(rewrite_type(r, *t))),
            is_record,
        },
        Parens { span, ty } => Parens { span, ty: Box::new(rewrite_type(r, *ty)) },
        TypeOp { span, left, op, right } => {
            // TypeOps are looked up by op name → fixity → target type;
            // rewriting their qualifier here is harmless and consistent
            // (resolve_type_op handles the per-namespace lookup).
            let resolved_op = rewrite_type_op_name(r, op);
            TypeOp {
                span,
                left: Box::new(rewrite_type(r, *left)),
                op: resolved_op,
                right: Box::new(rewrite_type(r, *right)),
            }
        }
        Kinded { span, ty, kind } => Kinded {
            span,
            ty: Box::new(rewrite_type(r, *ty)),
            kind: Box::new(rewrite_type(r, *kind)),
        },
        ArrayPattern { span, elements } => ArrayPattern {
            span,
            elements: elements.into_iter().map(|e| rewrite_type(r, e)).collect(),
        },
        AsPattern { span, name, ty } => AsPattern {
            span,
            name,
            ty: Box::new(rewrite_type(r, *ty)),
        },
        // Vars, holes, wildcards, literals: no qualifier to resolve.
        Var { span, name } => Var { span, name },
        Hole { span, name } => Hole { span, name },
        Wildcard { span } => Wildcard { span },
        StringLiteral { span, value } => StringLiteral { span, value },
        IntLiteral { span, value } => IntLiteral { span, value },
    }
}

fn rewrite_type_op_name(
    _r: &NameResolver,
    op: cst::Spanned<Qualified<TypeOpName>>,
) -> cst::Spanned<Qualified<TypeOpName>> {
    // Type-op origins aren't currently tracked in a dedicated map;
    // leave the qualifier as the source carried.  Downstream fixity
    // lookup remains source-of-truth for resolving the operator to
    // its target type.
    op
}

// ===========================================================================
// Tests — re-export resolution semantics
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::module_registry::ModuleRegistry;
    use crate::typecheck_db::passes::instance_index::ClassInfo;
    use crate::typecheck_db::passes::names::{
        free_names, resolve_names, FreeNames, NameKind, Reference,
    };
    use crate::typecheck_db::prim::prim_exports;
    use crate::typecheck_db::types::{Scheme, Type, QName};

    fn parse_mod(src: &str) -> cst::Module {
        parse(src).expect("parse")
    }

    fn int_scheme() -> Scheme {
        Scheme::mono(Type::Con(QName::unqualified("Int")))
    }

    /// `Data.Eq` defines `class Eq`, `Eq.eq`; `Prelude` re-exports both.
    fn registry_with_reexports() -> ModuleRegistry {
        let mut r = ModuleRegistry::new();

        // Data.Eq — defines Eq + eq.
        let mut data_eq = ModuleExports::default();
        data_eq.classes.insert("Eq".into(), ClassInfo {
            type_vars: vec!["a".into()],
            fundeps: vec![],
            superclasses: vec![],
        });
        data_eq.class_origins.insert("Eq".into(), "Data.Eq".into());
        data_eq
            .values
            .insert("eq".into(), std::sync::Arc::new(int_scheme()));
        data_eq.value_origins.insert("eq".into(), "Data.Eq".into());
        r.insert("Data.Eq", data_eq);

        // Control.Apply — defines `apply`.
        let mut control_apply = ModuleExports::default();
        control_apply
            .values
            .insert("apply".into(), std::sync::Arc::new(int_scheme()));
        control_apply
            .value_origins
            .insert("apply".into(), "Control.Apply".into());
        r.insert("Control.Apply", control_apply);

        // Data.Maybe — defines `data Maybe` (no ctors needed for these tests).
        let mut data_maybe = ModuleExports::default();
        data_maybe.type_arities.insert("Maybe".into(), 1);
        data_maybe
            .type_origins
            .insert("Maybe".into(), "Data.Maybe".into());
        r.insert("Data.Maybe", data_maybe);

        // Prelude re-exports `Eq`, `eq`, `apply`, `Maybe` — origin maps
        // point at the DEFINING modules even though they live under
        // Prelude's name.
        let mut prelude = ModuleExports::default();
        prelude.classes.insert("Eq".into(), ClassInfo {
            type_vars: vec!["a".into()],
            fundeps: vec![],
            superclasses: vec![],
        });
        prelude.class_origins.insert("Eq".into(), "Data.Eq".into());
        prelude
            .values
            .insert("eq".into(), std::sync::Arc::new(int_scheme()));
        prelude.value_origins.insert("eq".into(), "Data.Eq".into());
        prelude
            .values
            .insert("apply".into(), std::sync::Arc::new(int_scheme()));
        prelude
            .value_origins
            .insert("apply".into(), "Control.Apply".into());
        prelude.type_arities.insert("Maybe".into(), 1);
        prelude
            .type_origins
            .insert("Maybe".into(), "Data.Maybe".into());
        r.insert("Prelude", prelude);

        r
    }

    fn resolve_for(scope: &ModuleScope, refs: Vec<Reference>) -> Vec<(Reference, String)> {
        let free = FreeNames { refs };
        let res = resolve_names::compute(&free, scope);
        res.resolved
            .into_iter()
            .map(|(r, rn)| (r, rn.module))
            .collect()
    }

    #[test]
    fn re_exported_value_resolves_to_defining_module() {
        let module = parse_mod("module M where\nimport Prelude\n");
        let scope = build_module_scope(&module, &registry_with_reexports(), &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![Reference {
                kind: NameKind::Value,
                module: None,
                name: "apply".into(),
            }],
        );
        assert_eq!(pairs.len(), 1);
        // Defining module is Control.Apply, NOT Prelude.
        assert_eq!(pairs[0].1, "Control.Apply");
    }

    #[test]
    fn re_exported_class_resolves_to_defining_module() {
        let module = parse_mod("module M where\nimport Prelude\n");
        let scope = build_module_scope(&module, &registry_with_reexports(), &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![Reference {
                kind: NameKind::Class,
                module: None,
                name: "Eq".into(),
            }],
        );
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].1, "Data.Eq");
    }

    #[test]
    fn re_exported_type_resolves_to_defining_module() {
        let module = parse_mod("module M where\nimport Prelude\n");
        let scope = build_module_scope(&module, &registry_with_reexports(), &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![Reference {
                kind: NameKind::Type,
                module: None,
                name: "Maybe".into(),
            }],
        );
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].1, "Data.Maybe");
    }

    #[test]
    fn qualified_import_alias_resolves_through_origin() {
        // `import Prelude as P` then `P.apply`. The qualifier in source
        // is `P`, but the resolved module must be `Control.Apply` (the
        // definer), not `Prelude` (the re-exporter) or `P` (the alias).
        let module = parse_mod("module M where\nimport Prelude as P\n");
        let scope = build_module_scope(&module, &registry_with_reexports(), &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![Reference {
                kind: NameKind::Value,
                module: Some("P".into()),
                name: "apply".into(),
            }],
        );
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].1, "Control.Apply");
    }

    #[test]
    fn explicit_import_filter_restricts_brought_names() {
        let module = parse_mod("module M where\nimport Prelude (apply)\n");
        let scope = build_module_scope(&module, &registry_with_reexports(), &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![
                Reference {
                    kind: NameKind::Value,
                    module: None,
                    name: "apply".into(),
                },
                Reference {
                    kind: NameKind::Value,
                    module: None,
                    name: "eq".into(),
                },
            ],
        );
        // `apply` resolves to defining module; `eq` is unresolved
        // because it wasn't in the explicit list.
        let by_name: HashMap<String, String> =
            pairs.into_iter().map(|(r, m)| (r.name, m)).collect();
        assert_eq!(by_name.get("apply").map(String::as_str), Some("Control.Apply"));
        assert!(!by_name.contains_key("eq"));
    }

    #[test]
    fn re_exported_operator_resolves_to_defining_module() {
        use crate::cst::Associativity;
        use crate::typecheck_db::module_registry::FixityDecl;
        let mut r = registry_with_reexports();

        // Control.Apply — defines the `$` operator (aliased to `apply`).
        let control_apply = r
            .get("Control.Apply")
            .cloned()
            .expect("Control.Apply seeded");
        let mut control_apply = control_apply;
        control_apply.value_fixities.insert(
            "$".into(),
            FixityDecl {
                associativity: Associativity::Right,
                precedence: 0,
                target_module: Some("Control.Apply".into()),
                target_name: "apply".into(),
            },
        );
        control_apply
            .values
            .insert("$".into(), std::sync::Arc::new(int_scheme()));
        control_apply
            .value_origins
            .insert("$".into(), "Control.Apply".into());
        r.insert("Control.Apply", control_apply);

        // Prelude re-exports `$` — origin must point at Control.Apply.
        let prelude = r.get("Prelude").cloned().expect("Prelude seeded");
        let mut prelude = prelude;
        prelude.value_fixities.insert(
            "$".into(),
            FixityDecl {
                associativity: Associativity::Right,
                precedence: 0,
                target_module: Some("Control.Apply".into()),
                target_name: "apply".into(),
            },
        );
        prelude
            .values
            .insert("$".into(), std::sync::Arc::new(int_scheme()));
        prelude
            .value_origins
            .insert("$".into(), "Control.Apply".into());
        r.insert("Prelude", prelude);

        let module = parse_mod("module M where\nimport Prelude\n");
        let scope = build_module_scope(&module, &r, &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![Reference {
                kind: NameKind::Op,
                module: None,
                name: "$".into(),
            }],
        );
        assert_eq!(pairs.len(), 1);
        // Defining module is Control.Apply, NOT Prelude.
        assert_eq!(pairs[0].1, "Control.Apply");
    }

    #[test]
    fn data_members_all_brings_in_all_ctors() {
        // Build a registry where `Data.Maybe` exposes `Maybe` plus two
        // ctors. `import Data.Maybe (Maybe(..))` must bring in BOTH
        // ctors with their defining-module origin.
        let mut r = registry_with_reexports();
        let mut data_maybe = ModuleExports::default();
        data_maybe.type_arities.insert("Maybe".into(), 1);
        data_maybe
            .type_origins
            .insert("Maybe".into(), "Data.Maybe".into());
        data_maybe.data_constructors.insert(
            "Maybe".into(),
            vec!["Nothing".into(), "Just".into()],
        );
        for ctor in ["Nothing", "Just"] {
            data_maybe.ctors.insert(
                ctor.into(),
                crate::typecheck_db::passes::exhaustiveness::CtorInfo {
                    parent_type: "Maybe".into(),
                    parent_module: None,
                    type_vars: vec!["a".into()],
                    fields: vec![],
                },
            );
            data_maybe
                .ctor_origins
                .insert(ctor.into(), "Data.Maybe".into());
        }
        r.insert("Data.Maybe", data_maybe);

        let module = parse_mod("module M where\nimport Data.Maybe (Maybe(..))\n");
        let scope = build_module_scope(&module, &r, &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![
                Reference {
                    kind: NameKind::Constructor,
                    module: None,
                    name: "Just".into(),
                },
                Reference {
                    kind: NameKind::Constructor,
                    module: None,
                    name: "Nothing".into(),
                },
            ],
        );
        let by_name: HashMap<String, String> =
            pairs.into_iter().map(|(r, m)| (r.name, m)).collect();
        assert_eq!(
            by_name.get("Just").map(String::as_str),
            Some("Data.Maybe")
        );
        assert_eq!(
            by_name.get("Nothing").map(String::as_str),
            Some("Data.Maybe")
        );
    }

    /// Lower a parsed module to IR using the same desugar pipeline the
    /// real driver uses.
    fn lower(src: &str) -> ir::Module {
        use crate::typecheck_db::desugar::{
            desugar_module, fixity_table_from_decls, DesugarContext,
        };
        let module = parse_mod(src);
        let (fixity_table, module_fixity_hash) = fixity_table_from_decls(&module.decls);
        let ctx = DesugarContext { module_fixity_hash, fixity_table, qualified_fixity_table: Default::default() };
        let decls = desugar_module(module.decls.clone(), &ctx);
        let desugared = cst::Module {
            span: module.span,
            name: module.name,
            exports: module.exports,
            imports: module.imports,
            decls,
            comments: module.comments,
            doc_comments: module.doc_comments,
        };
        ir::lower_module(desugared).expect("lower")
    }

    fn module_of(name: &Qualified<impl crate::names::NameLike>) -> Option<String> {
        name.module.map(|m| resolve_symbol(m.symbol()))
    }

    fn resolved_module_of(
        name: &crate::names::Resolved<impl crate::names::NameLike>,
    ) -> Option<String> {
        if name.module.is_unresolved() {
            None
        } else {
            Some(resolve_symbol(name.module.symbol()))
        }
    }

    #[test]
    fn resolve_module_rewrites_re_exported_value() {
        // `M` imports Prelude unqualified, references `apply`. After
        // resolve_module, the Var node must carry Some("Control.Apply").
        let module = lower("module M where\nimport Prelude\nfoo = apply\n");
        let resolved = resolve_module(
            module,
            "M",
            &registry_with_reexports(),
            &prim_exports(),
        );
        // Find the `foo` decl's body and confirm its `apply` reference
        // carries the defining module.
        for d in &resolved.decls {
            if let ir::Decl::Value { name, guarded, .. } = d {
                if resolve_symbol(name.value.symbol()) != "foo" {
                    continue;
                }
                if let ir::GuardedExpr::Unconditional(e) = guarded {
                    if let ir::Expr::Var { name, .. } = &**e {
                        assert_eq!(resolved_module_of(name).as_deref(), Some("Control.Apply"));
                        return;
                    }
                }
            }
        }
        panic!("no Var(apply) found in resolved module");
    }

    #[test]
    fn resolve_module_rewrites_re_exported_class_in_instance_head() {
        // `instance Eq M where eq _ _ = true` after `import Prelude`.
        // The class_name's module must resolve to Data.Eq.
        let module = lower(
            "module M where\nimport Prelude\ndata X = X\ninstance Eq X where\n  eq _ _ = true\n",
        );
        let resolved = resolve_module(
            module,
            "M",
            &registry_with_reexports(),
            &prim_exports(),
        );
        for d in &resolved.decls {
            if let ir::Decl::Instance { class_name, .. } = d {
                if resolve_symbol(class_name.name.symbol()) == "Eq" {
                    assert_eq!(resolved_module_of(class_name).as_deref(), Some("Data.Eq"));
                    return;
                }
            }
        }
        panic!("no Eq instance found");
    }

    #[test]
    fn resolve_module_leaves_locally_bound_names_unqualified() {
        // `\x -> x` — the inner `x` is locally bound, must stay
        // unqualified after resolve.
        let module = lower("module M where\nimport Prelude\nfoo = \\x -> x\n");
        let resolved = resolve_module(
            module,
            "M",
            &registry_with_reexports(),
            &prim_exports(),
        );
        for d in &resolved.decls {
            if let ir::Decl::Value { guarded, .. } = d {
                if let ir::GuardedExpr::Unconditional(e) = guarded {
                    if let ir::Expr::Lambda { body, .. } = &**e {
                        if let ir::Expr::Var { name, .. } = &**body {
                            // Local binder — module stays as the
                            // unresolved sentinel (resolver doesn't
                            // rewrite locally-bound refs).
                            assert!(
                                name.module.is_unresolved(),
                                "expected unresolved, got {:?}",
                                name.module
                            );
                            return;
                        }
                    }
                }
            }
        }
        panic!("expected lambda body");
    }

    #[test]
    fn hiding_list_excludes_listed_names() {
        let module = parse_mod("module M where\nimport Prelude hiding (eq)\n");
        let scope = build_module_scope(&module, &registry_with_reexports(), &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![
                Reference {
                    kind: NameKind::Value,
                    module: None,
                    name: "apply".into(),
                },
                Reference {
                    kind: NameKind::Value,
                    module: None,
                    name: "eq".into(),
                },
            ],
        );
        let by_name: HashMap<String, String> =
            pairs.into_iter().map(|(r, m)| (r.name, m)).collect();
        // `apply` still resolves (not hidden).
        assert_eq!(by_name.get("apply").map(String::as_str), Some("Control.Apply"));
        // `eq` was hidden → unresolved.
        assert!(!by_name.contains_key("eq"));
    }

    #[test]
    fn local_decl_takes_precedence_over_import() {
        let module = parse_mod(
            "module M where\nimport Prelude\napply = 1\n",
        );
        let scope = build_module_scope(&module, &registry_with_reexports(), &prim_exports());
        let pairs = resolve_for(
            &scope,
            vec![Reference {
                kind: NameKind::Value,
                module: None,
                name: "apply".into(),
            }],
        );
        assert_eq!(pairs.len(), 1);
        // Local definition wins — resolves to this module ("M").
        assert_eq!(pairs[0].1, "M");
    }
}
