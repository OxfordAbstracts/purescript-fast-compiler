//! Module cache for incremental builds.
//!
//! Uses a lightweight index file (hashes + imports) loaded eagerly,
//! and per-module export files loaded lazily on demand.
//! Exports hash comparison avoids rebuilding dependents when only
//! function bodies change (not signatures).

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};
use std::io;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::cst;
use crate::interner;
use crate::typechecker::registry::ModuleExports;

use super::portable::{PModuleExports, StringTableBuilder, StringTableReader};

// ===== Import Details for Smart Rebuild =====

/// What a module imports from a single dependency.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum CachedImportKind {
    /// `import Foo` — imports everything
    Everything,
    /// `import Foo (bar, Baz(..), class Qux)` — explicit import list
    Explicit(Vec<CachedImportItem>),
    /// `import Foo hiding (bar)` — everything except listed items
    Hiding(Vec<CachedImportItem>),
}

/// A single imported item.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum CachedImportItem {
    Value(String),
    Type(String),
    Class(String),
    TypeOp(String),
}

impl CachedImportItem {
    pub fn name(&self) -> &str {
        match self {
            CachedImportItem::Value(n)
            | CachedImportItem::Type(n)
            | CachedImportItem::Class(n)
            | CachedImportItem::TypeOp(n) => n,
        }
    }
}

/// Extract import details from a CST ImportDecl.
pub fn extract_import_items(imports: &[cst::ImportDecl]) -> HashMap<String, CachedImportKind> {
    let mut result = HashMap::new();
    for import in imports {
        let module_name = interner::resolve_module_name(&import.module.parts);
        let kind = match &import.imports {
            None => CachedImportKind::Everything,
            Some(cst::ImportList::Explicit(items)) => {
                CachedImportKind::Explicit(items.iter().map(convert_import).collect())
            }
            Some(cst::ImportList::Hiding(items)) => {
                CachedImportKind::Hiding(items.iter().map(convert_import).collect())
            }
        };
        result.insert(module_name, kind);
    }
    result
}

fn convert_import(import: &cst::Import) -> CachedImportItem {
    match import {
        cst::Import::Value(name) => {
            CachedImportItem::Value(interner::resolve(name.value).unwrap_or_default().to_string())
        }
        cst::Import::Type(name, _) => {
            CachedImportItem::Type(interner::resolve(name.value).unwrap_or_default().to_string())
        }
        cst::Import::Class(name) => {
            CachedImportItem::Class(interner::resolve(name.value).unwrap_or_default().to_string())
        }
        cst::Import::TypeOp(name) => {
            CachedImportItem::TypeOp(interner::resolve(name.value).unwrap_or_default().to_string())
        }
    }
}

// ===== Export Diff for Smart Rebuild =====

/// Tracks what changed between old and new exports of a module.
#[derive(Debug, Default)]
pub struct ExportDiff {
    pub changed_values: HashSet<String>,
    pub changed_types: HashSet<String>,
    pub changed_classes: HashSet<String>,
    pub instances_changed: bool,
    pub operators_changed: bool,
}

impl ExportDiff {
    /// Returns true if nothing actually changed.
    pub fn is_empty(&self) -> bool {
        self.changed_values.is_empty()
            && self.changed_types.is_empty()
            && self.changed_classes.is_empty()
            && !self.instances_changed
            && !self.operators_changed
    }

    /// Compute the diff between old and new exports.
    pub fn compute(old: &ModuleExports, new: &ModuleExports) -> Self {
        let mut diff = ExportDiff::default();

        // Compare values (type schemes)
        diff_map_by_debug(&old.values, &new.values, &mut diff.changed_values);

        // Compare data constructors
        diff_map_by_debug(&old.data_constructors, &new.data_constructors, &mut diff.changed_types);

        // Compare constructor details
        diff_map_by_debug(&old.ctor_details, &new.ctor_details, &mut diff.changed_types);

        // Compare type aliases
        diff_map_by_debug(&old.type_aliases, &new.type_aliases, &mut diff.changed_types);

        // Compare type constructor arities
        diff_map_by_eq(&old.type_con_arities, &new.type_con_arities, &mut diff.changed_types);

        // Compare type roles
        diff_sym_map_by_eq(&old.type_roles, &new.type_roles, &mut diff.changed_types);

        // Compare newtype names
        diff_sym_set(&old.newtype_names, &new.newtype_names, &mut diff.changed_types);

        // Compare type kinds
        diff_sym_map_by_debug(&old.type_kinds, &new.type_kinds, &mut diff.changed_types);

        // Compare class methods
        diff_map_by_debug(&old.class_methods, &new.class_methods, &mut diff.changed_classes);

        // Compare class param counts
        diff_map_by_eq(&old.class_param_counts, &new.class_param_counts, &mut diff.changed_classes);

        // Compare class superclasses
        diff_map_by_debug(&old.class_superclasses, &new.class_superclasses, &mut diff.changed_classes);

        // Compare class type kinds
        diff_sym_map_by_debug(&old.class_type_kinds, &new.class_type_kinds, &mut diff.changed_classes);

        // Compare class functional dependencies
        diff_sym_map_by_debug(&old.class_fundeps, &new.class_fundeps, &mut diff.changed_classes);

        // Compare constrained class methods
        diff_qi_set(&old.constrained_class_methods, &new.constrained_class_methods, &mut diff.changed_classes);

        // Compare method own constraints
        diff_map_by_debug(&old.method_own_constraints, &new.method_own_constraints, &mut diff.changed_classes);

        // Compare class origins
        diff_sym_map_by_eq(&old.class_origins, &new.class_origins, &mut diff.changed_classes);

        // Instances — compare deterministically by sorting keys
        diff.instances_changed = !qi_maps_debug_equal(&old.instances, &new.instances);

        // Operators — compare each map deterministically
        if !qi_maps_debug_equal(&old.type_operators, &new.type_operators)
            || !qi_maps_debug_equal(&old.value_fixities, &new.value_fixities)
            || !qi_maps_debug_equal(&old.type_fixities, &new.type_fixities)
            || old.function_op_aliases != new.function_op_aliases
            || !qi_maps_debug_equal(&old.value_operator_targets, &new.value_operator_targets)
            || !sym_maps_debug_equal(&old.operator_class_targets, &new.operator_class_targets)
        {
            diff.operators_changed = true;
        }

        diff
    }

    /// Check if a given import kind overlaps with this diff.
    pub fn affects_import(&self, import_kind: &CachedImportKind) -> bool {
        // Instances are always implicitly imported — any instance change requires rebuild
        if self.instances_changed {
            return true;
        }

        match import_kind {
            CachedImportKind::Everything => {
                // Wildcard import — any change matters
                !self.changed_values.is_empty()
                    || !self.changed_types.is_empty()
                    || !self.changed_classes.is_empty()
                    || self.operators_changed
            }
            CachedImportKind::Explicit(items) => {
                // Only rebuild if an explicitly imported item changed
                for item in items {
                    match item {
                        CachedImportItem::Value(name) => {
                            if self.changed_values.contains(name) {
                                return true;
                            }
                        }
                        CachedImportItem::Type(name) => {
                            if self.changed_types.contains(name) {
                                return true;
                            }
                            // Type import also brings in constructors as values
                            if self.changed_values.contains(name) {
                                return true;
                            }
                        }
                        CachedImportItem::Class(name) => {
                            if self.changed_classes.contains(name) {
                                return true;
                            }
                        }
                        CachedImportItem::TypeOp(name) => {
                            if self.operators_changed {
                                // Conservative: any operator change
                                return true;
                            }
                            // Also check if the type operator target changed
                            if self.changed_types.contains(name) {
                                return true;
                            }
                        }
                    }
                }
                false
            }
            CachedImportKind::Hiding(items) => {
                // Everything except listed items — check if any changed name is NOT hidden
                let hidden: HashSet<&str> = items.iter().map(|i| i.name()).collect();

                for name in &self.changed_values {
                    if !hidden.contains(name.as_str()) {
                        return true;
                    }
                }
                for name in &self.changed_types {
                    if !hidden.contains(name.as_str()) {
                        return true;
                    }
                }
                for name in &self.changed_classes {
                    if !hidden.contains(name.as_str()) {
                        return true;
                    }
                }
                if self.operators_changed {
                    return true; // Conservative for operator changes with hiding
                }
                false
            }
        }
    }
}

/// Helper: diff two HashMap<QualifiedIdent, V> where V: Debug, collecting changed names.
fn diff_map_by_debug<V: std::fmt::Debug>(
    old: &HashMap<crate::cst::QualifiedIdent, V>,
    new: &HashMap<crate::cst::QualifiedIdent, V>,
    changed: &mut HashSet<String>,
) {
    for (key, old_val) in old {
        match new.get(key) {
            None => { changed.insert(format!("{}", key)); }
            Some(new_val) => {
                if format!("{:?}", old_val) != format!("{:?}", new_val) {
                    changed.insert(format!("{}", key));
                }
            }
        }
    }
    for key in new.keys() {
        if !old.contains_key(key) {
            changed.insert(format!("{}", key));
        }
    }
}

/// Helper: diff two HashMap<QualifiedIdent, V> where V: PartialEq, collecting changed names.
fn diff_map_by_eq<V: PartialEq>(
    old: &HashMap<crate::cst::QualifiedIdent, V>,
    new: &HashMap<crate::cst::QualifiedIdent, V>,
    changed: &mut HashSet<String>,
) {
    for (key, old_val) in old {
        match new.get(key) {
            None => { changed.insert(format!("{}", key)); }
            Some(new_val) => {
                if old_val != new_val {
                    changed.insert(format!("{}", key));
                }
            }
        }
    }
    for key in new.keys() {
        if !old.contains_key(key) {
            changed.insert(format!("{}", key));
        }
    }
}

/// Helper: diff two HashMap<Symbol, V> where V: Debug, collecting changed names.
fn diff_sym_map_by_debug<V: std::fmt::Debug>(
    old: &HashMap<crate::interner::Symbol, V>,
    new: &HashMap<crate::interner::Symbol, V>,
    changed: &mut HashSet<String>,
) {
    for (key, old_val) in old {
        match new.get(key) {
            None => { changed.insert(interner::resolve(*key).unwrap_or_default().to_string()); }
            Some(new_val) => {
                if format!("{:?}", old_val) != format!("{:?}", new_val) {
                    changed.insert(interner::resolve(*key).unwrap_or_default().to_string());
                }
            }
        }
    }
    for key in new.keys() {
        if !old.contains_key(key) {
            changed.insert(interner::resolve(*key).unwrap_or_default().to_string());
        }
    }
}

/// Helper: diff two HashMap<Symbol, V> where V: PartialEq, collecting changed names.
fn diff_sym_map_by_eq<V: PartialEq>(
    old: &HashMap<crate::interner::Symbol, V>,
    new: &HashMap<crate::interner::Symbol, V>,
    changed: &mut HashSet<String>,
) {
    for (key, old_val) in old {
        match new.get(key) {
            None => { changed.insert(interner::resolve(*key).unwrap_or_default().to_string()); }
            Some(new_val) => {
                if old_val != new_val {
                    changed.insert(interner::resolve(*key).unwrap_or_default().to_string());
                }
            }
        }
    }
    for key in new.keys() {
        if !old.contains_key(key) {
            changed.insert(interner::resolve(*key).unwrap_or_default().to_string());
        }
    }
}

/// Helper: diff two HashSet<Symbol>, collecting changed names.
fn diff_sym_set(
    old: &HashSet<crate::interner::Symbol>,
    new: &HashSet<crate::interner::Symbol>,
    changed: &mut HashSet<String>,
) {
    for sym in old.symmetric_difference(new) {
        changed.insert(interner::resolve(*sym).unwrap_or_default().to_string());
    }
}

/// Helper: diff two HashSet<QualifiedIdent>, collecting changed names.
fn diff_qi_set(
    old: &HashSet<crate::cst::QualifiedIdent>,
    new: &HashSet<crate::cst::QualifiedIdent>,
    changed: &mut HashSet<String>,
) {
    for qi in old.symmetric_difference(new) {
        changed.insert(format!("{}", qi));
    }
}

/// Deterministic equality for HashMap<QualifiedIdent, V> where V: Debug.
/// Sorts keys to avoid non-deterministic HashMap iteration order.
fn qi_maps_debug_equal<V: std::fmt::Debug>(
    a: &HashMap<crate::cst::QualifiedIdent, V>,
    b: &HashMap<crate::cst::QualifiedIdent, V>,
) -> bool {
    if a.len() != b.len() {
        return false;
    }
    for (key, a_val) in a {
        match b.get(key) {
            None => return false,
            Some(b_val) => {
                if format!("{:?}", a_val) != format!("{:?}", b_val) {
                    return false;
                }
            }
        }
    }
    true
}

/// Deterministic equality for HashMap<Symbol, V> where V: Debug.
fn sym_maps_debug_equal<V: std::fmt::Debug>(
    a: &HashMap<crate::interner::Symbol, V>,
    b: &HashMap<crate::interner::Symbol, V>,
) -> bool {
    if a.len() != b.len() {
        return false;
    }
    for (key, a_val) in a {
        match b.get(key) {
            None => return false,
            Some(b_val) => {
                if format!("{:?}", a_val) != format!("{:?}", b_val) {
                    return false;
                }
            }
        }
    }
    true
}

// ===== Cache Index (loaded eagerly, small) =====

#[derive(Serialize, Deserialize, Default)]
struct CacheIndex {
    modules: HashMap<String, CacheIndexEntry>,
    /// Maps file paths to module names for fast lookup during incremental builds
    #[serde(default)]
    path_to_module: HashMap<String, String>,
}

#[derive(Serialize, Deserialize, Clone)]
struct CacheIndexEntry {
    content_hash: u64,
    exports_hash: u64,
    imports: Vec<String>,
    /// Per-dependency import details for smart rebuild decisions
    #[serde(default)]
    import_items: HashMap<String, CachedImportKind>,
}

// ===== Per-Module Cache File =====

#[derive(Serialize, Deserialize)]
struct ModuleCacheFile {
    string_table: Vec<String>,
    exports: PModuleExports,
}

// ===== In-Memory Module State =====

enum CachedModule {
    /// Only index loaded — exports on disk, not yet read
    Indexed {
        content_hash: u64,
        exports_hash: u64,
        imports: Vec<String>,
        import_items: HashMap<String, CachedImportKind>,
    },
    /// Fully loaded in memory (from disk or from typechecking)
    Loaded {
        content_hash: u64,
        exports_hash: u64,
        imports: Vec<String>,
        import_items: HashMap<String, CachedImportKind>,
        exports: ModuleExports,
        dirty: bool,
    },
}

impl CachedModule {
    fn content_hash(&self) -> u64 {
        match self {
            CachedModule::Indexed { content_hash, .. } => *content_hash,
            CachedModule::Loaded { content_hash, .. } => *content_hash,
        }
    }

    fn exports_hash(&self) -> u64 {
        match self {
            CachedModule::Indexed { exports_hash, .. } => *exports_hash,
            CachedModule::Loaded { exports_hash, .. } => *exports_hash,
        }
    }

    fn imports(&self) -> &[String] {
        match self {
            CachedModule::Indexed { imports, .. } => imports,
            CachedModule::Loaded { imports, .. } => imports,
        }
    }

    fn import_items(&self) -> &HashMap<String, CachedImportKind> {
        match self {
            CachedModule::Indexed { import_items, .. } => import_items,
            CachedModule::Loaded { import_items, .. } => import_items,
        }
    }

    fn is_dirty(&self) -> bool {
        match self {
            CachedModule::Indexed { .. } => false,
            CachedModule::Loaded { dirty, .. } => *dirty,
        }
    }
}

// ===== Public API =====

/// In-memory cache of typechecked modules for incremental builds.
/// Index is loaded eagerly; per-module exports are loaded lazily.
pub struct ModuleCache {
    entries: HashMap<String, CachedModule>,
    /// Reverse dependency graph: module → modules that import it
    dependents: HashMap<String, Vec<String>>,
    /// Maps file paths to module names for skipping parse on warm builds
    path_index: HashMap<String, String>,
    /// Directory for per-module cache files
    cache_dir: Option<PathBuf>,
    /// Whether the index needs to be rewritten
    index_dirty: bool,
}

impl Default for ModuleCache {
    fn default() -> Self {
        Self {
            entries: HashMap::new(),
            dependents: HashMap::new(),
            path_index: HashMap::new(),
            cache_dir: None,
            index_dirty: false,
        }
    }
}

impl ModuleCache {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns true if the cache has any module entries (i.e. a prior build populated it).
    pub fn has_entries(&self) -> bool {
        !self.entries.is_empty()
    }

    /// Compute a content hash for a source string.
    pub fn content_hash(source: &str) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        source.hash(&mut hasher);
        hasher.finish()
    }

    /// Compute a hash of serialized exports for change detection.
    pub fn exports_hash(exports: &ModuleExports) -> u64 {
        let mut st = StringTableBuilder::new();
        let portable = PModuleExports::from_exports(exports, &mut st);
        let bytes = bincode::serialize(&(st.into_table(), &portable)).unwrap_or_default();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        bytes.hash(&mut hasher);
        hasher.finish()
    }

    /// Check if a module needs to be rebuilt.
    ///
    /// Returns true if:
    /// - The module is not in the cache
    /// - Its content hash has changed
    /// - Any of its imports was rebuilt in this cycle
    pub fn needs_rebuild(
        &self,
        module_name: &str,
        content_hash: u64,
        rebuilt: &HashSet<String>,
    ) -> bool {
        match self.entries.get(module_name) {
            None => true,
            Some(cached) => {
                if cached.content_hash() != content_hash {
                    return true;
                }
                // Check if any dependency was rebuilt (exports changed)
                cached.imports().iter().any(|dep| rebuilt.contains(dep))
            }
        }
    }

    /// Smart rebuild check using per-symbol export diffs and import details.
    ///
    /// Returns true if:
    /// - The module is not in the cache
    /// - Its content hash has changed
    /// - Any import has a diff that affects the symbols this module actually imports
    pub fn needs_rebuild_smart(
        &self,
        module_name: &str,
        content_hash: u64,
        export_diffs: &HashMap<String, ExportDiff>,
    ) -> bool {
        match self.entries.get(module_name) {
            None => {
                log::debug!("[build-plan] {module_name}: rebuild (not in cache)");
                true
            }
            Some(cached) => {
                if cached.content_hash() != content_hash {
                    log::debug!("[build-plan] {module_name}: rebuild (source changed)");
                    return true;
                }
                let my_import_items = cached.import_items();
                for dep in cached.imports() {
                    if let Some(diff) = export_diffs.get(dep) {
                        let import_kind = my_import_items.get(dep);
                        match import_kind {
                            Some(kind) => {
                                if diff.affects_import(kind) {
                                    log::debug!(
                                        "[build-plan] {module_name}: rebuild (import from {dep} affected: \
                                         values={:?}, types={:?}, classes={:?}, instances={}, operators={})",
                                        diff.changed_values, diff.changed_types, diff.changed_classes,
                                        diff.instances_changed, diff.operators_changed
                                    );
                                    return true;
                                }
                            }
                            None => {
                                log::debug!("[build-plan] {module_name}: rebuild (no import details for {dep}, conservative)");
                                return true;
                            }
                        }
                    }
                }
                false
            }
        }
    }

    /// Get the cached import details for a module.
    pub fn get_import_items(&self, module_name: &str) -> Option<&HashMap<String, CachedImportKind>> {
        self.entries.get(module_name).map(|c| c.import_items())
    }

    /// Look up the module name associated with a file path.
    /// Canonicalizes the path for consistent lookups regardless of relative/absolute form.
    pub fn module_name_for_path(&self, path: &str) -> Option<&str> {
        let canonical = std::path::Path::new(path)
            .canonicalize()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| path.to_string());
        self.path_index.get(&canonical).map(|s| s.as_str())
    }

    /// Register a file path → module name mapping.
    /// Canonicalizes the path for consistent lookups regardless of relative/absolute form.
    pub fn register_path(&mut self, path: String, module_name: String) {
        let canonical = std::path::Path::new(&path)
            .canonicalize()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| path);
        if self.path_index.get(&canonical).map(|s| s.as_str()) != Some(&module_name) {
            self.path_index.insert(canonical, module_name);
            self.index_dirty = true;
        }
    }

    /// Get the cached imports for a module by name.
    pub fn get_imports(&self, module_name: &str) -> Option<&[String]> {
        self.entries.get(module_name).map(|c| c.imports())
    }

    /// Get cached exports for a module, loading from disk if needed.
    pub fn get_exports(&mut self, module_name: &str) -> Option<&ModuleExports> {
        // Check if we need to load from disk first
        let needs_load = matches!(
            self.entries.get(module_name),
            Some(CachedModule::Indexed { .. })
        );

        if needs_load {
            if let Some(ref cache_dir) = self.cache_dir {
                let module_path = module_file_path(cache_dir, module_name);
                if let Ok(exports) = load_module_file(&module_path) {
                    if let Some(entry) = self.entries.remove(module_name) {
                        let (content_hash, exports_hash, imports, import_items) = match entry {
                            CachedModule::Indexed { content_hash, exports_hash, imports, import_items } => {
                                (content_hash, exports_hash, imports, import_items)
                            }
                            _ => unreachable!(),
                        };
                        self.entries.insert(module_name.to_string(), CachedModule::Loaded {
                            content_hash,
                            exports_hash,
                            imports,
                            import_items,
                            exports,
                            dirty: false,
                        });
                    }
                } else {
                    // File missing/corrupt — remove from cache
                    self.entries.remove(module_name);
                    self.index_dirty = true;
                    return None;
                }
            } else {
                // No cache dir — can't load
                return None;
            }
        }

        match self.entries.get(module_name) {
            Some(CachedModule::Loaded { exports, .. }) => Some(exports),
            _ => None,
        }
    }

    /// Update the cache entry for a module after typechecking.
    /// Returns true if the module's exports actually changed (different exports_hash).
    pub fn update(
        &mut self,
        module_name: String,
        content_hash: u64,
        exports: ModuleExports,
        imports: Vec<String>,
        import_items: HashMap<String, CachedImportKind>,
    ) -> bool {
        let new_exports_hash = Self::exports_hash(&exports);

        let exports_changed = self.entries.get(&module_name)
            .map_or(true, |old| old.exports_hash() != new_exports_hash);

        self.entries.insert(module_name, CachedModule::Loaded {
            content_hash,
            exports_hash: new_exports_hash,
            imports,
            import_items,
            exports,
            dirty: true,
        });
        self.index_dirty = true;
        exports_changed
    }

    /// Remove a module from the cache (e.g. when it fails typechecking).
    pub fn remove(&mut self, module_name: &str) {
        if self.entries.remove(module_name).is_some() {
            self.index_dirty = true;
        }
    }

    /// Build the reverse dependency graph from cached import data.
    pub fn build_reverse_deps(&mut self) {
        self.dependents.clear();
        for (module, cached) in &self.entries {
            for dep in cached.imports() {
                self.dependents
                    .entry(dep.clone())
                    .or_default()
                    .push(module.clone());
            }
        }
    }

    /// Find all transitive dependents of a module (BFS).
    pub fn transitive_dependents(&self, module: &str) -> HashSet<String> {
        let mut result = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(module.to_string());

        while let Some(current) = queue.pop_front() {
            if let Some(deps) = self.dependents.get(&current) {
                for dep in deps {
                    if result.insert(dep.clone()) {
                        queue.push_back(dep.clone());
                    }
                }
            }
        }

        result
    }

    /// Remove modules that are no longer in the source set.
    pub fn retain_modules(&mut self, module_names: &HashSet<String>) {
        let before = self.entries.len();
        self.entries.retain(|k, _| module_names.contains(k));
        if self.entries.len() != before {
            self.path_index.retain(|_, v| module_names.contains(v));
            self.index_dirty = true;
        }
    }

    // ===== Disk I/O =====

    /// Save cache to disk: index file + per-module files for dirty modules.
    pub fn save_to_disk(&self, cache_dir: &Path) -> io::Result<()> {
        if !self.index_dirty && !self.entries.values().any(|m| m.is_dirty()) {
            log::debug!("Cache unchanged, skipping save");
            return Ok(());
        }

        let modules_dir = cache_dir.join("modules");
        std::fs::create_dir_all(&modules_dir)?;

        // Write dirty module files
        let mut saved_count = 0;
        for (name, cached) in &self.entries {
            if let CachedModule::Loaded { exports, dirty: true, .. } = cached {
                let module_path = module_file_path(cache_dir, name);
                save_module_file(&module_path, exports)?;
                saved_count += 1;
            }
        }

        // Write index
        let index = CacheIndex {
            modules: self.entries.iter().map(|(name, cached)| {
                (name.clone(), CacheIndexEntry {
                    content_hash: cached.content_hash(),
                    exports_hash: cached.exports_hash(),
                    imports: cached.imports().to_vec(),
                    import_items: cached.import_items().clone(),
                })
            }).collect(),
            path_to_module: self.path_index.clone(),
        };

        let index_path = cache_dir.join("index.bin");
        let encoded = bincode::serialize(&index)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;
        let compressed = zstd::bulk::compress(&encoded, 1)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
        std::fs::write(&index_path, compressed)?;

        log::debug!("Cache save: wrote index + {} module files", saved_count);
        Ok(())
    }

    /// Load cache index from disk. Module exports are loaded lazily.
    pub fn load_from_disk(cache_dir: &Path) -> io::Result<Self> {
        let index_path = cache_dir.join("index.bin");
        let compressed = std::fs::read(&index_path)?;
        let data = zstd::bulk::decompress(&compressed, 64 * 1024 * 1024)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
        let index: CacheIndex = bincode::deserialize(&data)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;

        let entries = index.modules.into_iter().map(|(name, entry)| {
            (name, CachedModule::Indexed {
                content_hash: entry.content_hash,
                exports_hash: entry.exports_hash,
                imports: entry.imports,
                import_items: entry.import_items,
            })
        }).collect();

        let mut cache = ModuleCache {
            entries,
            dependents: HashMap::new(),
            path_index: index.path_to_module,
            cache_dir: Some(cache_dir.to_path_buf()),
            index_dirty: false,
        };
        cache.build_reverse_deps();
        Ok(cache)
    }
}

// ===== File helpers =====

fn module_file_path(cache_dir: &Path, module_name: &str) -> PathBuf {
    cache_dir.join("modules").join(format!("{}.bin", module_name))
}

fn save_module_file(path: &Path, exports: &ModuleExports) -> io::Result<()> {
    let mut st = StringTableBuilder::new();
    let portable = PModuleExports::from_exports(exports, &mut st);
    let file = ModuleCacheFile {
        string_table: st.into_table(),
        exports: portable,
    };

    let mut encoder = zstd::Encoder::new(std::fs::File::create(path)?, 1)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
    bincode::serialize_into(&mut encoder, &file)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;
    encoder.finish()
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
    Ok(())
}

fn load_module_file(path: &Path) -> io::Result<ModuleExports> {
    let file = std::fs::File::open(path)?;
    let decoder = io::BufReader::new(zstd::Decoder::new(file)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?);
    let cache_file: ModuleCacheFile = bincode::deserialize_from(decoder)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;

    let st = StringTableReader::new(cache_file.string_table);
    Ok(cache_file.exports.to_exports(&st))
}

// ===== Registry Snapshot (single-file save/load for entire ModuleRegistry) =====

use crate::typechecker::registry::ModuleRegistry;

#[derive(Serialize, Deserialize)]
struct RegistrySnapshot {
    string_table: Vec<String>,
    /// Each entry: (module_parts as Vec<u32>, portable exports)
    modules: Vec<(Vec<u32>, PModuleExports)>,
}

/// Save the entire registry to a single compressed file.
pub fn save_registry_snapshot(registry: &ModuleRegistry, path: &Path) -> io::Result<()> {
    let mut st = StringTableBuilder::new();
    let modules: Vec<(Vec<u32>, PModuleExports)> = registry
        .iter_all()
        .iter()
        .map(|(name_parts, exports)| {
            let parts: Vec<u32> = name_parts.iter().map(|s| st.add(*s)).collect();
            let pexports = PModuleExports::from_exports(exports, &mut st);
            (parts, pexports)
        })
        .collect();

    let snapshot = RegistrySnapshot {
        string_table: st.into_table(),
        modules,
    };

    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }

    let encoded = bincode::serialize(&snapshot)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;
    let compressed = zstd::bulk::compress(&encoded, 1)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
    std::fs::write(path, compressed)
}

/// Load a registry from a single compressed snapshot file.
pub fn load_registry_snapshot(path: &Path) -> io::Result<ModuleRegistry> {
    let compressed = std::fs::read(path)?;
    let data = zstd::bulk::decompress(&compressed, 256 * 1024 * 1024)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
    let snapshot: RegistrySnapshot = bincode::deserialize(&data)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;

    let st = StringTableReader::new(snapshot.string_table);
    let mut registry = ModuleRegistry::new();
    for (parts, pexports) in &snapshot.modules {
        let name: Vec<interner::Symbol> = parts.iter().map(|&idx| st.sym(idx)).collect();
        let exports = pexports.to_exports(&st);
        registry.register(&name, exports);
    }
    Ok(registry)
}

// ===== Module File Map Snapshot =====

/// Save module_file_map (HashMap<String, String>) to disk.
pub fn save_module_file_map(map: &HashMap<String, String>, path: &Path) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let encoded = bincode::serialize(map)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;
    let compressed = zstd::bulk::compress(&encoded, 1)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
    std::fs::write(path, compressed)
}

/// Load module_file_map from disk.
pub fn load_module_file_map(path: &Path) -> io::Result<HashMap<String, String>> {
    let compressed = std::fs::read(path)?;
    let data = zstd::bulk::decompress(&compressed, 64 * 1024 * 1024)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
    bincode::deserialize(&data)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))
}
