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

use crate::typechecker::registry::ModuleExports;

use super::portable::{PModuleExports, StringTableBuilder, StringTableReader};

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
    },
    /// Fully loaded in memory (from disk or from typechecking)
    Loaded {
        content_hash: u64,
        exports_hash: u64,
        imports: Vec<String>,
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
                        let (content_hash, exports_hash, imports) = match entry {
                            CachedModule::Indexed { content_hash, exports_hash, imports } => {
                                (content_hash, exports_hash, imports)
                            }
                            _ => unreachable!(),
                        };
                        self.entries.insert(module_name.to_string(), CachedModule::Loaded {
                            content_hash,
                            exports_hash,
                            imports,
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
    ) -> bool {
        let new_exports_hash = Self::exports_hash(&exports);

        let exports_changed = self.entries.get(&module_name)
            .map_or(true, |old| old.exports_hash() != new_exports_hash);

        self.entries.insert(module_name, CachedModule::Loaded {
            content_hash,
            exports_hash: new_exports_hash,
            imports,
            exports,
            dirty: true,
        });
        self.index_dirty = true;
        exports_changed
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
use crate::interner;

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
