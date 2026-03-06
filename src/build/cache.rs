//! Module cache for incremental builds.
//!
//! Tracks content hashes and cached ModuleExports to skip typechecking
//! unchanged modules. Supports on-disk persistence via bincode serialization.

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};
use std::io;
use std::path::Path;
use std::sync::Arc;

use rayon::prelude::*;

use crate::typechecker::registry::ModuleExports;

use super::portable::{PModuleExports, PortableCacheFile, PortableCachedModule, StringTableBuilder, StringTableReader};

// ===== Module Cache =====

/// Cached state for a single module.
struct CachedModule {
    content_hash: u64,
    exports: ModuleExports,
    imports: Vec<String>,
}

/// In-memory cache of typechecked modules for incremental builds.
#[derive(Default)]
pub struct ModuleCache {
    entries: HashMap<String, CachedModule>,
    /// Reverse dependency graph: module → modules that import it
    dependents: HashMap<String, Vec<String>>,
    /// Whether the cache has been modified since last save/load.
    dirty: bool,
}

impl ModuleCache {
    pub fn new() -> Self {
        Self::default()
    }

    /// Compute a content hash for a source string.
    pub fn content_hash(source: &str) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        source.hash(&mut hasher);
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
                if cached.content_hash != content_hash {
                    return true;
                }
                // Check if any dependency was rebuilt
                cached.imports.iter().any(|dep| rebuilt.contains(dep))
            }
        }
    }

    /// Get cached exports for a module (if available).
    pub fn get_exports(&self, module_name: &str) -> Option<&ModuleExports> {
        self.entries.get(module_name).map(|c| &c.exports)
    }

    /// Update the cache entry for a module after typechecking.
    pub fn update(
        &mut self,
        module_name: String,
        content_hash: u64,
        exports: ModuleExports,
        imports: Vec<String>,
    ) {
        self.entries.insert(module_name, CachedModule {
            content_hash,
            exports,
            imports,
        });
        self.dirty = true;
    }

    /// Build the reverse dependency graph from cached import data.
    pub fn build_reverse_deps(&mut self) {
        self.dependents.clear();
        for (module, cached) in &self.entries {
            for dep in &cached.imports {
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
            self.dirty = true;
        }
    }

    /// Returns true if the cache has been modified since load.
    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Save cache to disk using bincode serialization with string table.
    pub fn save_to_disk(&self, path: &Path) -> io::Result<()> {
        if !self.dirty {
            log::debug!("Cache unchanged, skipping save");
            return Ok(());
        }
        let mut st = StringTableBuilder::new();

        let modules = self.entries.iter().map(|(name, cached)| {
            (name.clone(), PortableCachedModule {
                content_hash: cached.content_hash,
                exports: PModuleExports::from_exports(&cached.exports, &mut st),
                imports: cached.imports.clone(),
            })
        }).collect();

        let portable = PortableCacheFile {
            string_table: st.into_table(),
            modules,
        };

        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let file = std::fs::File::create(path)?;
        let mut encoder = zstd::Encoder::new(file, 1)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd encoder: {e}")))?;
        bincode::serialize_into(&mut encoder, &portable)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode serialize: {e}")))?;
        encoder.finish()
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd finish: {e}")))?;
        Ok(())
    }

    /// Load cache from disk.
    pub fn load_from_disk(path: &Path) -> io::Result<Self> {
        let file = std::fs::File::open(path)?;
        let decoder = io::BufReader::new(zstd::Decoder::new(file)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd decoder: {e}")))?);
        let portable: PortableCacheFile = bincode::deserialize_from(decoder)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode deserialize: {e}")))?;

        let st = Arc::new(StringTableReader::new(portable.string_table));

        let entries: HashMap<String, CachedModule> = portable.modules.into_par_iter().map(|(name, cached)| {
            (name, CachedModule {
                content_hash: cached.content_hash,
                exports: cached.exports.to_exports(&st),
                imports: cached.imports,
            })
        }).collect();

        let mut cache = ModuleCache {
            entries,
            dependents: HashMap::new(),
            dirty: false,
        };
        cache.build_reverse_deps();
        Ok(cache)
    }
}
