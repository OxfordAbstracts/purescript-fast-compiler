//! Demand-driven driver that fronts the SQLite store with an in-process memo
//! cache.
//!
//! M1 exposes generic `get_cached`/`put` entry points that passes can build
//! on. Pass-specific wrappers (M2+) will layer `InputHasher` + dep tracking
//! on top.

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::typecheck_db::key::{hash_bytes, InputHash, OutputHash, PassKey};
use crate::typecheck_db::store::{DepEdge, PassRow, Store, StoreError};

/// Whether a pass output came from the cache or was freshly computed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheOutcome {
    Hit,
    Miss,
}

#[derive(Debug, thiserror::Error)]
pub enum DriverError {
    #[error(transparent)]
    Store(#[from] StoreError),
    #[error("bincode: {0}")]
    Bincode(#[from] bincode::Error),
}

/// One memoized entry: serialized output + hashes. `Arc` so repeated reads
/// don't clone the blob.
#[derive(Clone)]
struct MemoEntry {
    input_hash: InputHash,
    output_hash: OutputHash,
    blob: Arc<Vec<u8>>,
}

pub struct TypecheckDb {
    store: Store,
    memo: HashMap<PassKey, MemoEntry>,
    /// When true, `check_one_module` runs the per-declaration JS codegen
    /// (the `DeclDb` engine) and populates `ModuleCheckResult::js_module_text`.
    /// Off by default so plain typechecking pays no codegen cost.
    codegen_enabled: bool,
}

impl TypecheckDb {
    pub fn open(path: &Path) -> Result<Self, DriverError> {
        Ok(Self {
            store: Store::open(path)?,
            memo: HashMap::new(),
            codegen_enabled: false,
        })
    }

    pub fn open_in_memory() -> Result<Self, DriverError> {
        Ok(Self {
            store: Store::open_in_memory()?,
            memo: HashMap::new(),
            codegen_enabled: false,
        })
    }

    /// Enable/disable per-declaration JS codegen for subsequent module checks.
    pub fn set_codegen(&mut self, enabled: bool) {
        self.codegen_enabled = enabled;
    }

    /// Whether per-declaration JS codegen is enabled.
    pub fn codegen_enabled(&self) -> bool {
        self.codegen_enabled
    }

    /// Look up a cached output for `key` and return it iff the stored
    /// `input_hash` matches the one the caller freshly computed.
    pub fn get_cached<T: DeserializeOwned>(
        &mut self,
        key: &PassKey,
        expected_input_hash: InputHash,
    ) -> Result<Option<(T, OutputHash)>, DriverError> {
        // Memo first.
        if let Some(entry) = self.memo.get(key) {
            if entry.input_hash == expected_input_hash {
                let value: T = bincode::deserialize(&entry.blob)?;
                return Ok(Some((value, entry.output_hash)));
            }
        }
        // Fall through to SQLite.
        let Some(PassRow { input_hash, output_hash, output_blob }) = self.store.get_output(key)? else {
            return Ok(None);
        };
        if input_hash != expected_input_hash {
            return Ok(None);
        }
        let value: T = bincode::deserialize(&output_blob)?;
        self.memo.insert(key.clone(), MemoEntry {
            input_hash,
            output_hash,
            blob: Arc::new(output_blob),
        });
        Ok(Some((value, output_hash)))
    }

    /// Persist a fresh pass output and return its `output_hash` (used by
    /// downstream passes to key their own `input_hash`).
    pub fn put<T: Serialize>(
        &mut self,
        key: &PassKey,
        input_hash: InputHash,
        value: &T,
    ) -> Result<OutputHash, DriverError> {
        self.put_with_debug(key, input_hash, value, "")
    }

    /// Like [`put`](Self::put) but attaches a human-readable label to
    /// the SQLite row (via `pass_output.decl_debug`). Useful for
    /// inspecting the cache after the fact without changing any hash
    /// semantics.
    pub fn put_with_debug<T: Serialize>(
        &mut self,
        key: &PassKey,
        input_hash: InputHash,
        value: &T,
        decl_debug: &str,
    ) -> Result<OutputHash, DriverError> {
        let blob = bincode::serialize(value)?;
        let output_hash = hash_bytes(&blob);
        self.store
            .put_output_with_debug(key, input_hash, output_hash, &blob, decl_debug)?;
        self.memo.insert(key.clone(), MemoEntry {
            input_hash,
            output_hash,
            blob: Arc::new(blob),
        });
        Ok(output_hash)
    }

    pub fn put_deps(&mut self, key: &PassKey, deps: &[DepEdge]) -> Result<(), DriverError> {
        self.store.put_deps(key, deps)?;
        Ok(())
    }

    pub fn store(&self) -> &Store {
        &self.store
    }

    pub fn clear_memo(&mut self) {
        self.memo.clear();
    }
}
