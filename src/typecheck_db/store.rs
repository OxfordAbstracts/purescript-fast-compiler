//! SQLite persistence layer for pass outputs and their dep edges.

use std::collections::HashMap;
use std::path::Path;

use rusqlite::{params, Connection, OptionalExtension};

use crate::typecheck_db::key::{InputHash, OutputHash, PassKey};

const SCHEMA: &str = r#"
CREATE TABLE IF NOT EXISTS pass_output (
    module      TEXT NOT NULL,
    decl        TEXT NOT NULL,
    pass        TEXT NOT NULL,
    input_hash  BLOB NOT NULL,
    output_hash BLOB NOT NULL,
    output_blob BLOB NOT NULL,
    decl_debug  TEXT NOT NULL DEFAULT '',
    PRIMARY KEY (module, decl, pass)
);

CREATE TABLE IF NOT EXISTS pass_dep (
    module     TEXT NOT NULL,
    decl       TEXT NOT NULL,
    pass       TEXT NOT NULL,
    dep_module TEXT NOT NULL,
    dep_decl   TEXT NOT NULL,
    dep_pass   TEXT NOT NULL,
    PRIMARY KEY (module, decl, pass, dep_module, dep_decl, dep_pass)
);

CREATE INDEX IF NOT EXISTS pass_dep_reverse
    ON pass_dep (dep_module, dep_decl, dep_pass);

CREATE TABLE IF NOT EXISTS module_source (
    module          TEXT PRIMARY KEY,
    source_hash     BLOB NOT NULL,
    decl_index_blob BLOB NOT NULL
);

-- Module-level memo for the build-plan fast path. `source_hash` is stored as
-- its own column so the build plan can read every module's hash without
-- deserializing the (large) memo blob. `memo_blob` is a bincode-serialized
-- `ModuleMemo` (exports + per-decl registry hashes + instances + generated JS)
-- restored into the `ModuleRegistry` when a module is proven clean.
--
-- `interface_hash` / `deps_combined_hash` are ALSO stored as their own columns
-- (like `source_hash`) so the build plan can detect cross-build interface
-- drift without deserializing any blob: `interface_hash` fingerprints this
-- module's own exported interface, and `deps_combined_hash` folds in the
-- interface fingerprints of its in-build dependencies AS SEEN when the memo
-- was written. A restored module is stale iff recomputing its
-- `deps_combined_hash` from its dependencies' CURRENT `interface_hash`es no
-- longer matches — which happens when a dependency's interface changed in a
-- build that did not include this module. Nullable so pre-existing rows
-- (written before these columns existed) read back as `None` and are treated
-- as "cannot verify → re-check", healing the cache on the first run.
CREATE TABLE IF NOT EXISTS module_memo (
    module             TEXT PRIMARY KEY,
    source_hash        BLOB NOT NULL,
    memo_blob          BLOB NOT NULL,
    interface_hash     BLOB,
    deps_combined_hash BLOB
);
"#;

/// Best-effort migration for older databases. We detect a missing column by
/// trying to select it and, if it errors, apply the ALTER. Idempotent on
/// fresh DBs because `CREATE TABLE IF NOT EXISTS` above already declares the
/// columns.
fn migrate(conn: &Connection) -> Result<(), StoreError> {
    let has_col: bool = conn
        .prepare("SELECT decl_debug FROM pass_output LIMIT 0")
        .is_ok();
    if !has_col {
        conn.execute(
            "ALTER TABLE pass_output ADD COLUMN decl_debug TEXT NOT NULL DEFAULT ''",
            [],
        )?;
    }
    // Build-plan drift columns (added after the initial module_memo shape).
    if conn
        .prepare("SELECT interface_hash FROM module_memo LIMIT 0")
        .is_err()
    {
        conn.execute("ALTER TABLE module_memo ADD COLUMN interface_hash BLOB", [])?;
    }
    if conn
        .prepare("SELECT deps_combined_hash FROM module_memo LIMIT 0")
        .is_err()
    {
        conn.execute(
            "ALTER TABLE module_memo ADD COLUMN deps_combined_hash BLOB",
            [],
        )?;
    }
    Ok(())
}

#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("sqlite: {0}")]
    Sqlite(#[from] rusqlite::Error),
    #[error("corrupt hash column (expected 32 bytes, got {0})")]
    CorruptHash(usize),
}

#[derive(Debug, Clone)]
pub struct PassRow {
    pub input_hash: InputHash,
    pub output_hash: OutputHash,
    pub output_blob: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct DepEdge {
    pub dep_module: String,
    pub dep_decl: String,
    pub dep_pass: String,
}

pub struct Store {
    conn: Connection,
}

impl Store {
    pub fn open(path: &Path) -> Result<Self, StoreError> {
        let conn = Connection::open(path)?;
        Self::init(conn, true)
    }

    pub fn open_in_memory() -> Result<Self, StoreError> {
        let conn = Connection::open_in_memory()?;
        Self::init(conn, false)
    }

    fn init(conn: Connection, on_disk: bool) -> Result<Self, StoreError> {
        if on_disk {
            conn.pragma_update(None, "journal_mode", "WAL")?;
            conn.pragma_update(None, "synchronous", "NORMAL")?;
        }
        conn.execute_batch(SCHEMA)?;
        migrate(&conn)?;
        Ok(Self { conn })
    }

    pub fn get_output(&self, key: &PassKey) -> Result<Option<PassRow>, StoreError> {
        let mut stmt = self.conn.prepare_cached(
            "SELECT input_hash, output_hash, output_blob
             FROM pass_output WHERE module = ?1 AND decl = ?2 AND pass = ?3",
        )?;
        let row = stmt
            .query_row(params![&key.module, &key.decl, key.pass], |r| {
                let ih: Vec<u8> = r.get(0)?;
                let oh: Vec<u8> = r.get(1)?;
                let ob: Vec<u8> = r.get(2)?;
                Ok((ih, oh, ob))
            })
            .optional()?;
        match row {
            None => Ok(None),
            Some((ih, oh, ob)) => Ok(Some(PassRow {
                input_hash: to_hash(&ih)?,
                output_hash: to_hash(&oh)?,
                output_blob: ob,
            })),
        }
    }

    pub fn put_output(
        &self,
        key: &PassKey,
        input_hash: InputHash,
        output_hash: OutputHash,
        output_blob: &[u8],
    ) -> Result<(), StoreError> {
        self.put_output_with_debug(key, input_hash, output_hash, output_blob, "")
    }

    /// Like [`put_output`](Self::put_output) but attaches a
    /// human-readable debug label to the row. Surfaced by the
    /// `decl_debug` column for ad-hoc cache inspection; ignored by
    /// cache correctness.
    pub fn put_output_with_debug(
        &self,
        key: &PassKey,
        input_hash: InputHash,
        output_hash: OutputHash,
        output_blob: &[u8],
        decl_debug: &str,
    ) -> Result<(), StoreError> {
        let mut stmt = self.conn.prepare_cached(
            "INSERT INTO pass_output (module, decl, pass, input_hash, output_hash, output_blob, decl_debug)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)
             ON CONFLICT (module, decl, pass) DO UPDATE SET
                input_hash  = excluded.input_hash,
                output_hash = excluded.output_hash,
                output_blob = excluded.output_blob,
                decl_debug  = excluded.decl_debug",
        )?;
        stmt.execute(params![
            &key.module,
            &key.decl,
            key.pass,
            &input_hash[..],
            &output_hash[..],
            output_blob,
            decl_debug,
        ])?;
        Ok(())
    }

    pub fn get_deps(&self, key: &PassKey) -> Result<Vec<DepEdge>, StoreError> {
        let mut stmt = self.conn.prepare_cached(
            "SELECT dep_module, dep_decl, dep_pass
             FROM pass_dep WHERE module = ?1 AND decl = ?2 AND pass = ?3
             ORDER BY dep_module, dep_decl, dep_pass",
        )?;
        let rows = stmt.query_map(params![&key.module, &key.decl, key.pass], |r| {
            Ok(DepEdge {
                dep_module: r.get(0)?,
                dep_decl: r.get(1)?,
                dep_pass: r.get(2)?,
            })
        })?;
        let mut out = Vec::new();
        for r in rows {
            out.push(r?);
        }
        Ok(out)
    }

    pub fn put_deps(&mut self, key: &PassKey, deps: &[DepEdge]) -> Result<(), StoreError> {
        let tx = self.conn.transaction()?;
        tx.execute(
            "DELETE FROM pass_dep WHERE module = ?1 AND decl = ?2 AND pass = ?3",
            params![&key.module, &key.decl, key.pass],
        )?;
        {
            let mut stmt = tx.prepare_cached(
                "INSERT OR IGNORE INTO pass_dep
                 (module, decl, pass, dep_module, dep_decl, dep_pass)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
            )?;
            for d in deps {
                stmt.execute(params![
                    &key.module,
                    &key.decl,
                    key.pass,
                    &d.dep_module,
                    &d.dep_decl,
                    &d.dep_pass,
                ])?;
            }
        }
        tx.commit()?;
        Ok(())
    }

    /// Reverse lookup: every (module, decl, pass) that depends on the given output.
    pub fn dependents_of(
        &self,
        dep_module: &str,
        dep_decl: &str,
        dep_pass: &str,
    ) -> Result<Vec<PassKey>, StoreError> {
        let mut stmt = self.conn.prepare_cached(
            "SELECT module, decl, pass FROM pass_dep
             WHERE dep_module = ?1 AND dep_decl = ?2 AND dep_pass = ?3",
        )?;
        let rows = stmt.query_map(params![dep_module, dep_decl, dep_pass], |r| {
            let module: String = r.get(0)?;
            let decl: String = r.get(1)?;
            let pass: String = r.get(2)?;
            Ok((module, decl, pass))
        })?;
        let mut out = Vec::new();
        for r in rows {
            let (module, decl, pass) = r?;
            out.push(PassKey { module, decl, pass: leak_str(pass) });
        }
        Ok(out)
    }

    // ===== Module-level memo (build-plan fast path) =====

    /// Every cached `(module, source_hash)` pair. Cheap — reads only the
    /// `source_hash` column, never the memo blob, so the build plan can
    /// diff all modules' source hashes up front in one query.
    pub fn module_source_hashes(&self) -> Result<HashMap<String, [u8; 32]>, StoreError> {
        let mut stmt = self
            .conn
            .prepare_cached("SELECT module, source_hash FROM module_memo")?;
        let rows = stmt.query_map([], |r| {
            let m: String = r.get(0)?;
            let h: Vec<u8> = r.get(1)?;
            Ok((m, h))
        })?;
        let mut out = HashMap::new();
        for r in rows {
            let (m, h) = r?;
            out.insert(m, to_hash(&h)?);
        }
        Ok(out)
    }

    /// Every cached `(module, interface_hash)` pair, skipping rows whose
    /// `interface_hash` is NULL (pre-drift-columns memos). Cheap — reads only
    /// the small hash column so the build plan can detect cross-build
    /// interface drift up front without deserializing any memo blob.
    pub fn module_interface_hashes(&self) -> Result<HashMap<String, [u8; 32]>, StoreError> {
        self.read_hash_column("interface_hash")
    }

    /// Every cached `(module, deps_combined_hash)` pair, skipping NULLs.
    /// `deps_combined_hash` folds in this module's dependencies' interface
    /// fingerprints as of the last successful check.
    pub fn module_deps_combined_hashes(&self) -> Result<HashMap<String, [u8; 32]>, StoreError> {
        self.read_hash_column("deps_combined_hash")
    }

    fn read_hash_column(&self, col: &str) -> Result<HashMap<String, [u8; 32]>, StoreError> {
        // `col` is a fixed internal identifier (never user input), so
        // interpolating it into the query text is safe here.
        let sql = format!("SELECT module, {col} FROM module_memo WHERE {col} IS NOT NULL");
        let mut stmt = self.conn.prepare_cached(&sql)?;
        let rows = stmt.query_map([], |r| {
            let m: String = r.get(0)?;
            let h: Vec<u8> = r.get(1)?;
            Ok((m, h))
        })?;
        let mut out = HashMap::new();
        for r in rows {
            let (m, h) = r?;
            out.insert(m, to_hash(&h)?);
        }
        Ok(out)
    }

    /// The serialized `ModuleMemo` blob for one module, if present.
    pub fn get_module_memo_blob(&self, module: &str) -> Result<Option<Vec<u8>>, StoreError> {
        let mut stmt = self
            .conn
            .prepare_cached("SELECT memo_blob FROM module_memo WHERE module = ?1")?;
        let row = stmt
            .query_row(params![module], |r| {
                let b: Vec<u8> = r.get(0)?;
                Ok(b)
            })
            .optional()?;
        Ok(row)
    }

    /// Persist (or overwrite) a module's memo blob plus its source-hash and
    /// drift-detection hashes (all stored as their own columns for cheap
    /// blob-free reads by the build plan).
    pub fn put_module_memo(
        &self,
        module: &str,
        source_hash: [u8; 32],
        memo_blob: &[u8],
        interface_hash: [u8; 32],
        deps_combined_hash: [u8; 32],
    ) -> Result<(), StoreError> {
        let mut stmt = self.conn.prepare_cached(
            "INSERT INTO module_memo
                (module, source_hash, memo_blob, interface_hash, deps_combined_hash)
             VALUES (?1, ?2, ?3, ?4, ?5)
             ON CONFLICT (module) DO UPDATE SET
                source_hash        = excluded.source_hash,
                memo_blob          = excluded.memo_blob,
                interface_hash     = excluded.interface_hash,
                deps_combined_hash = excluded.deps_combined_hash",
        )?;
        stmt.execute(params![
            module,
            &source_hash[..],
            memo_blob,
            &interface_hash[..],
            &deps_combined_hash[..],
        ])?;
        Ok(())
    }
}

fn to_hash(bytes: &[u8]) -> Result<[u8; 32], StoreError> {
    if bytes.len() != 32 {
        return Err(StoreError::CorruptHash(bytes.len()));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(bytes);
    Ok(out)
}

// `PassKey::pass` is `&'static str`, but pass names read back from the DB are
// owned `String`s. Leak them so the returned `PassKey` can use `&'static str`.
// Pass names are a small, fixed set so total leaked bytes are bounded.
fn leak_str(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(module: &str, decl: &str) -> PassKey {
        PassKey::new(module, decl, "test_pass")
    }

    #[test]
    fn round_trip_output() {
        let store = Store::open_in_memory().unwrap();
        let k = key("M", "foo");
        assert!(store.get_output(&k).unwrap().is_none());
        store.put_output(&k, [1u8; 32], [2u8; 32], b"hello").unwrap();
        let row = store.get_output(&k).unwrap().expect("present after put");
        assert_eq!(row.input_hash, [1u8; 32]);
        assert_eq!(row.output_hash, [2u8; 32]);
        assert_eq!(row.output_blob, b"hello");
    }

    #[test]
    fn overwrite_output() {
        let store = Store::open_in_memory().unwrap();
        let k = key("M", "foo");
        store.put_output(&k, [1u8; 32], [2u8; 32], b"v1").unwrap();
        store.put_output(&k, [3u8; 32], [4u8; 32], b"v2").unwrap();
        let row = store.get_output(&k).unwrap().unwrap();
        assert_eq!(row.input_hash, [3u8; 32]);
        assert_eq!(row.output_blob, b"v2");
    }

    #[test]
    fn deps_round_trip_and_reverse() {
        let mut store = Store::open_in_memory().unwrap();
        let k = key("M", "foo");
        let deps = vec![
            DepEdge { dep_module: "M".into(), dep_decl: "bar".into(), dep_pass: "test_pass".into() },
            DepEdge { dep_module: "N".into(), dep_decl: "baz".into(), dep_pass: "test_pass".into() },
        ];
        store.put_deps(&k, &deps).unwrap();
        let got = store.get_deps(&k).unwrap();
        assert_eq!(got.len(), 2);
        let rev = store.dependents_of("N", "baz", "test_pass").unwrap();
        assert_eq!(rev.len(), 1);
        assert_eq!(rev[0].module, "M");
        assert_eq!(rev[0].decl, "foo");
    }

    #[test]
    fn put_deps_replaces() {
        let mut store = Store::open_in_memory().unwrap();
        let k = key("M", "foo");
        store.put_deps(&k, &[DepEdge {
            dep_module: "X".into(), dep_decl: "a".into(), dep_pass: "test_pass".into(),
        }]).unwrap();
        store.put_deps(&k, &[DepEdge {
            dep_module: "Y".into(), dep_decl: "b".into(), dep_pass: "test_pass".into(),
        }]).unwrap();
        let got = store.get_deps(&k).unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].dep_module, "Y");
    }

    #[test]
    fn module_memo_round_trip_and_source_hashes() {
        let store = Store::open_in_memory().unwrap();
        assert!(store.get_module_memo_blob("M").unwrap().is_none());
        assert!(store.module_source_hashes().unwrap().is_empty());

        store.put_module_memo("M", [7u8; 32], b"memo-blob", [1u8; 32], [2u8; 32]).unwrap();
        store.put_module_memo("N", [9u8; 32], b"other", [3u8; 32], [4u8; 32]).unwrap();

        assert_eq!(store.get_module_memo_blob("M").unwrap().unwrap(), b"memo-blob");
        let hashes = store.module_source_hashes().unwrap();
        assert_eq!(hashes.get("M"), Some(&[7u8; 32]));
        assert_eq!(hashes.get("N"), Some(&[9u8; 32]));
        assert_eq!(store.module_interface_hashes().unwrap().get("M"), Some(&[1u8; 32]));
        assert_eq!(store.module_deps_combined_hashes().unwrap().get("M"), Some(&[2u8; 32]));

        // Overwrite updates blob, source hash, and drift hashes.
        store.put_module_memo("M", [8u8; 32], b"memo-v2", [5u8; 32], [6u8; 32]).unwrap();
        assert_eq!(store.get_module_memo_blob("M").unwrap().unwrap(), b"memo-v2");
        assert_eq!(store.module_source_hashes().unwrap().get("M"), Some(&[8u8; 32]));
        assert_eq!(store.module_interface_hashes().unwrap().get("M"), Some(&[5u8; 32]));
        assert_eq!(store.module_deps_combined_hashes().unwrap().get("M"), Some(&[6u8; 32]));
    }

    #[test]
    fn module_memo_persists_across_reopen() {
        let tmp = tempfile::NamedTempFile::new().unwrap();
        let path = tmp.path().to_path_buf();
        drop(tmp);
        {
            let store = Store::open(&path).unwrap();
            store.put_module_memo("M", [3u8; 32], b"persisted", [1u8; 32], [2u8; 32]).unwrap();
        }
        {
            let store = Store::open(&path).unwrap();
            assert_eq!(store.get_module_memo_blob("M").unwrap().unwrap(), b"persisted");
            assert_eq!(store.module_source_hashes().unwrap().get("M"), Some(&[3u8; 32]));
            assert_eq!(store.module_interface_hashes().unwrap().get("M"), Some(&[1u8; 32]));
        }
        let _ = std::fs::remove_file(&path);
    }
}
