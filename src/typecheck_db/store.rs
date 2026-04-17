//! SQLite persistence layer for pass outputs and their dep edges.

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
"#;

/// Best-effort migration for pre-`decl_debug` databases. We detect the
/// missing column by trying to select it and, if it errors, apply the
/// ALTER. Idempotent on fresh DBs because `CREATE TABLE IF NOT EXISTS`
/// above already declares the column.
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
}
