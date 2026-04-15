//! M1 scaffolding pass: a trivial `parse_decl` that takes decl source bytes
//! and emits a small cacheable stub.
//!
//! Its purpose is to exercise the store/driver/key layers end-to-end —
//! actual CST slicing of a decl from a module lands in M2 together with the
//! names passes that need it.

use serde::{Deserialize, Serialize};

use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::key::{hash_bytes, InputHasher, OutputHash, PassKey};

pub const PASS_NAME: &str = "parse_decl";
pub const PASS_VERSION: u32 = 1;

/// Stub output for M1. Holds the decl's source plus a couple of cheap
/// derived stats so downstream passes have something to key on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParsedDeclStub {
    pub source: String,
    pub byte_len: u32,
    pub line_count: u32,
}

impl ParsedDeclStub {
    fn from_source(src: &str) -> Self {
        let line_count = 1 + src.bytes().filter(|b| *b == b'\n').count() as u32;
        Self {
            source: src.to_string(),
            byte_len: src.len() as u32,
            line_count,
        }
    }
}

/// Run `parse_decl` for one decl, going through the cache.
pub fn run(
    db: &mut TypecheckDb,
    module: &str,
    decl: &str,
    source: &str,
) -> Result<(ParsedDeclStub, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(module, decl, PASS_NAME);
    let input_hash = InputHasher::new(PASS_NAME, PASS_VERSION)
        .with_source_hash(hash_bytes(source.as_bytes()))
        .finish();

    if let Some((value, output_hash)) = db.get_cached::<ParsedDeclStub>(&key, input_hash)? {
        return Ok((value, output_hash, CacheOutcome::Hit));
    }

    let value = ParsedDeclStub::from_source(source);
    let output_hash = db.put(&key, input_hash, &value)?;
    Ok((value, output_hash, CacheOutcome::Miss))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_through_memo_and_sqlite() {
        let mut db = TypecheckDb::open_in_memory().unwrap();

        let (v1, h1, outcome1) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
        assert_eq!(outcome1, CacheOutcome::Miss);
        assert_eq!(v1.byte_len, 7);

        // Second call with same source: served from the in-process memo.
        let (v2, h2, outcome2) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
        assert_eq!(outcome2, CacheOutcome::Hit);
        assert_eq!(v1, v2);
        assert_eq!(h1, h2);

        // Drop the memo so the next read must come from SQLite.
        db.clear_memo();
        let (v3, h3, outcome3) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
        assert_eq!(outcome3, CacheOutcome::Hit);
        assert_eq!(v3, v1);
        assert_eq!(h3, h1);
    }

    #[test]
    fn source_change_invalidates_cache() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let (_, h1, o1) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
        assert_eq!(o1, CacheOutcome::Miss);
        let (_, h2, o2) = run(&mut db, "Main", "foo", "foo = 2").unwrap();
        assert_eq!(o2, CacheOutcome::Miss);
        assert_ne!(h1, h2);

        // Restoring the original source hits the stored row, even after the
        // overwrite from the `foo = 2` call.
        db.clear_memo();
        let (_, h3, o3) = run(&mut db, "Main", "foo", "foo = 2").unwrap();
        assert_eq!(o3, CacheOutcome::Hit);
        assert_eq!(h3, h2);
    }

    #[test]
    fn different_decls_cache_independently() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let (_, _, o1) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
        let (_, _, o2) = run(&mut db, "Main", "bar", "bar = 2").unwrap();
        let (_, _, o3) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
        assert_eq!(o1, CacheOutcome::Miss);
        assert_eq!(o2, CacheOutcome::Miss);
        assert_eq!(o3, CacheOutcome::Hit);
    }

    #[test]
    fn persists_across_store_reopen() {
        let tmp = tempfile::NamedTempFile::new().unwrap();
        let path = tmp.path().to_path_buf();
        drop(tmp);

        {
            let mut db = TypecheckDb::open(&path).unwrap();
            let (_, _, o) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
            assert_eq!(o, CacheOutcome::Miss);
        }
        {
            let mut db = TypecheckDb::open(&path).unwrap();
            let (v, _, o) = run(&mut db, "Main", "foo", "foo = 1").unwrap();
            assert_eq!(o, CacheOutcome::Hit);
            assert_eq!(v.source, "foo = 1");
        }
        let _ = std::fs::remove_file(&path);
    }
}
