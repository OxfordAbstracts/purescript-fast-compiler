//! `desugar_decl` pass: caching wrapper around
//! [`crate::typecheck_db::desugar::desugar`].
//!
//! The desugar pipeline is composed of several sub-transforms (see
//! [`crate::typecheck_db::desugar`]), but we cache the *whole* pipeline as
//! one unit — individual sub-transforms are too cheap to earn their own
//! cache rows.
//!
//! The pass's `output_hash` is the stable identity downstream passes key
//! off of. Under the current invariant ("desugar is a function of
//! `(decl_source_hash, module_fixity_hash)`"), that output_hash is itself a
//! function of those same inputs, which is exactly what we want: a body
//! edit that preserves the normalized form produces the same output_hash
//! and propagates no invalidation downstream.

use serde::{Deserialize, Serialize};

use crate::cst::Decl;
use crate::typecheck_db::desugar::{desugar, DesugarContext};
use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::key::{InputHasher, OutputHash, PassKey};

pub const PASS_NAME: &str = "desugar_decl";
pub const PASS_VERSION: u32 = 1;

/// Cache payload.
///
/// We don't serialize the full [`Decl`] here: downstream passes receive
/// the normalized decl in-memory from the driver (just like `free_names`,
/// `infer_value_scc`, etc., all of which take `&Decl` as an in-memory
/// argument alongside a cache-key hash). What the cache row *does* need to
/// produce is a stable `output_hash` — and [`TypecheckDb::put`] derives
/// that from the serialized blob, so we persist a small `DesugarOutput`
/// whose `content_hash` is the normalized decl's stable identity.
///
/// MDa sets `content_hash = decl_source_hash` because the identity
/// transform preserves the input. MDb..MDe will replace that with a real
/// content hash of the normalized decl.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DesugarOutput {
    pub content_hash: [u8; 32],
}

pub fn run(
    db: &mut TypecheckDb,
    module: &str,
    decl_key: &str,
    decl_source_hash: [u8; 32],
    ctx: &DesugarContext,
    decl: &Decl,
) -> Result<(Decl, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(module, decl_key, PASS_NAME);
    let input_hash = InputHasher::new(PASS_NAME, PASS_VERSION)
        .with_source_hash(decl_source_hash)
        .with_module_context(ctx.module_fixity_hash)
        .finish();

    if let Some((_, output_hash)) = db.get_cached::<DesugarOutput>(&key, input_hash)? {
        let out = desugar(decl, ctx);
        return Ok((out, output_hash, CacheOutcome::Hit));
    }

    let out = desugar(decl, ctx);
    let marker = DesugarOutput { content_hash: decl_source_hash };
    let output_hash = db.put(&key, input_hash, &marker)?;
    Ok((out, output_hash, CacheOutcome::Miss))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn first_decl(src: &str) -> Decl {
        let m = parse(src).unwrap();
        m.decls.into_iter().next().unwrap()
    }

    #[test]
    fn round_trips_through_cache() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let d = first_decl("module M where\nfoo = 1\n");
        let ctx = DesugarContext::default();
        let sh = [7u8; 32];

        let (out1, h1, o1) = run(&mut db, "M", "foo", sh, &ctx, &d).unwrap();
        assert_eq!(o1, CacheOutcome::Miss);

        let (out2, h2, o2) = run(&mut db, "M", "foo", sh, &ctx, &d).unwrap();
        assert_eq!(o2, CacheOutcome::Hit);
        assert_eq!(h1, h2);
        assert_eq!(out1, out2);
    }

    #[test]
    fn source_change_invalidates() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let d = first_decl("module M where\nfoo = 1\n");
        let ctx = DesugarContext::default();

        let (_, h1, _) = run(&mut db, "M", "foo", [1u8; 32], &ctx, &d).unwrap();
        let (_, h2, o2) = run(&mut db, "M", "foo", [2u8; 32], &ctx, &d).unwrap();
        assert_eq!(o2, CacheOutcome::Miss);
        assert_ne!(h1, h2);
    }

    #[test]
    fn fixity_context_change_invalidates() {
        // A fixity-context change must cause a cache miss (the input_hash
        // changes), even though — for MDa's identity transform — the
        // normalized output is the same and the output_hash therefore
        // stays equal. When MDe's rebracketer lands, changing fixity can
        // legitimately change the normalized output too, and the
        // output_hash will diverge; that's tested at that milestone.
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let d = first_decl("module M where\nfoo = 1\n");
        let sh = [0u8; 32];

        let ctx1 = DesugarContext { module_fixity_hash: [1u8; 32] };
        let ctx2 = DesugarContext { module_fixity_hash: [2u8; 32] };

        let (_, _, o1) = run(&mut db, "M", "foo", sh, &ctx1, &d).unwrap();
        assert_eq!(o1, CacheOutcome::Miss);
        let (_, _, o2) = run(&mut db, "M", "foo", sh, &ctx2, &d).unwrap();
        assert_eq!(o2, CacheOutcome::Miss);
    }

    #[test]
    fn persists_across_store_reopen() {
        let tmp = tempfile::NamedTempFile::new().unwrap();
        let path = tmp.path().to_path_buf();
        drop(tmp);

        let d = first_decl("module M where\nfoo = 1\n");
        let ctx = DesugarContext::default();
        let sh = [3u8; 32];

        {
            let mut db = TypecheckDb::open(&path).unwrap();
            let (_, _, o) = run(&mut db, "M", "foo", sh, &ctx, &d).unwrap();
            assert_eq!(o, CacheOutcome::Miss);
        }
        {
            let mut db = TypecheckDb::open(&path).unwrap();
            let (_, _, o) = run(&mut db, "M", "foo", sh, &ctx, &d).unwrap();
            assert_eq!(o, CacheOutcome::Hit);
        }
        let _ = std::fs::remove_file(&path);
    }
}
