//! Incremental typechecker with a persistent per-declaration cache.
//!
//! See `~/.claude/plans/wondrous-fluttering-moonbeam.md` for the design.
//!
//! M1 scope: storage + keying infrastructure + a trivial `parse_decl` pass
//! that demonstrates a cache round-trip. No typechecking yet.

pub mod key;
pub mod store;
pub mod driver;
pub mod passes;

pub use driver::{CacheOutcome, TypecheckDb};
pub use key::{InputHash, InputHasher, OutputHash, PassKey};
pub use store::{PassRow, Store, StoreError};
