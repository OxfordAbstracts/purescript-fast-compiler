//! Incremental typechecker with a persistent per-declaration cache.
//!
//! See `~/.claude/plans/wondrous-fluttering-moonbeam.md` for the design.
//!
//! M1 scope: storage + keying infrastructure + a trivial `parse_decl` pass
//! that demonstrates a cache round-trip. No typechecking yet.

pub mod key;
pub mod store;
pub mod driver;
pub mod util;
pub mod types;
pub mod unify;
pub mod env;
pub mod generalize;
pub mod desugar;
pub mod ir;
pub mod module_registry;
pub mod prim;
pub mod driver_multi;
pub mod passes;

#[cfg(test)]
mod tests;

pub use driver::{CacheOutcome, TypecheckDb};
pub use key::{InputHash, InputHasher, OutputHash, PassKey};
pub use store::{PassRow, Store, StoreError};
pub use types::{Constraint, QName, Scheme, Type, TypeOpMap};
