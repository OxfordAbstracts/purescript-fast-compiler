//! Nanopass stages for the incremental typechecker.
//!
//! Each pass is a pure function `(inputs) -> output`, cached in
//! [`crate::typecheck_db::TypecheckDb`] under a key derived from its input
//! hash. See the design doc for the full pipeline.

pub mod parse_decl;
pub mod names;
pub mod signatures;
pub mod ctor_details;
pub mod kinds;
