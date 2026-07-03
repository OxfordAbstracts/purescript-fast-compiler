//! Nanopass stages for the incremental typechecker.
//!
//! Each pass is a pure function `(inputs) -> output`, cached in
//! [`crate::typecheck_db::TypecheckDb`] under a key derived from its input
//! hash. See the design doc for the full pipeline.

pub mod parse_decl;
pub mod desugar_decl;
pub mod names;
pub mod resolve_pass;
pub mod signatures;
pub mod ctor_details;
pub mod kinds;
pub mod infer_value;
pub mod exhaustiveness;
pub mod instance_index;
pub mod constraints;
pub mod imports;
pub mod check_nonvalue;
pub mod validate_decls;
pub mod kind_check;
pub mod coercible_check;
pub mod check_ffi;
pub mod codegen_decl;
pub mod warnings;
