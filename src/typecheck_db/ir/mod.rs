//! Post-desugar intermediate representation.
//!
//! This IR is what the typechecker actually consumes. It's a
//! faithful mirror of [`crate::cst`] with two deliberate omissions:
//!
//! - `Expr::Op` / `Expr::OpParens` / `Expr::BacktickApp` don't exist.
//! - `Binder::Op` doesn't exist.
//!
//! [`lower::lower_module`] is the only way to build an `ir::Module`
//! from a [`crate::cst::Module`]. Every operator is rebracketed into
//! a plain application during lowering, so any code downstream of
//! this IR sees exclusively `App` / `Constructor` — it cannot
//! structurally observe an operator node. The `Unsupported("operator")`
//! branch in [`crate::typecheck_db::passes::infer_value`] is gone by
//! construction.
//!
//! `TypeExpr` is *not* mirrored here — type-level nodes don't carry
//! value-level operators, and the typechecker already converts them
//! via [`crate::typecheck_db::types::convert_type_expr`]. We reuse
//! [`crate::cst::TypeExpr`] in type positions.
//!
//! Later milestones will add further narrowings (imports removed
//! after name resolution, `Do`/`Ado` desugared to `bind`/`ap`, etc.),
//! each as its own IR stage with its own lowering pass.

pub mod expr;
pub mod binder;
pub mod decl;
pub mod lower;

pub use binder::{Binder, RecordBinderField};
pub use decl::{
    CaseAlternative, Decl, DoStatement, Guard, GuardPattern, GuardedExpr, LetBinding,
    Module,
};
pub use expr::{Expr, Literal, RecordField, RecordUpdate};
pub use lower::{lower_decl, lower_module, LoweringError};
