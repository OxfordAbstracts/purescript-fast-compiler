//! Expression IR — `cst::Expr` minus operator-shaped nodes.
//!
//! After [`super::lower::lower_module`], every operator has been
//! rebracketed into an `App`; every operator-in-parens has been
//! replaced by the target `Var`; every backtick application has
//! been expanded into nested `App` calls. The removed variants are:
//!
//! - `Op { left, op, right }`
//! - `OpParens { op }`
//! - `BacktickApp { func, left, right }`
//!
//! Everything else is one-to-one with [`crate::cst::Expr`] except
//! the child `Expr` slots are [`Expr`], the binders are
//! [`super::Binder`], etc.

use crate::cst;
use crate::names::{ConstructorName, Qualified, Resolved, ValueName};
use crate::span::Span;

use super::binder::{Binder, RecordBinderField};

/// Type-level sub-structures are reused from the CST since we
/// don't lower type syntax in this pass.
pub use crate::cst::{Spanned, TypeExpr};
pub use crate::names::{LabelName, ModuleQualifier};

/// Mirror of [`crate::cst::Literal`] — the `Array` variant carries
/// [`Expr`] rather than `cst::Expr`, so literals transitively stay
/// operator-free.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
    Char(char),
    Boolean(bool),
    Array(Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var {
        span: Span,
        /// Post-lowering, this is a `Resolved<ValueName>` — the module
        /// qualifier is always present. Pre-resolve_pass the module
        /// field carries `ModuleQualifier::unresolved()` as a
        /// sentinel; resolve_pass replaces it with the defining
        /// module. Downstream consumers can rely on the field being
        /// non-Option.
        name: Resolved<ValueName>,
    },
    Constructor {
        span: Span,
        name: Resolved<ConstructorName>,
    },
    Literal {
        span: Span,
        lit: Literal,
    },
    App {
        span: Span,
        func: Box<Expr>,
        arg: Box<Expr>,
    },
    VisibleTypeApp {
        span: Span,
        func: Box<Expr>,
        ty: TypeExpr,
    },
    Lambda {
        span: Span,
        binders: Vec<Binder>,
        body: Box<Expr>,
    },
    If {
        span: Span,
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    Case {
        span: Span,
        exprs: Vec<Expr>,
        alts: Vec<super::decl::CaseAlternative>,
    },
    Let {
        span: Span,
        bindings: Vec<super::decl::LetBinding>,
        body: Box<Expr>,
        /// true when this Let was synthesized from a `where` clause.
        /// `where` bindings are mutually recursive — pattern-bound names
        /// are in scope for all sibling value definitions. Plain `let`
        /// expressions use source-order sequential semantics instead.
        is_where: bool,
    },
    Do {
        span: Span,
        module: Option<ModuleQualifier>,
        statements: Vec<super::decl::DoStatement>,
    },
    Ado {
        span: Span,
        module: Option<ModuleQualifier>,
        statements: Vec<super::decl::DoStatement>,
        result: Box<Expr>,
    },
    Record {
        span: Span,
        fields: Vec<RecordField>,
    },
    RecordAccess {
        span: Span,
        expr: Box<Expr>,
        field: Spanned<LabelName>,
    },
    RecordUpdate {
        span: Span,
        expr: Box<Expr>,
        updates: Vec<RecordUpdate>,
    },
    Parens {
        span: Span,
        expr: Box<Expr>,
    },
    TypeAnnotation {
        span: Span,
        expr: Box<Expr>,
        ty: TypeExpr,
    },
    Wildcard {
        span: Span,
    },
    Hole {
        span: Span,
        name: ValueName,
    },
    Array {
        span: Span,
        elements: Vec<Expr>,
    },
    Negate {
        span: Span,
        expr: Box<Expr>,
    },
    AsPattern {
        span: Span,
        name: Box<Expr>,
        pattern: Box<Expr>,
    },
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var { span, .. }
            | Expr::Constructor { span, .. }
            | Expr::Literal { span, .. }
            | Expr::App { span, .. }
            | Expr::VisibleTypeApp { span, .. }
            | Expr::Lambda { span, .. }
            | Expr::If { span, .. }
            | Expr::Case { span, .. }
            | Expr::Let { span, .. }
            | Expr::Do { span, .. }
            | Expr::Ado { span, .. }
            | Expr::Record { span, .. }
            | Expr::RecordAccess { span, .. }
            | Expr::RecordUpdate { span, .. }
            | Expr::Parens { span, .. }
            | Expr::TypeAnnotation { span, .. }
            | Expr::Wildcard { span }
            | Expr::Hole { span, .. }
            | Expr::Array { span, .. }
            | Expr::Negate { span, .. }
            | Expr::AsPattern { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub span: Span,
    pub label: Spanned<LabelName>,
    pub value: Option<Expr>,
    pub type_ann: Option<TypeExpr>,
    pub is_update: bool,
    pub is_nested: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordUpdate {
    pub span: Span,
    pub label: Spanned<LabelName>,
    pub value: Expr,
}

// Silence unused-import complaints when an `ir::Expr` test fixture
// is compiled without the downstream typechecker consumers.
#[allow(dead_code)]
fn _touch_cst_anchor(_: &cst::Expr) {}
