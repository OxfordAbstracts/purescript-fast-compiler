//! Binder IR — `cst::Binder` minus `Binder::Op`.
//!
//! After [`super::lower::lower_module`], every operator pattern
//! (`x : xs`, `l /\ r`) has been rebracketed into a
//! `Binder::Constructor { args: [...] }`. Downstream code can
//! assume operator binders don't exist.

use crate::names::{ConstructorName, Resolved, ValueName};
#[allow(unused_imports)]
use crate::names::Qualified;
use crate::span::Span;

pub use crate::cst::{Spanned, TypeExpr};
pub use crate::names::LabelName;
pub use super::expr::Literal;

#[derive(Debug, Clone, PartialEq)]
pub enum Binder {
    Wildcard {
        span: Span,
    },
    Var {
        span: Span,
        name: Spanned<ValueName>,
    },
    Literal {
        span: Span,
        lit: Literal,
    },
    Constructor {
        span: Span,
        name: Resolved<ConstructorName>,
        args: Vec<Binder>,
    },
    Record {
        span: Span,
        fields: Vec<RecordBinderField>,
    },
    As {
        span: Span,
        name: Spanned<ValueName>,
        binder: Box<Binder>,
    },
    Parens {
        span: Span,
        binder: Box<Binder>,
    },
    Array {
        span: Span,
        elements: Vec<Binder>,
    },
    Typed {
        span: Span,
        binder: Box<Binder>,
        ty: TypeExpr,
    },
}

impl Binder {
    pub fn span(&self) -> Span {
        match self {
            Binder::Wildcard { span }
            | Binder::Var { span, .. }
            | Binder::Literal { span, .. }
            | Binder::Constructor { span, .. }
            | Binder::Record { span, .. }
            | Binder::As { span, .. }
            | Binder::Parens { span, .. }
            | Binder::Array { span, .. }
            | Binder::Typed { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordBinderField {
    pub span: Span,
    pub label: Spanned<LabelName>,
    pub binder: Option<Binder>,
}
