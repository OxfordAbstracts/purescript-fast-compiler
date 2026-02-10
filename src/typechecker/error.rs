use std::fmt;

use crate::ast::span::Span;
use crate::interner;
use crate::typechecker::types::{Type, TyVarId};
use crate::interner::Symbol;

/// Type checking errors with source location information.
#[derive(Debug, Clone)]
pub enum TypeError {
    /// Two types could not be unified
    UnificationError {
        span: Span,
        expected: Type,
        found: Type,
    },

    /// Occurs check failure (infinite type)
    InfiniteType {
        span: Span,
        var: TyVarId,
        ty: Type,
    },

    /// Variable not found in scope
    UndefinedVariable {
        span: Span,
        name: Symbol,
    },

    /// Feature not yet implemented in the typechecker
    NotImplemented {
        span: Span,
        feature: String,
    },
}

impl TypeError {
    pub fn span(&self) -> Span {
        match self {
            TypeError::UnificationError { span, .. } => *span,
            TypeError::InfiniteType { span, .. } => *span,
            TypeError::UndefinedVariable { span, .. } => *span,
            TypeError::NotImplemented { span, .. } => *span,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnificationError { expected, found, .. } => {
                write!(f, "could not match type {} with {}", expected, found)
            }
            TypeError::InfiniteType { var, ty, .. } => {
                write!(f, "infinite type: ?{} occurs in {}", var.0, ty)
            }
            TypeError::UndefinedVariable { name, .. } => {
                write!(
                    f,
                    "variable not in scope: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::NotImplemented { feature, .. } => {
                write!(f, "not yet implemented: {}", feature)
            }
        }
    }
}

impl std::error::Error for TypeError {}
