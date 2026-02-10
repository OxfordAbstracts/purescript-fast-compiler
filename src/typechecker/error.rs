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

    /// Type signature without a corresponding value declaration
    OrphanTypeSignature {
        span: Span,
        name: Symbol,
    },

    /// Duplicate type signature for the same name
    DuplicateTypeSignature {
        span: Span,
        name: Symbol,
    },

    /// Typed hole: ?name reports the inferred type at that point
    TypeHole {
        span: Span,
        name: Symbol,
        ty: Type,
    },

    /// Arity mismatch between equations of the same function
    ArityMismatch {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    /// No instance found for a type class constraint
    NoClassInstance {
        span: Span,
        class_name: Symbol,
        type_args: Vec<Type>,
    },

    /// Non-exhaustive pattern match
    NonExhaustivePattern {
        span: Span,
        type_name: Symbol,
        missing: Vec<Symbol>,
    },

    /// Export of undeclared name
    UndefinedExport {
        span: Span,
        name: Symbol,
    },
}

impl TypeError {
    pub fn span(&self) -> Span {
        match self {
            TypeError::UnificationError { span, .. }
            | TypeError::InfiniteType { span, .. }
            | TypeError::UndefinedVariable { span, .. }
            | TypeError::NotImplemented { span, .. }
            | TypeError::OrphanTypeSignature { span, .. }
            | TypeError::DuplicateTypeSignature { span, .. }
            | TypeError::TypeHole { span, .. }
            | TypeError::ArityMismatch { span, .. }
            | TypeError::NoClassInstance { span, .. }
            | TypeError::NonExhaustivePattern { span, .. }
            | TypeError::UndefinedExport { span, .. } => *span,
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
            TypeError::OrphanTypeSignature { name, .. } => {
                write!(
                    f,
                    "orphan type signature: {} has no corresponding value declaration",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::DuplicateTypeSignature { name, .. } => {
                write!(
                    f,
                    "duplicate type signature for {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::TypeHole { name, ty, .. } => {
                write!(
                    f,
                    "hole ?{} has type: {}",
                    interner::resolve(*name).unwrap_or_default(),
                    ty
                )
            }
            TypeError::ArityMismatch { name, expected, found, .. } => {
                write!(
                    f,
                    "arity mismatch for {}: expected {} arguments but found {}",
                    interner::resolve(*name).unwrap_or_default(),
                    expected,
                    found
                )
            }
            TypeError::NoClassInstance { class_name, type_args, .. } => {
                let args_str = type_args
                    .iter()
                    .map(|ty| format!("{}", ty))
                    .collect::<Vec<_>>()
                    .join(" ");
                write!(
                    f,
                    "no instance found for {} {}",
                    interner::resolve(*class_name).unwrap_or_default(),
                    args_str
                )
            }
            TypeError::NonExhaustivePattern { type_name, missing, .. } => {
                let missing_str = missing
                    .iter()
                    .map(|s| interner::resolve(*s).unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    f,
                    "non-exhaustive pattern match on {}: missing {}",
                    interner::resolve(*type_name).unwrap_or_default(),
                    missing_str
                )
            }
            TypeError::UndefinedExport { name, .. } => {
                write!(
                    f,
                    "export of undeclared name: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
        }

    }
}

impl std::error::Error for TypeError {}
