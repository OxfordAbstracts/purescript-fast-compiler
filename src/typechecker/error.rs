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
        missing: Vec<String>,
    },

    /// Export of undeclared name
    UnkownExport {
        span: Span,
        name: Symbol,
    },

    /// Unknown type
    UnknownType { 
        span: Span,
        name: Symbol,
    },
    
    /// Duplicate value declaration for the same name
    DuplicateValueDeclaration {
        spans: Vec<Span>,
        name: Symbol,
    },

    OrphanKindDeclaration {
        span: Span,
        name: Symbol,
    },

    /// Imported module not found
    ModuleNotFound {
        span: Span,
        name: Symbol,
    },

    /// Multiple fixity declarations for the same operator
    MultipleValueOpFixities {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Multiple fixity declarations for the same type operator
    MultipleTypeOpFixities {
        spans: Vec<Span>,
        name: Symbol,
    }, 

    /// Overlapping names in a let binding
    OverlappingNamesInLet {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Unknown import (name not found in imported module)
    UnknownImport {
        span: Span,
        name: Symbol,
    },

    /// Unknown data constructor import: import A (MyType(Exists, DoesNotExist))
    UnknownImportDataConstructor {
        span: Span,
        name: Symbol,
    },

    /// Incorrect number of arguments to a data constructor in a binder
    IncorrectConstructorArity {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    /// Duplicate field labels in a record type or pattern
    DuplicateLabel {
        record_span: Span,
        field_spans: Vec<Span>,
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
            | TypeError::UnkownExport { span, .. }
            | TypeError::UnknownType { span, .. }
            | TypeError::OrphanKindDeclaration { span, .. }
            | TypeError::ModuleNotFound { span, .. }
            | TypeError::UnknownImport { span, .. }
            | TypeError::UnknownImportDataConstructor { span, .. }
            | TypeError::IncorrectConstructorArity { span, .. } => *span,
            TypeError::DuplicateValueDeclaration { spans, .. }
            | TypeError::MultipleValueOpFixities { spans, .. }
            | TypeError::MultipleTypeOpFixities { spans, .. }
            | TypeError::OverlappingNamesInLet { spans, .. } => spans[0],
            TypeError::DuplicateLabel { record_span, .. } => *record_span,
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
                let missing_str = missing.join(", ");
                write!(
                    f,
                    "non-exhaustive pattern match on {}: missing {}",
                    interner::resolve(*type_name).unwrap_or_default(),
                    missing_str
                )
            }
            TypeError::UnkownExport { name, .. } => {
                write!(
                    f,
                    "export of undeclared name: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::UnknownType { name, .. } => {
                write!(
                    f,
                    "unknown type constructor: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::DuplicateValueDeclaration { name, .. } => {
                write!(
                    f,
                    "duplicate value declaration for {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::OrphanKindDeclaration { name, .. } => {
                write!(
                    f,
                    "orphan kind declaration: {} has no corresponding type declaration",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::ModuleNotFound { name, .. } => {
                write!(
                    f,
                    "module not found: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::MultipleValueOpFixities { name, .. } => {
                write!(
                    f,
                    "multiple fixity declarations for operator {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::MultipleTypeOpFixities { name, .. } => {
                write!(
                    f,
                    "multiple fixity declarations for type operator {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::OverlappingNamesInLet { name, .. } => {
                write!(
                    f,
                    "overlapping names in let binding: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::UnknownImport { name, .. } => {
                write!(
                    f,
                    "unknown import: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::UnknownImportDataConstructor { name, .. } => {
                write!(
                    f,
                    "unknown data constructor in import: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::IncorrectConstructorArity { name, expected, found, .. } => {
                write!(
                    f,
                    "incorrect constructor arity for {}: expected {} arguments but found {}",
                    interner::resolve(*name).unwrap_or_default(),
                    expected,
                    found
                )
            }
            TypeError::DuplicateLabel { name, .. } => {
                write!(
                    f,
                    "duplicate label in record: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
        }

    }
}

impl std::error::Error for TypeError {}
