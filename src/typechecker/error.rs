use thiserror;

use crate::ast::span::Span;
use crate::interner;
use crate::interner::Symbol;
use crate::typechecker::types::{TyVarId, Type};

/// Type checking errors with source location information.
#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    /// Two types could not be unified
    #[error("Could not match type {expected} with type {found}")]
    UnificationError {
        span: Span,
        expected: Type,
        found: Type,
    },

    /// Occurs check failure (infinite type)
    #[error("An infinite type was inferred for type variable t{}: {ty}", var.0)]
    InfiniteType {
        span: Span,
        var: TyVarId,
        ty: Type,
    },

    /// Variable not found in scope
    #[error("Unknown value {}", interner::resolve(*name).unwrap_or_default())]
    UndefinedVariable {
        span: Span,
        name: Symbol,
    },

    /// Type signature without a corresponding value declaration
    #[error("The type declaration for {} has no corresponding value declaration", interner::resolve(*name).unwrap_or_default())]
    OrphanTypeSignature {
        span: Span,
        name: Symbol,
    },

    /// Duplicate type signature for the same name
    #[error("Duplicate type declaration for {}", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeSignature {
        span: Span,
        name: Symbol,
    },

    /// Typed hole: ?name reports the inferred type at that point
    #[error("Hole ?{} has the inferred type {ty}", interner::resolve(*name).unwrap_or_default())]
    TypeHole {
        span: Span,
        name: Symbol,
        ty: Type,
    },

    /// Arity mismatch between equations of the same function
    #[error("The function {} was defined with {expected} arguments in one equation but {found} in another", interner::resolve(*name).unwrap_or_default())]
    ArityMismatch {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    /// No instance found for a type class constraint
    #[error("No type class instance was found for {class} {args}",
        class = interner::resolve(*class_name).unwrap_or_default(),
        args = type_args.iter().map(|ty| format!("{}", ty)).collect::<Vec<_>>().join(" ")
    )]
    NoInstanceFound {
        span: Span,
        class_name: Symbol,
        type_args: Vec<Type>,
    },

    /// Non-exhaustive pattern match
    #[error("A case expression could not be determined to cover all inputs. The following patterns are missing: {}", missing.join(", "))]
    NonExhaustivePattern {
        span: Span,
        type_name: Symbol,
        missing: Vec<String>,
    },

    /// Export of undeclared name
    #[error("Cannot export undeclared value {}", interner::resolve(*name).unwrap_or_default())]
    UnkownExport {
        span: Span,
        name: Symbol,
    },

    /// Unknown type
    #[error("Unknown type {}", interner::resolve(*name).unwrap_or_default())]
    UnknownType {
        span: Span,
        name: Symbol,
    },

    /// Duplicate value declaration for the same name
    #[error("The value {} has been defined multiple times", interner::resolve(*name).unwrap_or_default())]
    DuplicateValueDeclaration {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Kind declaration without a corresponding type declaration
    #[error("The kind declaration for {} has no corresponding type declaration", interner::resolve(*name).unwrap_or_default())]
    OrphanKindDeclaration {
        span: Span,
        name: Symbol,
    },

    /// Imported module not found
    #[error("Module {} was not found", interner::resolve(*name).unwrap_or_default())]
    ModuleNotFound {
        span: Span,
        name: Symbol,
    },

    /// Multiple fixity declarations for the same operator
    #[error("Multiple fixity declarations for operator {}", interner::resolve(*name).unwrap_or_default())]
    MultipleValueOpFixities {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Multiple fixity declarations for the same type operator
    #[error("Multiple fixity declarations for type operator {}", interner::resolve(*name).unwrap_or_default())]
    MultipleTypeOpFixities {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Overlapping names in a let binding
    #[error("The value {} has been defined multiple times in a let binding", interner::resolve(*name).unwrap_or_default())]
    OverlappingNamesInLet {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Overlapping pattern variable names in a pattern match
    #[error("The variable {} appears more than once in a pattern", interner::resolve(*name).unwrap_or_default())]
    OverlappingPattern {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Unknown import (name not found in imported module)
    #[error("Cannot import {}, as it is not exported by the module", interner::resolve(*name).unwrap_or_default())]
    UnknownImport {
        span: Span,
        name: Symbol,
    },

    /// Unknown data constructor import: import A (MyType(Exists, DoesNotExist))
    #[error("Cannot import unknown data constructor {}", interner::resolve(*name).unwrap_or_default())]
    UnknownImportDataConstructor {
        span: Span,
        name: Symbol,
    },

    /// Incorrect number of arguments to a data constructor in a binder
    #[error("Constructor {} expects {expected} arguments but was given {found}", interner::resolve(*name).unwrap_or_default())]
    IncorrectConstructorArity {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    /// Duplicate field labels in a record type or pattern
    #[error("The label {} appears more than once in a record", interner::resolve(*name).unwrap_or_default())]
    DuplicateLabel {
        record_span: Span,
        field_spans: Vec<Span>,
        name: Symbol,
    },

    /// Invalid newtype derived instance. E.g. derive instance Newtype NotANewtype
    #[error("Cannot derive a Newtype instance for {}: it is not a newtype", interner::resolve(*name).unwrap_or_default())]
    InvalidNewtypeInstance {
        span: Span,
        name: Symbol,
    },

    /// derive newtype instance on a type that isn't an instance of Newtype. E.g. derive newtype instance MyClass NotANewtype
    #[error("Cannot use newtype deriving for {} because it does not have a Newtype instance", interner::resolve(*name).unwrap_or_default())]
    InvalidNewtypeDerivation {
        span: Span,
        name: Symbol,
    },

    /// 2 modules have the same name in the project
    #[error("Module {} has been defined multiple times (also defined in {other_file_path})", interner::resolve(*name).unwrap_or_default())]
    DuplicateModule {
        span: Span,
        name: Symbol,
        other_file_path: String,
    },

    /// Multiple type classes with the same name
    #[error("The type class {} has been defined multiple times", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeClass {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Multiple class instances with the same name
    #[error("The instance {} has been defined multiple times", interner::resolve(*name).unwrap_or_default())]
    DuplicateInstance {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Multiple args to a type with the same name
    #[error("The type variable {} appears more than once in a type declaration", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeArgument {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Invalid do bind. Eg on the last line of a do block
    #[error("A bind statement cannot be the last statement in a do block")]
    InvalidDoBind {
        span: Span,
    },

    /// Invalid do let. Eg on the last line of a do block
    #[error("A let statement cannot be the last statement in a do block")]
    InvalidDoLet {
        span: Span,
    },

    /// Multiple type synonyms that reference each other in a cycle
    #[error("A cycle was found in type synonym declarations involving {}: {}",
        interner::resolve(*name).unwrap_or_default(),
        names_in_cycle.iter().map(|n| interner::resolve(*n).unwrap_or_default()).collect::<Vec<_>>().join(" -> ")
    )]
    CycleInTypeSynonym {
        name: Symbol,
        span: Span,
        names_in_cycle: Vec<Symbol>,
        spans: Vec<Span>,
    },

    /// Multiple type classes that reference each other in a cycle
    #[error("A cycle was found in type class declarations involving {}: {}",
        interner::resolve(*name).unwrap_or_default(),
        names_in_cycle.iter().map(|n| interner::resolve(*n).unwrap_or_default()).collect::<Vec<_>>().join(" -> ")
    )]
    CycleInTypeClassDeclaration {
        name: Symbol,
        span: Span,
        names_in_cycle: Vec<Symbol>,
        spans: Vec<Span>,
    },

    /// Cycle in kind declarations
    #[error("A cycle was found in kind declarations involving {}: {}",
        interner::resolve(*name).unwrap_or_default(),
        names_in_cycle.iter().map(|n| interner::resolve(*n).unwrap_or_default()).collect::<Vec<_>>().join(" -> ")
    )]
    CycleInKindDeclaration {
        name: Symbol,
        span: Span,
        names_in_cycle: Vec<Symbol>,
        spans: Vec<Span>,
    },

    /// Cycle in module imports
    #[error("A cycle was found in module imports involving {}: {}",
        interner::resolve(*name).unwrap_or_default(),
        other_modules.iter().map(|(n, _)| interner::resolve(*n).unwrap_or_default()).collect::<Vec<_>>().join(" -> ")
    )]
    CycleInModules {
        name: Symbol,
        span: Span,
        other_modules: Vec<(Symbol, String)>,
    },

    /// Overlapping argument names in a function
    #[error("The argument {} appears more than once in a function definition", interner::resolve(*name).unwrap_or_default())]
    OverlappingArgNames {
        span: Span,
        name: Symbol,
        spans: Vec<Span>,
    },

    /// Feature not yet implemented in the typechecker
    #[error("Not yet implemented: {feature}")]
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
            | TypeError::NoInstanceFound { span, .. }
            | TypeError::NonExhaustivePattern { span, .. }
            | TypeError::UnkownExport { span, .. }
            | TypeError::UnknownType { span, .. }
            | TypeError::OrphanKindDeclaration { span, .. }
            | TypeError::ModuleNotFound { span, .. }
            | TypeError::UnknownImport { span, .. }
            | TypeError::UnknownImportDataConstructor { span, .. }
            | TypeError::InvalidNewtypeDerivation { span, .. }
            | TypeError::InvalidNewtypeInstance { span, .. }
            | TypeError::IncorrectConstructorArity { span, .. }
            | TypeError::DuplicateModule { span, .. }
            | TypeError::InvalidDoBind { span, .. }
            | TypeError::InvalidDoLet { span, .. }
            | TypeError::CycleInTypeSynonym { span, .. }
            | TypeError::CycleInTypeClassDeclaration { span, .. }
            | TypeError::CycleInKindDeclaration { span, .. }
            | TypeError::CycleInModules { span, .. }
            | TypeError::OverlappingArgNames { span, .. } => *span,
            TypeError::DuplicateValueDeclaration { spans, .. }
            | TypeError::MultipleValueOpFixities { spans, .. }
            | TypeError::MultipleTypeOpFixities { spans, .. }
            | TypeError::OverlappingNamesInLet { spans, .. }
            | TypeError::OverlappingPattern { spans, .. }
            | TypeError::DuplicateTypeClass { spans, .. }
            | TypeError::DuplicateInstance { spans, .. }
            | TypeError::DuplicateTypeArgument { spans, .. } => spans[0],
            TypeError::DuplicateLabel { record_span, .. } => *record_span,
        }
    }
}
