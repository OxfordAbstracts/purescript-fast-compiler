use thiserror;

use crate::ast::span::Span;
use crate::interner;
use crate::interner::Symbol;
use crate::typechecker::types::{TyVarId, Type};

/// Type checking errors with source location information.
#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    /// Two types could not be unified
    #[error("Could not match type {expected} with type {found} at {span}")]
    UnificationError {
        span: Span,
        expected: Type,
        found: Type,
    },

    /// Occurs check failure (infinite type)
    #[error("An infinite type was inferred for type variable t{}: {ty} at {span} ", var.0)]
    InfiniteType { span: Span, var: TyVarId, ty: Type },

    #[error("An infinite kind was inferred for type t{}: {ty} at {span} ", var.0)]
    InfiniteKind { span: Span, var: TyVarId, ty: Type },

    /// Variable not found in scope
    #[error("Unknown value {} at {span}", interner::resolve(*name).unwrap_or_default())]
    UndefinedVariable { span: Span, name: Symbol },

    /// Type signature without a corresponding value declaration
    #[error("The type declaration for {} has no corresponding value declaration at {span}", interner::resolve(*name).unwrap_or_default())]
    OrphanTypeSignature { span: Span, name: Symbol },

    /// Duplicate type signature for the same name
    #[error("Duplicate type declaration for {} at {span}", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeSignature { span: Span, name: Symbol },

    /// Typed hole: ?name reports the inferred type at that point
    #[error("Hole ?{} has the inferred type {ty} at {span}", interner::resolve(*name).unwrap_or_default())]
    HoleInferredType { span: Span, name: Symbol, ty: Type },

    /// Arity mismatch between equations of the same function
    #[error("The function {} was defined with {expected} arguments in one equation but {found} in another at {span}", interner::resolve(*name).unwrap_or_default())]
    ArityMismatch {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    /// No instance found for a type class constraint
    #[error("No type class instance was found for {class} {args} at {span}",
        class = interner::resolve(*class_name).unwrap_or_default(),
        args = type_args.iter().map(|ty| format!("{}", ty)).collect::<Vec<_>>().join(" ")
    )]
    NoInstanceFound {
        span: Span,
        class_name: Symbol,
        type_args: Vec<Type>,
    },

    /// Non-exhaustive pattern match
    #[error("A case expression could not be determined to cover all inputs. The following patterns are missing: {} at {span}", missing.join(", "))]
    NonExhaustivePattern {
        span: Span,
        type_name: Symbol,
        missing: Vec<String>,
    },

    /// Export of undeclared name
    #[error("Cannot export undeclared value {} at {span}", interner::resolve(*name).unwrap_or_default())]
    UnkownExport { span: Span, name: Symbol },

    /// Unknown type
    #[error("Unknown type {} at {span}", interner::resolve(*name).unwrap_or_default())]
    UnknownType { span: Span, name: Symbol },

    /// Duplicate value declaration for the same name
    #[error("The value {} has been defined multiple times at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    DuplicateValueDeclaration { spans: Vec<Span>, name: Symbol },

    /// Kind declaration without a corresponding type declaration
    #[error("The kind declaration for {} has no corresponding type declaration at {span}", interner::resolve(*name).unwrap_or_default())]
    OrphanKindDeclaration { span: Span, name: Symbol },

    /// Imported module not found
    #[error("Module {} was not found at {span}", interner::resolve(*name).unwrap_or_default())]
    ModuleNotFound { span: Span, name: Symbol },

    /// Multiple fixity declarations for the same operator
    #[error("Multiple fixity declarations for operator {} at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    MultipleValueOpFixities { spans: Vec<Span>, name: Symbol },

    /// Multiple fixity declarations for the same type operator
    #[error("Multiple fixity declarations for type operator {} at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    MultipleTypeOpFixities { spans: Vec<Span>, name: Symbol },

    /// Overlapping names in a let binding
    #[error("The value {} has been defined multiple times in a let binding at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    OverlappingNamesInLet { spans: Vec<Span>, name: Symbol },

    /// Overlapping pattern variable names in a pattern match
    #[error("The variable {} appears more than once in a pattern at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    OverlappingPattern { spans: Vec<Span>, name: Symbol },

    /// Unknown import (name not found in imported module)
    #[error("Cannot import {}, as it is not exported by the module at {span}", interner::resolve(*name).unwrap_or_default())]
    UnknownImport { span: Span, name: Symbol },

    /// Unknown data constructor import: import A (MyType(Exists, DoesNotExist))
    #[error("Cannot import unknown data constructor {} at {span}", interner::resolve(*name).unwrap_or_default())]
    UnknownImportDataConstructor { span: Span, name: Symbol },

    /// Incorrect number of arguments to a data constructor in a binder
    #[error("Constructor {} expects {expected} arguments but was given {found} at {span}", interner::resolve(*name).unwrap_or_default())]
    IncorrectConstructorArity {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    /// Duplicate field labels in a record type or pattern
    #[error("The label {} appears more than once in a record at {record_span}", interner::resolve(*name).unwrap_or_default())]
    DuplicateLabel {
        record_span: Span,
        field_spans: Vec<Span>,
        name: Symbol,
    },

    /// Invalid newtype derived instance. E.g. derive instance Newtype NotANewtype
    #[error("Cannot derive a Newtype instance for {}: it is not a newtype at {span}", interner::resolve(*name).unwrap_or_default())]
    InvalidNewtypeInstance { span: Span, name: Symbol },

    /// derive newtype instance on a type that isn't an instance of Newtype. E.g. derive newtype instance MyClass NotANewtype
    #[error("Cannot use newtype deriving for {} because it does not have a Newtype instance at {span}", interner::resolve(*name).unwrap_or_default())]
    InvalidNewtypeDerivation { span: Span, name: Symbol },

    /// Multiple type classes with the same name
    #[error("The type class {} has been defined multiple times at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeClass { spans: Vec<Span>, name: Symbol },

    /// Multiple class instances with the same name
    #[error("The instance {} has been defined multiple times at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    DuplicateInstance { spans: Vec<Span>, name: Symbol },

    /// Multiple args to a type with the same name
    #[error("The type variable {} appears more than once in a type declaration at {spans:?}", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeArgument { spans: Vec<Span>, name: Symbol },

    /// Invalid do bind. Eg on the last line of a do block
    #[error("A bind statement cannot be the last statement in a do block at {span}")]
    InvalidDoBind { span: Span },

    /// Invalid do let. Eg on the last line of a do block
    #[error("A let statement cannot be the last statement in a do block at {span}")]
    InvalidDoLet { span: Span },

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

    /// Overlapping argument names in a function
    #[error("The argument {} appears more than once in a function definition at {span}", interner::resolve(*name).unwrap_or_default())]
    OverlappingArgNames {
        span: Span,
        name: Symbol,
        spans: Vec<Span>,
    },

    /// Feature not yet implemented in the typechecker
    #[error("Not yet implemented: {feature} at {span}")]
    NotImplemented { span: Span, feature: String },
    #[error("The name {} cannot be brought into scope in a do notation block, since do notation uses the same name at {span}", interner::resolve(*name).unwrap_or_default())]
    CannotUseBindWithDo { span: Span, name: Symbol },

    #[error("A cycle was found in declarations involving {} at {span}. Others: {}",
        interner::resolve(*name).unwrap_or_default(),
        others_in_cycle.iter().map(|(n, _)| interner::resolve(*n).unwrap_or_default()).collect::<Vec<_>>().join(" -> ")
    )]
    CycleInDeclaration {
        name: Symbol,
        span: Span,
        others_in_cycle: Vec<(Symbol, Span)>,
    },

    #[error("The class {} is not defined at {span}", interner::resolve(*name).unwrap_or_default())]
    UnknownClass { span: Span, name: Symbol },

    #[error("The class {} is missing the following members at {span}: {}",
        interner::resolve(*class_name).unwrap_or_default(),
        members.iter().map(|(n, ty)| format!("{} :: {}", interner::resolve(*n).unwrap_or_default(), ty)).collect::<Vec<_>>().join(", ")
    )]
    MissingClassMember {
        span: Span,
        class_name: Symbol,
        members: Vec<(Symbol, Type)>,
    },

    #[error("The class {} has the following extraneous member at {span}: {}",
        interner::resolve(*class_name).unwrap_or_default(),
        interner::resolve(*member_name).unwrap_or_default()
    )]
    ExtraneousClassMember {
        span: Span,
        class_name: Symbol,
        member_name: Symbol,
    },
    /// Declaration conflict: a name is used for two different kinds of declarations
    #[error("Declaration for {new_kind} {} conflicts with an existing {existing_kind} of the same name at {span}",
        interner::resolve(*name).unwrap_or_default()
    )]
    DeclConflict {
        span: Span,
        name: Symbol,
        new_kind: &'static str,
        existing_kind: &'static str,
    },

    // paras [ line $ "Unable to generalize the type of the recursive function " <> markCode (showIdent ident) <> "."
    //       , line $ "The inferred type of " <> markCode (showIdent ident) <> " was:"
    //       , markCodeBox $ indent $ prettyType ty
    //       , line "Try adding a type signature."
    //       ]
    #[error("Unable to generalize the type of the recursive function {}. The inferred type was {} at {span}. Try adding a type signature.", interner::resolve(*name).unwrap_or_default(), type_)]
    CannotGeneralizeRecursiveFunction {
        span: Span,
        name: Symbol,
        type_: Type,
    },

    #[error("Integer value {value} is out of range at {span}. Acceptable values fall within the range -2147483648 to 2147483647 (inclusive).")]
    IntOutOfRange {
        span: Span,
        value: i64,
    },

    #[error("The role declaration for {} should follow its definition at {span}", interner::resolve(*name).unwrap_or_default())]
    OrphanRoleDeclaration {
        span: Span,
        name: Symbol,
    },

    #[error("Duplicate role declaration for {} at {span}", interner::resolve(*name).unwrap_or_default())]
    DuplicateRoleDeclaration {
        span: Span,
        name: Symbol,
    },

    #[error("Role declarations are only supported for data types, not for type synonyms nor type classes at {span}")]
    UnsupportedRoleDeclaration {
        span: Span,
        name: Symbol,
    },

    #[error("Role declaration for {} declares {found} roles, but the type has {expected} parameters at {span}", interner::resolve(*name).unwrap_or_default())]
    RoleDeclarationArityMismatch {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    #[error("A case expression has {found} binders but {expected} scrutinee(s) at {span}")]
    CaseBinderLengthDiffers {
        span: Span,
        expected: usize,
        found: usize,
    },

    #[error("Non-associative operator {} used with another operator of the same precedence at {span}", interner::resolve(*op).unwrap_or_default())]
    NonAssociativeError {
        span: Span,
        op: Symbol,
    },

    #[error("Operators with mixed associativity at the same precedence at {span}")]
    MixedAssociativityError {
        span: Span,
    },

    #[error("The name {} in a foreign import contains a prime character which is not allowed at {span}", interner::resolve(*name).unwrap_or_default())]
    DeprecatedFFIPrime {
        span: Span,
        name: Symbol,
    },

    #[error("Type wildcards are not allowed in type definitions at {span}")]
    WildcardInTypeDefinition {
        span: Span,
    },

    #[error("Constraints are not allowed in foreign import types at {span}")]
    ConstraintInForeignImport {
        span: Span,
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
            | TypeError::HoleInferredType { span, .. }
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
            | TypeError::InvalidDoBind { span, .. }
            | TypeError::InvalidDoLet { span, .. }
            | TypeError::CycleInTypeSynonym { span, .. }
            | TypeError::CycleInTypeClassDeclaration { span, .. }
            | TypeError::CycleInKindDeclaration { span, .. }
            | TypeError::OverlappingArgNames { span, .. }
            | TypeError::InfiniteKind { span, .. }
            | TypeError::CannotUseBindWithDo { span, .. }
            | TypeError::CycleInDeclaration { span, .. }
            | TypeError::UnknownClass { span, .. }
            | TypeError::MissingClassMember { span, .. }
            | TypeError::ExtraneousClassMember { span, .. }
            | TypeError::CannotGeneralizeRecursiveFunction { span, .. }
            | TypeError::IntOutOfRange { span, .. }
            | TypeError::OrphanRoleDeclaration { span, .. }
            | TypeError::DuplicateRoleDeclaration { span, .. }
            | TypeError::UnsupportedRoleDeclaration { span, .. }
            | TypeError::RoleDeclarationArityMismatch { span, .. }
            | TypeError::CaseBinderLengthDiffers { span, .. }
            | TypeError::NonAssociativeError { span, .. }
            | TypeError::MixedAssociativityError { span, .. }
            | TypeError::DeprecatedFFIPrime { span, .. }
            | TypeError::DeclConflict { span, .. }
            | TypeError::WildcardInTypeDefinition { span, .. }
            | TypeError::ConstraintInForeignImport { span, .. } => *span,
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

    pub fn code(&self) -> String {
        match self {
            TypeError::UnificationError { .. } => "UnificationError".into(),
            TypeError::InfiniteType { .. } => "InfiniteType".into(),
            TypeError::UndefinedVariable { .. } => "UndefinedVariable".into(),
            TypeError::OrphanTypeSignature { .. } => "OrphanTypeSignature".into(),
            TypeError::DuplicateTypeSignature { .. } => "DuplicateTypeSignature".into(),
            TypeError::HoleInferredType { .. } => "HoleInferredType".into(),
            TypeError::ArityMismatch { .. } => "ArityMismatch".into(),
            TypeError::NoInstanceFound { .. } => "NoInstanceFound".into(),
            TypeError::NonExhaustivePattern { .. } => "NonExhaustivePattern".into(),
            TypeError::UnkownExport { .. } => "UnkownExport".into(),
            TypeError::UnknownType { .. } => "UnknownType".into(),
            TypeError::DuplicateValueDeclaration { .. } => "DuplicateValueDeclaration".into(),
            TypeError::OrphanKindDeclaration { .. } => "OrphanKindDeclaration".into(),
            TypeError::ModuleNotFound { .. } => "ModuleNotFound".into(),
            TypeError::UnknownImport { .. } => "UnknownImport".into(),
            TypeError::UnknownImportDataConstructor { .. } => "UnknownImportDataConstructor".into(),
            TypeError::IncorrectConstructorArity { .. } => "IncorrectConstructorArity".into(),
            TypeError::DuplicateLabel { .. } => "DuplicateLabel".into(),
            TypeError::InvalidNewtypeInstance { .. } => "InvalidNewtypeInstance".into(),
            TypeError::InvalidNewtypeDerivation { .. } => "InvalidNewtypeDerivation".into(),
            TypeError::DuplicateTypeClass { .. } => "DuplicateTypeClass".into(),
            TypeError::DuplicateInstance { .. } => "DuplicateInstance".into(),
            TypeError::DuplicateTypeArgument { .. } => "DuplicateTypeArgument".into(),
            TypeError::InvalidDoBind { .. } => "InvalidDoBind".into(),
            TypeError::InvalidDoLet { .. } => "InvalidDoLet".into(),
            TypeError::CycleInTypeSynonym { .. } => "CycleInTypeSynonym".into(),
            TypeError::CycleInTypeClassDeclaration { .. } => "CycleInTypeClassDeclaration".into(),
            TypeError::CycleInKindDeclaration { .. } => "CycleInKindDeclaration".into(),
            TypeError::MultipleValueOpFixities { .. } => "MultipleValueOpFixities".into(),
            TypeError::MultipleTypeOpFixities { .. } => "MultipleTypeOpFixities".into(),
            TypeError::OverlappingNamesInLet { .. } => "OverlappingNamesInLet".into(),
            TypeError::OverlappingPattern { .. } => "OverlappingPattern".into(),
            TypeError::OverlappingArgNames { .. } => "OverlappingArgNames".into(),
            TypeError::NotImplemented { .. } => "NotImplemented".into(),
            TypeError::InfiniteKind { .. } => "InfiniteKind".into(),
            TypeError::CannotUseBindWithDo { .. } => "CannotUseBindWithDo".into(),
            TypeError::CycleInDeclaration { .. } => "CycleInDeclaration".into(),
            TypeError::UnknownClass { .. } => "UnknownClass".into(),
            TypeError::MissingClassMember { .. } => "MissingClassMember".into(),
            TypeError::ExtraneousClassMember { .. } => "ExtraneousClassMember".into(),
            TypeError::CannotGeneralizeRecursiveFunction { .. } => "CannotGeneralizeRecursiveFunction".into(),
            TypeError::IntOutOfRange { .. } => "IntOutOfRange".into(),
            TypeError::OrphanRoleDeclaration { .. } => "OrphanRoleDeclaration".into(),
            TypeError::DuplicateRoleDeclaration { .. } => "DuplicateRoleDeclaration".into(),
            TypeError::UnsupportedRoleDeclaration { .. } => "UnsupportedRoleDeclaration".into(),
            TypeError::RoleDeclarationArityMismatch { .. } => "RoleDeclarationArityMismatch".into(),
            TypeError::CaseBinderLengthDiffers { .. } => "CaseBinderLengthDiffers".into(),
            TypeError::NonAssociativeError { .. } => "NonAssociativeError".into(),
            TypeError::MixedAssociativityError { .. } => "MixedAssociativityError".into(),
            TypeError::DeprecatedFFIPrime { .. } => "DeprecatedFFIPrime".into(),
            TypeError::DeclConflict { .. } => "DeclConflict".into(),
            TypeError::WildcardInTypeDefinition { .. } => "SyntaxError".into(),
            TypeError::ConstraintInForeignImport { .. } => "SyntaxError".into(),
        }
    }
}
