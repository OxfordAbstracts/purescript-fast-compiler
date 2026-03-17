use std::collections::HashMap;
use std::fmt::Write;

use thiserror;

use crate::cst::QualifiedIdent;
use crate::interner;
use crate::interner::Symbol;
use crate::span::Span;
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

    /// Record fields do not match: some labels are missing and/or extra
    #[error("Record fields do not match")]
    RecordLabelMismatch {
        span: Span,
        missing: Vec<Symbol>,
        extra: Vec<Symbol>,
        expected: Type,
        found: Type,
    },

    /// Occurs check failure (infinite type)
    #[error("An infinite type was inferred for type variable t{}: {ty}", var.0)]
    InfiniteType { span: Span, var: TyVarId, ty: Type },

    #[error("An infinite kind was inferred for type t{}: {ty}", var.0)]
    InfiniteKind { span: Span, var: TyVarId, ty: Type },

    /// Variable not found in scope
    #[error("Unknown value {}", interner::resolve(*name).unwrap_or_default())]
    UndefinedVariable { span: Span, name: Symbol },

    /// Name not found in scope (used during AST name resolution, corresponds to PureScript's UnknownName)
    #[error("Unknown name {}", interner::resolve(*name).unwrap_or_default())]
    UnknownName { span: Span, name: Symbol },

    /// Type signature without a corresponding value declaration
    #[error("The type declaration for {} has no corresponding value declaration", interner::resolve(*name).unwrap_or_default())]
    OrphanTypeSignature { span: Span, name: Symbol },

    /// Duplicate type signature for the same name
    #[error("Duplicate type declaration for {}", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeSignature { span: Span, name: Symbol },

    /// Typed hole: ?name reports the inferred type at that point
    #[error("Hole ?{} has the inferred type {ty}", interner::resolve(*name).unwrap_or_default())]
    HoleInferredType {
        span: Span,
        name: Symbol,
        ty: Type,
        /// Type class constraints relevant to the hole type (class_name, type_args)
        constraints: Vec<(Symbol, Vec<Type>)>,
        /// Local bindings in scope at the hole site (name, type)
        local_bindings: Vec<(Symbol, Type)>,
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
    #[error("No type class instance was found for {class_name} {args}",
        args = type_args.iter().map(|ty| format!("{}", ty)).collect::<Vec<_>>().join(" "),
    )]
    NoInstanceFound {
        span: Span,
        class_name: QualifiedIdent,
        type_args: Vec<Type>,
    },

    /// Non-exhaustive pattern match
    #[error("A case expression could not be determined to cover all inputs. The following patterns are missing: {}", missing.join(", "))]
    NonExhaustivePattern {
        span: Span,
        type_name: QualifiedIdent,
        missing: Vec<String>,
    },

    /// Export of undeclared name
    #[error("Cannot export undeclared value {}", interner::resolve(*name).unwrap_or_default())]
    UnkownExport { span: Span, name: Symbol },

    /// Unknown type
    #[error("Unknown type {}", interner::resolve(*name).unwrap_or_default())]
    UnknownType { span: Span, name: Symbol },

    /// Duplicate value declaration for the same name
    #[error("The value {} has been defined multiple times", interner::resolve(*name).unwrap_or_default())]
    DuplicateValueDeclaration { spans: Vec<Span>, name: Symbol },

    /// Kind declaration without a corresponding type declaration
    #[error("The kind declaration for {} has no corresponding type declaration", interner::resolve(*name).unwrap_or_default())]
    OrphanKindDeclaration { span: Span, name: Symbol },

    /// Imported module not found
    #[error("Module {} was not found", interner::resolve(*name).unwrap_or_default())]
    ModuleNotFound { span: Span, name: Symbol },

    /// Multiple fixity declarations for the same operator
    #[error("Multiple fixity declarations for operator {}", interner::resolve(*name).unwrap_or_default())]
    MultipleValueOpFixities { spans: Vec<Span>, name: Symbol },

    /// Multiple fixity declarations for the same type operator
    #[error("Multiple fixity declarations for type operator {}", interner::resolve(*name).unwrap_or_default())]
    MultipleTypeOpFixities { spans: Vec<Span>, name: Symbol },

    /// Overlapping names in a let binding
    #[error("The value {} has been defined multiple times in a let binding", interner::resolve(*name).unwrap_or_default())]
    OverlappingNamesInLet { spans: Vec<Span>, name: Symbol },

    /// Overlapping pattern variable names in a pattern match
    #[error("The variable {} appears more than once in a pattern", interner::resolve(*name).unwrap_or_default())]
    OverlappingPattern { spans: Vec<Span>, name: Symbol },

    /// Unknown import (name not found in imported module)
    #[error("Cannot import {}, as it is not exported by the module", interner::resolve(*name).unwrap_or_default())]
    UnknownImport { span: Span, name: Symbol },

    /// Unknown data constructor import: import A (MyType(Exists, DoesNotExist))
    #[error("Cannot import unknown data constructor {}", interner::resolve(*name).unwrap_or_default())]
    UnknownImportDataConstructor { span: Span, name: Symbol },

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
    #[error("Cannot derive a Newtype instance for {}: it is not a newtype", name)]
    InvalidNewtypeInstance { span: Span, name: QualifiedIdent },

    /// derive newtype instance on a type that isn't an instance of Newtype. E.g. derive newtype instance MyClass NotANewtype
    #[error("Cannot use newtype deriving for {} because it does not have a Newtype instance", name)]
    InvalidNewtypeDerivation { span: Span, name: QualifiedIdent },

    /// A constructor argument is not valid for the derived class (e.g. contravariant position for Functor)
    #[error("Cannot derive instance: invalid constructor argument")]
    CannotDeriveInvalidConstructorArg { span: Span },

    /// Multiple type classes with the same name
    #[error("The type class {} has been defined multiple times", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeClass { spans: Vec<Span>, name: Symbol },

    /// Multiple class instances with the same name
    #[error("The instance {} has been defined multiple times", interner::resolve(*name).unwrap_or_default())]
    DuplicateInstance { spans: Vec<Span>, name: Symbol },

    /// Multiple args to a type with the same name
    #[error("The type variable {} appears more than once in a type declaration", interner::resolve(*name).unwrap_or_default())]
    DuplicateTypeArgument { spans: Vec<Span>, name: Symbol },

    /// Invalid do bind. Eg on the last line of a do block
    #[error("A bind statement cannot be the last statement in a do block")]
    InvalidDoBind { span: Span },

    /// Invalid do let. Eg on the last line of a do block
    #[error("A let statement cannot be the last statement in a do block")]
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
    #[error("The argument {} appears more than once in a function definition", interner::resolve(*name).unwrap_or_default())]
    OverlappingArgNames {
        span: Span,
        name: Symbol,
        spans: Vec<Span>,
    },

    /// Feature not yet implemented in the typechecker
    #[error("Not yet implemented: {feature}")]
    NotImplemented { span: Span, feature: String },
    #[error("The name {} cannot be brought into scope in a do notation block, since do notation uses the same name", interner::resolve(*name).unwrap_or_default())]
    CannotUseBindWithDo { span: Span, name: Symbol },

    #[error("A cycle was found in declarations involving {}. Others: {}",
        interner::resolve(*name).unwrap_or_default(),
        others_in_cycle.iter().map(|(n, _)| interner::resolve(*n).unwrap_or_default()).collect::<Vec<_>>().join(" -> ")
    )]
    CycleInDeclaration {
        name: Symbol,
        span: Span,
        others_in_cycle: Vec<(Symbol, Span)>,
    },

    #[error("The class {name} is not defined")]
    UnknownClass { span: Span, name: QualifiedIdent },

    #[error("The class {class_name} is missing the following members: {}",
        members.iter().map(|(n, ty)| format!("{} :: {}", interner::resolve(*n).unwrap_or_default(), ty)).collect::<Vec<_>>().join(", ")
    )]
    MissingClassMember {
        span: Span,
        class_name: QualifiedIdent,
        members: Vec<(Symbol, Type)>,
    },

    #[error("The class {class_name} has the following extraneous member: {}",
        interner::resolve(*member_name).unwrap_or_default()
    )]
    ExtraneousClassMember {
        span: Span,
        class_name: QualifiedIdent,
        member_name: Symbol,
    },
    /// Declaration conflict: a name is used for two different kinds of declarations
    #[error("Declaration for {new_kind} {} conflicts with an existing {existing_kind} of the same name",
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
    #[error("Unable to generalize the type of the recursive function {}. The inferred type was {}. Try adding a type signature.", interner::resolve(*name).unwrap_or_default(), type_)]
    CannotGeneralizeRecursiveFunction {
        span: Span,
        name: Symbol,
        type_: Type,
    },

    #[error("Cannot apply expression of type {type_} to a type argument")]
    CannotApplyExpressionOfTypeOnType { span: Span, type_: Type },

    #[error("An anonymous function argument _ appears in an invalid context")]
    IncorrectAnonymousArgument { span: Span },

    #[error("Operator {} cannot be used in a pattern as it is an alias for a function, not a data constructor",
        interner::resolve(*op).unwrap_or_default()
    )]
    InvalidOperatorInBinder { span: Span, op: Symbol },

    #[error("Integer value {value} is out of range. Acceptable values fall within the range -2147483648 to 2147483647 (inclusive).")]
    IntOutOfRange { span: Span, value: i64 },

    #[error("The role declaration for {} should follow its definition", interner::resolve(*name).unwrap_or_default())]
    OrphanRoleDeclaration { span: Span, name: Symbol },

    #[error("Duplicate role declaration for {}", interner::resolve(*name).unwrap_or_default())]
    DuplicateRoleDeclaration { span: Span, name: Symbol },

    #[error("Role declarations are only supported for data types, not for type synonyms nor type classes")]
    UnsupportedRoleDeclaration { span: Span, name: Symbol },

    #[error("Role declaration for {} declares {found} roles, but the type has {expected} parameters", interner::resolve(*name).unwrap_or_default())]
    RoleDeclarationArityMismatch {
        span: Span,
        name: Symbol,
        expected: usize,
        found: usize,
    },

    #[error("A case expression has {found} binders but {expected} scrutinee(s)")]
    CaseBinderLengthDiffers {
        span: Span,
        expected: usize,
        found: usize,
    },

    #[error("Non-associative operator {} used with another operator of the same precedence", interner::resolve(*op).unwrap_or_default())]
    NonAssociativeError { span: Span, op: Symbol },

    #[error("Operators with mixed associativity at the same precedence")]
    MixedAssociativityError { span: Span },

    #[error("The name {} in a foreign import contains a prime character which is not allowed", interner::resolve(*name).unwrap_or_default())]
    DeprecatedFFIPrime { span: Span, name: Symbol },

    #[error("Type wildcards are not allowed in type definitions")]
    WildcardInTypeDefinition { span: Span },

    #[error("Constraints are not allowed in foreign import types")]
    ConstraintInForeignImport { span: Span },

    #[error("A forall or wildcard is not allowed in a constraint argument")]
    InvalidConstraintArgument { span: Span },

    /// Syntax error in type expression (corresponds to PureScript's ErrorParsingModule)
    #[error("Syntax error")]
    SyntaxError { span: Span },

    /// Expected a wildcard type argument in a Newtype derive instance
    #[error("Expected a wildcard (_) in the Newtype instance")]
    ExpectedWildcard { span: Span, name: QualifiedIdent },

    #[error(
        "Kind mismatch: type synonym {} expects {} argument(s) but was given {}",
        name,
        expected,
        found
    )]
    KindArityMismatch {
        span: Span,
        name: QualifiedIdent,
        expected: usize,
        found: usize,
    },

    #[error("The type class {class_name} expects {expected} type argument(s), but the instance provided {found}")]
    ClassInstanceArityMismatch {
        span: Span,
        class_name: QualifiedIdent,
        expected: usize,
        found: usize,
    },

    #[error("Type variable {} is undefined", interner::resolve(*name).unwrap_or_default())]
    UndefinedTypeVariable { span: Span, name: Symbol },

    #[error("Invalid type in instance head")]
    InvalidInstanceHead { span: Span },

    #[error("Type synonym {} is partially applied", name)]
    PartiallyAppliedSynonym { span: Span, name: QualifiedIdent },

    #[error(
        "A transitive export error occurred: {} depends on {} which is not exported",
        exported,
        dependency
    )]
    TransitiveExportError {
        span: Span,
        exported: QualifiedIdent,
        dependency: QualifiedIdent,
    },

    #[error("Scope conflict: the name {} is ambiguous, imported from multiple modules",
        interner::resolve(*name).unwrap_or_default()
    )]
    ScopeConflict { span: Span, name: Symbol },

    #[error("Export conflict: the name {} is exported by multiple re-exported modules",
        interner::resolve(*name).unwrap_or_default()
    )]
    ExportConflict { span: Span, name: Symbol },

    #[error("Overlapping instances found for {class_name} {args}",
        args = type_args.iter().map(|ty| format!("{}", ty)).collect::<Vec<_>>().join(" ")
    )]
    OverlappingInstances {
        span: Span,
        class_name: QualifiedIdent,
        type_args: Vec<Type>,
    },

    #[error("An orphan instance was found for class {class_name}. Instances must be defined in the same module as the class or one of the types in the instance head.")]
    OrphanInstance {
        span: Span,
        class_name: QualifiedIdent,
    },

    #[error("Type class instance for {class_name} {args} is possibly infinite",
        args = type_args.iter().map(|ty| format!("{}", ty)).collect::<Vec<_>>().join(" ")
    )]
    PossiblyInfiniteInstance {
        span: Span,
        class_name: QualifiedIdent,
        type_args: Vec<Type>,
    },

    #[error("The type variable {name_str} is ambiguous",
        name_str = names.iter().map(|n| interner::resolve(*n).unwrap_or_default()).collect::<Vec<_>>().join(", ")
    )]
    AmbiguousTypeVariables { span: Span, names: Vec<Symbol> },

    #[error("Invalid Coercible instance declaration")]
    InvalidCoercibleInstanceDeclaration { span: Span },

    #[error("Role mismatch for type {}", interner::resolve(*name).unwrap_or_default())]
    RoleMismatch { span: Span, name: Symbol },

    #[error("Possibly infinite Coercible instance")]
    PossiblyInfiniteCoercibleInstance {
        span: Span,
        class_name: QualifiedIdent,
        type_args: Vec<crate::typechecker::types::Type>,
    },

    /// Kind unification failure: two kinds could not be unified
    #[error("Could not match kind {expected} with kind {found}")]
    KindsDoNotUnify {
        span: Span,
        expected: Type,
        found: Type,
    },

    /// Expected a type of kind Type, but found a higher-kinded type
    #[error("Expected type of kind Type, but found kind {found}")]
    ExpectedType { span: Span, found: Type },

    /// Constraint used in kind position (e.g., `foreign data Bad :: Ok => Type`)
    #[error("Unsupported type in kind")]
    UnsupportedTypeInKind { span: Span },

    /// A rigid type variable (skolem) has escaped its scope
    #[error("A type variable has escaped its scope")]
    EscapedSkolem { span: Span, name: Symbol, ty: Type },

    /// Implicit kind quantification would be needed inside a user-written forall (type-level)
    #[error("Cannot unambiguously generalize type kinds for {ty}")]
    QuantificationCheckFailureInType { ty: Type, span: Span },

    /// Implicit kind quantification would be needed inside a kind annotation
    #[error("Cannot unambiguously generalize kinds for {ty}")]
    QuantificationCheckFailureInKind { ty: Type, span: Span },

    /// Visible dependent quantification is not supported
    #[error("Visible dependent quantification is not supported")]
    VisibleQuantificationCheckFailureInType { span: Span },
}

impl TypeError {
    pub fn span(&self) -> Span {
        match self {
            TypeError::UnificationError { span, .. }
            | TypeError::RecordLabelMismatch { span, .. }
            | TypeError::InfiniteType { span, .. }
            | TypeError::UndefinedVariable { span, .. }
            | TypeError::UnknownName { span, .. }
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
            | TypeError::CannotDeriveInvalidConstructorArg { span, .. }
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
            | TypeError::ConstraintInForeignImport { span, .. }
            | TypeError::InvalidConstraintArgument { span, .. }
            | TypeError::SyntaxError { span, .. }
            | TypeError::ExpectedWildcard { span, .. }
            | TypeError::KindArityMismatch { span, .. }
            | TypeError::ClassInstanceArityMismatch { span, .. }
            | TypeError::UndefinedTypeVariable { span, .. }
            | TypeError::InvalidInstanceHead { span, .. }
            | TypeError::PartiallyAppliedSynonym { span, .. }
            | TypeError::TransitiveExportError { span, .. }
            | TypeError::ScopeConflict { span, .. }
            | TypeError::ExportConflict { span, .. }
            | TypeError::CannotApplyExpressionOfTypeOnType { span, .. }
            | TypeError::IncorrectAnonymousArgument { span, .. }
            | TypeError::InvalidOperatorInBinder { span, .. }
            | TypeError::OverlappingInstances { span, .. }
            | TypeError::OrphanInstance { span, .. }
            | TypeError::PossiblyInfiniteInstance { span, .. }
            | TypeError::AmbiguousTypeVariables { span, .. }
            | TypeError::InvalidCoercibleInstanceDeclaration { span, .. }
            | TypeError::RoleMismatch { span, .. }
            | TypeError::PossiblyInfiniteCoercibleInstance { span, .. }
            | TypeError::KindsDoNotUnify { span, .. }
            | TypeError::ExpectedType { span, .. }
            | TypeError::UnsupportedTypeInKind { span, .. }
            | TypeError::EscapedSkolem { span, .. }
            | TypeError::QuantificationCheckFailureInType { span, .. }
            | TypeError::QuantificationCheckFailureInKind { span, .. }
            | TypeError::VisibleQuantificationCheckFailureInType { span, .. } => *span,
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
            TypeError::RecordLabelMismatch { .. } => "RecordLabelMismatch".into(),
            TypeError::InfiniteType { .. } => "InfiniteType".into(),
            TypeError::UndefinedVariable { .. } => "UndefinedVariable".into(),
            TypeError::UnknownName { .. } => "UnknownName".into(),
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
            TypeError::CannotDeriveInvalidConstructorArg { .. } => {
                "CannotDeriveInvalidConstructorArg".into()
            }
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
            TypeError::CannotGeneralizeRecursiveFunction { .. } => {
                "CannotGeneralizeRecursiveFunction".into()
            }
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
            TypeError::WildcardInTypeDefinition { .. } => "WildcardInTypeDefinition".into(),
            TypeError::ConstraintInForeignImport { .. } => "ConstraintInForeignImport".into(),
            TypeError::InvalidConstraintArgument { .. } => "InvalidConstraintArgument".into(),
            TypeError::SyntaxError { .. } => "SyntaxError".into(),
            TypeError::ExpectedWildcard { .. } => "ExpectedWildcard".into(),
            TypeError::KindArityMismatch { .. } => "KindArityMismatch".into(),
            TypeError::ClassInstanceArityMismatch { .. } => "ClassInstanceArityMismatch".into(),
            TypeError::UndefinedTypeVariable { .. } => "UndefinedTypeVariable".into(),
            TypeError::InvalidInstanceHead { .. } => "InvalidInstanceHead".into(),
            TypeError::PartiallyAppliedSynonym { .. } => "PartiallyAppliedSynonym".into(),
            TypeError::TransitiveExportError { .. } => "TransitiveExportError".into(),
            TypeError::ScopeConflict { .. } => "ScopeConflict".into(),
            TypeError::ExportConflict { .. } => "ExportConflict".into(),
            TypeError::CannotApplyExpressionOfTypeOnType { .. } => {
                "CannotApplyExpressionOfTypeOnType".into()
            }
            TypeError::IncorrectAnonymousArgument { .. } => "IncorrectAnonymousArgument".into(),
            TypeError::InvalidOperatorInBinder { .. } => "InvalidOperatorInBinder".into(),
            TypeError::OverlappingInstances { .. } => "OverlappingInstances".into(),
            TypeError::OrphanInstance { .. } => "OrphanInstance".into(),
            TypeError::PossiblyInfiniteInstance { .. } => "PossiblyInfiniteInstance".into(),
            TypeError::AmbiguousTypeVariables { .. } => "AmbiguousTypeVariables".into(),
            TypeError::InvalidCoercibleInstanceDeclaration { .. } => {
                "InvalidCoercibleInstanceDeclaration".into()
            }
            TypeError::RoleMismatch { .. } => "RoleMismatch".into(),
            TypeError::PossiblyInfiniteCoercibleInstance { .. } => {
                "PossiblyInfiniteCoercibleInstance".into()
            }
            TypeError::KindsDoNotUnify { .. } => "KindsDoNotUnify".into(),
            TypeError::ExpectedType { .. } => "ExpectedType".into(),
            TypeError::UnsupportedTypeInKind { .. } => "UnsupportedTypeInKind".into(),
            TypeError::EscapedSkolem { .. } => "EscapedSkolem".into(),
            TypeError::QuantificationCheckFailureInType { .. } => {
                "QuantificationCheckFailureInType".into()
            }
            TypeError::QuantificationCheckFailureInKind { .. } => {
                "QuantificationCheckFailureInKind".into()
            }
            TypeError::VisibleQuantificationCheckFailureInType { .. } => {
                "VisibleQuantificationCheckFailureInType".into()
            }
        }
    }

    /// Format the error with readable multi-line layout and normalized type variables.
    /// Unification variables like `?120` become `t0`, `t1`, etc.
    pub fn format_pretty(&self) -> String {
        let var_map = self.build_var_map();
        match self {
            TypeError::UnificationError { expected, found, .. } => {
                format!(
                    "Expected type\n\n    {}\n\n  but found type\n\n    {}",
                    pretty_type(expected, &var_map),
                    pretty_type(found, &var_map),
                )
            }
            TypeError::RecordLabelMismatch { missing, extra, expected, found, .. } => {
                let mut s = String::from("Record fields do not match.");
                if !missing.is_empty() {
                    let labels: Vec<_> = missing.iter()
                        .map(|l| interner::resolve(*l).unwrap_or_default())
                        .collect();
                    let _ = write!(s, "\n  Missing labels:\n{}", labels.join("\n    "));
                }
                if !extra.is_empty() {
                    let labels: Vec<_> = extra.iter()
                        .map(|l| interner::resolve(*l).unwrap_or_default())
                        .collect();
                    let _ = write!(s, "\n  Extra labels:\n{}", labels.join("\n    "));
                }
                let _ = write!(s,
                    "\n\n  Expected type\n\n    {}\n\n  but found type\n\n    {}",
                    pretty_type(expected, &var_map),
                    pretty_type(found, &var_map),
                );
                s
            }
            TypeError::KindsDoNotUnify { expected, found, .. } => {
                format!(
                    "Expected kind\n\n    {}\n\n  but found kind\n\n    {}",
                    pretty_type(expected, &var_map),
                    pretty_type(found, &var_map),
                )
            }
            TypeError::HoleInferredType { name, ty, constraints, local_bindings, .. } => {
                let mut s = String::new();
                let _ = write!(s, "Hole ?{} has the inferred type\n\n    ",
                    interner::resolve(*name).unwrap_or_default());
                if !constraints.is_empty() {
                    let constraint_strs: Vec<String> = constraints.iter().map(|(cn, args)| {
                        let args_str: Vec<String> = args.iter().map(|a| pretty_type(a, &var_map)).collect();
                        if args_str.is_empty() {
                            interner::resolve(*cn).unwrap_or_default().to_string()
                        } else {
                            format!("{} {}", interner::resolve(*cn).unwrap_or_default(), args_str.join(" "))
                        }
                    }).collect();
                    let _ = write!(s, "{} => ", constraint_strs.join(", "));
                }
                let _ = write!(s, "{}", pretty_type(ty, &var_map));
                if !local_bindings.is_empty() {
                    s.push_str("\n\n  in the following context:\n");
                    for (bname, bty) in local_bindings {
                        let _ = write!(s, "\n    {} :: {}",
                            interner::resolve(*bname).unwrap_or_default(),
                            pretty_type(bty, &var_map));
                    }
                }
                s
            }
            TypeError::InfiniteType { var, ty, .. } => {
                format!(
                    "An infinite type was inferred for type variable t{}\n\n    {}",
                    var.0,
                    pretty_type(ty, &var_map),
                )
            }
            TypeError::InfiniteKind { var, ty, .. } => {
                format!(
                    "An infinite kind was inferred for type t{}\n\n    {}",
                    var.0,
                    pretty_type(ty, &var_map),
                )
            }
            TypeError::NoInstanceFound { class_name, type_args, .. } => {
                let args: Vec<String> = type_args.iter().map(|ty| pretty_type(ty, &var_map)).collect();
                format!(
                    "No type class instance was found for\n\n    {} {}",
                    class_name,
                    args.join(" "),
                )
            }
            TypeError::CannotGeneralizeRecursiveFunction { name, type_, .. } => {
                format!(
                    "Unable to generalize the type of the recursive function {}.\n  The inferred type was\n\n    {}\n\n  Try adding a type signature.",
                    interner::resolve(*name).unwrap_or_default(),
                    pretty_type(type_, &var_map),
                )
            }
            TypeError::MissingClassMember { class_name, members, .. } => {
                let mut s = format!("The class {} is missing the following members:\n", class_name);
                for (name, ty) in members {
                    let _ = write!(s, "\n    {} :: {}", interner::resolve(*name).unwrap_or_default(), pretty_type(ty, &var_map));
                }
                s
            }
            TypeError::EscapedSkolem { name, ty, .. } => {
                format!(
                    "A type variable has escaped its scope: {}\n\n    {}",
                    interner::resolve(*name).unwrap_or_default(),
                    pretty_type(ty, &var_map),
                )
            }
            TypeError::ExpectedType { found, .. } => {
                format!(
                    "Expected type of kind Type, but found kind\n\n    {}",
                    pretty_type(found, &var_map),
                )
            }
            TypeError::CannotApplyExpressionOfTypeOnType { type_, .. } => {
                format!(
                    "Cannot apply expression of type\n\n    {}\n\n  to a type argument",
                    pretty_type(type_, &var_map),
                )
            }
            // For all other errors, use the default Display but with normalized unif vars
            _ => {
                if var_map.is_empty() {
                    format!("{self}")
                } else {
                    // Replace ?N patterns in the default display string
                    let s = format!("{self}");
                    replace_unif_vars_in_string(&s, &var_map)
                }
            }
        }
    }

    /// Collect all types referenced by this error and build a normalized var mapping.
    fn build_var_map(&self) -> HashMap<u32, usize> {
        let mut unif_ids = Vec::new();
        self.collect_types(&mut |ty| collect_unif_vars(ty, &mut unif_ids));
        let mut map = HashMap::new();
        for id in &unif_ids {
            let len = map.len();
            map.entry(*id).or_insert(len);
        }
        map
    }

    /// Visit all Type values in this error variant.
    fn collect_types(&self, visitor: &mut dyn FnMut(&Type)) {
        match self {
            TypeError::UnificationError { expected, found, .. }
            | TypeError::RecordLabelMismatch { expected, found, .. } => { visitor(expected); visitor(found); }
            TypeError::InfiniteType { ty, .. } | TypeError::InfiniteKind { ty, .. } => visitor(ty),
            TypeError::HoleInferredType { ty, constraints, local_bindings, .. } => {
                visitor(ty);
                for (_, args) in constraints { for a in args { visitor(a); } }
                for (_, bty) in local_bindings { visitor(bty); }
            }
            TypeError::NoInstanceFound { type_args, .. }
            | TypeError::OverlappingInstances { type_args, .. }
            | TypeError::PossiblyInfiniteInstance { type_args, .. }
            | TypeError::PossiblyInfiniteCoercibleInstance { type_args, .. } => {
                for ty in type_args { visitor(ty); }
            }
            TypeError::CannotGeneralizeRecursiveFunction { type_, .. }
            | TypeError::CannotApplyExpressionOfTypeOnType { type_, .. } => visitor(type_),
            TypeError::MissingClassMember { members, .. } => {
                for (_, ty) in members { visitor(ty); }
            }
            TypeError::KindsDoNotUnify { expected, found, .. } => { visitor(expected); visitor(found); }
            TypeError::ExpectedType { found, .. } => visitor(found),
            TypeError::EscapedSkolem { ty, .. } => visitor(ty),
            TypeError::QuantificationCheckFailureInType { ty, .. }
            | TypeError::QuantificationCheckFailureInKind { ty, .. } => visitor(ty),
            _ => {}
        }
    }
}

/// Collect unification variable IDs from a type in order of first appearance.
fn collect_unif_vars(ty: &Type, ids: &mut Vec<u32>) {
    match ty {
        Type::Unif(id) => {
            if !ids.contains(&id.0) {
                ids.push(id.0);
            }
        }
        Type::App(f, a) => { collect_unif_vars(f, ids); collect_unif_vars(a, ids); }
        Type::Fun(a, b) => { collect_unif_vars(a, ids); collect_unif_vars(b, ids); }
        Type::Forall(_, t) => collect_unif_vars(t, ids),
        Type::Record(fields, tail) => {
            for (_, t) in fields { collect_unif_vars(t, ids); }
            if let Some(t) = tail { collect_unif_vars(t, ids); }
        }
        _ => {}
    }
}

/// Format a type with normalized unification variable names.
fn pretty_type(ty: &Type, var_map: &HashMap<u32, usize>) -> String {
    if var_map.is_empty() {
        return format!("{ty}");
    }
    let mut out = String::new();
    fmt_type(&mut out, ty, var_map, false);
    out
}

fn fmt_type(out: &mut String, ty: &Type, var_map: &HashMap<u32, usize>, nested: bool) {
    match ty {
        Type::Unif(id) => {
            if let Some(&idx) = var_map.get(&id.0) {
                let _ = write!(out, "t{idx}");
            } else {
                let _ = write!(out, "t{}", id.0);
            }
        }
        Type::Var(sym) => {
            let _ = write!(out, "{}", interner::resolve(*sym).unwrap_or_default());
        }
        Type::Con(sym) => {
            let _ = write!(out, "{sym}");
        }
        Type::App(func, arg) => {
            if nested { out.push('('); }
            match func.as_ref() {
                Type::App(..) | Type::Con(..) | Type::Var(..) | Type::Unif(..) => fmt_type(out, func, var_map, false),
                _ => fmt_type(out, func, var_map, true),
            }
            out.push(' ');
            fmt_type(out, arg, var_map, true);
            if nested { out.push(')'); }
        }
        Type::Fun(from, to) => {
            if nested { out.push('('); }
            fmt_type(out, from, var_map, true);
            out.push_str(" -> ");
            fmt_type(out, to, var_map, false);
            if nested { out.push(')'); }
        }
        Type::Forall(vars, body) => {
            if nested { out.push('('); }
            out.push_str("forall");
            for (v, visible) in vars {
                if *visible {
                    let _ = write!(out, " @{}", interner::resolve(*v).unwrap_or_default());
                } else {
                    let _ = write!(out, " {}", interner::resolve(*v).unwrap_or_default());
                }
            }
            out.push_str(". ");
            fmt_type(out, body, var_map, false);
            if nested { out.push(')'); }
        }
        Type::TypeString(sym) => {
            let _ = write!(out, "\"{}\"", interner::resolve(*sym).unwrap_or_default());
        }
        Type::TypeInt(n) => {
            let _ = write!(out, "{n}");
        }
        Type::Record(fields, tail) => {
            out.push_str("{ ");
            for (i, (label, field_ty)) in fields.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                let _ = write!(out, "{} :: ", interner::resolve(*label).unwrap_or_default());
                fmt_type(out, field_ty, var_map, false);
            }
            if let Some(tail) = tail {
                if !fields.is_empty() { out.push_str(" | "); }
                fmt_type(out, tail, var_map, false);
            }
            out.push_str(" }");
        }
    }
}

/// Replace `?N` patterns in a pre-formatted string with normalized `tN` names.
fn replace_unif_vars_in_string(s: &str, var_map: &HashMap<u32, usize>) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        if c == '?' {
            // Try to parse a number after '?'
            let start = i + 1;
            let mut end = start;
            while let Some(&(j, d)) = chars.peek() {
                if d.is_ascii_digit() {
                    end = j + 1;
                    chars.next();
                } else {
                    break;
                }
            }
            if end > start {
                if let Ok(id) = s[start..end].parse::<u32>() {
                    if let Some(&idx) = var_map.get(&id) {
                        let _ = write!(result, "t{idx}");
                        continue;
                    }
                }
            }
            result.push(c);
            result.push_str(&s[start..end]);
        } else {
            result.push(c);
        }
    }
    result
}
