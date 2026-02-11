use std::fmt;

use crate::ast::span::Span;
use crate::interner;
use crate::interner::Symbol;
use crate::typechecker::types::{TyVarId, Type};

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
    NoInstanceFound {
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

    /// Overlapping pattern variable names in a pattern match
    OverlappingPattern { 
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

    /// Invalid newtype derived instance. E.g. derive instance Newtype NotANewtype
    InvalidNewtypeInstance {
        span: Span,
        name: Symbol,
    },

    // derive newtype instance on a type that isn't an instance of Newtype. E.g. derive newtype instance MyClass NotANewtype
    InvalidNewtypeDerivation {
        span: Span,
        name: Symbol,
    },

    /// 2 modules have the same name in the project
    DuplicateModule {
        span: Span,
        name: Symbol,
        other_file_path: String,
    },

    /// Multiple type classes with the same name
    DuplicateTypeClass {
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Multiple class instances with the name
    /// instance myEq :: Eq MyType where ...
    /// instance myEq :: Eq OtherType where ...
    DuplicateInstance { 
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Multiple args to a type with the same name
    /// data MyType a a = MyConstructor
    DuplicateTypeArgument { 
        spans: Vec<Span>,
        name: Symbol,
    },

    /// Invalid do bind. Eg on the last line of a do block
    InvalidDoBind { 
        span: Span,
    },
    /// Invalid do let. Eg on the last line of a do block
    InvalidDoLet { 
        span: Span,
    },

    /// multiple type synonyms that reference each other in a cycle
    /// type A = B
    /// type B = A
    CycleInTypeSynonym { 
        name: Symbol,
        span: Span,
        names_in_cycle: Vec<Symbol>,
        spans: Vec<Span>,
    },
    /// multiple type classes that reference each other in a cycle
    /// e.g.
    /// class (Foo a) <= Foo a
    /// OR
    /// class (Foo a) <= Bar a
    /// class (Bar a) <= Foo a
    /// instance barString :: Bar String
    /// instance fooString :: Foo String
    CycleInTypeClassDeclaration { 
        name: Symbol,
        span: Span,
        names_in_cycle: Vec<Symbol>,
        spans: Vec<Span>,
    },

    /// cycle in kind declarations. E.g.
    /// foreign import data Foo :: Bar
    /// foreign import data Bar :: Foo
    CycleInKindDeclaration { 
        name: Symbol,
        span: Span,
        names_in_cycle: Vec<Symbol>,
        spans: Vec<Span>,
    },

    /// cycle in modules. E.g. module A imports B, module B imports A
    CycleInModules { 
        name: Symbol,
        span: Span,
        other_modules: Vec<(Symbol, String)>,
    },

    /// overlapping argument names in a function
    OverlappingArgNames { 
        span: Span,
        name: Symbol,
        spans: Vec<Span>,
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

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnificationError {
                expected, found, ..
            } => {
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
            TypeError::ArityMismatch {
                name,
                expected,
                found,
                ..
            } => {
                write!(
                    f,
                    "arity mismatch for {}: expected {} arguments but found {}",
                    interner::resolve(*name).unwrap_or_default(),
                    expected,
                    found
                )
            }
            TypeError::NoInstanceFound {
                class_name,
                type_args,
                ..
            } => {
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
            TypeError::NonExhaustivePattern {
                type_name, missing, ..
            } => {
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
            TypeError::IncorrectConstructorArity {
                name,
                expected,
                found,
                ..
            } => {
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
            TypeError::InvalidNewtypeDerivation { name, .. } => {
                write!(
                    f,
                    "invalid newtype derivation for {}: type is not a newtype",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::InvalidNewtypeInstance { name, .. } => {
                write!(
                    f,
                    "invalid Newtype instance for {}: type is not a newtype",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::OverlappingPattern { name, .. } => {
                write!(
                    f,
                    "overlapping pattern variable: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::DuplicateModule { name, other_file_path, .. } => {
                write!(
                    f,
                    "duplicate module: {} (also defined in {})",
                    interner::resolve(*name).unwrap_or_default(),
                    other_file_path
                )
            }
            TypeError::DuplicateTypeClass { name, .. } => {
                write!(
                    f,
                    "duplicate type class declaration: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::DuplicateInstance { name, .. } => {
                write!(
                    f,
                    "duplicate instance declaration: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::DuplicateTypeArgument { name, .. } => {
                write!(
                    f,
                    "duplicate type argument: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
            TypeError::InvalidDoBind { .. } => {
                write!(f, "bind statement cannot be the last statement in a do block")
            }
            TypeError::InvalidDoLet { .. } => {
                write!(f, "let statement cannot be the last statement in a do block")
            }
            TypeError::CycleInTypeSynonym { name, names_in_cycle, .. } => {
                let cycle_str: Vec<_> = names_in_cycle
                    .iter()
                    .map(|n| interner::resolve(*n).unwrap_or_default())
                    .collect();
                write!(
                    f,
                    "cycle in type synonyms: {} (cycle: {})",
                    interner::resolve(*name).unwrap_or_default(),
                    cycle_str.join(" -> ")
                )
            }
            TypeError::CycleInTypeClassDeclaration { name, names_in_cycle, .. } => {
                let cycle_str: Vec<_> = names_in_cycle
                    .iter()
                    .map(|n| interner::resolve(*n).unwrap_or_default())
                    .collect();
                write!(
                    f,
                    "cycle in type class declarations: {} (cycle: {})",
                    interner::resolve(*name).unwrap_or_default(),
                    cycle_str.join(" -> ")
                )
            }
            TypeError::CycleInKindDeclaration { name, names_in_cycle, .. } => {
                let cycle_str: Vec<_> = names_in_cycle
                    .iter()
                    .map(|n| interner::resolve(*n).unwrap_or_default())
                    .collect();
                write!(
                    f,
                    "cycle in kind declarations: {} (cycle: {})",
                    interner::resolve(*name).unwrap_or_default(),
                    cycle_str.join(" -> ")
                )
            }
            TypeError::CycleInModules { name, other_modules, .. } => {
                let modules_str: Vec<_> = other_modules
                    .iter()
                    .map(|(n, _)| interner::resolve(*n).unwrap_or_default())
                    .collect();
                write!(
                    f,
                    "cycle in module imports: {} (cycle: {})",
                    interner::resolve(*name).unwrap_or_default(),
                    modules_str.join(" -> ")
                )
            }

            TypeError::OverlappingArgNames { name, .. } => {
                write!(
                    f,
                    "overlapping argument names: {}",
                    interner::resolve(*name).unwrap_or_default()
                )
            }
        }
    }
}

impl std::error::Error for TypeError {}
