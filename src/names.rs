//! Strongly-typed name wrappers for different categories of identifiers.
//!
//! PureScript has distinct namespaces for values, types, classes, constructors,
//! type variables, record labels, and operators. These wrappers ensure that
//! names from different namespaces cannot be silently confused at the type level.
//!
//! Construction and casting between name types is restricted to this module.
//! Cross-category casts are documented with their rationale.

use crate::interner::{self, Symbol};

// ---------------------------------------------------------------------------
// Name wrapper macro
// ---------------------------------------------------------------------------

macro_rules! name_wrapper {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Copy, Clone, Hash, Eq, PartialEq, Debug, PartialOrd, Ord)]
        pub struct $name(Symbol);

        impl $name {
            /// Create a new name from a raw Symbol.
            pub fn new(sym: Symbol) -> Self {
                Self(sym)
            }

            /// Access the underlying Symbol.
            /// Restricted to crate-internal use — prefer typed operations instead.
            pub(crate) fn symbol(self) -> Symbol {
                self.0
            }

            /// Resolve to the interned string value.
            pub fn resolve(self) -> Option<String> {
                interner::resolve(self.0)
            }

            /// Compare with a string literal without allocation.
            pub fn eq_str(self, s: &str) -> bool {
                interner::symbol_eq(self.0, s)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match interner::resolve(self.0) {
                    Some(s) => write!(f, "{}", s),
                    None => write!(f, "<unresolved>"),
                }
            }
        }
    };
}

// ---------------------------------------------------------------------------
// Name types
// ---------------------------------------------------------------------------

name_wrapper!(
    /// A value-level name: function bindings, let bindings, where bindings,
    /// class method names in value position, foreign imports.
    ValueName
);

name_wrapper!(
    /// A type-level name: data types, type aliases, newtypes, foreign data.
    TypeName
);

name_wrapper!(
    /// A type class name: `Eq`, `Show`, `Functor`, etc.
    ClassName
);

name_wrapper!(
    /// An instance declaration name (the optional label before the class name).
    InstanceName
);

name_wrapper!(
    /// A data or newtype constructor name: `Just`, `Nothing`, `Cons`, etc.
    ConstructorName
);

name_wrapper!(
    /// A type variable name from forall quantification or data type parameters: `a`, `b`, `m`.
    TypeVarName
);

name_wrapper!(
    /// A record or row field label: `name`, `age`, `id`.
    LabelName
);

name_wrapper!(
    /// A value-level operator symbol: `+`, `<>`, `>>>`, `>>=`.
    OpName
);

name_wrapper!(
    /// A type-level operator symbol: `~>`, `/\`.
    TypeOpName
);

name_wrapper!(
    /// A module qualifier, stored as a single interned dot-joined string
    /// (e.g. `"Data.Array"`).
    ///
    /// Distinct from `cst::ModuleName` which stores individual parts as `Vec<Ident>`.
    ModuleQualifier
);

// ---------------------------------------------------------------------------
// matches_ident — CST boundary bridge
//
// Only implemented for types that actually compare against raw CST Idents.
// Temporary until Phase 2 migrates CST to typed names.
// ---------------------------------------------------------------------------

macro_rules! impl_matches_ident {
    ($name:ident) => {
        impl $name {
            /// Check if this name matches a raw Ident (Symbol) from the CST.
            /// Temporary bridge for use at CST/typechecker boundaries until
            /// Phase 2 migrates CST to typed names.
            pub(crate) fn matches_ident(self, ident: Symbol) -> bool {
                self.0 == ident
            }
        }
    };
}

impl_matches_ident!(TypeVarName);
impl_matches_ident!(TypeName);

// ---------------------------------------------------------------------------
// Qualified<N> — a name with an optional module qualifier
// ---------------------------------------------------------------------------

/// A name optionally qualified with a module prefix.
///
/// Replaces the untyped `QualifiedIdent` with a generic version that
/// preserves the semantic category of the name.
#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
pub struct Qualified<N> {
    pub module: Option<ModuleQualifier>,
    pub name: N,
}

impl<N> Qualified<N> {
    /// Create an unqualified name (no module prefix).
    pub fn unqualified(name: N) -> Self {
        Qualified { module: None, name }
    }

    /// Create a qualified name with a module prefix.
    pub fn qualified(module: ModuleQualifier, name: N) -> Self {
        Qualified {
            module: Some(module),
            name,
        }
    }

    /// Map the name component, preserving the module qualifier.
    pub fn map<M>(self, f: impl FnOnce(N) -> M) -> Qualified<M> {
        Qualified {
            module: self.module,
            name: f(self.name),
        }
    }
}

impl<N: Copy> Qualified<N> {
    /// Get the module qualifier, if any.
    pub fn module(&self) -> Option<ModuleQualifier> {
        self.module
    }
}

impl<N: std::fmt::Display> std::fmt::Display for Qualified<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(module) = &self.module {
            write!(f, "{}.{}", module, self.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

// ---------------------------------------------------------------------------
// QualifiedIdent ↔ Qualified<N> conversion
//
// Bridge between untyped CST QualifiedIdent and typed Qualified<N>.
// Used at CST/typechecker boundaries during the migration.
// ---------------------------------------------------------------------------

impl<N: NameLike> Qualified<N> {
    /// Convert an untyped CST QualifiedIdent to a typed Qualified<N>.
    /// Used at CST/typechecker boundaries where the CST still uses untyped Ident.
    pub(crate) fn from_qi(qi: &crate::cst::QualifiedIdent) -> Self {
        Qualified {
            module: qi.module.map(ModuleQualifier::new),
            name: N::from_symbol(qi.name),
        }
    }

    /// Convert back to an untyped QualifiedIdent for CST interop.
    /// Temporary bridge until CST itself is migrated to typed names.
    pub(crate) fn to_qi(self) -> crate::cst::QualifiedIdent {
        crate::cst::QualifiedIdent {
            module: self.module.map(|m| m.symbol()),
            name: self.name.symbol(),
        }
    }

    /// Access the raw name Symbol for interop with untyped code.
    /// Temporary bridge — prefer typed operations.
    pub(crate) fn name_symbol(self) -> Symbol {
        self.name.symbol()
    }
}

// Convenience constructors for qualified names from string literals.

pub fn qualified_value(module: &str, name: &str) -> Qualified<ValueName> {
    Qualified::qualified(module_qualifier(module), value_name(name))
}

pub fn unqualified_value(name: &str) -> Qualified<ValueName> {
    Qualified::unqualified(value_name(name))
}

pub fn qualified_type(module: &str, name: &str) -> Qualified<TypeName> {
    Qualified::qualified(module_qualifier(module), type_name(name))
}

pub fn unqualified_type(name: &str) -> Qualified<TypeName> {
    Qualified::unqualified(type_name(name))
}

pub fn qualified_class(module: &str, name: &str) -> Qualified<ClassName> {
    Qualified::qualified(module_qualifier(module), class_name(name))
}

pub fn unqualified_class(name: &str) -> Qualified<ClassName> {
    Qualified::unqualified(class_name(name))
}

pub fn qualified_ctor(module: &str, name: &str) -> Qualified<ConstructorName> {
    Qualified::qualified(module_qualifier(module), constructor_name(name))
}

pub fn unqualified_ctor(name: &str) -> Qualified<ConstructorName> {
    Qualified::unqualified(constructor_name(name))
}

pub fn qualified_type_op(module: &str, name: &str) -> Qualified<TypeOpName> {
    Qualified::qualified(module_qualifier(module), type_op_name(name))
}

pub fn unqualified_type_op(name: &str) -> Qualified<TypeOpName> {
    Qualified::unqualified(type_op_name(name))
}

pub fn qualified_op(module: &str, name: &str) -> Qualified<OpName> {
    Qualified::qualified(module_qualifier(module), op_name(name))
}

pub fn unqualified_op(name: &str) -> Qualified<OpName> {
    Qualified::unqualified(op_name(name))
}

// ---------------------------------------------------------------------------
// Cross-category casting functions
//
// Each cast documents WHY it is needed. If you need a new cast, add it here
// with a rationale — do not bypass the wrapper via .symbol() + ::new().
// ---------------------------------------------------------------------------

/// Class methods are looked up as values in the type environment.
/// e.g. `show` from `class Show` has type `Show a => a -> String` and lives
/// in the value namespace.
pub fn class_method_as_value(name: ClassName) -> ValueName {
    ValueName(name.0)
}

/// Data constructors are values: they have function types and can be applied
/// like regular functions (e.g. `Just : a -> Maybe a`).
pub fn constructor_as_value(name: ConstructorName) -> ValueName {
    ValueName(name.0)
}

/// Value-level operators (e.g. `+`, `<>`) are looked up in the value namespace
/// for signature constraints and env entries.
pub fn op_as_value(name: OpName) -> ValueName {
    ValueName(name.0)
}

/// Fixity declarations target either a value or constructor by name.
/// Constructor targets from `Decl::Fixity` need ConstructorName for `ctor_details` lookup.
pub fn value_as_constructor(name: ValueName) -> ConstructorName {
    ConstructorName(name.0)
}

/// Classes and types share the same string name when looking up kind signatures
/// or building `Type::Con` for class-as-type usage (e.g. `Functor` as a type in
/// `derive instance` or kind checking).
pub fn class_as_type(name: ClassName) -> TypeName {
    TypeName(name.0)
}

/// Constructor names can appear in type position for VTA (Visible Type Application)
/// where a data constructor expression is reinterpreted as a type constructor.
pub fn constructor_as_type(name: ConstructorName) -> TypeName {
    TypeName(name.0)
}

/// Type operators resolve to type names via fixity declarations.
/// The CST stores the operator name which must be looked up against type names.
pub fn type_op_as_type(name: TypeOpName) -> TypeName {
    TypeName(name.0)
}

/// Type operator names in the CST sometimes arrive as TypeName through TypeExpr.
/// This casts them for lookup in type_operators maps.
pub fn type_as_type_op(name: TypeName) -> TypeOpName {
    TypeOpName(name.0)
}

/// Type variable names and value names share the same string in binder conversion.
/// When a TypeExpr::Var is reinterpreted as a Binder::Var, the type var becomes a value binding.
pub fn type_var_as_value(name: TypeVarName) -> ValueName {
    ValueName(name.0)
}

/// Value names can be reinterpreted as type variable names in expr-to-type conversion.
/// Used when VTA parses an expression that needs to become a type.
pub fn value_as_type_var(name: ValueName) -> TypeVarName {
    TypeVarName(name.0)
}

/// Type constructor names are reinterpreted as data constructors in binder conversion.
/// When a TypeExpr::Constructor appears in a pattern, it refers to a data constructor.
pub fn type_as_constructor(name: TypeName) -> ConstructorName {
    ConstructorName(name.0)
}

/// Type-level operators are reinterpreted as value-level operators in binder conversion.
/// When a TypeOp appears in a binder pattern (e.g. `a /\ b`), it's a value operator.
pub fn type_op_as_op(name: TypeOpName) -> OpName {
    OpName(name.0)
}

// ---------------------------------------------------------------------------
// NameLike trait — shared interface for all name types
// ---------------------------------------------------------------------------

/// Trait implemented by all name wrapper types.
/// Provides deserialization support and common name operations.
/// Crate-internal: external code should use the inherent methods on each name type.
pub trait NameLike: Copy + std::hash::Hash + Eq + std::fmt::Debug + std::fmt::Display {
    /// Construct from a raw Symbol (deserialization, CST boundary).
    fn from_symbol(sym: Symbol) -> Self;

    /// Access the underlying Symbol for serialization and CST interop.
    fn symbol(self) -> Symbol;
}

macro_rules! impl_name_like {
    ($name:ident) => {
        impl NameLike for $name {
            fn from_symbol(sym: Symbol) -> Self {
                Self(sym)
            }
            fn symbol(self) -> Symbol {
                self.0
            }
        }
    };
}

impl_name_like!(ValueName);
impl_name_like!(TypeName);
impl_name_like!(ClassName);
impl_name_like!(InstanceName);
impl_name_like!(ConstructorName);
impl_name_like!(TypeVarName);
impl_name_like!(LabelName);
impl_name_like!(OpName);
impl_name_like!(TypeOpName);
impl_name_like!(ModuleQualifier);

// ---------------------------------------------------------------------------
// Convenience constructors from string literals
// ---------------------------------------------------------------------------

pub fn value_name(s: &str) -> ValueName {
    ValueName::new(interner::intern(s))
}

pub fn type_name(s: &str) -> TypeName {
    TypeName::new(interner::intern(s))
}

pub fn class_name(s: &str) -> ClassName {
    ClassName::new(interner::intern(s))
}

pub fn instance_name(s: &str) -> InstanceName {
    InstanceName::new(interner::intern(s))
}

pub fn constructor_name(s: &str) -> ConstructorName {
    ConstructorName::new(interner::intern(s))
}

pub fn type_var_name(s: &str) -> TypeVarName {
    TypeVarName::new(interner::intern(s))
}

pub fn label_name(s: &str) -> LabelName {
    LabelName::new(interner::intern(s))
}

pub fn op_name(s: &str) -> OpName {
    OpName::new(interner::intern(s))
}

pub fn type_op_name(s: &str) -> TypeOpName {
    TypeOpName::new(interner::intern(s))
}

pub fn module_qualifier(s: &str) -> ModuleQualifier {
    ModuleQualifier::new(interner::intern(s))
}

/// Create a module qualifier from CST module name parts (Vec<Symbol>).
pub fn module_qualifier_from_parts(parts: &[Symbol]) -> ModuleQualifier {
    ModuleQualifier::new(interner::intern_module_name(parts))
}
