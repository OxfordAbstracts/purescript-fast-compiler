//! Structural validation of a module's declarations — no type
//! inference involved. Runs after import resolution, before any
//! of the cached per-decl passes. Produces diagnostics that the
//! old compiler emits during name-resolution.
//!
//! Covers:
//!   - Duplicate value declarations (same `foo = …` twice non-adjacent)
//!   - Duplicate type declarations (data/type/newtype/class)
//!   - Duplicate type-class declarations
//!   - Duplicate role declarations
//!   - Duplicate type arguments on a single type/class/data decl
//!   - Orphan type signatures (`foo :: …` with no matching `foo = …`)
//!   - Orphan kind signatures (`data Foo :: …` with no matching data/newtype/class/type)
//!   - Orphan role declarations (`type role Foo …` with no matching data/newtype)
//!   - Multiple value/type operator fixities for the same operator
//!
//! Deliberately does NOT cover anything requiring type/kind inference.

use std::collections::{HashMap, HashSet};

use crate::cst;
use crate::interner::Symbol;
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationError {
    pub span: Span,
    pub kind: ValidationErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationErrorKind {
    DuplicateValueDeclaration(String),
    DuplicateTypeDeclaration(String),
    DuplicateTypeClass(String),
    DuplicateTypeArgument(String),
    DuplicateRoleDeclaration(String),
    OrphanTypeSignature(String),
    OrphanKindDeclaration(String),
    OrphanRoleDeclaration(String),
    MultipleValueOpFixities(String),
    MultipleTypeOpFixities(String),
    CycleInTypeSynonym(Vec<String>),
    CycleInTypeClassDeclaration(Vec<String>),
    CycleInKindDeclaration(Vec<String>),
    CycleInDeclaration(Vec<String>),
    PartiallyAppliedSynonym(String),
    OrphanInstance(String),
    DeclConflict(String),
    RoleDeclarationArityMismatch(String),
    ClassInstanceArityMismatch { class: String, expected: usize, got: usize },
    WildcardInTypeDefinition,
    ConstraintInForeignImport,
    InvalidConstraintArgument,
    TransitiveDctorExportError(String),
    TransitiveExportError(String),
    InvalidInstanceHead,
    /// `module C (module A, module B) where` — both A and B export
    /// the same name, so re-exporting both via two `module N`
    /// clauses creates an unresolvable ambiguity at C's surface.
    /// Original compiler's `ExportConflict` failure.
    ExportConflict(String),
    /// Same name used twice in a single argument list / case
    /// pattern. `f x x = x` or `case x of (S y (S y@_)) -> y`.
    OverlappingArgNames(String),
    /// Same name declared twice non-adjacently inside a single
    /// `let` block (or `where`). Reference compiler's
    /// `OverlappingNamesInLet`.
    OverlappingNamesInLet(String),
    /// `derive newtype instance C (T ...)` where T was declared
    /// `data` (not `newtype`).
    CannotDeriveNewtypeForData(String),
    /// `Int` literal whose value falls outside the i32 range.
    IntOutOfRange,
    /// Operator used in a binder position (e.g. `(_ : x : _)`).
    /// The reference compiler routes operator parsing in binders
    /// through the same fixity machinery as expressions, but only
    /// for ctor-shaped operators (`infixl 6 Cons as :` works,
    /// alias of plain function does not).
    InvalidOperatorInBinder(String),
    /// `type role` declared on a class or type-alias (only valid
    /// for data/newtype/foreign-data).
    UnsupportedRoleDeclaration(String),
    /// Instance for a locally-declared class is missing one or more
    /// of the class's methods.
    MissingClassMember(String),
    /// Instance for a locally-declared class defines a method the
    /// class did not declare.
    ExtraneousClassMember(String),
    /// Pattern uses a constructor with an arity that doesn't match
    /// its declaration. `data Pair a b = Pair a b; f (Pair x) = x`.
    IncorrectConstructorArity {
        ctor: String,
        expected: usize,
        got: usize,
    },
    /// Type-variable referenced in a position where it isn't in
    /// scope. Examples: `class (Foo b) <= Bar a` (b not in
    /// `[a]`), or `type B y z = a` (a not in `[y, z]`).
    UndefinedTypeVariable(String),
    /// Two equations of the same value name with different binder
    /// counts. `f x y = ...; f = ...` is `ArgListLengthsDiffer`.
    ArgListLengthsDiffer(String),
    /// Two `instance i :: ...` declarations sharing the same
    /// instance name (regardless of class/types).
    DuplicateInstance(String),
    /// Export-list refers to a name not declared in the module.
    UnknownExport(String),
    /// Export-list refers to a constructor not belonging to the
    /// declared type.
    UnknownExportDataConstructor(String),
    /// `derive newtype instance C ...` where the head doesn't fit
    /// the newtype-deriving shape (no type, or applied to a
    /// concrete type that isn't a newtype, etc.).
    InvalidNewtypeInstance(String),
    /// Instance defines a TypeSignature for a name without also
    /// providing the value definition. The reference compiler
    /// reports as `OrphanTypeDeclaration`.
    OrphanTypeDeclaration(String),
    /// Foreign import name contains an apostrophe — `foreign import
    /// a' :: …`. The reference compiler reports as
    /// `DeprecatedFFIPrime`.
    DeprecatedFFIPrime(String),
    /// Type-variable applied to itself — `data F a = F (a a)` has
    /// `a` applied to `a`, requiring kind `k -> k -> ...`. Reference
    /// compiler reports as `InfiniteKind`.
    InfiniteKind(String),
    /// Reference to a name that doesn't resolve — typically a
    /// class name in an instance/superclass that isn't declared
    /// anywhere, or a type constructor used in a signature when
    /// it isn't imported. Reference compiler reports as
    /// `UnknownName`.
    UnknownName(String),
    /// Module name contains characters that aren't valid in
    /// PureScript module names (apostrophe, underscore). Reference
    /// compiler reports as `ErrorParsingModule`.
    InvalidModuleName(String),
    /// Non-associative operator chained with itself (`a == b == c`
    /// where `==` is `infix` not `infixl`/`infixr`).
    NonAssociativeError(String),
    /// Two operators at the same precedence with different
    /// associativity used in a chain — `f <$> x == f <$> y` mixes
    /// `<$>` (left, prec 4) with `==` (none, prec 4).
    MixedAssociativityError(String),
    /// Two instance declarations of the same class whose heads
    /// can match the same type — typically because one head is
    /// strictly more general than (or equal to) the other.
    OverlappingInstances(String),
    /// A `derive instance` (Functor / Foldable / Traversable /
    /// Contravariant / Bifunctor / Profunctor / Bifoldable /
    /// Bitraversable / Bicontravariant) where one of the data
    /// constructor's argument types uses the abstracted type-var
    /// in a position incompatible with the class's variance —
    /// e.g. `Functor` requires `a` covariant, so `Test (a -> Int)`
    /// is invalid. Reference compiler reports as
    /// `CannotDeriveInvalidConstructorArg`.
    CannotDeriveInvalidConstructorArg(String),
    /// A type annotation expects a Type-kinded type but received a
    /// type-constructor of a higher kind. E.g. `(x :: F)` where
    /// `data F a = F a` (`F :: Type -> Type`). Reference compiler
    /// reports as `ExpectedType`.
    ExpectedType(String),
    /// A kind signature (typically on `foreign import data X :: K`)
    /// uses a constrained-arrow shape `C => K` that the reference
    /// compiler doesn't support. Reports as `UnsupportedTypeInKind`.
    UnsupportedTypeInKind(String),
    /// `f @T` where `f`'s declared type doesn't have a top-level
    /// VISIBLE forall (`forall @a. ...`). Either the sig has no
    /// outer forall (`f :: Int -> Int`) or its outer forall is
    /// INVISIBLE (`f :: forall a. a -> a`). Reference compiler
    /// reports as `CannotApplyExpressionOfTypeOnType`.
    CannotApplyExpressionOfTypeOnType(String),
    /// A value declaration whose every equation has only guarded
    /// branches with no unconditional fallback (`| true = ...` /
    /// `| otherwise = ...` / refutable-pattern-free guard). The
    /// reference compiler reports this as needing a `Partial`
    /// constraint, which it then can't find — emitted as
    /// `NoInstanceFound` or `NonExhaustivePattern` upstream.
    NonExhaustiveGuardOnlyDecl(String),
    /// A recursive (self- or mutually-) value decl without a type
    /// signature whose body uses a class-method operator (`<>`,
    /// `+`, etc.) on a parameter binder. Generalization would
    /// need to introduce a constraint on a quantified var, which
    /// the reference compiler rejects as
    /// `CannotGeneralizeRecursiveFunction`.
    CannotGeneralizeRecursiveFunction(String),
    /// An instance member's explicit signature contradicts the
    /// class's declared member signature after substituting the
    /// instance's type arguments. E.g. `class Foo a where foo :: a;
    /// instance Foo Number where foo :: Int; foo = 0`. Reference
    /// compiler reports as `TypesDoNotUnify`.
    InstanceMemberSigMismatch(String),
    /// A value decl whose body is a bare reference to another
    /// signed value, where the two sigs are structurally different
    /// concrete types. E.g. `a :: { field :: Int }; a = ...;
    /// b :: { field :: String }; b = a`. Reference compiler
    /// reports as `TypesDoNotUnify`.
    ValueDeclSigAliasMismatch(String),
    /// A no-arg value decl whose body is a primitive literal
    /// (Int / Number / String / Char / Boolean) whose type
    /// doesn't match its declared signature. E.g.
    /// `foo :: Number; foo = true`. Reference compiler reports
    /// as `TypesDoNotUnify`.
    LiteralBodySigMismatch(String),
    /// A `do`-block ending in a `<-` bind. The last statement of
    /// a do block must be an expression — `do x <- y` alone is
    /// invalid. Reference compiler reports as `InvalidDoBind`.
    InvalidDoBind,
    /// A `do`-block ending in a `let`. The last statement of a
    /// do block must be an expression — `do let x = 1` alone is
    /// invalid. Reference compiler reports as `InvalidDoLet`.
    InvalidDoLet,
    /// A data constructor field of shape `forall a. F a` where
    /// `F` is locally polykinded (declared `data F a = …` with
    /// `a` not used in any constructor field, hence its kind is
    /// implicitly polymorphic). The kind of the inner `a` would
    /// have to be implicitly quantified at the field level,
    /// which the reference compiler rejects as
    /// `QuantificationCheckFailureInType`.
    QuantificationCheckFailureInType(String),
    /// Row labels supplied don't match the expected row in a
    /// kind annotation. E.g. `data P :: R (x, y) -> Type` applied
    /// to `Z :: forall r. R (z | r)` — Z's open row label `z`
    /// isn't in P's expected closed row `{x, y}`. Reference
    /// compiler reports as `KindsDoNotUnify`.
    KindsDoNotUnify(String),
    /// Visible kind quantification failure: a type alias body
    /// applies a kind annotation to a foreign-import-data type
    /// whose kind has multiple forall-bound vars. The annotation
    /// can't visibly bind all of them. Reference compiler reports
    /// as `VisibleQuantificationCheckFailureInType`.
    VisibleQuantificationCheckFailureInType(String),
    /// Skolem escape via rank-2 kind annotation. `type T = Proxy A`
    /// where `data A (a :: forall k. k -> Type) = A` — using A
    /// unapplied as an argument to a Type-expecting position lets
    /// the rank-2 quantifier escape. Reference compiler reports as
    /// `EscapedSkolem`.
    EscapedSkolem(String),
    /// An infinite type: `go :: Array _ -> Int; go xs = go [xs]`
    /// where the recursive call wraps the parameter in an extra
    /// constructor, forcing the wildcard to satisfy `_ = Array _`.
    /// Reference compiler reports as `InfiniteType`.
    InfiniteType(String),
    /// Standalone kind sig with unannotated forall var at a
    /// position whose expected kind is itself an applied type,
    /// requiring ill-ordered implicit kind generalization.
    /// Reference compiler reports as
    /// `QuantificationCheckFailureInKind`.
    QuantificationCheckFailureInKind(String),
    /// Chain instance fall-through to a `Fail`-constrained link.
    /// `class C` has chain instances starting with `C (X x x)`
    /// (repeated vars), and a use of the class method on a value
    /// of type `X a Int` (different positions) forces fall-through.
    /// Reference compiler reports as `NoInstanceFound`.
    NoInstanceFound(String),
}

impl ValidationErrorKind {
    pub fn code(&self) -> &'static str {
        match self {
            Self::DuplicateValueDeclaration(_) => "DuplicateValueDeclaration",
            Self::DuplicateTypeDeclaration(_) => "DuplicateTypeDeclaration",
            Self::DuplicateTypeClass(_) => "DuplicateTypeClass",
            Self::DuplicateTypeArgument(_) => "DuplicateTypeArgument",
            Self::DuplicateRoleDeclaration(_) => "DuplicateRoleDeclaration",
            Self::OrphanTypeSignature(_) => "OrphanTypeSignature",
            Self::OrphanKindDeclaration(_) => "OrphanKindDeclaration",
            Self::OrphanRoleDeclaration(_) => "OrphanRoleDeclaration",
            Self::MultipleValueOpFixities(_) => "MultipleValueOpFixities",
            Self::MultipleTypeOpFixities(_) => "MultipleTypeOpFixities",
            Self::CycleInTypeSynonym(_) => "CycleInTypeSynonym",
            Self::CycleInTypeClassDeclaration(_) => "CycleInTypeClassDeclaration",
            Self::CycleInKindDeclaration(_) => "CycleInKindDeclaration",
            Self::CycleInDeclaration(_) => "CycleInDeclaration",
            Self::PartiallyAppliedSynonym(_) => "PartiallyAppliedSynonym",
            Self::OrphanInstance(_) => "OrphanInstance",
            Self::DeclConflict(_) => "DeclConflict",
            Self::RoleDeclarationArityMismatch(_) => "RoleDeclarationArityMismatch",
            Self::ClassInstanceArityMismatch { .. } => "ClassInstanceArityMismatch",
            Self::WildcardInTypeDefinition => "WildcardInTypeDefinition",
            Self::ConstraintInForeignImport => "ConstraintInForeignImport",
            Self::InvalidConstraintArgument => "InvalidConstraintArgument",
            Self::TransitiveDctorExportError(_) => "TransitiveDctorExportError",
            Self::TransitiveExportError(_) => "TransitiveExportError",
            Self::InvalidInstanceHead => "InvalidInstanceHead",
            Self::ExportConflict(_) => "ExportConflict",
            Self::OverlappingArgNames(_) => "OverlappingArgNames",
            Self::OverlappingNamesInLet(_) => "OverlappingNamesInLet",
            Self::CannotDeriveNewtypeForData(_) => "CannotDeriveNewtypeForData",
            Self::IntOutOfRange => "IntOutOfRange",
            Self::InvalidOperatorInBinder(_) => "InvalidOperatorInBinder",
            Self::UnsupportedRoleDeclaration(_) => "UnsupportedRoleDeclaration",
            Self::MissingClassMember(_) => "MissingClassMember",
            Self::ExtraneousClassMember(_) => "ExtraneousClassMember",
            Self::IncorrectConstructorArity { .. } => "IncorrectConstructorArity",
            Self::UndefinedTypeVariable(_) => "UndefinedTypeVariable",
            Self::ArgListLengthsDiffer(_) => "ArgListLengthsDiffer",
            Self::DuplicateInstance(_) => "DuplicateInstance",
            Self::UnknownExport(_) => "UnknownExport",
            Self::UnknownExportDataConstructor(_) => "UnknownExportDataConstructor",
            Self::InvalidNewtypeInstance(_) => "InvalidNewtypeInstance",
            Self::OrphanTypeDeclaration(_) => "OrphanTypeDeclaration",
            Self::DeprecatedFFIPrime(_) => "DeprecatedFFIPrime",
            Self::InfiniteKind(_) => "InfiniteKind",
            Self::UnknownName(_) => "UnknownName",
            Self::InvalidModuleName(_) => "ErrorParsingModule",
            Self::NonAssociativeError(_) => "NonAssociativeError",
            Self::MixedAssociativityError(_) => "MixedAssociativityError",
            Self::OverlappingInstances(_) => "OverlappingInstances",
            Self::CannotDeriveInvalidConstructorArg(_) => {
                "CannotDeriveInvalidConstructorArg"
            }
            Self::ExpectedType(_) => "ExpectedType",
            Self::UnsupportedTypeInKind(_) => "UnsupportedTypeInKind",
            Self::CannotApplyExpressionOfTypeOnType(_) => {
                "CannotApplyExpressionOfTypeOnType"
            }
            Self::NonExhaustiveGuardOnlyDecl(_) => "NonExhaustivePattern",
            Self::CannotGeneralizeRecursiveFunction(_) => {
                "CannotGeneralizeRecursiveFunction"
            }
            Self::InstanceMemberSigMismatch(_) => "UnificationError",
            Self::ValueDeclSigAliasMismatch(_) => "UnificationError",
            Self::LiteralBodySigMismatch(_) => "UnificationError",
            Self::InvalidDoBind => "InvalidDoBind",
            Self::InvalidDoLet => "InvalidDoLet",
            Self::QuantificationCheckFailureInType(_) => {
                "QuantificationCheckFailureInType"
            }
            Self::KindsDoNotUnify(_) => "KindsDoNotUnify",
            Self::VisibleQuantificationCheckFailureInType(_) => {
                "VisibleQuantificationCheckFailureInType"
            }
            Self::EscapedSkolem(_) => "EscapedSkolem",
            Self::InfiniteType(_) => "InfiniteType",
            Self::QuantificationCheckFailureInKind(_) => {
                "QuantificationCheckFailureInKind"
            }
            Self::NoInstanceFound(_) => "NoInstanceFound",
        }
    }
}

/// Top-level entry point. Walks the module's decls once, emitting
/// every structural issue it finds.
pub fn validate_module(module: &cst::Module) -> Vec<ValidationError> {
    validate_module_with_imports(module, &HashMap::new())
}

/// Like [`validate_module`], but also given a map of imported alias
/// names → arity (interned). Used by `detect_partially_applied_synonyms`
/// so that operator-aliased imported synonyms (e.g. `(~>)` from a
/// `infixr 4 type NaturalTransformation as ~>` declaration in a
/// supporting module) are caught.
pub fn validate_module_with_imports(
    module: &cst::Module,
    imported_alias_arity: &HashMap<Symbol, usize>,
) -> Vec<ValidationError> {
    validate_module_with_full_imports(module, imported_alias_arity, &HashMap::new())
}

/// Like [`validate_module_with_imports`], but also given a map of
/// imported class names → arity. Used by the
/// `ClassInstanceArityMismatch` detector so that `derive instance
/// eqX :: Eq X X` (Eq has 1 type-var) is caught even when `Eq` was
/// imported.
pub fn validate_module_with_full_imports(
    module: &cst::Module,
    imported_alias_arity: &HashMap<Symbol, usize>,
    imported_class_arity: &HashMap<Symbol, usize>,
) -> Vec<ValidationError> {
    validate_module_with_class_fundeps(
        module,
        imported_alias_arity,
        &HashSet::new(),
        imported_class_arity,
        &HashMap::new(),
    )
}

/// Like [`validate_module_with_full_imports`], but also given a map
/// of imported class names → positional fundeps. Used by the
/// `OrphanInstance` detector for fundep-aware covering-set checks.
/// Each `FunDepPositions(determiners, determined)` is a pair of
/// `Vec<usize>` indexing into the class's type_vars.
pub fn validate_module_with_class_fundeps(
    module: &cst::Module,
    imported_alias_arity: &HashMap<Symbol, usize>,
    imported_poly_kind_set: &HashSet<Symbol>,
    imported_class_arity: &HashMap<Symbol, usize>,
    imported_class_fundeps: &HashMap<Symbol, Vec<(Vec<usize>, Vec<usize>)>>,
) -> Vec<ValidationError> {
    let mut errors: Vec<ValidationError> = Vec::new();

    // Collect symbol-keyed views of each namespace. We need both
    // "has declaration" (for orphan detection) and "how many, with
    // spans" (for duplicates).
    // Track value declarations in two layers:
    //   - `value_groups`: count of *distinct* (non-adjacent) groups per name.
    //     A multi-equation function like `f Nothing = 0 / f (Just x) = x`
    //     is ONE group, not two. Only non-adjacent re-definitions count as
    //     duplicates.
    //   - `value_has_any`: hash-set of every name that has at least one
    //     value decl. Used for orphan-signature detection.
    let mut value_groups: HashMap<Symbol, Vec<Span>> = HashMap::new();
    let mut value_has_any: HashSet<Symbol> = HashSet::new();
    let mut last_value_name: Option<Symbol> = None;
    let mut type_sigs: HashMap<Symbol, Span> = HashMap::new();
    let mut type_decls: HashMap<Symbol, Vec<Span>> = HashMap::new();
    let mut class_decls: HashMap<Symbol, Vec<Span>> = HashMap::new();
    let mut standalone_kinds: HashMap<Symbol, Span> = HashMap::new();
    let mut role_decls: HashMap<Symbol, Vec<Span>> = HashMap::new();
    let mut value_ops: HashMap<Symbol, Vec<Span>> = HashMap::new();
    let mut type_ops: HashMap<Symbol, Vec<Span>> = HashMap::new();
    let mut class_members: HashSet<Symbol> = HashSet::new();

    for decl in &module.decls {
        match decl {
            cst::Decl::Value { span, name, binders, .. } => {
                let sym = name.value.symbol();
                value_has_any.insert(sym);
                // Start a new group unless this equation is adjacent
                // to the previous one with the same name. An
                // arg-less equation (`foo = 1`) is itself a complete
                // definition — a second `foo = 2` even adjacent is a
                // genuine duplicate.
                if last_value_name != Some(sym) || binders.is_empty() {
                    value_groups.entry(sym).or_default().push(*span);
                }
                last_value_name = Some(sym);
            }
            cst::Decl::TypeSignature { span, name, .. } => {
                if type_sigs.contains_key(&name.value.symbol()) {
                    // Two signatures for the same name — second is the
                    // duplicate. Emit once per extra signature.
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::DuplicateValueDeclaration(
                            resolve(name.value.symbol()),
                        ),
                    });
                } else {
                    type_sigs.insert(name.value.symbol(), *span);
                }
            }
            cst::Decl::Data {
                span,
                name,
                type_vars,
                kind_sig,
                is_role_decl,
                ..
            } => {
                if *is_role_decl {
                    role_decls.entry(name.value.symbol()).or_default().push(*span);
                } else if matches!(kind_sig, cst::KindSigSource::None) {
                    type_decls.entry(name.value.symbol()).or_default().push(*span);
                    check_duplicate_type_args(type_vars, &mut errors);
                } else {
                    // Standalone kind signature (`data Foo :: Kind`)
                    standalone_kinds.entry(name.value.symbol()).or_insert(*span);
                }
            }
            cst::Decl::TypeAlias { span, name, type_vars, .. } => {
                type_decls.entry(name.value.symbol()).or_default().push(*span);
                check_duplicate_type_args(type_vars, &mut errors);
            }
            cst::Decl::Newtype { span, name, type_vars, .. } => {
                type_decls.entry(name.value.symbol()).or_default().push(*span);
                check_duplicate_type_args(type_vars, &mut errors);
            }
            cst::Decl::Class {
                span,
                name,
                type_vars,
                is_kind_sig,
                members,
                ..
            } => {
                if *is_kind_sig {
                    standalone_kinds.entry(name.value.symbol()).or_insert(*span);
                } else {
                    class_decls.entry(name.value.symbol()).or_default().push(*span);
                    check_duplicate_type_args(type_vars, &mut errors);
                    for m in members {
                        class_members.insert(m.name.value.symbol());
                    }
                }
            }
            cst::Decl::Foreign { span, name, .. } => {
                let sym = name.value.symbol();
                // Foreign import acts as both signature and value.
                type_sigs.entry(sym).or_insert(*span);
                value_has_any.insert(sym);
                if last_value_name != Some(sym) {
                    value_groups.entry(sym).or_default().push(*span);
                }
                last_value_name = Some(sym);
            }
            cst::Decl::ForeignData { span, name, .. } => {
                type_decls.entry(name.value.symbol()).or_default().push(*span);
            }
            cst::Decl::Fixity {
                span,
                operator,
                is_type,
                ..
            } => {
                if *is_type {
                    type_ops.entry(operator.value.symbol()).or_default().push(*span);
                } else {
                    value_ops.entry(operator.value.symbol()).or_default().push(*span);
                }
            }
            cst::Decl::Instance { members, .. } => {
                // Walk each instance member's name with the same
                // adjacency rule as top-level values, emitting
                // `DuplicateValueDeclaration` for non-adjacent
                // re-definitions of the same method.
                let mut last_method: Option<Symbol> = None;
                let mut method_groups: HashMap<Symbol, Vec<Span>> = HashMap::new();
                for m in members {
                    if let cst::Decl::Value { span, name, binders, .. } = m {
                        let sym = name.value.symbol();
                        if last_method != Some(sym) || binders.is_empty() {
                            method_groups.entry(sym).or_default().push(*span);
                        }
                        last_method = Some(sym);
                    } else {
                        last_method = None;
                    }
                }
                for (sym, spans) in &method_groups {
                    if spans.len() > 1 {
                        for span in spans.iter().skip(1) {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::DuplicateValueDeclaration(
                                    resolve(*sym),
                                ),
                            });
                        }
                    }
                }
            }
            cst::Decl::Derive { .. } => {
                // Overlapping / duplicate instance checking happens in
                // Bucket 6 — needs InstanceIndex which is built later.
            }
        }
    }

    // Duplicate value declarations: the NAME appeared in more than one
    // non-adjacent group of equations.
    for (sym, spans) in &value_groups {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::DuplicateValueDeclaration(resolve(*sym)),
                });
            }
        }
    }

    // Duplicate type decls — `data Fail; data Fail` and friends.
    // Reference compiler reports these as `DeclConflict`, not as a
    // distinct "duplicate" category, so use that variant. The
    // `DuplicateTypeDeclaration` ValidationErrorKind is retained
    // for downstream-API stability but no longer surfaced from
    // this pass.
    for (sym, spans) in &type_decls {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::DeclConflict(resolve(*sym)),
                });
            }
        }
    }

    // Duplicate classes
    for (sym, spans) in &class_decls {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::DuplicateTypeClass(resolve(*sym)),
                });
            }
        }
    }

    // Duplicate role decls
    for (sym, spans) in &role_decls {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::DuplicateRoleDeclaration(resolve(*sym)),
                });
            }
        }
    }

    // Multiple fixities for the same operator.
    for (sym, spans) in &value_ops {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::MultipleValueOpFixities(resolve(*sym)),
                });
            }
        }
    }
    for (sym, spans) in &type_ops {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::MultipleTypeOpFixities(resolve(*sym)),
                });
            }
        }
    }

    // Orphan type signatures: a signature with no matching value decl
    // (and not a class method).
    for (sym, span) in &type_sigs {
        if !value_has_any.contains(sym) && !class_members.contains(sym) {
            errors.push(ValidationError {
                span: *span,
                kind: ValidationErrorKind::OrphanTypeSignature(resolve(*sym)),
            });
        }
    }

    // Orphan kind signatures: a standalone kind sig with no matching
    // data/newtype/type/class.
    for (sym, span) in &standalone_kinds {
        if !type_decls.contains_key(sym) && !class_decls.contains_key(sym) {
            errors.push(ValidationError {
                span: *span,
                kind: ValidationErrorKind::OrphanKindDeclaration(resolve(*sym)),
            });
        }
    }

    // Orphan role decls. Two conditions:
    //   (a) role targets a name that doesn't exist locally, OR
    //   (b) role isn't adjacent (immediately before or after) the
    //       matching data/newtype decl.
    {
        // Build positional indices of each Decl::Data (real, not
        // role/kind), Decl::Newtype, Decl::ForeignData, plus the
        // role decls themselves.
        let mut data_positions: HashMap<Symbol, Vec<usize>> = HashMap::new();
        let mut role_positions: HashMap<Symbol, Vec<usize>> = HashMap::new();
        for (i, d) in module.decls.iter().enumerate() {
            match d {
                cst::Decl::Data { name, kind_sig, is_role_decl, .. } => {
                    if *is_role_decl {
                        role_positions.entry(name.value.symbol()).or_default().push(i);
                    } else if matches!(kind_sig, cst::KindSigSource::None) {
                        data_positions.entry(name.value.symbol()).or_default().push(i);
                    }
                }
                cst::Decl::Newtype { name, .. } => {
                    data_positions.entry(name.value.symbol()).or_default().push(i);
                }
                cst::Decl::ForeignData { name, .. } => {
                    data_positions.entry(name.value.symbol()).or_default().push(i);
                }
                _ => {}
            }
        }
        for (sym, spans) in &role_decls {
            // No matching data decl at all → orphan.
            if !type_decls.contains_key(sym) {
                for span in spans {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::OrphanRoleDeclaration(resolve(*sym)),
                    });
                }
                continue;
            }
            // Adjacency check: role must be at index ±1 of its data
            // decl. Otherwise the original compiler reports it as
            // orphan (a role separated from its decl by other decls
            // is treated the same as an unattached role).
            let Some(role_idxs) = role_positions.get(sym) else { continue };
            let Some(data_idxs) = data_positions.get(sym) else { continue };
            for (role_idx, span) in role_idxs.iter().zip(spans.iter()) {
                // Role must IMMEDIATELY follow its matching data
                // decl (i.e. data_idx == role_idx - 1). The original
                // compiler does not accept role-before-data nor
                // role separated by intervening decls.
                let well_placed = data_idxs.iter().any(|d| {
                    *d + 1 == *role_idx
                });
                if !well_placed {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::OrphanRoleDeclaration(resolve(*sym)),
                    });
                }
            }
        }
    }

    // Cycle detection --------------------------------------------------
    detect_alias_cycles(&module.decls, &mut errors);
    detect_class_cycles(&module.decls, &mut errors);
    detect_kind_sig_cycles(&module.decls, &mut errors);
    detect_value_cycles(&module.decls, &mut errors);

    // Transitive export errors (subset — only catches the cases
    // decidable purely from the CST):
    //   - TransitiveDctorExportError: `T(A)` names fewer constructors
    //     than `data T = A | B | …` has.
    //   - TransitiveExportError: an exported value-operator alias
    //     whose fixity target isn't also exported.
    detect_transitive_export_errors(module, &mut errors);

    // Parse-level structural rejections that our grammar lets through:
    //   - Wildcards in type definitions (type/data/newtype RHS).
    //   - `=>` in foreign-import signatures.
    //   - Invalid constraint arguments (forall-quantified / wildcard).
    detect_parse_level_rejections(&module.decls, &mut errors);

    // ClassInstanceArityMismatch: instance head's type-arg count must
    // match the class's parameter count. Local classes are read from
    // decls; imported classes come in via `imported_class_arity`.
    detect_class_instance_arity(&module.decls, imported_class_arity, &mut errors);

    // RoleDeclarationArityMismatch: `type role Foo r1 r2 …` must match the
    // arity of the matching data/newtype/foreign-data.
    detect_role_arity_mismatches(&module.decls, &mut errors);

    // DeclConflict: cross-namespace name collisions at the type level
    // (e.g. `class Fail` + `data Fail`), plus duplicate data-constructor
    // names inside one decl or across data decls in the module.
    detect_decl_conflicts(&module.decls, &mut errors);

    // Unknown class references: instance / derive / class
    // superclass clauses that name a class neither declared locally
    // nor brought in via an unqualified import.
    detect_unknown_class_references(
        &module.decls,
        imported_class_arity,
        &mut errors,
    );


    // Orphan instances: declared where neither the class nor any type
    // constructor in the instance head is defined locally. Skips
    // instances whose class is unknown — those already emitted
    // UnknownName above.
    detect_orphan_instances(
        &module.decls,
        imported_class_arity,
        imported_class_fundeps,
        &mut errors,
    );

    detect_partially_applied_synonyms(
        &module.decls,
        imported_alias_arity,
        imported_poly_kind_set,
        &mut errors,
    );
    detect_invalid_instance_heads(
        &module.decls,
        imported_class_fundeps,
        &mut errors,
    );

    // Single-pass walk over each Decl::Value's binders + every nested
    // Case alternative + every Lambda inside it. Looks for the same
    // var name appearing twice in a single binder list (or one
    // top-level Decl::Value's whole arg list).
    detect_overlapping_arg_names(&module.decls, &mut errors);

    // Walk each `let` / `where` block looking for the same name
    // declared twice non-adjacently (multi-equation defs are
    // allowed when contiguous, just like at the module level).
    detect_overlapping_names_in_let(&module.decls, &mut errors);

    // `derive newtype instance C (T ...)` requires T to be a `newtype`,
    // not a `data`. Local data/newtype distinction only.
    detect_cannot_derive_newtype_for_data(&module.decls, &mut errors);

    // Operator usage in binder position — only ctor-shaped operators
    // (`infixl 6 Cons as :`) are valid binders. Function-aliased
    // operators (`infixl 6 cons as :` where `cons` is a function)
    // make the binder un-deconstructable.
    detect_invalid_operator_in_binder(&module.decls, &mut errors);

    // `Int` literal whose value is outside the i32 range.
    detect_int_out_of_range(&module.decls, &mut errors);

    // `type role` only valid on data/newtype/foreign-data.
    detect_unsupported_role_declaration(&module.decls, &mut errors);

    // Instance member sets must match the class's declared method
    // set (Missing- or ExtraneousClassMember). Local classes only.
    detect_class_member_mismatch(&module.decls, &mut errors);

    // Constructor pattern arity must match the declared ctor.
    detect_incorrect_constructor_arity(&module.decls, &mut errors);

    // Free type variables in class superclasses + alias bodies must
    // be in scope.
    detect_undefined_type_variables(&module.decls, &mut errors);

    // Direct self-referential let bindings (`let x = x in ...`).
    detect_let_self_cycle(&module.decls, &mut errors);

    // `do`-block whose final statement is a `<-` bind or `let`.
    // Reference compiler reports `InvalidDoBind` / `InvalidDoLet`.
    detect_invalid_do_terminal(&module.decls, &mut errors);

    // Flat record update field whose value is itself a record-update
    // section: `outer { a = { b = 42 } }` sets `a` to the section
    // `{ b = 42 }` (function type), which can't unify with whatever
    // record type `a` was declared as. Reference compiler reports as
    // `TypesDoNotUnify`.
    detect_record_update_section_as_value(&module.decls, &mut errors);

    // `data X = X (forall a. P a)` where `P` is a LOCAL polykinded
    // data type (its parameter doesn't appear in any constructor
    // field). The reference compiler infers `P :: forall k. k ->
    // Type`, which means the inner `a`'s kind would have to be an
    // implicit kind variable not bound by any visible quantifier —
    // rejected as `QuantificationCheckFailureInType`.
    detect_polykinded_rank2_in_ctor(&module.decls, &mut errors);

    // Row-in-kind label mismatch: `data P :: R (x, y) -> Type`
    // applied to `Z :: forall r. R (z | r)` where the open-row
    // labels of Z aren't a subset of the closed-row labels of P's
    // expected param. Reference compiler reports as
    // `KindsDoNotUnify`.
    detect_row_kind_label_mismatch(&module.decls, &mut errors);

    // ScopedTypeVariables-via-alias: `foo :: T` (where T is a type
    // alias whose body has explicit forall) followed by an inner
    // where/let signature with type vars that aren't in the inner
    // sig's own explicit forall. The outer alias hides the forall
    // from the inner scope, making the inner vars unbound.
    // Reference compiler reports as `UndefinedTypeVariable`.
    detect_scoped_var_via_alias(&module.decls, &mut errors);

    // Visible-quantification kind annotation: `type T = (X :: K)`
    // where X is a foreign-import-data with 2+ forall-bound kind
    // variables. The annotation can't visibly bind all of them.
    detect_visible_quant_kind_ann(&module.decls, &mut errors);

    // Skolem escape via rank-2 kind: `type B = Proxy A` where A
    // has a rank-2 kind annotation on its param (`data A
    // (a :: forall k. k -> Type) = A`). Using A unapplied as an
    // arg to Proxy (which expects Type) lets the rank-2 quantifier
    // escape. Reference compiler reports as `EscapedSkolem`.
    detect_skolem_escape_via_rank2_kind(&module.decls, &mut errors);

    // Polymorphic-proxy kind mismatch: `put (SProxy :: SProxy
    // "apple")` where put has signature `forall proxy a. proxy a
    // -> TProxy a` (a appears at both proxy-position and a
    // Type-kinded position). The arg's literal forces a to be
    // Symbol/Int kind, conflicting with the Type-kinded use site.
    detect_polymorphic_proxy_kind_mismatch(&module.decls, &mut errors);

    // Recursive-wrap infinite type: `go :: Array _ -> Int; go xs =
    // go [xs]` where the recursive call wraps the parameter in an
    // additional Array, forcing the wildcard to be infinite.
    detect_recursive_wildcard_wrap(&module.decls, &mut errors);

    // Quantification-check failure in kind: standalone kind sig
    // with unannotated forall var used at a position whose
    // expected kind is itself an applied type (depends on other
    // vars). E.g. `data T :: forall ... d. Relate b d -> Type`
    // where Relate's 2nd arg expects `Proxy b'`. d's kind would
    // need implicit generalization referencing another forall var.
    detect_quant_check_failure_in_kind(&module.decls, &mut errors);

    // Chain-instance fall-through to Fail: `class C` with chain
    // instances where the first head has repeated type vars
    // (`C (X x x)`) and a later chain link has `Fail` constraint.
    // A use site of the method on a value whose type has
    // DIFFERENT positions (`X a Int`) forces the chain to fall
    // through to the Fail-constrained instance, emitting
    // `NoInstanceFound`.
    detect_chain_fail_fall_through(&module.decls, &mut errors);

    // Polykind-instantiated class instance: a local class method
    // `f :: (a -> b) -> ... -> f a -> ...` called with a primitive
    // literal in a wildcard kind annotation `(C :: _ "foo")`. The
    // surrounding call constrains a's kind to Type but the
    // annotation forces Symbol. Reference compiler reports as
    // `KindsDoNotUnify`.
    detect_polykind_class_method_kind_mismatch(&module.decls, &mut errors);

    // Nested update setting a row-parameterized field to a
    // primitive literal: `state { context { fields = "Not a
    // record" } }` where some local type alias declares
    // `... fields :: { | row_param }, ...`. The field expects a
    // record but is assigned a string. Reference compiler reports
    // as `TypesDoNotUnify`.
    detect_nested_update_row_field_mismatch(&module.decls, &mut errors);

    // Recursive chain ambiguity in where-binding: `go :: forall
    // i. C i => ... -> ...` recursively calls itself with
    // `Proxy (Cons i)` annotation, where C has a chain instance
    // `C x => C (Cons x)`. The recursive constraint can't be
    // discharged, leading to NoInstanceFound.
    detect_where_binding_chain_ambiguity(&module.decls, &mut errors);

    // Instance method CAF cycle: a 0-binder method body that
    // references another method of the same class without a lambda
    // barrier creates a dictionary-construction cycle.
    detect_instance_method_caf_cycle(&module.decls, &mut errors);

    // InfiniteKind: type-variable applied to itself
    // (`data F a = F (a a)`). A self-application would require an
    // infinite kind, so the kind unifier rejects it.
    detect_infinite_kind(&module.decls, &mut errors);

    // Invalid module name: apostrophes / underscores in any part
    // of the module name string. The reference compiler reports
    // these as `ErrorParsingModule`.
    detect_invalid_module_name(module, &mut errors);

    // Non-associative operator chained with itself (`a == b == c`
    // or `a >> b >> a` where the op is `infix`).
    detect_non_associative_chain(&module.decls, &mut errors);

    // Mixed associativity at the same precedence — local-only
    // version (no imports). Driver re-runs the imported variant.
    detect_mixed_associativity(
        &module.decls,
        &HashMap::new(),
        &HashMap::new(),
        &mut errors,
    );

    // OverlappingInstances: two instances of the same local class
    // whose heads can match the same type (one is at least as
    // general as the other).
    detect_overlapping_instances(&module.decls, &mut errors);

    // CannotDeriveInvalidConstructorArg: walk derive-instance
    // constructor field types tracking variance; flag if the
    // tracked type-var(s) appear in a position incompatible with
    // the class's variance contract.
    detect_invalid_derive_constructor_arg(&module.decls, &mut errors);

    // Equation arity mismatch (same value name, different binder
    // counts).
    detect_arg_list_lengths_differ(&module.decls, &mut errors);

    // Two `instance i :: ...` decls with the same instance name.
    detect_duplicate_instance(&module.decls, &mut errors);

    // Export-list referencing names / ctors not declared in this
    // module. Open imports cause us to skip the value/class/op
    // checks entirely (callers with registry access can run a more
    // precise version); the `T(C1, C2)` ctor-membership check
    // still fires unconditionally since it's local-only.
    detect_unknown_exports(module, &mut errors);

    // Refined orphan-kind detection: a `type Foo :: Type` standalone
    // kind sig (KindSigSource::Type) requires a matching type alias,
    // not a data/newtype. Same for the other source variants.
    detect_orphan_kind_source_mismatch(&module.decls, &mut errors);

    // Inside an instance body, a TypeSignature without a matching
    // Value definition becomes `OrphanTypeDeclaration`.
    detect_instance_orphan_type_signatures(&module.decls, &mut errors);

    // `derive newtype instance ...` shape checks (`InvalidNewtypeInstance`).
    detect_invalid_newtype_derive(&module.decls, &mut errors);

    // `foreign import a'` etc. — apostrophe in FFI names is
    // deprecated.
    detect_deprecated_ffi_prime(&module.decls, &mut errors);

    // Type annotations like `(x :: F)` where `F` is a higher-kinded
    // type constructor (`data F a = ...`) used without args.
    detect_expected_type_in_annotations(&module.decls, &mut errors);

    // Constraint-arrow shapes inside kind signatures (`foreign
    // import data X :: C => K`) — reference compiler rejects.
    detect_unsupported_type_in_kind(&module.decls, &mut errors);

    // Exported values whose body uses local data constructors
    // whose parent type isn't itself exported → TransitiveExportError.
    detect_transitive_export_via_hidden_type(module, &mut errors);

    // `f @Int` where `f`'s declared sig either has no forall or
    // has an INVISIBLE forall — VTA isn't allowed there.
    detect_visible_type_app_on_non_visible_forall(&module.decls, &mut errors);

    // `f x | 1 <- x = x` and similar: a value decl whose every
    // equation has only conditional guards (no `| true` /
    // `| otherwise` fallback) and no other unconditional equation
    // is non-exhaustive at the guard level.
    detect_non_exhaustive_guard_only_decl(&module.decls, &mut errors);

    // Recursive sig-less value decls whose body uses a class-method
    // operator on a parameter binder (e.g. `foo n x = x <> bar n x`):
    // generalization can't introduce the required class constraint
    // on the recursive function's quantified type-var.
    detect_cannot_generalize_recursive_function(&module.decls, &mut errors);

    // Instance member sigs that contradict the class's declared
    // sig after substitution (`class Foo a where foo :: a;
    // instance Foo Number where foo :: Int`).
    detect_instance_member_sig_mismatch(&module.decls, &mut errors);

    // `a :: T1; a = ...; b :: T2; b = a` where T1 and T2 are
    // structurally different concrete types.
    detect_value_decl_sig_alias_mismatch(&module.decls, &mut errors);

    // `foo :: Number; foo = true` — body literal type clashes
    // with the declared signature.
    detect_literal_body_sig_mismatch(&module.decls, &mut errors);

    errors
}

/// Reject instance heads whose argument is structurally invalid:
/// - A bare record literal `{}` or `{ … }` (`derive instance eqRecord :: Eq {}`).
/// - A wildcard `_` (`instance showFoo :: Show (Foo _)`).
/// - A reference to a *local* type-alias whose body is a record/row
///   (`type T = {}; derive instance eqT :: Eq T`,
///   `type X r = { x :: Int | r }; instance showX :: Show (X r)`).
///
/// Reference compiler reports these as `InvalidInstanceHead`. Imported
/// aliases aren't accessible here so we conservatively skip them.
fn detect_invalid_instance_heads(
    decls: &[cst::Decl],
    imported_class_fundeps: &HashMap<Symbol, Vec<(Vec<usize>, Vec<usize>)>>,
    errors: &mut Vec<ValidationError>,
) {
    // Build a map of local type-alias name → body, so we can look
    // through one level of aliasing for the record/row check.
    let mut alias_body: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
    // Per-class positional fundep info. We use this to compute
    // "allowed-record positions" — a position p is allowed to be
    // a bare record/row literal iff p is in some fundep's
    // `determined` AND p is NOT in any fundep's `determiners`.
    // (Cyclic fundeps like `a -> b, b -> a` make every position
    // both — none qualifies as truly determined.)
    let mut local_class_fundeps: HashMap<Symbol, Vec<(Vec<usize>, Vec<usize>)>> =
        HashMap::new();
    for d in decls {
        match d {
            cst::Decl::TypeAlias { name, ty, .. } => {
                alias_body.insert(name.value.symbol(), ty);
            }
            cst::Decl::Class { name, type_vars, fundeps, .. } if !fundeps.is_empty() => {
                let var_names: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                let fd: Vec<(Vec<usize>, Vec<usize>)> = fundeps
                    .iter()
                    .map(|f| {
                        let lhs: Vec<usize> = f
                            .lhs
                            .iter()
                            .filter_map(|v| {
                                var_names.iter().position(|s| *s == v.symbol())
                            })
                            .collect();
                        let rhs: Vec<usize> = f
                            .rhs
                            .iter()
                            .filter_map(|v| {
                                var_names.iter().position(|s| *s == v.symbol())
                            })
                            .collect();
                        (lhs, rhs)
                    })
                    .collect();
                local_class_fundeps.insert(name.value.symbol(), fd);
            }
            _ => {}
        }
    }

    fn walk_to_record_alias(
        te: &cst::TypeExpr,
        alias_body: &HashMap<Symbol, &cst::TypeExpr>,
        seen: &mut HashSet<Symbol>,
    ) -> bool {
        match te {
            cst::TypeExpr::Parens { ty, .. } => {
                walk_to_record_alias(ty, alias_body, seen)
            }
            cst::TypeExpr::Constructor { name, .. } if name.module.is_none() => {
                let sym = name.name.symbol();
                if !seen.insert(sym) {
                    return false;
                }
                if let Some(body) = alias_body.get(&sym) {
                    // Alias body that's a bare Record literal (closed
                    // record) is record-headed. A Row with
                    // `is_record = true` (the `{ … | tail }` form)
                    // is record-headed only when its tail is a
                    // *bare type variable* — that's the open-record
                    // case the original compiler rejects. When the
                    // tail is an APPLICATION (`EnvRow ()`) we can't
                    // tell from the CST whether it's open or closed,
                    // so we conservatively allow it.
                    match peel_parens(body) {
                        cst::TypeExpr::Record { .. } => true,
                        // `{ fields | r }` with non-empty fields is concrete/partial → record-headed.
                        // `{ | r }` (no fields) is just `Record r` — NOT record-headed.
                        cst::TypeExpr::Row {
                            is_record: true,
                            fields,
                            tail: Some(t),
                            ..
                        } if !fields.is_empty()
                            && matches!(peel_parens(t), cst::TypeExpr::Var { .. }) =>
                        {
                            true
                        }
                        _ => walk_to_record_alias(body, alias_body, seen),
                    }
                } else {
                    false
                }
            }
            cst::TypeExpr::App { constructor, .. } => {
                // App-headed alias: head must be the alias.
                walk_to_record_alias(constructor, alias_body, seen)
            }
            _ => false,
        }
    }

    fn head_is_invalid(
        te: &cst::TypeExpr,
        alias_body: &HashMap<Symbol, &cst::TypeExpr>,
        allow_top_wildcard: bool,
    ) -> bool {
        match peel_parens(te) {
            cst::TypeExpr::Wildcard { .. } => !allow_top_wildcard,
            // Bare record literal `{}` / `{ x :: Int }` — not a named
            // type. Always invalid regardless of fundeps.
            cst::TypeExpr::Record { .. } => true,
            // `{ fields | r }` with non-empty fields: partially
            // concrete open record → invalid unless determined.
            // `{ | r }` (no fields): equivalent to `Record r`, a
            // type-constructor application to a variable → VALID,
            // never flag it.
            cst::TypeExpr::Row {
                is_record: true,
                fields,
                tail: Some(t),
                ..
            } if !fields.is_empty()
                && matches!(peel_parens(t), cst::TypeExpr::Var { .. }) =>
            {
                true
            }
            other => {
                if has_wildcard(other) {
                    return true;
                }
                let mut seen: HashSet<Symbol> = HashSet::new();
                walk_to_record_alias(other, alias_body, &mut seen)
            }
        }
    }

    for d in decls {
        let (types, class_name, span, is_derive) = match d {
            cst::Decl::Instance { types, class_name, span, .. } => {
                (types, class_name, span, false)
            }
            cst::Decl::Derive { types, class_name, span, .. } => {
                (types, class_name, span, true)
            }
            _ => continue,
        };
        let cqi = class_name.to_qi();
        if cqi.module.is_some() {
            continue;
        }
        // Per-position record-allowed mask. Classes WITH fundeps
        // get fundep-aware checks (record allowed only in truly
        // determined positions); classes without fundeps disallow
        // record/row in every position.
        let fundeps = local_class_fundeps
            .get(&cqi.name)
            .or_else(|| imported_class_fundeps.get(&cqi.name));
        let allowed_record_pos: Vec<bool> = match fundeps {
            None => vec![false; types.len()],
            Some(fds) => {
                // A position is "allowed-record" iff it is NOT in
                // any MINIMAL covering set of the fundep system.
                // (A covering set S is one whose fundep-closure
                // covers every position. Minimal = no proper subset
                // is covering.) Cyclic fundeps like `a -> b, b -> a`
                // produce minimal covers {a} and {b} — both
                // positions appear in some minimal cover, so
                // neither is allowed-record. But for `a -> b` alone,
                // {a, c} is the only minimal cover (where c is
                // unmentioned), so b is never in a minimal cover
                // → allowed-record.
                let n = types.len();
                always_determined_positions(n, fds)
            }
        };
        for (i, t) in types.iter().enumerate() {
            if allowed_record_pos.get(i).copied().unwrap_or(false) {
                continue;
            }
            // `derive instance Newtype (Min a) _` puts a top-level
            // wildcard in the second arg as the canonical
            // newtype-representation pattern; that's legitimate.
            // Wildcards nested inside a constructor (`Show (Foo _)`)
            // are still rejected.
            if head_is_invalid(t, &alias_body, is_derive) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::InvalidInstanceHead,
                });
                break;
            }
        }
    }
}

fn peel_parens(te: &cst::TypeExpr) -> &cst::TypeExpr {
    let mut cur = te;
    while let cst::TypeExpr::Parens { ty, .. } = cur {
        cur = ty;
    }
    cur
}

/// Compute `[bool; n]` where `out[i]` is `true` iff position `i`
/// is "always determined" — i.e. NOT in any minimal covering set
/// of the fundep system. Falls back to `false` (not allowed for
/// record) when computation would be infeasible.
///
/// Algorithm: enumerate all 2^n subsets, compute closure under
/// fundeps, retain those whose closure covers all `n` positions
/// (covering sets), filter to MINIMAL covers (no proper subset is
/// also a cover). A position is always-determined iff it appears
/// in NONE of the minimal covers.
fn always_determined_positions(
    n: usize,
    fundeps: &[(Vec<usize>, Vec<usize>)],
) -> Vec<bool> {
    if n == 0 || n > 12 {
        // 2^12 = 4096 subsets is the practical limit; bail on
        // larger classes (extraordinarily rare in practice).
        return vec![false; n];
    }
    let total = 1u32 << n;
    let mut covers: Vec<u32> = Vec::new();
    for s in 0..total {
        let closure = fundep_closure(s, n, fundeps);
        if closure == total - 1 {
            covers.push(s);
        }
    }
    // Filter to minimal: drop any cover that has a strict subset
    // also in the cover list.
    let minimal: Vec<u32> = covers
        .iter()
        .copied()
        .filter(|&c| {
            !covers
                .iter()
                .any(|&other| other != c && (other & c) == other)
        })
        .collect();
    let mut union: u32 = 0;
    for c in &minimal {
        union |= c;
    }
    // Position i is always-determined iff its bit is NOT in union.
    (0..n).map(|i| (union & (1u32 << i)) == 0).collect()
}

/// Bitset closure: starting from `set`, repeatedly add `rhs` of
/// any fundep whose `lhs` is fully contained.
fn fundep_closure(
    initial: u32,
    n: usize,
    fundeps: &[(Vec<usize>, Vec<usize>)],
) -> u32 {
    let _ = n;
    let mut cur = initial;
    loop {
        let mut next = cur;
        for (lhs, rhs) in fundeps {
            let lhs_bits: u32 = lhs.iter().fold(0, |acc, &p| acc | (1u32 << p));
            if (cur & lhs_bits) == lhs_bits {
                let rhs_bits: u32 =
                    rhs.iter().fold(0, |acc, &p| acc | (1u32 << p));
                next |= rhs_bits;
            }
        }
        if next == cur {
            return cur;
        }
        cur = next;
    }
}

/// CannotDeriveInvalidConstructorArg. Walks data-ctor field types
/// for `derive instance C T` where C is a variance-bearing class
/// (Functor/Foldable/Traversable/Contravariant/Bifunctor/Profunctor
/// /Bifoldable/Bitraversable). For each tracked type-var, walks
/// the field type tracking variance and flags any occurrence in
/// a position incompatible with the class's contract.
///
/// Variance accounting:
///   - Function arrow `from -> to`: `from` flips, `to` keeps.
///   - App on a known-contravariant ctor (Predicate, Op, …):
///     the arg's variance is flipped.
///   - App on any other ctor / type-var: assumed COVARIANT
///     (conservative; misses some cases but avoids false
///     positives on user types whose variance we don't know).
///   - Forall / Constrained: skip (the body's variance involves
///     the constraint context which our shallow walk can't
///     analyse — we conservatively flag any tracked-var
///     occurrence inside as "invalid" only when the surrounding
///     position itself was already invalid).
fn detect_invalid_derive_constructor_arg(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap;
    // Build local data-ctor field lists keyed by data-type name,
    // along with the type-var list (in source order).
    let mut data_info: HashMap<Symbol, (Vec<Symbol>, Vec<Vec<&cst::TypeExpr>>)> =
        HashMap::new();
    // Track foreign-imported type constructors. Their variance is
    // unknown (no instance machinery available), so any tracked-var
    // occurrence under such a head should be flagged.
    let mut foreign_types: HashSet<Symbol> = HashSet::new();
    for d in decls {
        match d {
            cst::Decl::Data {
                name,
                type_vars,
                constructors,
                kind_sig: cst::KindSigSource::None,
                is_role_decl: false,
                ..
            } => {
                let vars: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                let fields: Vec<Vec<&cst::TypeExpr>> = constructors
                    .iter()
                    .map(|c| c.fields.iter().collect())
                    .collect();
                data_info.insert(name.value.symbol(), (vars, fields));
            }
            cst::Decl::Newtype { name, type_vars, ty, .. } => {
                let vars: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                let fields: Vec<Vec<&cst::TypeExpr>> = vec![vec![ty]];
                data_info.insert(name.value.symbol(), (vars, fields));
            }
            cst::Decl::ForeignData { name, .. } => {
                foreign_types.insert(name.value.symbol());
            }
            _ => {}
        }
    }
    for d in decls {
        if let cst::Decl::Derive {
            newtype: false,
            class_name,
            types,
            constraints,
            span,
            ..
        } = d
        {
            let class_qi = class_name.to_qi();
            // Determine which positions of the head data type are
            // "tracked" (and with what variance). We model:
            //   class           tracked positions (last-N)  required-variance
            //   Functor / Foldable / Traversable           1   covariant
            //   Contravariant                              1   contravariant
            //   Bifunctor / Bifoldable / Bitraversable     2   covariant, covariant
            //   Profunctor                                 2   contravariant, covariant
            let class_str: &str = &resolve(class_qi.name);
            let track: &[Variance] = match class_str {
                "Functor" | "Foldable" | "Traversable" | "Filterable" => {
                    &[Variance::Co]
                }
                "Contravariant" => &[Variance::Contra],
                "Bifunctor" | "Bifoldable" | "Bitraversable" => {
                    &[Variance::Co, Variance::Co]
                }
                "Profunctor" => &[Variance::Contra, Variance::Co],
                _ => continue,
            };
            // Foldable/Traversable variants additionally reject any
            // tracked-var occurrence under a forall or constraint —
            // the body would need an arbitrary `t :: Type` (or a
            // dictionary) at fold time, which derivation can't
            // produce. Functor/Profunctor/etc. work through forall
            // bodies as long as variance is right.
            let strict_forall = matches!(
                class_str,
                "Foldable" | "Traversable" | "Bifoldable" | "Bitraversable"
            );
            // Head type: last position is the data type's name + applied vars.
            let Some(head) = types.last() else { continue };
            let Some(head_sym) = data_decl_head_symbol(head) else { continue };
            let Some((data_vars, ctor_fields)) = data_info.get(&head_sym) else {
                continue;
            };
            // Tracked vars = the LAST N type-vars of the data
            // declaration, paired with the required-variance
            // class's signature.
            if data_vars.len() < track.len() {
                continue;
            }
            let tracked: Vec<(Symbol, Variance)> = data_vars
                .iter()
                .skip(data_vars.len() - track.len())
                .zip(track.iter())
                .map(|(s, v)| (*s, *v))
                .collect();
            // Map instance-bound type-var names back to their
            // corresponding data-decl type-var names by walking the
            // instance head's App spine. Without this, a derive
            // like `Functor k => Functor (TypedCache k)` for
            // `data TypedCache key a` would fail to translate the
            // constraint's `k` to the data decl's `key`, leaving
            // `key` looking unconstrained and the field `key a`
            // wrongly flagged.
            let mut inst_to_data: HashMap<Symbol, Symbol> = HashMap::new();
            {
                let mut args: Vec<Option<Symbol>> = Vec::new();
                let mut cur = head;
                loop {
                    match peel_parens(cur) {
                        cst::TypeExpr::App { constructor, arg, .. } => {
                            if let cst::TypeExpr::Var { name, .. } = peel_parens(arg)
                            {
                                args.push(Some(name.value.symbol()));
                            } else {
                                args.push(None);
                            }
                            cur = constructor;
                        }
                        _ => break,
                    }
                }
                args.reverse();
                for (i, inst_var) in args.iter().enumerate() {
                    if let (Some(iv), Some(dv)) = (inst_var, data_vars.get(i)) {
                        inst_to_data.insert(*iv, *dv);
                    }
                }
            }
            // Build per-typevar variance signatures from the
            // derive's CONSTRAINTS. `Contravariant f =>` records
            // f's last-arg as Contra; `Functor f =>` Co; etc. The
            // App walker uses this when the head is a Var.
            let mut var_variance: HashMap<Symbol, Vec<Variance>> = HashMap::new();
            for c in constraints {
                let cqi = c.class.to_qi();
                let cname = resolve(cqi.name);
                let sig: &[Variance] = match cname.as_str() {
                    "Functor" | "Foldable" | "Traversable" | "Filterable" => {
                        &[Variance::Co]
                    }
                    "Contravariant" => &[Variance::Contra],
                    "Bifunctor" | "Bifoldable" | "Bitraversable" => {
                        &[Variance::Co, Variance::Co]
                    }
                    "Profunctor" => &[Variance::Contra, Variance::Co],
                    _ => continue,
                };
                if c.args.len() == 1 {
                    if let cst::TypeExpr::Var { name, .. } = peel_parens(&c.args[0])
                    {
                        let inst_sym = name.value.symbol();
                        // Store under the data-decl-side name when
                        // we have a mapping (lookups in the field
                        // walker use data-var names).
                        let key = inst_to_data.get(&inst_sym).copied().unwrap_or(inst_sym);
                        var_variance.insert(key, sig.to_vec());
                    }
                }
            }
            // Data-vars whose corresponding instance head arg is a
            // bare type variable (i.e. "passed through" rather than
            // substituted to something concrete). The
            // unconstrained-var check should only fire for these:
            // when an instance substitutes the data var to a
            // concrete shape like `Const k`, the substituted
            // shape's variance applies and the data-var name in
            // the field text is irrelevant.
            //
            // When the instance head has fewer ARG SLOTS than the
            // data type has type vars (e.g. `derive instance
            // Foldable Foo` for `data Foo f = …`), the trailing
            // data vars are effectively forall-bound at the
            // instance level — treat them as passed-through too.
            let head_arg_count = {
                let mut count = 0usize;
                let mut cur = head;
                loop {
                    match peel_parens(cur) {
                        cst::TypeExpr::App { constructor, .. } => {
                            count += 1;
                            cur = constructor;
                        }
                        _ => break,
                    }
                }
                count
            };
            let mut passed_through: HashSet<Symbol> =
                inst_to_data.values().copied().collect();
            if head_arg_count < data_vars.len() {
                for dv in &data_vars[head_arg_count..] {
                    passed_through.insert(*dv);
                }
            }
            let mut bad = false;
            for fields in ctor_fields {
                for f in fields {
                    if !bad {
                        bad = check_variance_field(
                            f,
                            &tracked,
                            &var_variance,
                            &passed_through,
                            Variance::Co,
                            strict_forall,
                        );
                    }
                    if !bad {
                        // Foreign-typed App: tracked-var inside is
                        // unsafe (we don't know foreign type's
                        // variance behavior).
                        bad = field_passes_tracked_through_foreign(
                            f,
                            &tracked,
                            &foreign_types,
                        );
                    }
                }
            }
            if bad {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::CannotDeriveInvalidConstructorArg(
                        resolve(head_sym),
                    ),
                });
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Variance {
    Co,
    Contra,
}

impl Variance {
    fn flip(self) -> Variance {
        match self {
            Variance::Co => Variance::Contra,
            Variance::Contra => Variance::Co,
        }
    }
}

/// Recursively check field type for tracked-var occurrences in
/// wrong-variance positions. Returns `true` if any violation is
/// found.
///
/// `strict_forall`: when true (Foldable/Traversable etc.), any
/// tracked-var occurrence under a Forall or Constrained is
/// flagged — derivation can't produce arbitrary `forall`-bound
/// values or constraint dictionaries at fold-time.
fn check_variance_field(
    te: &cst::TypeExpr,
    tracked: &[(Symbol, Variance)],
    var_variance: &HashMap<Symbol, Vec<Variance>>,
    passed_through: &HashSet<Symbol>,
    cur: Variance,
    strict_forall: bool,
) -> bool {
    match te {
        cst::TypeExpr::Var { name, .. } => {
            let sym = name.value.symbol();
            for (t, required) in tracked {
                if *t == sym && *required != cur {
                    return true;
                }
            }
            false
        }
        cst::TypeExpr::Constructor { .. }
        | cst::TypeExpr::Hole { .. }
        | cst::TypeExpr::Wildcard { .. }
        | cst::TypeExpr::StringLiteral { .. }
        | cst::TypeExpr::IntLiteral { .. } => false,
        cst::TypeExpr::Function { from, to, .. } => {
            check_variance_field(
                from,
                tracked,
                var_variance,
                passed_through,
                cur.flip(),
                strict_forall,
            ) || check_variance_field(
                to,
                tracked,
                var_variance,
                passed_through,
                cur,
                strict_forall,
            )
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            // App whose head is an unconstrained type variable
            // (e.g. `f a a` in `data Test f a = Test (f a a)`):
            // we don't know `f`'s variance signature, so any
            // tracked-var occurrence in the spine is unsafe. The
            // reference compiler rejects these unless the derive
            // carries a `Functor f =>` (or similar) constraint
            // (captured in `var_variance`).
            //
            // Only fires for data-vars that are passed through to
            // the instance head as bare type variables. When the
            // instance substitutes the data-var to something
            // concrete (e.g. `derive instance Functor (Test (Const k))`
            // for `data Test key a = ...(key a)`), the derive is
            // well-defined and we don't flag.
            if app_head_is_unconstrained_var_passed_through(
                constructor,
                var_variance,
                passed_through,
            ) {
                if forall_contains_tracked(te, tracked) {
                    return true;
                }
                return false;
            }
            // Determine arg's variance via:
            //   - hardcoded contravariant Constructors (Predicate,
            //     Op, Comparison, Equivalence)
            //   - constraint-derived var_variance map (head Var
            //     with constraint `Contravariant f` etc.)
            let arg_var = match app_head_arg_position_variance(
                constructor,
                arg,
                var_variance,
            ) {
                Some(arg_pos_v) => match arg_pos_v {
                    Variance::Co => cur,
                    Variance::Contra => cur.flip(),
                },
                None => {
                    if is_contravariant_head(constructor) {
                        cur.flip()
                    } else {
                        cur
                    }
                }
            };
            check_variance_field(
                constructor,
                tracked,
                var_variance,
                passed_through,
                cur,
                strict_forall,
            ) || check_variance_field(
                arg,
                tracked,
                var_variance,
                passed_through,
                arg_var,
                strict_forall,
            )
        }
        cst::TypeExpr::Forall { vars, ty, .. } => {
            if strict_forall {
                forall_contains_tracked(te, tracked)
            } else {
                let inner: Vec<(Symbol, Variance)> = tracked
                    .iter()
                    .copied()
                    .filter(|(s, _)| {
                        !vars.iter().any(|(v, _, _)| v.value.symbol() == *s)
                    })
                    .collect();
                check_variance_field(
                    ty,
                    &inner,
                    var_variance,
                    passed_through,
                    cur,
                    strict_forall,
                )
            }
        }
        cst::TypeExpr::Constrained { ty, .. } => {
            if strict_forall {
                forall_contains_tracked(te, tracked)
            } else {
                check_variance_field(
                    ty,
                    tracked,
                    var_variance,
                    passed_through,
                    cur,
                    strict_forall,
                )
            }
        }
        cst::TypeExpr::Record { fields, .. } => fields.iter().any(|f| {
            check_variance_field(
                &f.ty,
                tracked,
                var_variance,
                passed_through,
                cur,
                strict_forall,
            )
        }),
        cst::TypeExpr::Row { fields, tail, .. } => {
            fields.iter().any(|f| {
                check_variance_field(
                    &f.ty,
                    tracked,
                    var_variance,
                    passed_through,
                    cur,
                    strict_forall,
                )
            }) || tail.as_ref().map_or(false, |t| {
                check_variance_field(
                    t,
                    tracked,
                    var_variance,
                    passed_through,
                    cur,
                    strict_forall,
                )
            })
        }
        cst::TypeExpr::Parens { ty, .. } => check_variance_field(
            ty,
            tracked,
            var_variance,
            passed_through,
            cur,
            strict_forall,
        ),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            check_variance_field(
                left,
                tracked,
                var_variance,
                passed_through,
                cur,
                strict_forall,
            ) || check_variance_field(
                right,
                tracked,
                var_variance,
                passed_through,
                cur,
                strict_forall,
            )
        }
        cst::TypeExpr::Kinded { ty, .. } => check_variance_field(
            ty,
            tracked,
            var_variance,
            passed_through,
            cur,
            strict_forall,
        ),
        _ => false,
    }
}

/// For an `App(constructor, arg)` node, look up the arg-position
/// variance of the constructor's head. Returns the variance of
/// the arg position relative to the constructor, or `None` to
/// fall back to default rules.
///
/// This walks the App spine of `constructor` to find the head Var
/// and the arg-index of THIS application. E.g. for `App(App(Var(f),
/// arg1), arg2)` and we're at the outer App, the arg-index is 1
/// (second arg). If `f` has constraint `Profunctor`, signature is
/// `[Contra, Co]`, so arg-index 1 is `Co`.
fn app_head_arg_position_variance(
    constructor: &cst::TypeExpr,
    _arg: &cst::TypeExpr,
    var_variance: &HashMap<Symbol, Vec<Variance>>,
) -> Option<Variance> {
    // Count how many App-spine slots are to the LEFT of `arg` —
    // that's our arg-index. Then walk to the head Var.
    let mut depth: usize = 0;
    let mut cur = constructor;
    loop {
        match peel_parens(cur) {
            cst::TypeExpr::App { constructor: c, .. } => {
                depth += 1;
                cur = c;
            }
            cst::TypeExpr::Var { name, .. } => {
                let sig = var_variance.get(&name.value.symbol())?;
                // arg-index in our App is `depth` (0 for innermost).
                return sig.get(depth).copied();
            }
            _ => return None,
        }
    }
}

/// True iff `te` contains a tracked type variable as an arg to a
/// foreign-imported type constructor (e.g. `Variant (left :: a)`
/// where `Variant` is `foreign import data`). The reference
/// compiler can't derive variance through foreign types, so any
/// such occurrence is unsafe.
fn field_passes_tracked_through_foreign(
    te: &cst::TypeExpr,
    tracked: &[(Symbol, Variance)],
    foreign_types: &HashSet<Symbol>,
) -> bool {
    let names: HashSet<Symbol> = tracked.iter().map(|(s, _)| *s).collect();
    let mut found = false;
    walk_field_for_foreign(te, &names, foreign_types, false, &mut found);
    found
}

fn walk_field_for_foreign(
    te: &cst::TypeExpr,
    tracked_names: &HashSet<Symbol>,
    foreign_types: &HashSet<Symbol>,
    under_foreign: bool,
    found: &mut bool,
) {
    if *found {
        return;
    }
    match te {
        cst::TypeExpr::Var { name, .. } => {
            if under_foreign && tracked_names.contains(&name.value.symbol()) {
                *found = true;
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            // Walk the constructor first (to detect a foreign head).
            walk_field_for_foreign(
                constructor,
                tracked_names,
                foreign_types,
                under_foreign,
                found,
            );
            // The arg position picks up `under_foreign` if the
            // App's head spine bottoms at a foreign Constructor.
            let arg_under = under_foreign
                || app_head_is_foreign(constructor, foreign_types);
            walk_field_for_foreign(
                arg,
                tracked_names,
                foreign_types,
                arg_under,
                found,
            );
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_field_for_foreign(
                from,
                tracked_names,
                foreign_types,
                under_foreign,
                found,
            );
            walk_field_for_foreign(
                to,
                tracked_names,
                foreign_types,
                under_foreign,
                found,
            );
        }
        cst::TypeExpr::Parens { ty, .. }
        | cst::TypeExpr::Kinded { ty, .. } => {
            walk_field_for_foreign(
                ty,
                tracked_names,
                foreign_types,
                under_foreign,
                found,
            );
        }
        cst::TypeExpr::Forall { ty, .. }
        | cst::TypeExpr::Constrained { ty, .. } => {
            walk_field_for_foreign(
                ty,
                tracked_names,
                foreign_types,
                under_foreign,
                found,
            );
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_field_for_foreign(
                    &f.ty,
                    tracked_names,
                    foreign_types,
                    under_foreign,
                    found,
                );
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_field_for_foreign(
                    &f.ty,
                    tracked_names,
                    foreign_types,
                    under_foreign,
                    found,
                );
            }
            if let Some(t) = tail {
                walk_field_for_foreign(
                    t,
                    tracked_names,
                    foreign_types,
                    under_foreign,
                    found,
                );
            }
        }
        _ => {}
    }
}

fn app_head_is_foreign(
    te: &cst::TypeExpr,
    foreign_types: &HashSet<Symbol>,
) -> bool {
    let mut cur = te;
    loop {
        match peel_parens(cur) {
            cst::TypeExpr::App { constructor, .. } => cur = constructor,
            cst::TypeExpr::Constructor { name, .. } => {
                let qi = name.to_qi();
                return qi.module.is_none()
                    && foreign_types.contains(&qi.name);
            }
            _ => return false,
        }
    }
}

/// True iff the App spine of `te` bottoms out at a `Var` that is
///   1. not in `var_variance` (no `Functor f =>`-style constraint
///      tells us its variance), AND
///   2. is in `passed_through` (the data-var is passed through
///      to the instance head as a bare type variable, not
///      substituted to something concrete).
///
/// Both conditions are needed: passing through without a constraint
/// is unsafe, but a substituted data-var (like `key` substituted to
/// `Const k` at the instance head) doesn't appear at runtime under
/// that name and doesn't need to be flagged.
fn app_head_is_unconstrained_var_passed_through(
    te: &cst::TypeExpr,
    var_variance: &HashMap<Symbol, Vec<Variance>>,
    passed_through: &HashSet<Symbol>,
) -> bool {
    let mut cur = te;
    loop {
        match peel_parens(cur) {
            cst::TypeExpr::App { constructor: c, .. } => cur = c,
            cst::TypeExpr::Var { name, .. } => {
                let sym = name.value.symbol();
                return !var_variance.contains_key(&sym)
                    && passed_through.contains(&sym);
            }
            _ => return false,
        }
    }
}

/// True iff `te` (a constructor, possibly under Parens / App
/// chain) is one of the well-known contravariant type
/// constructors (Predicate, Op, Comparison, Equivalence).
fn is_contravariant_head(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Constructor { name, .. } => {
            let s = resolve(name.name.symbol());
            matches!(s.as_str(), "Predicate" | "Op" | "Comparison" | "Equivalence")
        }
        cst::TypeExpr::Parens { ty, .. } => is_contravariant_head(ty),
        cst::TypeExpr::App { constructor, .. } => is_contravariant_head(constructor),
        _ => false,
    }
}

/// True iff `te` contains any tracked type-variable as a free
/// reference (used as a fallback for Forall/Constrained where
/// variance analysis is infeasible).
fn forall_contains_tracked(
    te: &cst::TypeExpr,
    tracked: &[(Symbol, Variance)],
) -> bool {
    let names: HashSet<Symbol> = tracked.iter().map(|(s, _)| *s).collect();
    let mut found = false;
    walk_type_find_var(te, &names, &mut found);
    found
}

fn walk_type_find_var(
    te: &cst::TypeExpr,
    names: &HashSet<Symbol>,
    found: &mut bool,
) {
    if *found {
        return;
    }
    match te {
        cst::TypeExpr::Var { name, .. } => {
            if names.contains(&name.value.symbol()) {
                *found = true;
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            walk_type_find_var(constructor, names, found);
            walk_type_find_var(arg, names, found);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_type_find_var(from, names, found);
            walk_type_find_var(to, names, found);
        }
        cst::TypeExpr::Forall { vars, ty, .. } => {
            // Inner forall may SHADOW outer tracked names.
            // Remove the shadowed ones from the tracked set
            // before recursing.
            let mut inner_names = names.clone();
            for (v, _, _) in vars {
                inner_names.remove(&v.value.symbol());
            }
            walk_type_find_var(ty, &inner_names, found);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for arg in &c.args {
                    walk_type_find_var(arg, names, found);
                }
            }
            walk_type_find_var(ty, names, found);
        }
        cst::TypeExpr::Parens { ty, .. } => walk_type_find_var(ty, names, found),
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_type_find_var(&f.ty, names, found);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_type_find_var(&f.ty, names, found);
            }
            if let Some(t) = tail {
                walk_type_find_var(t, names, found);
            }
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_type_find_var(left, names, found);
            walk_type_find_var(right, names, found);
        }
        cst::TypeExpr::Kinded { ty, .. } => walk_type_find_var(ty, names, found),
        _ => {}
    }
}

/// Extract the head data-type symbol from a derive-instance type
/// argument: `Functor (Test f g)` → `Test`. Walks Parens and
/// peels App's constructor side until reaching a Constructor.
fn data_decl_head_symbol(te: &cst::TypeExpr) -> Option<Symbol> {
    match peel_parens(te) {
        cst::TypeExpr::Constructor { name, .. } if name.module.is_none() => {
            Some(name.name.symbol())
        }
        cst::TypeExpr::App { constructor, .. } => {
            data_decl_head_symbol(constructor)
        }
        _ => None,
    }
}

fn has_wildcard(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Wildcard { .. } => true,
        cst::TypeExpr::Parens { ty, .. } => has_wildcard(ty),
        cst::TypeExpr::App { constructor, arg, .. } => {
            has_wildcard(constructor) || has_wildcard(arg)
        }
        cst::TypeExpr::Function { from, to, .. } => {
            has_wildcard(from) || has_wildcard(to)
        }
        _ => false,
    }
}

/// Transitive export error subset detectable from the CST alone.
fn detect_transitive_export_errors(
    module: &cst::Module,
    errors: &mut Vec<ValidationError>,
) {
    let export_list = match &module.exports {
        Some(e) => &e.value.exports,
        None => return,
    };

    // Collect per-data-type constructor sets.
    let mut data_ctors: HashMap<Symbol, (Span, Vec<Symbol>)> = HashMap::new();
    for d in &module.decls {
        if let cst::Decl::Data {
            span,
            name,
            constructors,
            is_role_decl: false,
            kind_sig: cst::KindSigSource::None,
            ..
        } = d
        {
            let ctors: Vec<Symbol> = constructors
                .iter()
                .map(|c| c.name.value.symbol())
                .collect();
            data_ctors.insert(name.value.symbol(), (*span, ctors));
        }
    }

    // Local value names (for checking whether a fixity target is
    // actually defined in this module).
    let mut local_values: HashSet<Symbol> = HashSet::new();
    for d in &module.decls {
        match d {
            cst::Decl::Value { name, .. } => {
                local_values.insert(name.value.symbol());
            }
            cst::Decl::Foreign { name, .. } => {
                local_values.insert(name.value.symbol());
            }
            _ => {}
        }
    }
    let mut local_ctors: HashSet<Symbol> = HashSet::new();
    for (_, ctors) in data_ctors.values() {
        for c in ctors {
            local_ctors.insert(*c);
        }
    }
    for d in &module.decls {
        if let cst::Decl::Newtype { constructor, .. } = d {
            local_ctors.insert(constructor.value.symbol());
        }
    }
    // Class → its method names. Used by the class/value export
    // coupling check below.
    let mut class_methods: HashMap<Symbol, (Span, Vec<(Span, Symbol)>)> =
        HashMap::new();
    let mut value_to_class: HashMap<Symbol, Symbol> = HashMap::new();
    // Class → its superclass class-names. Cross-module superclasses
    // (`class.module.is_some()`) aren't recorded — only locally
    // defined classes matter for the export-coupling rule.
    let mut class_superclasses: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    let mut local_classes: HashSet<Symbol> = HashSet::new();
    for d in &module.decls {
        if let cst::Decl::Class { span, name, members, constraints, .. } = d {
            let cname = name.value.symbol();
            local_classes.insert(cname);
            let mems: Vec<(Span, Symbol)> = members
                .iter()
                .map(|m| (m.span, m.name.value.symbol()))
                .collect();
            for (_, msym) in &mems {
                value_to_class.insert(*msym, cname);
            }
            class_methods.insert(cname, (*span, mems));
            let supers: Vec<Symbol> = constraints
                .iter()
                .filter_map(|c| {
                    if c.class.module.is_none() {
                        Some(c.class.name.symbol())
                    } else {
                        None
                    }
                })
                .collect();
            class_superclasses.insert(cname, supers);
        }
    }

    // Collect value fixities so we can map exported operator aliases
    // back to their target. Only track fixities whose target is
    // locally defined — if the target is imported, the reference
    // compiler treats the alias as its own export and doesn't require
    // separate re-export of the underlying name.
    let mut value_op_target: HashMap<Symbol, (Span, Symbol)> = HashMap::new();
    for d in &module.decls {
        if let cst::Decl::Fixity { span, operator, is_type: false, target, .. } = d {
            if target.module.is_none()
                && (local_values.contains(&target.name)
                    || local_ctors.contains(&target.name))
            {
                value_op_target
                    .insert(operator.value.symbol(), (*span, target.name));
            }
        }
    }
    // Same for type-level fixity: `infixl 6 type Tuple as ×` makes
    // `(×)` an alias for the local `Tuple` data type. Exporting
    // `(×)` without exporting `Tuple` is a TransitiveExportError.
    // Skip when the target isn't locally defined — `infixr 6 type
    // Either as \/` in `Data.Either.Nested` aliases an imported
    // `Either`, which is a legitimate re-export.
    let mut local_types: HashSet<Symbol> = HashSet::new();
    let mut local_type_aliases: HashSet<Symbol> = HashSet::new();
    for d in &module.decls {
        match d {
            cst::Decl::Data { name, .. }
            | cst::Decl::Newtype { name, .. }
            | cst::Decl::ForeignData { name, .. } => {
                local_types.insert(name.value.symbol());
            }
            cst::Decl::TypeAlias { name, .. } => {
                local_types.insert(name.value.symbol());
                local_type_aliases.insert(name.value.symbol());
            }
            _ => {}
        }
    }
    let mut type_op_target: HashMap<Symbol, (Span, Symbol)> = HashMap::new();
    for d in &module.decls {
        if let cst::Decl::Fixity { span, operator, is_type: true, target, .. } = d {
            if target.module.is_none() && local_types.contains(&target.name) {
                type_op_target
                    .insert(operator.value.symbol(), (*span, target.name));
            }
        }
    }

    // Build "is this name reachable from the export list?" lookups.
    // Values, constructors (via `T(..)` or `T(C1, C2)`), and types are
    // tracked separately. A fixity target may be a value OR a
    // constructor — `infix 4 Bar' as :->` targets the `Bar'` ctor.
    let mut exported_values: HashSet<Symbol> = HashSet::new();
    let mut exported_ctors: HashSet<Symbol> = HashSet::new();
    let mut exported_types: HashSet<Symbol> = HashSet::new();
    let mut exported_classes: HashSet<Symbol> = HashSet::new();
    let mut re_exports_wild = false;
    for e in export_list {
        match e {
            cst::Export::Value(n) => {
                exported_values.insert(n.symbol());
            }
            cst::Export::Type(t, members) => {
                let tsym = t.symbol();
                exported_types.insert(tsym);
                match members {
                    Some(cst::DataMembers::All) => {
                        if let Some((_, ctors)) = data_ctors.get(&tsym) {
                            exported_ctors.extend(ctors.iter().copied());
                        }
                    }
                    Some(cst::DataMembers::Explicit(cs)) => {
                        for c in cs {
                            exported_ctors.insert(c.value.symbol());
                        }
                    }
                    None => {}
                }
            }
            cst::Export::Class(c) => {
                exported_classes.insert(c.symbol());
            }
            cst::Export::Module(_) => {
                // `module X` re-exports everything from X. We don't
                // track what X actually re-exports without the
                // registry, so conservatively turn off operator-alias
                // checking for this module.
                re_exports_wild = true;
            }
            _ => {}
        }
    }

    for e in export_list {
        match e {
            cst::Export::Type(type_name, Some(cst::DataMembers::Explicit(ctors))) => {
                // Empty ctor list `Type()` = opaque export (no ctors).
                // That is valid — treat it the same as `Type` alone.
                if ctors.is_empty() {
                    // nothing to check
                } else {
                    // Partial-ctor export: if the local data type has more
                    // ctors than this explicit list, the reference compiler
                    // rejects with TransitiveDctorExportError.
                    let tsym = type_name.symbol();
                    if let Some((span, all_ctors)) = data_ctors.get(&tsym) {
                        let named: HashSet<Symbol> =
                            ctors.iter().map(|c| c.value.symbol()).collect();
                        let all: HashSet<Symbol> = all_ctors.iter().copied().collect();
                        if named != all {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::TransitiveDctorExportError(
                                    resolve(tsym),
                                ),
                            });
                        }
                    }
                }
            }
            cst::Export::Value(opn) => {
                // Operator alias in export list → its fixity target
                // must also be exported (as a value or as a ctor).
                // Skip if this module uses `module X` re-export: we
                // can't see through that without the registry.
                if re_exports_wild {
                    continue;
                }
                let op = opn.symbol();
                if let Some((span, target)) = value_op_target.get(&op) {
                    if !exported_values.contains(target)
                        && !exported_ctors.contains(target)
                    {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::TransitiveExportError(
                                resolve(op),
                            ),
                        });
                    }
                }
            }
            cst::Export::TypeOp(opn) => {
                // Type-operator alias in export list → its fixity
                // target type must also be exported.
                if re_exports_wild {
                    continue;
                }
                let op = opn.symbol();
                if let Some((span, target)) = type_op_target.get(&op) {
                    if !exported_types.contains(target) {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::TransitiveExportError(
                                resolve(op),
                            ),
                        });
                    }
                }
            }
            _ => {}
        }
    }

    // Class/method export coupling. Reference compiler:
    // - Exporting a class method without exporting its class →
    //   TransitiveExportError on the value name.
    // - Exporting a class without also exporting all its methods →
    //   TransitiveExportError on the class.
    if !re_exports_wild {
        for v in &exported_values {
            if let Some(parent_class) = value_to_class.get(v) {
                if !exported_classes.contains(parent_class) {
                    let span = class_methods
                        .get(parent_class)
                        .and_then(|(_, mems)| mems.iter().find(|(_, m)| m == v))
                        .map(|(s, _)| *s)
                        .unwrap_or(crate::span::Span::new(0, 0));
                    errors.push(ValidationError {
                        span,
                        kind: ValidationErrorKind::TransitiveExportError(resolve(*v)),
                    });
                }
            }
        }
        for c in &exported_classes {
            if let Some((cspan, mems)) = class_methods.get(c) {
                for (_, msym) in mems {
                    if !exported_values.contains(msym) {
                        errors.push(ValidationError {
                            span: *cspan,
                            kind: ValidationErrorKind::TransitiveExportError(
                                resolve(*c),
                            ),
                        });
                        break;
                    }
                }
            }
        }
        // Build a name → decl-span lookup for value/type/alias lookups
        // we need below.
        let mut value_decl_span: HashMap<Symbol, Span> = HashMap::new();
        let mut value_decl_ty: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
        let mut data_decl_span: HashMap<Symbol, Span> = HashMap::new();
        let mut data_decl_fields: HashMap<Symbol, Vec<&cst::TypeExpr>> = HashMap::new();
        let mut data_decl_kind_anns: HashMap<Symbol, Vec<&cst::TypeExpr>> = HashMap::new();
        let mut alias_decl_span: HashMap<Symbol, Span> = HashMap::new();
        let mut alias_decl_body: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
        let mut newtype_decl_span: HashMap<Symbol, Span> = HashMap::new();
        let mut newtype_decl_field: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
        let mut newtype_decl_kind_anns: HashMap<Symbol, Vec<&cst::TypeExpr>> = HashMap::new();
        // Maps newtype type-name → constructor name, for gating the field-type check.
        let mut newtype_ctor_sym: HashMap<Symbol, Symbol> = HashMap::new();
        for d in &module.decls {
            match d {
                cst::Decl::TypeSignature { name, ty, span, .. } => {
                    value_decl_span.insert(name.value.symbol(), *span);
                    value_decl_ty.insert(name.value.symbol(), ty);
                }
                cst::Decl::Data {
                    name,
                    constructors,
                    span,
                    type_var_kind_anns,
                    ..
                } => {
                    let n = name.value.symbol();
                    data_decl_span.insert(n, *span);
                    let fs: Vec<&cst::TypeExpr> = constructors
                        .iter()
                        .flat_map(|c| c.fields.iter())
                        .collect();
                    data_decl_fields.insert(n, fs);
                    let anns: Vec<&cst::TypeExpr> = type_var_kind_anns
                        .iter()
                        .filter_map(|a| a.as_deref())
                        .collect();
                    data_decl_kind_anns.insert(n, anns);
                }
                cst::Decl::TypeAlias { name, ty, span, .. } => {
                    alias_decl_span.insert(name.value.symbol(), *span);
                    alias_decl_body.insert(name.value.symbol(), ty);
                }
                cst::Decl::Newtype {
                    name,
                    ty,
                    span,
                    type_var_kind_anns,
                    constructor,
                    ..
                } => {
                    let n = name.value.symbol();
                    newtype_decl_span.insert(n, *span);
                    newtype_decl_field.insert(n, ty);
                    newtype_ctor_sym.insert(n, constructor.value.symbol());
                    let anns: Vec<&cst::TypeExpr> = type_var_kind_anns
                        .iter()
                        .filter_map(|a| a.as_deref())
                        .collect();
                    newtype_decl_kind_anns.insert(n, anns);
                }
                _ => {}
            }
        }

        // Helper: walk a TypeExpr and emit a TransitiveExportError on
        // `owner_sym` if the body references a local-but-unexported type.
        // `skip_aliases`: type aliases are transparent in value sigs (the
        // inferred/exported type has them expanded), so skip them for values.
        // For exported type alias bodies and data ctor fields, aliases are
        // NOT transparent (the surface form is part of the module interface).
        let mut check_ty_refs_inner = |
            owner_sym: Symbol,
            owner_span: Span,
            ty: &cst::TypeExpr,
            skip_aliases: bool,
            errors: &mut Vec<ValidationError>,
            reported: &mut HashSet<Symbol>,
        | {
            collect_type_refs(ty, &mut |name: Symbol, _is_class| {
                if !local_types.contains(&name) {
                    return;
                }
                if skip_aliases && local_type_aliases.contains(&name) {
                    return;
                }
                if exported_types.contains(&name) {
                    return;
                }
                if reported.insert(owner_sym) {
                    errors.push(ValidationError {
                        span: owner_span,
                        kind: ValidationErrorKind::TransitiveExportError(
                            resolve(owner_sym),
                        ),
                    });
                }
            });
        };

        let mut reported_decl: HashSet<Symbol> = HashSet::new();

        // NOTE: We do NOT check exported value type signatures here.
        // In PureScript, TransitiveExportError fires for EXPORTED TYPE
        // DECLARATIONS (alias bodies, data ctor fields) — not for value
        // type annotations. A value can be exported even if its type
        // references unexported types (opaque types are intentional).

        // Exported alias with body referring to a non-exported local type.
        // Alias bodies are part of the module interface — aliases not transparent here.
        for t in &exported_types {
            if let Some(body) = alias_decl_body.get(t) {
                let span = alias_decl_span.get(t).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                check_ty_refs_inner(*t, span, body, false, errors, &mut reported_decl);
            }
        }

        // Exported data type whose ctor fields or kind annotations
        // reference a non-exported local type — only relevant when
        // ctors are exported (otherwise the field types aren't
        // observable to the importer).
        for c in &exported_ctors {
            // Find the parent data type for this ctor.
            let parent_opt = data_ctors
                .iter()
                .find(|(_, (_, cs))| cs.contains(c))
                .map(|(t, _)| *t);
            if let Some(parent) = parent_opt {
                if let Some(fields) = data_decl_fields.get(&parent) {
                    let span = data_decl_span.get(&parent).copied()
                        .unwrap_or(crate::span::Span::new(0, 0));
                    for f in fields {
                        check_ty_refs_inner(parent, span, f, false, errors, &mut reported_decl);
                    }
                }
            }
        }
        for t in &exported_types {
            if let Some(anns) = data_decl_kind_anns.get(t) {
                let span = data_decl_span.get(t).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                for ann in anns {
                    check_ty_refs_inner(*t, span, ann, false, errors, &mut reported_decl);
                }
            }
            if let Some(anns) = newtype_decl_kind_anns.get(t) {
                let span = newtype_decl_span.get(t).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                for ann in anns {
                    check_ty_refs_inner(*t, span, ann, false, errors, &mut reported_decl);
                }
            }
            if let Some(body) = newtype_decl_field.get(t) {
                // Only check the internal field type if the newtype's
                // constructor is also exported. Without the constructor,
                // the representation is opaque to importers.
                let ctor_exported = newtype_ctor_sym
                    .get(t)
                    .map_or(false, |c| exported_ctors.contains(c));
                if ctor_exported {
                    let span = newtype_decl_span.get(t).copied()
                        .unwrap_or(crate::span::Span::new(0, 0));
                    check_ty_refs_inner(*t, span, body, false, errors, &mut reported_decl);
                }
            }
        }

        // Transitive superclass export: an exported class's locally
        // defined superclasses (and their superclasses) must also be
        // exported. `class C1 <= C2 a; class C2 a <= C3 a b` →
        // exporting `class C3` requires `class C2` and `class C1`.
        for c in exported_classes.clone() {
            let mut stack: Vec<Symbol> = class_superclasses
                .get(&c)
                .cloned()
                .unwrap_or_default();
            let mut visited: HashSet<Symbol> = HashSet::new();
            while let Some(sup) = stack.pop() {
                if !visited.insert(sup) {
                    continue;
                }
                if !local_classes.contains(&sup) {
                    continue;
                }
                if !exported_classes.contains(&sup) {
                    let span = class_methods
                        .get(&c)
                        .map(|(s, _)| *s)
                        .unwrap_or(crate::span::Span::new(0, 0));
                    errors.push(ValidationError {
                        span,
                        kind: ValidationErrorKind::TransitiveExportError(
                            resolve(c),
                        ),
                    });
                    break;
                }
                if let Some(more) = class_superclasses.get(&sup) {
                    stack.extend(more.iter().copied());
                }
            }
        }
    }
}

/// Parser-level rejections the reference compiler makes at parse time
/// but our grammar doesn't. Caught structurally post-parse so we can
/// still report ErrorParsingModule-class issues without grammar churn.
fn detect_parse_level_rejections(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::TypeAlias { ty, span, .. } => {
                if contains_wildcard(ty) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::WildcardInTypeDefinition,
                    });
                }
            }
            cst::Decl::Data { constructors, span, .. } => {
                for c in constructors {
                    for f in &c.fields {
                        if contains_wildcard(f) {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::WildcardInTypeDefinition,
                            });
                            break;
                        }
                    }
                }
            }
            cst::Decl::Newtype { ty, span, .. } => {
                if contains_wildcard(ty) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::WildcardInTypeDefinition,
                    });
                }
            }
            cst::Decl::Foreign { ty, span, .. } => {
                if contains_constraint_arrow(ty) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::ConstraintInForeignImport,
                    });
                }
            }
            // InvalidConstraintArgument: a `Constraint` whose arg contains
            // a forall-quantifier or a wildcard. Walk every type site
            // that may carry constraints: instance/derive heads, class
            // superclasses, value signatures.
            cst::Decl::Instance { constraints, .. }
            | cst::Decl::Derive { constraints, .. } => {
                check_constraint_args(constraints, errors);
            }
            cst::Decl::Class { constraints, .. } => {
                check_constraint_args(constraints, errors);
                // Class-method bodies (the `members` field) are value
                // type signatures semantically, and PureScript allows
                // wildcards in value-sig constraint args as inference
                // hints (`test :: MonadAsk _ m => …`), so we don't
                // descend into them.
            }
            _ => {}
        }
    }
}

fn contains_wildcard(te: &cst::TypeExpr) -> bool {
    let mut found = false;
    walk_type_find(te, &mut |t| {
        if matches!(t, cst::TypeExpr::Wildcard { .. }) {
            found = true;
        }
    });
    found
}

fn contains_constraint_arrow(te: &cst::TypeExpr) -> bool {
    let mut found = false;
    walk_type_find(te, &mut |t| {
        if matches!(t, cst::TypeExpr::Constrained { .. }) {
            found = true;
        }
    });
    found
}

fn check_constraint_args(
    constraints: &[cst::Constraint],
    errors: &mut Vec<ValidationError>,
) {
    for c in constraints {
        for a in &c.args {
            if constraint_arg_invalid(a) {
                errors.push(ValidationError {
                    span: c.span,
                    kind: ValidationErrorKind::InvalidConstraintArgument,
                });
                break;
            }
        }
    }
}

fn check_constrained_type(te: &cst::TypeExpr, errors: &mut Vec<ValidationError>) {
    if let cst::TypeExpr::Constrained { constraints, ty, .. } = te {
        check_constraint_args(constraints, errors);
        check_constrained_type(ty, errors);
    } else if let cst::TypeExpr::Forall { ty, .. } = te {
        check_constrained_type(ty, errors);
    } else if let cst::TypeExpr::Parens { ty, .. } = te {
        check_constrained_type(ty, errors);
    }
}

/// A constraint arg is invalid if it contains a forall (rank-n type)
/// or a wildcard. `Show a` is fine; `Show (forall t. t)` is not;
/// `(Baz _) => …` is not.
fn constraint_arg_invalid(te: &cst::TypeExpr) -> bool {
    let mut bad = false;
    walk_type_find(te, &mut |t| match t {
        cst::TypeExpr::Forall { .. } | cst::TypeExpr::Wildcard { .. } => {
            bad = true;
        }
        _ => {}
    });
    bad
}

/// Pre-order walker that applies `f` to every sub-TypeExpr.
fn walk_type_find<F>(te: &cst::TypeExpr, f: &mut F)
where
    F: FnMut(&cst::TypeExpr),
{
    f(te);
    match te {
        cst::TypeExpr::App { constructor, arg, .. } => {
            walk_type_find(constructor, f);
            walk_type_find(arg, f);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_type_find(from, f);
            walk_type_find(to, f);
        }
        cst::TypeExpr::Forall { ty, vars, .. } => {
            for (_, _, k) in vars {
                if let Some(k) = k {
                    walk_type_find(k, f);
                }
            }
            walk_type_find(ty, f);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for a in &c.args {
                    walk_type_find(a, f);
                }
            }
            walk_type_find(ty, f);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for fd in fields {
                walk_type_find(&fd.ty, f);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for fd in fields {
                walk_type_find(&fd.ty, f);
            }
            if let Some(t) = tail {
                walk_type_find(t, f);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => walk_type_find(ty, f),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_type_find(left, f);
            walk_type_find(right, f);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_type_find(ty, f);
            walk_type_find(kind, f);
        }
        cst::TypeExpr::ArrayPattern { elements, .. } => {
            for e in elements {
                walk_type_find(e, f);
            }
        }
        cst::TypeExpr::AsPattern { ty, .. } => walk_type_find(ty, f),
        _ => {}
    }
}

/// Local-class instance-arity mismatch. For imported classes the class
/// arity isn't accessible here; those cases are left for later passes
/// that hold the registry.
fn detect_class_instance_arity(
    decls: &[cst::Decl],
    imported_class_arity: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    let mut class_arity: HashMap<Symbol, usize> = imported_class_arity.clone();
    for d in decls {
        if let cst::Decl::Class { name, type_vars, is_kind_sig: false, .. } = d {
            // Local classes win — imported alias takes a back seat
            // when a local class with the same name is declared.
            class_arity.insert(name.value.symbol(), type_vars.len());
        }
    }
    if class_arity.is_empty() {
        return;
    }
    for d in decls {
        let (span, class_name, types) = match d {
            cst::Decl::Instance { span, class_name, types, .. } => (*span, class_name, types),
            cst::Decl::Derive { span, class_name, types, .. } => (*span, class_name, types),
            _ => continue,
        };
        if class_name.module.is_some() {
            continue;
        }
        let sym = class_name.name.symbol();
        if let Some(&expected) = class_arity.get(&sym) {
            if types.len() != expected {
                errors.push(ValidationError {
                    span,
                    kind: ValidationErrorKind::ClassInstanceArityMismatch {
                        class: resolve(sym),
                        expected,
                        got: types.len(),
                    },
                });
            }
        }
    }
}

/// Roles on a data/newtype/foreign-data must match its arity exactly.
/// `data A = A` + `type role A nominal` = one role for a zero-arity
/// data → mismatch. For foreign data, arity is the arrow-count in its
/// declared kind (kind `Type` → arity 0, `Type -> Type` → 1, etc.).
fn detect_role_arity_mismatches(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // First pass: record arity of every type-level name.
    let mut arity: HashMap<Symbol, usize> = HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Data { name, type_vars, is_role_decl: false, kind_sig: cst::KindSigSource::None, .. } => {
                arity.insert(name.value.symbol(), type_vars.len());
            }
            cst::Decl::Newtype { name, type_vars, .. } => {
                arity.insert(name.value.symbol(), type_vars.len());
            }
            cst::Decl::ForeignData { name, kind, .. } => {
                arity.insert(name.value.symbol(), count_kind_arrows(kind));
            }
            _ => {}
        }
    }

    // Second pass: compare each role decl against the matching arity.
    for d in decls {
        if let cst::Decl::Data {
            span,
            name,
            type_vars,
            is_role_decl: true,
            ..
        } = d
        {
            let n = name.value.symbol();
            if let Some(&expected) = arity.get(&n) {
                if type_vars.len() != expected {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::RoleDeclarationArityMismatch(
                            resolve(n),
                        ),
                    });
                }
            }
        }
    }
}

/// Count the number of `a -> b -> c -> …` arrows in a kind expression.
/// `Type` → 0, `Type -> Type` → 1, `Type -> (Type -> Type)` → 2.
fn count_kind_arrows(te: &cst::TypeExpr) -> usize {
    match te {
        cst::TypeExpr::Function { to, .. } => 1 + count_kind_arrows(to),
        cst::TypeExpr::Parens { ty, .. } => count_kind_arrows(ty),
        cst::TypeExpr::Forall { ty, .. } => count_kind_arrows(ty),
        _ => 0,
    }
}

/// Cross-namespace name collisions at the type level: `class Foo` +
/// `data Foo`, `type Foo` + `data Foo`, etc. Data constructors also
/// share a namespace, so `data T = A | A` and `data T1 = X; data T2 = X`
/// both count.
fn detect_decl_conflicts(decls: &[cst::Decl], errors: &mut Vec<ValidationError>) {
    // Track where each type-level name first appeared. Second and later
    // collisions emit DeclConflict.
    let mut type_level_names: HashMap<Symbol, &'static str> = HashMap::new();
    let mut ctor_names: HashMap<Symbol, Span> = HashMap::new();

    for d in decls {
        match d {
            cst::Decl::Data { span, name, is_role_decl: false, kind_sig: cst::KindSigSource::None, constructors, .. } => {
                emit_conflict(&mut type_level_names, name.value.symbol(), "data", *span, errors);
                for c in constructors {
                    let csym = c.name.value.symbol();
                    if ctor_names.contains_key(&csym) {
                        errors.push(ValidationError {
                            span: c.name.span,
                            kind: ValidationErrorKind::DeclConflict(resolve(csym)),
                        });
                    } else {
                        ctor_names.insert(csym, c.name.span);
                    }
                    // Cross-namespace: a class declared (here or
                    // earlier) under the same name as a data ctor
                    // collides — `data T = Fail; class Fail` and
                    // its reverse.
                    if type_level_names.get(&csym) == Some(&"class") {
                        errors.push(ValidationError {
                            span: c.name.span,
                            kind: ValidationErrorKind::DeclConflict(resolve(csym)),
                        });
                    }
                }
            }
            cst::Decl::Newtype { span, name, constructor, .. } => {
                emit_conflict(&mut type_level_names, name.value.symbol(), "newtype", *span, errors);
                let csym = constructor.value.symbol();
                if ctor_names.contains_key(&csym) {
                    errors.push(ValidationError {
                        span: constructor.span,
                        kind: ValidationErrorKind::DeclConflict(resolve(csym)),
                    });
                } else {
                    ctor_names.insert(csym, constructor.span);
                }
                if type_level_names.get(&csym) == Some(&"class") {
                    errors.push(ValidationError {
                        span: constructor.span,
                        kind: ValidationErrorKind::DeclConflict(resolve(csym)),
                    });
                }
            }
            cst::Decl::TypeAlias { span, name, .. } => {
                emit_conflict(&mut type_level_names, name.value.symbol(), "type", *span, errors);
            }
            cst::Decl::Class { span, name, is_kind_sig: false, .. } => {
                let sym = name.value.symbol();
                emit_conflict(&mut type_level_names, sym, "class", *span, errors);
                // Cross-namespace: a class whose name was already
                // claimed by a previously-declared data ctor.
                if ctor_names.contains_key(&sym) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::DeclConflict(resolve(sym)),
                    });
                }
            }
            cst::Decl::ForeignData { span, name, .. } => {
                emit_conflict(&mut type_level_names, name.value.symbol(), "foreign data", *span, errors);
            }
            _ => {}
        }
    }
}

fn emit_conflict(
    seen: &mut HashMap<Symbol, &'static str>,
    sym: Symbol,
    kind: &'static str,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    if let Some(prev_kind) = seen.get(&sym) {
        // Don't emit when both are the same kind — DuplicateTypeClass /
        // DuplicateTypeDeclaration already cover the homogeneous case.
        if *prev_kind != kind {
            errors.push(ValidationError {
                span,
                kind: ValidationErrorKind::DeclConflict(resolve(sym)),
            });
        }
    } else {
        seen.insert(sym, kind);
    }
}

/// Orphan-instance detection.
///
/// An instance is orphan when it's declared in a module where none of
/// the following are true:
///   - The class is defined locally.
///   - At least one type constructor in the instance head is defined
///     locally (as `data`/`newtype`/`foreign import data`, NOT `type`).
///
/// Type aliases don't count — `type Something = Int` followed by
/// `derive instance Eq Something` is still an orphan because `Something`
/// is just an alias; PureScript's orphan check sees through it.
fn detect_orphan_instances(
    decls: &[cst::Decl],
    imported_class_arity: &HashMap<Symbol, usize>,
    imported_class_fundeps: &HashMap<Symbol, Vec<(Vec<usize>, Vec<usize>)>>,
    errors: &mut Vec<ValidationError>,
) {
    // Collect local class and data/newtype/foreign-data names.
    let mut local_classes: HashSet<Symbol> = HashSet::new();
    let mut local_data: HashSet<Symbol> = HashSet::new();
    let mut local_aliases: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    // Local class fundeps in positional form, mirrors the imported map.
    let mut local_class_fundeps: HashMap<Symbol, Vec<(Vec<usize>, Vec<usize>)>> =
        HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Class { name, type_vars, fundeps, is_kind_sig: false, .. } => {
                local_classes.insert(name.value.symbol());
                let var_names: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                let fd: Vec<(Vec<usize>, Vec<usize>)> = fundeps
                    .iter()
                    .map(|f| {
                        let lhs: Vec<usize> = f
                            .lhs
                            .iter()
                            .filter_map(|v| {
                                var_names.iter().position(|s| *s == v.symbol())
                            })
                            .collect();
                        let rhs: Vec<usize> = f
                            .rhs
                            .iter()
                            .filter_map(|v| {
                                var_names.iter().position(|s| *s == v.symbol())
                            })
                            .collect();
                        (lhs, rhs)
                    })
                    .collect();
                local_class_fundeps.insert(name.value.symbol(), fd);
            }
            cst::Decl::Data { name, kind_sig: cst::KindSigSource::None, is_role_decl: false, .. } => {
                local_data.insert(name.value.symbol());
            }
            cst::Decl::Newtype { name, .. } => {
                local_data.insert(name.value.symbol());
            }
            cst::Decl::ForeignData { name, .. } => {
                local_data.insert(name.value.symbol());
            }
            cst::Decl::TypeAlias { name, ty, .. } => {
                // An alias "anchors locally" iff its expansion reaches a
                // local data/newtype/foreign-data. Track body references
                // so we can compute the closure below.
                let refs = head_type_cons(ty);
                local_aliases.insert(name.value.symbol(), refs);
            }
            cst::Decl::Fixity { is_type: true, operator, .. } => {
                // A locally-declared type operator (e.g. `infix 6 type
                // NumCons as :*`) anchors instances that use it in their
                // head, just like the underlying type does.
                local_data.insert(operator.value.symbol());
            }
            _ => {}
        }
    }

    // Propagate local-anchoring through aliases. `type T = Maybe Int`
    // anchors T locally because Maybe is local data. Transitive:
    // `type A = B; type B = Maybe Int` anchors both A and B.
    let mut alias_anchors_locally: HashSet<Symbol> = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for (alias, refs) in &local_aliases {
            if alias_anchors_locally.contains(alias) {
                continue;
            }
            if refs.iter().any(|r| {
                local_data.contains(r) || alias_anchors_locally.contains(r)
            }) {
                alias_anchors_locally.insert(*alias);
                changed = true;
            }
        }
    }

    for d in decls {
        let (span, class_name, types, is_derive) = match d {
            cst::Decl::Instance { span, class_name, types, .. } => {
                (*span, class_name, types, false)
            }
            cst::Decl::Derive { span, class_name, types, .. } => {
                (*span, class_name, types, true)
            }
            _ => continue,
        };
        let _ = is_derive;

        // Class is local if referenced unqualified AND it's defined locally.
        let class_local = class_name.module.is_none()
            && local_classes.contains(&class_name.name.symbol());
        if class_local {
            continue;
        }
        // Skip orphan check entirely if the class isn't known
        // (neither local nor imported). The unknown-class check
        // already emitted `UnknownName` for these cases — we
        // don't want to ALSO emit OrphanInstance.
        if class_name.module.is_none() {
            let csym = class_name.name.symbol();
            let class_known = local_classes.contains(&csym)
                || imported_class_arity.contains_key(&csym);
            if !class_known {
                continue;
            }
        }

        // Per-position locality: positions[i] = true when types[i]'s
        // head references a locally-defined data/newtype/foreign-data
        // (or a local alias that transitively anchors locally).
        let positions_local: Vec<bool> = types
            .iter()
            .map(|t| {
                head_type_cons(t).iter().any(|sym| {
                    local_data.contains(sym) || alias_anchors_locally.contains(sym)
                })
            })
            .collect();

        // Look up the class's fundeps. Local classes win over imported.
        let class_sym = class_name.name.symbol();
        let fundeps_for_class: Option<&Vec<(Vec<usize>, Vec<usize>)>> =
            local_class_fundeps
                .get(&class_sym)
                .or_else(|| imported_class_fundeps.get(&class_sym));

        // Compute "is orphan" per the fundep-aware rule:
        //   - No fundeps (or unknown class): orphan iff NO position is local.
        //   - With fundeps: for each fundep, the COVERING SET is the set
        //     of positions NOT in the fundep's `determined` list. If any
        //     covering set is entirely foreign, the instance is orphan.
        let is_orphan = match fundeps_for_class {
            Some(fds) if !fds.is_empty() => fds.iter().any(|(_lhs, determined)| {
                // Covering set = positions not in `determined`.
                let det_set: HashSet<usize> = determined.iter().copied().collect();
                let covering_has_local = positions_local
                    .iter()
                    .enumerate()
                    .any(|(i, local)| *local && !det_set.contains(&i));
                !covering_has_local
            }),
            _ => positions_local.iter().all(|local| !*local),
        };

        if is_orphan {
            let class_display = resolve(class_sym);
            errors.push(ValidationError {
                span,
                kind: ValidationErrorKind::OrphanInstance(class_display),
            });
        }
    }
}

/// Extract constructor names (unqualified) that appear in a type — both
/// spine heads of applications and bare Constructor nodes. Used for
/// orphan detection: any occurrence of a local data type in the instance
/// head anchors the instance to this module.
fn head_type_cons(te: &cst::TypeExpr) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    collect_all_cons(te, &mut out);
    out
}

fn collect_all_cons(te: &cst::TypeExpr, out: &mut Vec<Symbol>) {
    match te {
        cst::TypeExpr::Constructor { name, .. } => {
            if name.module.is_none() {
                out.push(name.name.symbol());
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            collect_all_cons(constructor, out);
            collect_all_cons(arg, out);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            collect_all_cons(from, out);
            collect_all_cons(to, out);
        }
        cst::TypeExpr::Parens { ty, .. } => collect_all_cons(ty, out),
        cst::TypeExpr::Kinded { ty, .. } => collect_all_cons(ty, out),
        cst::TypeExpr::TypeOp { left, right, op, .. } => {
            collect_all_cons(left, out);
            collect_all_cons(right, out);
            // The operator itself (e.g. `:*`) may be a locally-declared
            // type alias; include it so orphan detection fires correctly.
            if op.value.module.is_none() {
                out.push(op.value.name.symbol());
            }
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                collect_all_cons(&f.ty, out);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                collect_all_cons(&f.ty, out);
            }
            if let Some(t) = tail {
                collect_all_cons(t, out);
            }
        }
        _ => {}
    }
}

/// Walk a TypeExpr and invoke `cb(name, is_class)` for every
/// unqualified type-constructor and class-constraint name reference.
/// Used by `detect_transitive_export_errors` to find type/class
/// references in exported decls' signatures, alias bodies, ctor fields,
/// and kind annotations.
fn collect_type_refs<F: FnMut(Symbol, bool)>(te: &cst::TypeExpr, cb: &mut F) {
    match te {
        cst::TypeExpr::Constructor { name, .. } => {
            if name.module.is_none() {
                cb(name.name.symbol(), false);
            }
        }
        cst::TypeExpr::Var { .. }
        | cst::TypeExpr::Hole { .. }
        | cst::TypeExpr::Wildcard { .. }
        | cst::TypeExpr::StringLiteral { .. }
        | cst::TypeExpr::IntLiteral { .. } => {}
        cst::TypeExpr::App { constructor, arg, .. } => {
            collect_type_refs(constructor, cb);
            collect_type_refs(arg, cb);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            collect_type_refs(from, cb);
            collect_type_refs(to, cb);
        }
        cst::TypeExpr::Forall { ty, vars, .. } => {
            for (_, _, k) in vars {
                if let Some(k) = k {
                    collect_type_refs(k, cb);
                }
            }
            collect_type_refs(ty, cb);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                if c.class.module.is_none() {
                    cb(c.class.name.symbol(), true);
                }
                for a in &c.args {
                    collect_type_refs(a, cb);
                }
            }
            collect_type_refs(ty, cb);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                collect_type_refs(&f.ty, cb);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                collect_type_refs(&f.ty, cb);
            }
            if let Some(t) = tail {
                collect_type_refs(t, cb);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => collect_type_refs(ty, cb),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            collect_type_refs(left, cb);
            collect_type_refs(right, cb);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            collect_type_refs(ty, cb);
            collect_type_refs(kind, cb);
        }
        cst::TypeExpr::ArrayPattern { elements, .. } => {
            for e in elements {
                collect_type_refs(e, cb);
            }
        }
        cst::TypeExpr::AsPattern { ty, .. } => collect_type_refs(ty, cb),
    }
}

/// Flag any use of a local type alias with fewer arguments than its
/// declared parameter count. Only catches LOCAL aliases; imported
/// aliases aren't accessible from this CST-only pass.
fn detect_partially_applied_synonyms(
    decls: &[cst::Decl],
    imported_alias_arity: &HashMap<Symbol, usize>,
    imported_poly_kind_set: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    // Start with imported aliases (and operator aliases) as the
    // baseline. Local declarations override these on collision.
    let mut alias_arity: HashMap<Symbol, usize> = imported_alias_arity.clone();
    // Collect type aliases that have a standalone kind signature
    // (`type Foo :: Kind`). These can always be partially applied since
    // the kind system validates their usage; the check here would only
    // produce false positives for them.
    let mut kinded_aliases: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::Data { name, kind_sig: cst::KindSigSource::Type, .. } = d {
            kinded_aliases.insert(name.value.symbol());
        }
    }
    for d in decls {
        match d {
            cst::Decl::TypeAlias { name, type_vars, .. } => {
                if !kinded_aliases.contains(&name.value.symbol()) {
                    alias_arity.insert(name.value.symbol(), type_vars.len());
                }
            }
            // Local data/newtype/foreign-data declarations shadow any
            // imported type alias with the same name. Remove from
            // alias_arity so we don't false-positive on the local type.
            cst::Decl::Data { name, is_role_decl: false, kind_sig: cst::KindSigSource::None, .. }
            | cst::Decl::Newtype { name, .. }
            | cst::Decl::ForeignData { name, .. } => {
                alias_arity.remove(&name.value.symbol());
            }
            _ => {}
        }
    }
    if alias_arity.is_empty() {
        return;
    }
    // Collect type-level fixity mappings from local Decl::Fixity:
    // an operator name like `~>` bound via `infixr 6 type Foo as ~>`
    // should resolve to its target alias's arity. (Imported type
    // fixities are already folded into `imported_alias_arity` by the
    // driver.)
    for d in decls {
        if let cst::Decl::Fixity { target, operator, is_type: true, .. } = d {
            if target.module.is_none() {
                if let Some(&n) = alias_arity.get(&target.name) {
                    alias_arity.insert(operator.value.symbol(), n);
                }
            }
        }
    }

    // Helper used on every TypeExpr site.
    let mut reported: HashSet<(Symbol, usize)> = HashSet::new();
    let mut check = |te: &cst::TypeExpr, errors: &mut Vec<ValidationError>| {
        walk_partial_apps(te, &alias_arity, imported_poly_kind_set, errors, &mut reported);
    };

    for d in decls {
        match d {
            cst::Decl::TypeAlias { ty, type_var_kind_anns, .. } => {
                check(ty, errors);
                for ann in type_var_kind_anns.iter().flatten() {
                    check(ann, errors);
                }
            }
            cst::Decl::TypeSignature { ty, .. } => check(ty, errors),
            cst::Decl::Foreign { ty, .. } => check(ty, errors),
            cst::Decl::ForeignData { kind, .. } => check(kind, errors),
            cst::Decl::Data {
                constructors, kind_type, type_var_kind_anns, ..
            } => {
                for c in constructors {
                    for f in &c.fields {
                        check(f, errors);
                    }
                }
                if let Some(k) = kind_type {
                    check(k, errors);
                }
                for ann in type_var_kind_anns.iter().flatten() {
                    check(ann, errors);
                }
            }
            cst::Decl::Newtype { ty, type_var_kind_anns, .. } => {
                check(ty, errors);
                for ann in type_var_kind_anns.iter().flatten() {
                    check(ann, errors);
                }
            }
            cst::Decl::Class {
                members, constraints, kind_type, type_var_kind_anns, ..
            } => {
                for c in constraints {
                    for arg in &c.args {
                        check(arg, errors);
                    }
                }
                for m in members {
                    check(&m.ty, errors);
                }
                if let Some(k) = kind_type {
                    check(k, errors);
                }
                for ann in type_var_kind_anns.iter().flatten() {
                    check(ann, errors);
                }
            }
            cst::Decl::Instance { constraints, types, .. }
            | cst::Decl::Derive { constraints, types, .. } => {
                for c in constraints {
                    for arg in &c.args {
                        check(arg, errors);
                    }
                }
                for t in types {
                    check(t, errors);
                }
            }
            _ => {}
        }
    }
}

fn walk_partial_apps(
    te: &cst::TypeExpr,
    alias_arity: &HashMap<Symbol, usize>,
    poly_kind_set: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
    reported: &mut HashSet<(Symbol, usize)>,
) {
    match te {
        cst::TypeExpr::Constructor { span, name } => {
            if name.module.is_none() {
                let sym = name.name.symbol();
                if let Some(&n) = alias_arity.get(&sym) {
                    // Zero arguments applied. Skip polykinded aliases:
                    // their forall-kind lets them unify with any kind at the
                    // use site (e.g. `Id` used bare as a `Type -> Type`).
                    if n > 0 && !poly_kind_set.contains(&sym) {
                        if reported.insert((sym, span.start)) {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::PartiallyAppliedSynonym(
                                    resolve(sym),
                                ),
                            });
                        }
                    }
                }
            }
        }
        cst::TypeExpr::App { span, .. } => {
            // Peel the App chain to find head + arg count.
            let (head, args) = peel_app_chain(te);
            let mut head_is_alias = false;
            if let cst::TypeExpr::Constructor { name, .. } = head {
                if name.module.is_none() {
                    let sym = name.name.symbol();
                    if let Some(&n) = alias_arity.get(&sym) {
                        head_is_alias = true;
                        if args.len() < n {
                            if reported.insert((sym, span.start)) {
                                errors.push(ValidationError {
                                    span: *span,
                                    kind: ValidationErrorKind::PartiallyAppliedSynonym(
                                        resolve(sym),
                                    ),
                                });
                            }
                        }
                    }
                }
            }
            // Skip recursing into args when the App is an alias call:
            // we can't tell whether each arg is expected to be saturated
            // (Type) or unsaturated (HKT) without kind information, so a
            // bare alias-Constructor in arg position (e.g. `Template Identity`
            // where `Template` expects an HKT) would otherwise be flagged
            // as PAS. The kind checker catches genuine arity mismatches at
            // the alias's own expansion site.
            if !head_is_alias {
                for a in &args {
                    walk_partial_apps(a, alias_arity, poly_kind_set, errors, reported);
                }
            }
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_partial_apps(from, alias_arity, poly_kind_set, errors, reported);
            walk_partial_apps(to, alias_arity, poly_kind_set, errors, reported);
        }
        cst::TypeExpr::Forall { ty, vars, .. } => {
            for (_, _, k) in vars {
                if let Some(k) = k {
                    walk_partial_apps(k, alias_arity, poly_kind_set, errors, reported);
                }
            }
            walk_partial_apps(ty, alias_arity, poly_kind_set, errors, reported);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for a in &c.args {
                    walk_partial_apps(a, alias_arity, poly_kind_set, errors, reported);
                }
            }
            walk_partial_apps(ty, alias_arity, poly_kind_set, errors, reported);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_partial_apps(&f.ty, alias_arity, poly_kind_set, errors, reported);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_partial_apps(&f.ty, alias_arity, poly_kind_set, errors, reported);
            }
            if let Some(t) = tail {
                walk_partial_apps(t, alias_arity, poly_kind_set, errors, reported);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => {
            walk_partial_apps(ty, alias_arity, poly_kind_set, errors, reported);
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            // Both operands of a binary type operator can be type
            // constructors (HKT), so a synonym applied to one fewer
            // arg than its arity is valid there — the operator itself
            // supplies the context for the missing argument.
            walk_partial_apps_allow_one_short(left, alias_arity, poly_kind_set, errors, reported);
            walk_partial_apps_allow_one_short(right, alias_arity, poly_kind_set, errors, reported);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_partial_apps(ty, alias_arity, poly_kind_set, errors, reported);
            walk_partial_apps(kind, alias_arity, poly_kind_set, errors, reported);
        }
        cst::TypeExpr::ArrayPattern { elements, .. } => {
            for e in elements {
                walk_partial_apps(e, alias_arity, poly_kind_set, errors, reported);
            }
        }
        cst::TypeExpr::AsPattern { ty, .. } => {
            walk_partial_apps(ty, alias_arity, poly_kind_set, errors, reported);
        }
        _ => {}
    }
}

/// Like `walk_partial_apps` but allows a synonym to be applied to
/// exactly `arity - 1` arguments at the top level. Used for the left
/// operand of the `+` row-extension operator, where `+` itself
/// provides the missing row-tail argument.
fn walk_partial_apps_allow_one_short(
    te: &cst::TypeExpr,
    alias_arity: &HashMap<Symbol, usize>,
    poly_kind_set: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
    reported: &mut HashSet<(Symbol, usize)>,
) {
    match te {
        cst::TypeExpr::App { span, .. } => {
            let (head, args) = peel_app_chain(te);
            let mut head_is_alias = false;
            if let cst::TypeExpr::Constructor { name, .. } = head {
                if name.module.is_none() {
                    let sym = name.name.symbol();
                    if let Some(&n) = alias_arity.get(&sym) {
                        head_is_alias = true;
                        // allow arity - 1 (the operator provides the last arg)
                        if args.len() + 1 < n {
                            if reported.insert((sym, span.start)) {
                                errors.push(ValidationError {
                                    span: *span,
                                    kind: ValidationErrorKind::PartiallyAppliedSynonym(
                                        resolve(sym),
                                    ),
                                });
                            }
                        }
                    }
                }
            }
            if !head_is_alias {
                for a in &args {
                    walk_partial_apps(a, alias_arity, poly_kind_set, errors, reported);
                }
            }
        }
        // A bare Constructor with arity 1 is OK on the left of `+`
        // (it's arity-1, applied with 0 args, which is 1 short).
        cst::TypeExpr::Constructor { .. } => {
            // allowed — `+` provides the missing 1 arg
        }
        // Parenthesized: recurse with allowance
        cst::TypeExpr::Parens { ty, .. } => {
            walk_partial_apps_allow_one_short(ty, alias_arity, poly_kind_set, errors, reported);
        }
        _ => walk_partial_apps(te, alias_arity, poly_kind_set, errors, reported),
    }
}

fn peel_app_chain(te: &cst::TypeExpr) -> (&cst::TypeExpr, Vec<&cst::TypeExpr>) {
    let mut args: Vec<&cst::TypeExpr> = Vec::new();
    let mut cur = te;
    loop {
        match cur {
            cst::TypeExpr::App { constructor, arg, .. } => {
                args.push(arg);
                cur = constructor;
            }
            cst::TypeExpr::Parens { ty, .. } => {
                cur = ty;
            }
            _ => break,
        }
    }
    args.reverse();
    (cur, args)
}

/// Cycle through type synonyms only. `type A = B; type B = A` is cyclic;
/// `type A = Array A` is not (Array is a type constructor, not an alias).
fn detect_alias_cycles(decls: &[cst::Decl], errors: &mut Vec<ValidationError>) {
    // First pass: find alias names in this module.
    let mut aliases: HashMap<Symbol, (Span, Vec<Symbol>)> = HashMap::new();
    for d in decls {
        if let cst::Decl::TypeAlias { span, name, ty, .. } = d {
            let refs = collect_type_cons(ty);
            aliases.insert(name.value.symbol(), (*span, refs));
        }
    }
    // Keep only edges that point to other aliases (the graph is alias-only).
    let alias_keys: HashSet<Symbol> = aliases.keys().copied().collect();
    for (_, (_span, refs)) in aliases.iter_mut() {
        refs.retain(|r| alias_keys.contains(r));
    }

    let mut graph: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    for (n, (_s, refs)) in &aliases {
        graph.insert(*n, refs.clone());
    }

    for cycle in find_cycles(&graph) {
        // Primary span = first alias in the cycle's span.
        let first = cycle[0];
        let span = aliases.get(&first).map(|(s, _)| *s).unwrap_or(Span::new(0, 0));
        errors.push(ValidationError {
            span,
            kind: ValidationErrorKind::CycleInTypeSynonym(
                cycle.iter().map(|s| resolve(*s)).collect(),
            ),
        });
    }
}

/// Cycle through class superclass constraints. `class Foo a <= Bar a; class Bar a <= Foo a`.
fn detect_class_cycles(decls: &[cst::Decl], errors: &mut Vec<ValidationError>) {
    let mut classes: HashMap<Symbol, (Span, Vec<Symbol>)> = HashMap::new();
    for d in decls {
        if let cst::Decl::Class { span, name, constraints, is_kind_sig, .. } = d {
            if *is_kind_sig {
                continue;
            }
            // Unqualified superclass refs only — `class P.Show a <= Show a`
            // is not a self-cycle because `P.Show` is an imported class.
            let sup: Vec<Symbol> = constraints
                .iter()
                .filter(|c| c.class.module.is_none())
                .map(|c| c.class.name.symbol())
                .collect();
            classes.insert(name.value.symbol(), (*span, sup));
        }
    }
    let class_keys: HashSet<Symbol> = classes.keys().copied().collect();
    for (_, (_s, refs)) in classes.iter_mut() {
        refs.retain(|r| class_keys.contains(r));
    }

    let graph: HashMap<Symbol, Vec<Symbol>> = classes
        .iter()
        .map(|(k, (_, v))| (*k, v.clone()))
        .collect();

    for cycle in find_cycles(&graph) {
        let first = cycle[0];
        let span = classes.get(&first).map(|(s, _)| *s).unwrap_or(Span::new(0, 0));
        errors.push(ValidationError {
            span,
            kind: ValidationErrorKind::CycleInTypeClassDeclaration(
                cycle.iter().map(|s| resolve(*s)).collect(),
            ),
        });
    }
}

/// Cycle through standalone kind signatures, including foreign-data kinds.
/// `foreign import data Foo :: Bar; foreign import data Bar :: Foo` → cycle.
/// `data Foo :: Foo -> Type; data Foo a = Foo` is a self-cycle on Foo's kind.
fn detect_kind_sig_cycles(decls: &[cst::Decl], errors: &mut Vec<ValidationError>) {
    // Collect every type-level name whose kind refers to other type-level names.
    // This includes:
    //   - `data Foo :: Kind` (standalone kind decl, is_kind_sig != None)
    //   - `newtype Foo :: Kind`
    //   - `class Foo :: Kind`  (is_kind_sig = true)
    //   - `type Foo :: Kind`
    //   - `foreign import data Foo :: Kind`
    let mut kinded: HashMap<Symbol, (Span, Vec<Symbol>)> = HashMap::new();

    for d in decls {
        match d {
            cst::Decl::Data {
                span,
                name,
                kind_sig,
                kind_type: Some(kt),
                ..
            } if !matches!(kind_sig, cst::KindSigSource::None) => {
                let refs = collect_type_cons(kt);
                kinded
                    .entry(name.value.symbol())
                    .and_modify(|(_, r)| r.extend(refs.iter().copied()))
                    .or_insert((*span, refs));
            }
            cst::Decl::Class { span, name, is_kind_sig: true, kind_type: Some(kt), .. } => {
                let refs = collect_type_cons(kt);
                kinded
                    .entry(name.value.symbol())
                    .and_modify(|(_, r)| r.extend(refs.iter().copied()))
                    .or_insert((*span, refs));
            }
            cst::Decl::ForeignData { span, name, kind, .. } => {
                let refs = collect_type_cons(kind);
                kinded
                    .entry(name.value.symbol())
                    .and_modify(|(_, r)| r.extend(refs.iter().copied()))
                    .or_insert((*span, refs));
            }
            _ => {}
        }
    }

    // Restrict to edges pointing at other kinded decls (local).
    let kinded_keys: HashSet<Symbol> = kinded.keys().copied().collect();
    for (_, (_, refs)) in kinded.iter_mut() {
        refs.retain(|r| kinded_keys.contains(r));
    }

    let graph: HashMap<Symbol, Vec<Symbol>> = kinded
        .iter()
        .map(|(k, (_, v))| (*k, v.clone()))
        .collect();

    for cycle in find_cycles(&graph) {
        let first = cycle[0];
        let span = kinded.get(&first).map(|(s, _)| *s).unwrap_or(Span::new(0, 0));
        errors.push(ValidationError {
            span,
            kind: ValidationErrorKind::CycleInKindDeclaration(
                cycle.iter().map(|s| resolve(*s)).collect(),
            ),
        });
    }
}

/// Cycle through value declarations at the top level, where the cycle
/// goes through bindings with NO function parameters (otherwise the
/// decl is a lazy function body and the recursion is fine).
///
/// `x = x` → cycle. `x = y; y = x` → cycle. `f x = f x` → NOT cycle
/// (function definition). `loop = loop + 1` → cycle (no binders).
fn detect_value_cycles(decls: &[cst::Decl], errors: &mut Vec<ValidationError>) {
    // First collect groups: merge adjacent equations as in the duplicate
    // detection above. We only care about groups with ZERO binders on
    // every equation. A group with mixed arities is handled by later
    // passes; we conservatively skip those.
    let mut zero_arity: HashMap<Symbol, (Span, Vec<Symbol>)> = HashMap::new();
    let mut last_name: Option<Symbol> = None;
    let mut i = 0usize;
    while i < decls.len() {
        if let cst::Decl::Value { span, name, binders, guarded, .. } = &decls[i] {
            let sym = name.value.symbol();
            if last_name == Some(sym) {
                // Part of a multi-equation group already recorded.
                i += 1;
                continue;
            }
            last_name = Some(sym);

            // Walk adjacent equations with same name, checking that ALL
            // have zero binders. If any has >=1 binder, this is a function
            // group — skip.
            let mut j = i;
            let mut all_zero_arity = true;
            let mut all_refs: Vec<Symbol> = Vec::new();
            while j < decls.len() {
                match &decls[j] {
                    cst::Decl::Value { name: n2, binders: b2, guarded: g2, .. }
                        if n2.value.symbol() == sym =>
                    {
                        if !b2.is_empty() {
                            all_zero_arity = false;
                        }
                        collect_value_refs(g2, &mut all_refs);
                        j += 1;
                    }
                    _ => break,
                }
            }
            let _ = guarded;
            let _ = binders;
            if all_zero_arity {
                zero_arity.insert(sym, (*span, all_refs));
            }
            i = j;
            continue;
        } else {
            last_name = None;
        }
        i += 1;
    }

    // Restrict to edges within the zero-arity set.
    let za_keys: HashSet<Symbol> = zero_arity.keys().copied().collect();
    for (_, (_, refs)) in zero_arity.iter_mut() {
        refs.retain(|r| za_keys.contains(r));
    }

    let graph: HashMap<Symbol, Vec<Symbol>> = zero_arity
        .iter()
        .map(|(k, (_, v))| (*k, v.clone()))
        .collect();

    for cycle in find_cycles(&graph) {
        let first = cycle[0];
        let span = zero_arity.get(&first).map(|(s, _)| *s).unwrap_or(Span::new(0, 0));
        errors.push(ValidationError {
            span,
            kind: ValidationErrorKind::CycleInDeclaration(
                cycle.iter().map(|s| resolve(*s)).collect(),
            ),
        });
    }
}

/// Collect every type-constructor symbol referenced inside a `TypeExpr`.
/// The caller is responsible for filtering out non-local names (constructors
/// that aren't defined in this module simply won't appear in the graph's
/// key set).
fn collect_type_cons(te: &cst::TypeExpr) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    walk_type_expr(te, &mut out);
    out
}

fn walk_type_expr(te: &cst::TypeExpr, out: &mut Vec<Symbol>) {
    match te {
        cst::TypeExpr::Constructor { name, .. } => {
            // Only collect UNQUALIFIED references. `P.Number` is a different
            // type from a local `type Number = …` even though the bare name
            // matches after qualifier stripping. Cycle detection must respect
            // module qualifiers or it will false-positive on fixtures like
            // `type Number = P.Number`.
            if name.module.is_none() {
                out.push(name.name.symbol());
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            walk_type_expr(constructor, out);
            walk_type_expr(arg, out);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_type_expr(from, out);
            walk_type_expr(to, out);
        }
        cst::TypeExpr::Forall { ty, vars, .. } => {
            for (_, _, k) in vars {
                if let Some(k) = k {
                    walk_type_expr(k, out);
                }
            }
            walk_type_expr(ty, out);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for arg in &c.args {
                    walk_type_expr(arg, out);
                }
            }
            walk_type_expr(ty, out);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_type_expr(&f.ty, out);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_type_expr(&f.ty, out);
            }
            if let Some(t) = tail {
                walk_type_expr(t, out);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => walk_type_expr(ty, out),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_type_expr(left, out);
            walk_type_expr(right, out);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_type_expr(ty, out);
            walk_type_expr(kind, out);
        }
        cst::TypeExpr::ArrayPattern { elements, .. } => {
            for e in elements {
                walk_type_expr(e, out);
            }
        }
        cst::TypeExpr::AsPattern { ty, .. } => walk_type_expr(ty, out),
        cst::TypeExpr::Var { .. }
        | cst::TypeExpr::Hole { .. }
        | cst::TypeExpr::Wildcard { .. }
        | cst::TypeExpr::StringLiteral { .. }
        | cst::TypeExpr::IntLiteral { .. } => {}
    }
}

/// Collect value-level references used by a guarded body, strictly for the
/// zero-arity value-cycle detector. Shallow — follows the common forms;
/// anything missed is a false-negative (no cycle reported), which is safe.
fn collect_value_refs(ge: &cst::GuardedExpr, out: &mut Vec<Symbol>) {
    match ge {
        cst::GuardedExpr::Unconditional(e) => walk_expr(e, out),
        cst::GuardedExpr::Guarded(guards) => {
            for g in guards {
                for p in &g.patterns {
                    match p {
                        cst::GuardPattern::Boolean(e) => walk_expr(e, out),
                        cst::GuardPattern::Pattern(_, e) => walk_expr(e, out),
                    }
                }
                walk_expr(&g.expr, out);
            }
        }
    }
}

fn walk_expr(e: &cst::Expr, out: &mut Vec<Symbol>) {
    use cst::Expr;
    match e {
        Expr::Var { name, .. } => {
            // Unqualified references to module-local names only.
            if name.module.is_none() {
                out.push(name.name.symbol());
            }
        }
        Expr::App { func, arg, .. } => {
            walk_expr(func, out);
            walk_expr(arg, out);
        }
        Expr::Op { left, right, .. } => {
            walk_expr(left, out);
            walk_expr(right, out);
        }
        Expr::BacktickApp { func, left, right, .. } => {
            walk_expr(func, out);
            walk_expr(left, out);
            walk_expr(right, out);
        }
        Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr(cond, out);
            walk_expr(then_expr, out);
            walk_expr(else_expr, out);
        }
        Expr::Parens { expr, .. } => walk_expr(expr, out),
        Expr::TypeAnnotation { expr, .. } => walk_expr(expr, out),
        Expr::Negate { expr, .. } => walk_expr(expr, out),
        Expr::VisibleTypeApp { func, .. } => walk_expr(func, out),
        Expr::RecordAccess { expr, .. } => walk_expr(expr, out),
        // Deliberately skip Let/Case/Do/Ado/Lambda/Record — these introduce
        // new binders / scopes and a cycle detector over the whole module
        // without scoping would produce false positives.
        _ => {}
    }
}

/// Simple cycle-finder. For each node, DFS and record all cycles containing
/// it. Deduplicates so a k-cycle emits once. Self-loops (x → x) are included.
fn find_cycles(graph: &HashMap<Symbol, Vec<Symbol>>) -> Vec<Vec<Symbol>> {
    let mut reported: HashSet<Vec<Symbol>> = HashSet::new();
    let mut cycles: Vec<Vec<Symbol>> = Vec::new();
    let mut nodes: Vec<Symbol> = graph.keys().copied().collect();
    nodes.sort_by_key(|s| (*s).to_string_rep());
    for start in nodes {
        let mut path: Vec<Symbol> = Vec::new();
        let mut on_path: HashSet<Symbol> = HashSet::new();
        dfs_cycle(start, graph, &mut path, &mut on_path, &mut cycles, &mut reported);
    }
    cycles
}

fn dfs_cycle(
    node: Symbol,
    graph: &HashMap<Symbol, Vec<Symbol>>,
    path: &mut Vec<Symbol>,
    on_path: &mut HashSet<Symbol>,
    out: &mut Vec<Vec<Symbol>>,
    reported: &mut HashSet<Vec<Symbol>>,
) {
    if on_path.contains(&node) {
        // Extract the cycle by finding node in path.
        let pos = path.iter().position(|&x| x == node).unwrap_or(0);
        let mut cycle = path[pos..].to_vec();
        // Canonicalise: rotate so smallest symbol comes first, for dedup.
        if !cycle.is_empty() {
            let min_pos = cycle
                .iter()
                .enumerate()
                .min_by_key(|(_, s)| s.to_string_rep())
                .map(|(i, _)| i)
                .unwrap_or(0);
            cycle.rotate_left(min_pos);
            if reported.insert(cycle.clone()) {
                out.push(cycle);
            }
        }
        return;
    }
    if path.contains(&node) {
        return;
    }
    path.push(node);
    on_path.insert(node);
    if let Some(children) = graph.get(&node) {
        for c in children {
            dfs_cycle(*c, graph, path, on_path, out, reported);
        }
    }
    on_path.remove(&node);
    path.pop();
}

trait SymExt {
    fn to_string_rep(self) -> String;
}
impl SymExt for Symbol {
    fn to_string_rep(self) -> String {
        crate::interner::resolve(self).unwrap_or_default()
    }
}

fn check_duplicate_type_args(
    type_vars: &[cst::Spanned<crate::names::TypeVarName>],
    errors: &mut Vec<ValidationError>,
) {
    let mut seen: HashSet<Symbol> = HashSet::new();
    for v in type_vars {
        let sym = v.value.symbol();
        if !seen.insert(sym) {
            errors.push(ValidationError {
                span: v.span,
                kind: ValidationErrorKind::DuplicateTypeArgument(resolve(sym)),
            });
        }
    }
}

fn resolve(sym: Symbol) -> String {
    crate::interner::resolve(sym).unwrap_or_default()
}

/// Walk a binder tree, collecting every name it introduces. Each
/// pushed entry is `(name, span_where_introduced)`. Punned record
/// fields (`{ x }`) introduce the label as a name. As-patterns
/// introduce both the bound name and recurse into the inner binder.
fn collect_binder_names(b: &cst::Binder, out: &mut Vec<(Symbol, Span)>) {
    match b {
        cst::Binder::Wildcard { .. } | cst::Binder::Literal { .. } => {}
        cst::Binder::Var { name, .. } => {
            out.push((name.value.symbol(), name.span));
        }
        cst::Binder::Constructor { args, .. } => {
            for a in args {
                collect_binder_names(a, out);
            }
        }
        cst::Binder::Record { fields, .. } => {
            for f in fields {
                match &f.binder {
                    Some(inner) => collect_binder_names(inner, out),
                    None => {
                        out.push((f.label.value.symbol(), f.label.span));
                    }
                }
            }
        }
        cst::Binder::As { name, binder, .. } => {
            out.push((name.value.symbol(), name.span));
            collect_binder_names(binder, out);
        }
        cst::Binder::Parens { binder, .. } => collect_binder_names(binder, out),
        cst::Binder::Array { elements, .. } => {
            for e in elements {
                collect_binder_names(e, out);
            }
        }
        cst::Binder::Op { left, right, .. } => {
            collect_binder_names(left, out);
            collect_binder_names(right, out);
        }
        cst::Binder::Typed { binder, .. } => collect_binder_names(binder, out),
    }
}

/// Run [`collect_binder_names`] over every binder in `binders`,
/// emitting an `OverlappingArgNames` for each repeated name.
fn check_binder_list_overlap(
    binders: &[cst::Binder],
    errors: &mut Vec<ValidationError>,
) {
    let mut names: Vec<(Symbol, Span)> = Vec::new();
    for b in binders {
        collect_binder_names(b, &mut names);
    }
    let mut seen: HashSet<Symbol> = HashSet::new();
    for (sym, span) in &names {
        if !seen.insert(*sym) {
            errors.push(ValidationError {
                span: *span,
                kind: ValidationErrorKind::OverlappingArgNames(resolve(*sym)),
            });
        }
    }
}

/// Walk every expression inside `expr` looking for binder lists
/// (Lambda args, Case alt patterns, Do/Ado bind patterns, nested
/// Let bindings) and apply the overlap check to each one.
fn walk_expr_for_overlapping_binders(
    expr: &cst::Expr,
    errors: &mut Vec<ValidationError>,
) {
    match expr {
        cst::Expr::Var { .. }
        | cst::Expr::Constructor { .. }
        | cst::Expr::Literal { .. }
        | cst::Expr::OpParens { .. }
        | cst::Expr::Wildcard { .. }
        | cst::Expr::Hole { .. } => {}
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_overlapping_binders(func, errors);
            walk_expr_for_overlapping_binders(arg, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_overlapping_binders(func, errors);
        }
        cst::Expr::Lambda { binders, body, .. } => {
            check_binder_list_overlap(binders, errors);
            walk_expr_for_overlapping_binders(body, errors);
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_overlapping_binders(left, errors);
            walk_expr_for_overlapping_binders(right, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_overlapping_binders(cond, errors);
            walk_expr_for_overlapping_binders(then_expr, errors);
            walk_expr_for_overlapping_binders(else_expr, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_overlapping_binders(e, errors);
            }
            for alt in alts {
                check_binder_list_overlap(&alt.binders, errors);
                walk_guarded_for_overlapping_binders(&alt.result, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            walk_let_bindings_for_overlapping_binders(bindings, errors);
            walk_expr_for_overlapping_binders(body, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            walk_do_statements_for_overlapping_binders(statements, errors);
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_overlapping_binders(result, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_overlapping_binders(v, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_overlapping_binders(expr, errors);
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_overlapping_binders(expr, errors);
            for u in updates {
                walk_expr_for_overlapping_binders(&u.value, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => {
            walk_expr_for_overlapping_binders(expr, errors);
        }
        cst::Expr::TypeAnnotation { expr, .. } => {
            walk_expr_for_overlapping_binders(expr, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_overlapping_binders(e, errors);
            }
        }
        cst::Expr::Negate { expr, .. } => {
            walk_expr_for_overlapping_binders(expr, errors);
        }
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_overlapping_binders(name, errors);
            walk_expr_for_overlapping_binders(pattern, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_overlapping_binders(func, errors);
            walk_expr_for_overlapping_binders(left, errors);
            walk_expr_for_overlapping_binders(right, errors);
        }
    }
}

fn walk_guarded_for_overlapping_binders(
    g: &cst::GuardedExpr,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_overlapping_binders(e, errors);
        }
        cst::GuardedExpr::Guarded(guards) => {
            for gd in guards {
                for p in &gd.patterns {
                    if let cst::GuardPattern::Pattern(b, e) = p {
                        check_binder_list_overlap(std::slice::from_ref(b), errors);
                        walk_expr_for_overlapping_binders(e, errors);
                    } else if let cst::GuardPattern::Boolean(e) = p {
                        walk_expr_for_overlapping_binders(e, errors);
                    }
                }
                walk_expr_for_overlapping_binders(&gd.expr, errors);
            }
        }
    }
}

fn walk_let_bindings_for_overlapping_binders(
    bindings: &[cst::LetBinding],
    errors: &mut Vec<ValidationError>,
) {
    for b in bindings {
        if let cst::LetBinding::Value { binder, expr, .. } = b {
            check_binder_list_overlap(std::slice::from_ref(binder), errors);
            walk_expr_for_overlapping_binders(expr, errors);
        }
    }
}

fn walk_do_statements_for_overlapping_binders(
    statements: &[cst::DoStatement],
    errors: &mut Vec<ValidationError>,
) {
    for s in statements {
        match s {
            cst::DoStatement::Bind { binder, expr, .. } => {
                check_binder_list_overlap(std::slice::from_ref(binder), errors);
                walk_expr_for_overlapping_binders(expr, errors);
            }
            cst::DoStatement::Let { bindings, .. } => {
                walk_let_bindings_for_overlapping_binders(bindings, errors);
            }
            cst::DoStatement::Discard { expr, .. } => {
                walk_expr_for_overlapping_binders(expr, errors);
            }
        }
    }
}

fn detect_overlapping_arg_names(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::Value { binders, guarded, where_clause, .. } => {
                check_binder_list_overlap(binders, errors);
                walk_guarded_for_overlapping_binders(guarded, errors);
                walk_let_bindings_for_overlapping_binders(where_clause, errors);
            }
            cst::Decl::Instance { members, .. } => {
                detect_overlapping_arg_names(members, errors);
            }
            _ => {}
        }
    }
}

/// Detect duplicate value names within a single `let` / `where` /
/// instance-member let block, with the same "non-adjacent group"
/// rule the top-level pass uses (multi-equation defs are fine when
/// contiguous, broken when interleaved).
fn check_let_block_for_dup_names(
    bindings: &[cst::LetBinding],
    errors: &mut Vec<ValidationError>,
) {
    // value_groups: name -> [span of each non-adjacent group]
    let mut value_groups: HashMap<Symbol, Vec<Span>> = HashMap::new();
    let mut last_value_name: Option<Symbol> = None;
    let mut sig_counts: HashMap<Symbol, Vec<Span>> = HashMap::new();
    for b in bindings {
        match b {
            cst::LetBinding::Value { binder, span, .. } => {
                // For overlap, only Var-shaped top-level binders carry
                // a let-name. Pattern lets (`(Tuple a b) = ...`) don't
                // create a value name in the same sense.
                if let cst::Binder::Var { name, .. } = peel_paren_binder(binder) {
                    let sym = name.value.symbol();
                    if last_value_name != Some(sym) {
                        value_groups.entry(sym).or_default().push(*span);
                    }
                    last_value_name = Some(sym);
                } else {
                    last_value_name = None;
                }
            }
            cst::LetBinding::Signature { name, span, .. } => {
                sig_counts.entry(name.value.symbol()).or_default().push(*span);
                last_value_name = None;
            }
        }
    }
    for (sym, spans) in &value_groups {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::OverlappingNamesInLet(resolve(*sym)),
                });
            }
        }
    }
    // Two signatures for the same name in a let block — a binding
    // error too. Also two value-defs with a sig in between gets
    // captured by the group walk.
    for (sym, spans) in &sig_counts {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::OverlappingNamesInLet(resolve(*sym)),
                });
            }
        }
    }
}

fn peel_paren_binder(b: &cst::Binder) -> &cst::Binder {
    let mut cur = b;
    while let cst::Binder::Parens { binder, .. } = cur {
        cur = binder;
    }
    cur
}

fn walk_expr_for_let_dup_names(
    expr: &cst::Expr,
    errors: &mut Vec<ValidationError>,
) {
    match expr {
        cst::Expr::Var { .. }
        | cst::Expr::Constructor { .. }
        | cst::Expr::Literal { .. }
        | cst::Expr::OpParens { .. }
        | cst::Expr::Wildcard { .. }
        | cst::Expr::Hole { .. } => {}
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_let_dup_names(func, errors);
            walk_expr_for_let_dup_names(arg, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_let_dup_names(func, errors);
        }
        cst::Expr::Lambda { body, .. } => {
            walk_expr_for_let_dup_names(body, errors);
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_let_dup_names(left, errors);
            walk_expr_for_let_dup_names(right, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_let_dup_names(cond, errors);
            walk_expr_for_let_dup_names(then_expr, errors);
            walk_expr_for_let_dup_names(else_expr, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_let_dup_names(e, errors);
            }
            for alt in alts {
                walk_guarded_for_let_dup_names(&alt.result, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            check_let_block_for_dup_names(bindings, errors);
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_let_dup_names(expr, errors);
                }
            }
            walk_expr_for_let_dup_names(body, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_let_dup_names(expr, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        check_let_block_for_dup_names(bindings, errors);
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_let_dup_names(expr, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_let_dup_names(result, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_let_dup_names(v, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_let_dup_names(expr, errors);
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_let_dup_names(expr, errors);
            for u in updates {
                walk_expr_for_let_dup_names(&u.value, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => walk_expr_for_let_dup_names(expr, errors),
        cst::Expr::TypeAnnotation { expr, .. } => {
            walk_expr_for_let_dup_names(expr, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_let_dup_names(e, errors);
            }
        }
        cst::Expr::Negate { expr, .. } => walk_expr_for_let_dup_names(expr, errors),
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_let_dup_names(name, errors);
            walk_expr_for_let_dup_names(pattern, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_let_dup_names(func, errors);
            walk_expr_for_let_dup_names(left, errors);
            walk_expr_for_let_dup_names(right, errors);
        }
    }
}

fn walk_guarded_for_let_dup_names(
    g: &cst::GuardedExpr,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_let_dup_names(e, errors);
        }
        cst::GuardedExpr::Guarded(guards) => {
            for gd in guards {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e) => {
                            walk_expr_for_let_dup_names(e, errors);
                        }
                        cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_let_dup_names(e, errors);
                        }
                    }
                }
                walk_expr_for_let_dup_names(&gd.expr, errors);
            }
        }
    }
}

fn detect_overlapping_names_in_let(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::Value { guarded, where_clause, .. } => {
                // The where clause behaves like a let block.
                check_let_block_for_dup_names(where_clause, errors);
                for b in where_clause {
                    if let cst::LetBinding::Value { expr, .. } = b {
                        walk_expr_for_let_dup_names(expr, errors);
                    }
                }
                walk_guarded_for_let_dup_names(guarded, errors);
            }
            cst::Decl::Instance { members, .. } => {
                detect_overlapping_names_in_let(members, errors);
            }
            _ => {}
        }
    }
}

/// `derive newtype instance C (T ...)` requires T to be a `newtype`.
/// We only check local types here — imported types are checked via
/// the registry elsewhere.
fn detect_cannot_derive_newtype_for_data(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut local_data: HashSet<Symbol> = HashSet::new();
    let mut local_newtype: HashSet<Symbol> = HashSet::new();
    for d in decls {
        match d {
            cst::Decl::Data { name, kind_sig, is_role_decl, .. } => {
                if !*is_role_decl && matches!(kind_sig, cst::KindSigSource::None) {
                    local_data.insert(name.value.symbol());
                }
            }
            cst::Decl::Newtype { name, .. } => {
                local_newtype.insert(name.value.symbol());
            }
            _ => {}
        }
    }
    for d in decls {
        if let cst::Decl::Derive { class_name, types, span, .. } = d {
            // Two paths surface this error in the original compiler:
            //   - `derive newtype instance C T` (Derive.newtype = true)
            //     — needs T to be a newtype.
            //   - `derive instance Newtype T _` — the `Newtype` class
            //     specifically requires its head to be a newtype,
            //     even without the `newtype` keyword.
            let class_sym = class_name.to_qi().name;
            let class_str = resolve(class_sym);
            let head = match d {
                cst::Decl::Derive { newtype: true, .. } => types.first(),
                _ if class_str == "Newtype" => types.first(),
                _ => None,
            };
            let Some(head) = head else { continue };
            let Some(head_sym) = type_head_symbol(head) else { continue };
            if local_data.contains(&head_sym)
                && !local_newtype.contains(&head_sym)
            {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::CannotDeriveNewtypeForData(
                        resolve(head_sym),
                    ),
                });
            }
        }
    }
}

fn type_head_symbol(te: &cst::TypeExpr) -> Option<Symbol> {
    match peel_parens(te) {
        cst::TypeExpr::Constructor { name, .. } if name.module.is_none() => {
            Some(name.name.symbol())
        }
        cst::TypeExpr::App { constructor, .. } => type_head_symbol(constructor),
        _ => None,
    }
}

/// Detect `Int` literals whose value falls outside the i32 range.
/// PureScript `Int` is 32-bit signed.
fn detect_int_out_of_range(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        if let cst::Decl::Value { guarded, where_clause, .. } = d {
            walk_guarded_for_int_range(guarded, errors);
            for b in where_clause {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_int_range(expr, errors);
                }
            }
        }
    }
}

fn walk_guarded_for_int_range(
    g: &cst::GuardedExpr,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => walk_expr_for_int_range(e, errors),
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    if let cst::GuardPattern::Boolean(e)
                    | cst::GuardPattern::Pattern(_, e) = p
                    {
                        walk_expr_for_int_range(e, errors);
                    }
                }
                walk_expr_for_int_range(&gd.expr, errors);
            }
        }
    }
}

fn walk_expr_for_int_range(
    expr: &cst::Expr,
    errors: &mut Vec<ValidationError>,
) {
    match expr {
        cst::Expr::Literal { lit, span } => {
            if let cst::Literal::Int(n) = lit {
                if *n > i32::MAX as i64 || *n < i32::MIN as i64 {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::IntOutOfRange,
                    });
                }
            }
        }
        // `Negate(Literal(Int(n)))` represents `-n`; the i32 range
        // is asymmetric (i32::MIN.abs() = 2^31 = i32::MAX + 1), so
        // `-2147483648` is valid even though `2147483648` alone
        // exceeds i32::MAX. Special-case this exact pattern so we
        // don't flag the syntactic literal under negation.
        cst::Expr::Negate { expr: inner, .. } => {
            if let cst::Expr::Literal {
                lit: cst::Literal::Int(n),
                span,
            } = inner.as_ref()
            {
                let neg = -(*n);
                if neg > i32::MAX as i64 || neg < i32::MIN as i64 {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::IntOutOfRange,
                    });
                }
            } else {
                walk_expr_for_int_range(inner, errors);
            }
        }
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_int_range(func, errors);
            walk_expr_for_int_range(arg, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_int_range(func, errors);
        }
        cst::Expr::Lambda { body, .. } => walk_expr_for_int_range(body, errors),
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_int_range(left, errors);
            walk_expr_for_int_range(right, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_int_range(cond, errors);
            walk_expr_for_int_range(then_expr, errors);
            walk_expr_for_int_range(else_expr, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_int_range(e, errors);
            }
            for alt in alts {
                walk_guarded_for_int_range(&alt.result, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_int_range(expr, errors);
                }
            }
            walk_expr_for_int_range(body, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_int_range(expr, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_int_range(expr, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_int_range(result, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_int_range(v, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => walk_expr_for_int_range(expr, errors),
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_int_range(expr, errors);
            for u in updates {
                walk_expr_for_int_range(&u.value, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => walk_expr_for_int_range(expr, errors),
        cst::Expr::TypeAnnotation { expr, .. } => walk_expr_for_int_range(expr, errors),
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_int_range(e, errors);
            }
        }
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_int_range(name, errors);
            walk_expr_for_int_range(pattern, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_int_range(func, errors);
            walk_expr_for_int_range(left, errors);
            walk_expr_for_int_range(right, errors);
        }
        _ => {}
    }
}

/// `Binder::Op` introduces an operator alias in pattern position.
/// Only ctor-shaped operators (`infixl 6 Cons as :`) are valid;
/// function-shaped (`infixl 6 cons as :`) are not deconstructable.
/// We approximate "ctor-shaped" by checking the local `Decl::Fixity`
/// list — if the operator's `target_name` is locally a value (not
/// a ctor), the binder is invalid.
fn detect_invalid_operator_in_binder(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut local_value_op_targets: HashMap<Symbol, Symbol> = HashMap::new();
    let mut local_values: HashSet<Symbol> = HashSet::new();
    let mut local_ctors: HashSet<Symbol> = HashSet::new();
    for d in decls {
        match d {
            cst::Decl::Fixity { operator, target, is_type, .. } if !*is_type => {
                local_value_op_targets
                    .insert(operator.value.symbol(), target.name);
            }
            cst::Decl::Value { name, .. } => {
                local_values.insert(name.value.symbol());
            }
            cst::Decl::Foreign { name, .. } => {
                local_values.insert(name.value.symbol());
            }
            cst::Decl::Data { constructors, .. } => {
                for c in constructors {
                    local_ctors.insert(c.name.value.symbol());
                }
            }
            cst::Decl::Newtype { constructor, .. } => {
                local_ctors.insert(constructor.value.symbol());
            }
            _ => {}
        }
    }
    for d in decls {
        match d {
            cst::Decl::Value { binders, guarded, where_clause, .. } => {
                for b in binders {
                    walk_binder_for_invalid_op(
                        b,
                        &local_value_op_targets,
                        &local_values,
                        &local_ctors,
                        errors,
                    );
                }
                walk_guarded_for_invalid_op_in_binder(
                    guarded,
                    &local_value_op_targets,
                    &local_values,
                    &local_ctors,
                    errors,
                );
                for b in where_clause {
                    if let cst::LetBinding::Value { binder, expr, .. } = b {
                        walk_binder_for_invalid_op(
                            binder,
                            &local_value_op_targets,
                            &local_values,
                            &local_ctors,
                            errors,
                        );
                        walk_expr_for_invalid_op_in_binder(
                            expr,
                            &local_value_op_targets,
                            &local_values,
                            &local_ctors,
                            errors,
                        );
                    }
                }
            }
            cst::Decl::Instance { members, .. } => {
                detect_invalid_operator_in_binder(members, errors);
            }
            _ => {}
        }
    }
}

fn walk_binder_for_invalid_op(
    b: &cst::Binder,
    op_targets: &HashMap<Symbol, Symbol>,
    local_values: &HashSet<Symbol>,
    local_ctors: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    match b {
        cst::Binder::Op { left, op, right, span } => {
            // Local function-aliased operator → invalid binder.
            // We only fire for definitively-local-and-value-aliased
            // operators; ambiguous cases (imported, unknown) are left
            // for downstream type inference.
            if op.value.module.is_none() {
                let op_sym = op.value.name.symbol();
                if let Some(target) = op_targets.get(&op_sym) {
                    if local_values.contains(target) && !local_ctors.contains(target) {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::InvalidOperatorInBinder(
                                resolve(op_sym),
                            ),
                        });
                    }
                }
            }
            walk_binder_for_invalid_op(left, op_targets, local_values, local_ctors, errors);
            walk_binder_for_invalid_op(right, op_targets, local_values, local_ctors, errors);
        }
        cst::Binder::Constructor { args, .. } => {
            for a in args {
                walk_binder_for_invalid_op(a, op_targets, local_values, local_ctors, errors);
            }
        }
        cst::Binder::Record { fields, .. } => {
            for f in fields {
                if let Some(inner) = &f.binder {
                    walk_binder_for_invalid_op(
                        inner,
                        op_targets,
                        local_values,
                        local_ctors,
                        errors,
                    );
                }
            }
        }
        cst::Binder::As { binder, .. }
        | cst::Binder::Parens { binder, .. }
        | cst::Binder::Typed { binder, .. } => {
            walk_binder_for_invalid_op(binder, op_targets, local_values, local_ctors, errors);
        }
        cst::Binder::Array { elements, .. } => {
            for e in elements {
                walk_binder_for_invalid_op(e, op_targets, local_values, local_ctors, errors);
            }
        }
        _ => {}
    }
}

fn walk_guarded_for_invalid_op_in_binder(
    g: &cst::GuardedExpr,
    op_targets: &HashMap<Symbol, Symbol>,
    local_values: &HashSet<Symbol>,
    local_ctors: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_invalid_op_in_binder(e, op_targets, local_values, local_ctors, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(b, e) => {
                            walk_binder_for_invalid_op(b, op_targets, local_values, local_ctors, errors);
                            walk_expr_for_invalid_op_in_binder(e, op_targets, local_values, local_ctors, errors);
                        }
                        cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_invalid_op_in_binder(e, op_targets, local_values, local_ctors, errors);
                        }
                    }
                }
                walk_expr_for_invalid_op_in_binder(&gd.expr, op_targets, local_values, local_ctors, errors);
            }
        }
    }
}

fn walk_expr_for_invalid_op_in_binder(
    expr: &cst::Expr,
    op_targets: &HashMap<Symbol, Symbol>,
    local_values: &HashSet<Symbol>,
    local_ctors: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    match expr {
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_invalid_op_in_binder(func, op_targets, local_values, local_ctors, errors);
            walk_expr_for_invalid_op_in_binder(arg, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_invalid_op_in_binder(func, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::Lambda { binders, body, .. } => {
            for b in binders {
                walk_binder_for_invalid_op(b, op_targets, local_values, local_ctors, errors);
            }
            walk_expr_for_invalid_op_in_binder(body, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_invalid_op_in_binder(left, op_targets, local_values, local_ctors, errors);
            walk_expr_for_invalid_op_in_binder(right, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_invalid_op_in_binder(cond, op_targets, local_values, local_ctors, errors);
            walk_expr_for_invalid_op_in_binder(then_expr, op_targets, local_values, local_ctors, errors);
            walk_expr_for_invalid_op_in_binder(else_expr, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_invalid_op_in_binder(e, op_targets, local_values, local_ctors, errors);
            }
            for alt in alts {
                for b in &alt.binders {
                    walk_binder_for_invalid_op(b, op_targets, local_values, local_ctors, errors);
                }
                walk_guarded_for_invalid_op_in_binder(&alt.result, op_targets, local_values, local_ctors, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { binder, expr, .. } = b {
                    walk_binder_for_invalid_op(binder, op_targets, local_values, local_ctors, errors);
                    walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
                }
            }
            walk_expr_for_invalid_op_in_binder(body, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { binder, expr, .. } => {
                        walk_binder_for_invalid_op(binder, op_targets, local_values, local_ctors, errors);
                        walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
                    }
                    cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { binder, expr, .. } = b {
                                walk_binder_for_invalid_op(binder, op_targets, local_values, local_ctors, errors);
                                walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_invalid_op_in_binder(result, op_targets, local_values, local_ctors, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_invalid_op_in_binder(v, op_targets, local_values, local_ctors, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
            for u in updates {
                walk_expr_for_invalid_op_in_binder(&u.value, op_targets, local_values, local_ctors, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => {
            walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::TypeAnnotation { expr, .. } => {
            walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_invalid_op_in_binder(e, op_targets, local_values, local_ctors, errors);
            }
        }
        cst::Expr::Negate { expr, .. } => {
            walk_expr_for_invalid_op_in_binder(expr, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_invalid_op_in_binder(name, op_targets, local_values, local_ctors, errors);
            walk_expr_for_invalid_op_in_binder(pattern, op_targets, local_values, local_ctors, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_invalid_op_in_binder(func, op_targets, local_values, local_ctors, errors);
            walk_expr_for_invalid_op_in_binder(left, op_targets, local_values, local_ctors, errors);
            walk_expr_for_invalid_op_in_binder(right, op_targets, local_values, local_ctors, errors);
        }
        _ => {}
    }
}

/// `type role` only valid on data/newtype/foreign-data. Reject roles
/// for type-aliases or classes (the original compiler reports
/// `UnsupportedRoleDeclaration`).
fn detect_unsupported_role_declaration(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut data_or_newtype: HashSet<Symbol> = HashSet::new();
    let mut aliases: HashSet<Symbol> = HashSet::new();
    let mut classes: HashSet<Symbol> = HashSet::new();
    for d in decls {
        match d {
            cst::Decl::Data { name, kind_sig, is_role_decl, .. } => {
                if !*is_role_decl && matches!(kind_sig, cst::KindSigSource::None) {
                    data_or_newtype.insert(name.value.symbol());
                }
            }
            cst::Decl::Newtype { name, .. } => {
                data_or_newtype.insert(name.value.symbol());
            }
            cst::Decl::ForeignData { name, .. } => {
                data_or_newtype.insert(name.value.symbol());
            }
            cst::Decl::TypeAlias { name, .. } => {
                aliases.insert(name.value.symbol());
            }
            cst::Decl::Class { name, is_kind_sig, .. } if !*is_kind_sig => {
                classes.insert(name.value.symbol());
            }
            _ => {}
        }
    }
    for d in decls {
        if let cst::Decl::Data { name, is_role_decl: true, span, .. } = d {
            let sym = name.value.symbol();
            if !data_or_newtype.contains(&sym)
                && (aliases.contains(&sym) || classes.contains(&sym))
            {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::UnsupportedRoleDeclaration(resolve(sym)),
                });
            }
        }
    }
}

/// MissingClassMember + ExtraneousClassMember.
///
/// For each instance whose class is locally declared, compare the
/// instance's defined methods against the class's declared members:
///   - members in class but not instance → MissingClassMember
///   - members in instance but not class → ExtraneousClassMember
fn detect_class_member_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut class_members: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    for d in decls {
        if let cst::Decl::Class { name, members, is_kind_sig, .. } = d {
            if !*is_kind_sig {
                let m_syms: Vec<Symbol> =
                    members.iter().map(|m| m.name.value.symbol()).collect();
                class_members.insert(name.value.symbol(), m_syms);
            }
        }
    }
    for d in decls {
        let cst::Decl::Instance { class_name, members, span, .. } = d else {
            continue;
        };
        // Only check locally-declared classes; imported classes
        // would need registry lookup, deferred.
        let cqi = class_name.to_qi();
        if cqi.module.is_some() {
            continue;
        }
        let Some(declared) = class_members.get(&cqi.name) else {
            continue;
        };
        let declared_set: HashSet<Symbol> = declared.iter().copied().collect();
        let mut instance_set: HashSet<Symbol> = HashSet::new();
        for m in members {
            // Instance members are themselves Decl::Value (or
            // Decl::TypeSignature for instance method sigs); only
            // count Value definitions toward the implementation
            // set — TypeSignature is a sig, not an impl.
            if let cst::Decl::Value { name, .. } = m {
                instance_set.insert(name.value.symbol());
            }
        }
        // The reference compiler permits the FULLY-empty instance
        // body (`instance Foo X`) — common when a `Fail` constraint
        // makes the instance unreachable. Only emit MissingClassMember
        // for *partial* implementations.
        if !instance_set.is_empty() {
            for n in &declared_set {
                if !instance_set.contains(n) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::MissingClassMember(resolve(*n)),
                    });
                }
            }
        }
        // Extraneous = in instance but not declared.
        for n in &instance_set {
            if !declared_set.contains(n) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::ExtraneousClassMember(resolve(*n)),
                });
            }
        }
    }
}

/// `b :: T2; b = a` where `a :: T1` and `T1` ≠ `T2` (both
/// concrete) — these are clear `TypesDoNotUnify`. Catches cases
/// like `a :: { field :: Int }; b :: { field :: String }; b = a`
/// without requiring sig-pinning.
fn detect_value_decl_sig_alias_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Build name → signed-type map for top-level value sigs.
    let mut sig_of: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
    for d in decls {
        if let cst::Decl::TypeSignature { name, ty, .. } = d {
            sig_of.insert(name.value.symbol(), ty);
        }
    }
    if sig_of.is_empty() {
        return;
    }
    // Collect local zero-parameter type aliases (`type Path =
    // String`). The alpha-eq below uses these to canonicalise
    // each side before comparing, so a sig `… -> String` paired
    // with a body `unwrap :: … -> Path` (where Path = String)
    // isn't false-flagged as a mismatch.
    let mut zero_param_aliases: HashMap<Symbol, Symbol> = HashMap::new();
    for d in decls {
        if let cst::Decl::TypeAlias { name, type_vars, ty, .. } = d {
            if !type_vars.is_empty() {
                continue;
            }
            let body = peel_parens(ty);
            if let cst::TypeExpr::Constructor { name: target, .. } = body {
                let q = target.to_qi();
                if q.module.is_none() {
                    zero_param_aliases.insert(name.value.symbol(), q.name);
                }
            }
        }
    }
    for d in decls {
        let cst::Decl::Value { name, binders, guarded, .. } = d else {
            continue;
        };
        if !binders.is_empty() {
            continue;
        }
        let cst::GuardedExpr::Unconditional(body) = guarded else {
            continue;
        };
        // Body must be a bare Var (modulo Parens / TypeAnnotation).
        let inner = peel_expr_parens(body);
        let cst::Expr::Var { name: ref_name, .. } = inner else {
            continue;
        };
        let qi = ref_name.to_qi();
        if qi.module.is_some() {
            continue;
        }
        let n = name.value.symbol();
        let Some(my_sig) = sig_of.get(&n) else {
            continue;
        };
        let Some(other_sig) = sig_of.get(&qi.name) else {
            continue;
        };
        // Skip when either side has forall/wildcard/constraints —
        // could be legitimately polymorphic, or the constraint
        // may discharge to a matching shape (`f :: C T => Int`,
        // `v :: Int; v = f` is valid when `C T` has an instance).
        if type_expr_has_forall(my_sig) || type_expr_has_forall(other_sig) {
            continue;
        }
        if type_expr_has_wildcard(my_sig) || type_expr_has_wildcard(other_sig) {
            continue;
        }
        if type_expr_has_constraint(my_sig)
            || type_expr_has_constraint(other_sig)
        {
            continue;
        }
        if !type_expr_alpha_eq_modulo_aliases(my_sig, other_sig, &zero_param_aliases) {
            errors.push(ValidationError {
                span: name.span,
                kind: ValidationErrorKind::ValueDeclSigAliasMismatch(resolve(n)),
            });
        }
    }
}

/// `foo :: Number; foo = true` — body is a primitive literal
/// whose primitive-type tag clashes with the declared sig's head
/// constructor. Reference compiler reports as `TypesDoNotUnify`.
fn detect_literal_body_sig_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Skip the entire check when the module declares any type
    // alias whose name shadows a primitive (e.g. `type Number =
    // Int`). The CST-level shadow rewrites `Number`-as-sig to mean
    // something else, and we don't expand aliases here.
    let mut local_alias_names: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::TypeAlias { name, .. } = d {
            local_alias_names.insert(name.value.symbol());
        }
    }
    let mut sig_of: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
    for d in decls {
        if let cst::Decl::TypeSignature { name, ty, .. } = d {
            sig_of.insert(name.value.symbol(), ty);
        }
    }
    if !sig_of.is_empty() {
        for d in decls {
            check_literal_body_decl(d, &sig_of, &local_alias_names, errors);
        }
    }
    for d in decls {
        if let cst::Decl::Instance { members, .. } = d {
            let mut inst_sigs: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
            for memb in members {
                if let cst::Decl::TypeSignature { name, ty, .. } = memb {
                    inst_sigs.insert(name.value.symbol(), ty);
                }
            }
            for memb in members {
                if !inst_sigs.is_empty() {
                    check_literal_body_decl(
                        memb,
                        &inst_sigs,
                        &local_alias_names,
                        errors,
                    );
                }
                // Also walk the instance member body's
                // where-clause for nested literal-body sig
                // mismatches (`bar :: String; bar = 1`).
                if let cst::Decl::Value { where_clause, guarded, .. } = memb {
                    walk_where_for_literal_body_sig_mismatch(
                        where_clause,
                        &local_alias_names,
                        errors,
                    );
                    walk_guarded_for_literal_body_sig_mismatch(
                        guarded,
                        &local_alias_names,
                        errors,
                    );
                }
            }
        }
    }
    // Top-level value decls' where-clauses + body let-bindings.
    for d in decls {
        if let cst::Decl::Value { where_clause, guarded, .. } = d {
            walk_where_for_literal_body_sig_mismatch(
                where_clause,
                &local_alias_names,
                errors,
            );
            walk_guarded_for_literal_body_sig_mismatch(
                guarded,
                &local_alias_names,
                errors,
            );
        }
    }
}

fn walk_where_for_literal_body_sig_mismatch(
    bindings: &[cst::LetBinding],
    local_alias_names: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    let mut sigs: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
    for lb in bindings {
        if let cst::LetBinding::Signature { name, ty, .. } = lb {
            sigs.insert(name.value.symbol(), ty);
        }
    }
    if sigs.is_empty() {
        return;
    }
    for lb in bindings {
        if let cst::LetBinding::Value { binder, expr, .. } = lb {
            if let cst::Binder::Var { name, span } = binder {
                let n = name.value.symbol();
                if let Some(sig) = sigs.get(&n) {
                    let dummy = cst::Decl::Value {
                        span: *span,
                        name: name.clone(),
                        binders: Vec::new(),
                        guarded: cst::GuardedExpr::Unconditional(Box::new(
                            expr.clone(),
                        )),
                        where_clause: Vec::new(),
                        doc_comments: Vec::new(),
                    };
                    let mut local_sigs: HashMap<Symbol, &cst::TypeExpr> =
                        HashMap::new();
                    local_sigs.insert(n, *sig);
                    check_literal_body_decl(
                        &dummy,
                        &local_sigs,
                        local_alias_names,
                        errors,
                    );
                }
            }
        }
    }
}

fn walk_guarded_for_literal_body_sig_mismatch(
    g: &cst::GuardedExpr,
    local_alias_names: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_literal_body_sig_mismatch(e, local_alias_names, errors);
        }
        cst::GuardedExpr::Guarded(guards) => {
            for gd in guards {
                walk_expr_for_literal_body_sig_mismatch(
                    &gd.expr,
                    local_alias_names,
                    errors,
                );
            }
        }
    }
}

fn walk_expr_for_literal_body_sig_mismatch(
    e: &cst::Expr,
    local_alias_names: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    match e {
        cst::Expr::Let { bindings, body, .. } => {
            walk_where_for_literal_body_sig_mismatch(
                bindings,
                local_alias_names,
                errors,
            );
            walk_expr_for_literal_body_sig_mismatch(body, local_alias_names, errors);
        }
        cst::Expr::Lambda { body, .. } => {
            walk_expr_for_literal_body_sig_mismatch(body, local_alias_names, errors);
        }
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_literal_body_sig_mismatch(func, local_alias_names, errors);
            walk_expr_for_literal_body_sig_mismatch(arg, local_alias_names, errors);
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::Negate { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. } => {
            walk_expr_for_literal_body_sig_mismatch(expr, local_alias_names, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_literal_body_sig_mismatch(cond, local_alias_names, errors);
            walk_expr_for_literal_body_sig_mismatch(then_expr, local_alias_names, errors);
            walk_expr_for_literal_body_sig_mismatch(else_expr, local_alias_names, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_literal_body_sig_mismatch(e, local_alias_names, errors);
            }
            for alt in alts {
                walk_guarded_for_literal_body_sig_mismatch(
                    &alt.result,
                    local_alias_names,
                    errors,
                );
            }
        }
        _ => {}
    }
}

fn check_literal_body_decl(
    d: &cst::Decl,
    sig_of: &HashMap<Symbol, &cst::TypeExpr>,
    local_alias_names: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    let cst::Decl::Value { name, binders, guarded, .. } = d else {
        return;
    };
    let cst::GuardedExpr::Unconditional(body) = guarded else {
        return;
    };
    let n = name.value.symbol();
    let Some(full_sig) = sig_of.get(&n) else {
        return;
    };
    if type_expr_has_forall(full_sig)
        || type_expr_has_wildcard(full_sig)
        || type_expr_has_constraint(full_sig)
    {
        return;
    }
    // Strip `binders.len()` arrows from the sig to get the
    // expected return type for this equation.
    let mut sig_cur: &cst::TypeExpr = full_sig;
    for _ in 0..binders.len() {
        sig_cur = peel_parens(sig_cur);
        if let cst::TypeExpr::Function { to, .. } = sig_cur {
            sig_cur = to;
        } else {
            return;
        }
    }
    let sig = sig_cur;
    // Skip when the sig's Constructor name shadows a local
    // type-alias — `type Number = Int; z :: Number; z = 0` is
    // valid through alias expansion which we don't perform here.
    if let cst::TypeExpr::Constructor { name: con, .. } = peel_parens(sig) {
        let qi = con.to_qi();
        if qi.module.is_none() && local_alias_names.contains(&qi.name) {
            return;
        }
    }
    let inner = peel_expr_parens(body);
    let lit_kind = match inner {
        cst::Expr::Literal { lit, .. } => Some(literal_primitive_name(lit)),
        cst::Expr::Negate { expr, .. } => match peel_expr_parens(expr) {
            cst::Expr::Literal { lit, .. } => Some(literal_primitive_name(lit)),
            _ => None,
        },
        _ => None,
    };
    if let Some(lit_name) = lit_kind {
        let sig_inner = peel_parens(sig);
        if let Some(sig_name) = primitive_con_name(sig_inner) {
            if !primitives_compatible(lit_name, sig_name) {
                errors.push(ValidationError {
                    span: name.span,
                    kind: ValidationErrorKind::LiteralBodySigMismatch(resolve(n)),
                });
            }
        }
        return;
    }
    // Record literal body vs record sig: compare each field's
    // literal type to the sig's field type. Fires only when ALL
    // fields are primitive literals with matching names.
    if let cst::Expr::Record { fields: body_fields, .. } = inner {
        let sig_inner = peel_parens(sig);
        let sig_fields: Option<Vec<(Symbol, &cst::TypeExpr)>> = match sig_inner {
            cst::TypeExpr::Record { fields, .. } => Some(
                fields
                    .iter()
                    .map(|f| (f.label.value.symbol(), &f.ty))
                    .collect(),
            ),
            cst::TypeExpr::Row { fields, tail: None, is_record: true, .. } => {
                Some(
                    fields
                        .iter()
                        .map(|f| (f.label.value.symbol(), &f.ty))
                        .collect(),
                )
            }
            _ => None,
        };
        let Some(sig_fields) = sig_fields else {
            return;
        };
        let sig_map: HashMap<Symbol, &cst::TypeExpr> =
            sig_fields.into_iter().collect();
        let mut bad = false;
        for f in body_fields {
            // Skip pun fields and update fields — only literal-
            // valued fields participate.
            if f.is_update {
                return;
            }
            let Some(value) = &f.value else { continue };
            let label_sym = f.label.value.symbol();
            let Some(field_sig) = sig_map.get(&label_sym) else {
                // Extra field not in sig — that's
                // AdditionalProperty, separate detector.
                return;
            };
            if type_expr_has_forall(field_sig)
                || type_expr_has_wildcard(field_sig)
                || type_expr_has_constraint(field_sig)
            {
                return;
            }
            let v_inner = peel_expr_parens(value);
            let v_lit = match v_inner {
                cst::Expr::Literal { lit, .. } => {
                    Some(literal_primitive_name(lit))
                }
                cst::Expr::Negate { expr, .. } => match peel_expr_parens(expr) {
                    cst::Expr::Literal { lit, .. } => {
                        Some(literal_primitive_name(lit))
                    }
                    _ => None,
                },
                _ => None,
            };
            let Some(v_lit) = v_lit else {
                return;
            };
            let f_sig_inner = peel_parens(field_sig);
            // Skip when the field sig's Constructor matches a
            // local type-alias.
            if let cst::TypeExpr::Constructor { name: con, .. } = f_sig_inner {
                let qi = con.to_qi();
                if qi.module.is_none() && local_alias_names.contains(&qi.name) {
                    return;
                }
            }
            let Some(f_sig_name) = primitive_con_name(f_sig_inner) else {
                return;
            };
            if !primitives_compatible(v_lit, f_sig_name) {
                bad = true;
                break;
            }
        }
        if bad {
            errors.push(ValidationError {
                span: name.span,
                kind: ValidationErrorKind::LiteralBodySigMismatch(resolve(n)),
            });
        }
    }
}

fn literal_primitive_name(lit: &cst::Literal) -> &'static str {
    match lit {
        cst::Literal::Int(_) => "Int",
        cst::Literal::Float(_) => "Number",
        cst::Literal::String(_) => "String",
        cst::Literal::Char(_) => "Char",
        cst::Literal::Boolean(_) => "Boolean",
        cst::Literal::Array(_) => "Array",
    }
}

fn primitive_con_name(te: &cst::TypeExpr) -> Option<&'static str> {
    if let cst::TypeExpr::Constructor { name, .. } = te {
        let qi = name.to_qi();
        let n = resolve(qi.name);
        match n.as_str() {
            "Int" => Some("Int"),
            "Number" => Some("Number"),
            "String" => Some("String"),
            "Char" => Some("Char"),
            "Boolean" => Some("Boolean"),
            _ => None,
        }
    } else {
        None
    }
}

fn primitives_compatible(lit: &str, sig: &str) -> bool {
    // Exact match always compatible.
    if lit == sig {
        return true;
    }
    // PureScript Int/Number numeric literals: an Int literal can
    // sometimes flow to a polymorphic numeric position, but here
    // sig is concrete. Different primitives → mismatch.
    false
}

fn type_expr_has_constraint(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Constrained { .. } => true,
        cst::TypeExpr::Forall { ty, .. }
        | cst::TypeExpr::Parens { ty, .. }
        | cst::TypeExpr::Kinded { ty, .. } => type_expr_has_constraint(ty),
        cst::TypeExpr::Function { from, to, .. } => {
            type_expr_has_constraint(from) || type_expr_has_constraint(to)
        }
        _ => false,
    }
}

fn type_expr_has_wildcard(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Wildcard { .. } => true,
        cst::TypeExpr::Parens { ty, .. } | cst::TypeExpr::Kinded { ty, .. } => {
            type_expr_has_wildcard(ty)
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            type_expr_has_wildcard(constructor) || type_expr_has_wildcard(arg)
        }
        cst::TypeExpr::Function { from, to, .. } => {
            type_expr_has_wildcard(from) || type_expr_has_wildcard(to)
        }
        cst::TypeExpr::Forall { ty, .. }
        | cst::TypeExpr::Constrained { ty, .. } => type_expr_has_wildcard(ty),
        cst::TypeExpr::Record { fields, .. } => {
            fields.iter().any(|f| type_expr_has_wildcard(&f.ty))
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            fields.iter().any(|f| type_expr_has_wildcard(&f.ty))
                || tail.as_ref().map_or(false, |t| type_expr_has_wildcard(t))
        }
        _ => false,
    }
}

/// Compare an instance member's explicit signature against the
/// class's declared member signature (after substituting class
/// type-vars with the instance's type arguments). Mismatches are
/// reference-compiler `TypesDoNotUnify`. CST-only — restricted to
/// locally-declared classes; imported classes' member sigs aren't
/// reachable here.
fn detect_instance_member_sig_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // class_name → (type_vars, member_name → member_ty)
    let mut class_info: HashMap<
        Symbol,
        (Vec<Symbol>, HashMap<Symbol, &cst::TypeExpr>),
    > = HashMap::new();
    for d in decls {
        if let cst::Decl::Class { name, type_vars, members, is_kind_sig: false, .. } =
            d
        {
            let vs: Vec<Symbol> =
                type_vars.iter().map(|v| v.value.symbol()).collect();
            let mut m: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
            for memb in members {
                m.insert(memb.name.value.symbol(), &memb.ty);
            }
            class_info.insert(name.value.symbol(), (vs, m));
        }
    }
    if class_info.is_empty() {
        return;
    }
    for d in decls {
        let cst::Decl::Instance { class_name, types, members, .. } = d else {
            continue;
        };
        let cqi = class_name.to_qi();
        if cqi.module.is_some() {
            continue;
        }
        let Some((cls_vars, cls_members)) = class_info.get(&cqi.name) else {
            continue;
        };
        if cls_vars.len() != types.len() {
            continue;
        }
        let subst: HashMap<Symbol, &cst::TypeExpr> = cls_vars
            .iter()
            .zip(types.iter())
            .map(|(v, t)| (*v, t))
            .collect();
        for memb in members {
            let cst::Decl::TypeSignature { name, ty: inst_sig, span, .. } = memb
            else {
                continue;
            };
            let Some(class_sig) = cls_members.get(&name.value.symbol()) else {
                continue;
            };
            // PureScript allows instance member sigs to be MORE
            // general than the class's expected sig (e.g.
            // `instance Eq Number where eq :: forall x y. x -> y
            // -> Boolean`). To stay conservative we only flag
            // when both sides are forall-free post-substitution
            // — those are clearly-mismatched concrete shapes.
            let expected = subst_type_expr(class_sig, &subst);
            if type_expr_has_forall(&expected) || type_expr_has_forall(inst_sig)
            {
                continue;
            }
            // Skip when either side uses row/record syntax (e.g. `{ | r }` vs
            // `Record r` — syntactically distinct but semantically equivalent).
            if type_expr_has_row_or_record(&expected)
                || type_expr_has_row_or_record(inst_sig)
            {
                continue;
            }
            if !type_expr_alpha_eq(&expected, inst_sig) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::InstanceMemberSigMismatch(
                        resolve(name.value.symbol()),
                    ),
                });
            }
        }
    }
}

/// Substitute `subst[var]` for each `TypeExpr::Var { var }` in
/// `te`, leaving everything else structurally identical. Used by
/// `detect_instance_member_sig_mismatch` to specialize the class's
/// member sig to the instance's type arguments before comparison.
fn subst_type_expr(
    te: &cst::TypeExpr,
    subst: &HashMap<Symbol, &cst::TypeExpr>,
) -> cst::TypeExpr {
    match te {
        cst::TypeExpr::Var { name, span } => {
            if let Some(replacement) = subst.get(&name.value.symbol()) {
                (*replacement).clone()
            } else {
                cst::TypeExpr::Var { name: name.clone(), span: *span }
            }
        }
        cst::TypeExpr::App { constructor, arg, span } => cst::TypeExpr::App {
            constructor: Box::new(subst_type_expr(constructor, subst)),
            arg: Box::new(subst_type_expr(arg, subst)),
            span: *span,
        },
        cst::TypeExpr::Function { from, to, span } => cst::TypeExpr::Function {
            from: Box::new(subst_type_expr(from, subst)),
            to: Box::new(subst_type_expr(to, subst)),
            span: *span,
        },
        cst::TypeExpr::Forall { vars, ty, span } => {
            // Drop substitutions for shadowed names.
            let mut inner = subst.clone();
            for (v, _, _) in vars {
                inner.remove(&v.value.symbol());
            }
            cst::TypeExpr::Forall {
                vars: vars.clone(),
                ty: Box::new(subst_type_expr(ty, &inner)),
                span: *span,
            }
        }
        cst::TypeExpr::Constrained { constraints, ty, span } => {
            let cs: Vec<cst::Constraint> = constraints
                .iter()
                .map(|c| cst::Constraint {
                    span: c.span,
                    class: c.class.clone(),
                    args: c.args.iter().map(|a| subst_type_expr(a, subst)).collect(),
                })
                .collect();
            cst::TypeExpr::Constrained {
                constraints: cs,
                ty: Box::new(subst_type_expr(ty, subst)),
                span: *span,
            }
        }
        cst::TypeExpr::Parens { ty, span } => cst::TypeExpr::Parens {
            ty: Box::new(subst_type_expr(ty, subst)),
            span: *span,
        },
        cst::TypeExpr::Kinded { ty, kind, span } => cst::TypeExpr::Kinded {
            ty: Box::new(subst_type_expr(ty, subst)),
            kind: Box::new(subst_type_expr(kind, subst)),
            span: *span,
        },
        cst::TypeExpr::Record { fields, span } => cst::TypeExpr::Record {
            fields: fields
                .iter()
                .map(|f| cst::TypeField {
                    span: f.span,
                    label: f.label.clone(),
                    ty: subst_type_expr(&f.ty, subst),
                })
                .collect(),
            span: *span,
        },
        cst::TypeExpr::Row { fields, tail, span, is_record } => cst::TypeExpr::Row {
            fields: fields
                .iter()
                .map(|f| cst::TypeField {
                    span: f.span,
                    label: f.label.clone(),
                    ty: subst_type_expr(&f.ty, subst),
                })
                .collect(),
            tail: tail.as_ref().map(|t| Box::new(subst_type_expr(t, subst))),
            span: *span,
            is_record: *is_record,
        },
        cst::TypeExpr::TypeOp { left, op, right, span } => cst::TypeExpr::TypeOp {
            left: Box::new(subst_type_expr(left, subst)),
            op: op.clone(),
            right: Box::new(subst_type_expr(right, subst)),
            span: *span,
        },
        _ => te.clone(),
    }
}

fn type_expr_has_forall(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Forall { .. } => true,
        cst::TypeExpr::Parens { ty, .. } | cst::TypeExpr::Kinded { ty, .. } => {
            type_expr_has_forall(ty)
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            type_expr_has_forall(constructor) || type_expr_has_forall(arg)
        }
        cst::TypeExpr::Function { from, to, .. } => {
            type_expr_has_forall(from) || type_expr_has_forall(to)
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            constraints
                .iter()
                .any(|c| c.args.iter().any(type_expr_has_forall))
                || type_expr_has_forall(ty)
        }
        cst::TypeExpr::Record { fields, .. } => {
            fields.iter().any(|f| type_expr_has_forall(&f.ty))
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            fields.iter().any(|f| type_expr_has_forall(&f.ty))
                || tail.as_ref().map_or(false, |t| type_expr_has_forall(t))
        }
        _ => false,
    }
}

/// True if `te` contains a `Row` or `Record` type expression anywhere.
/// Used to skip instance-member-sig-mismatch checks when row/record sugar
/// may be in use (e.g. `{ | r }` ≡ `Record r` but they're structurally
/// distinct in the CST).
fn type_expr_has_row_or_record(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Record { .. } | cst::TypeExpr::Row { .. } => true,
        cst::TypeExpr::Parens { ty, .. } | cst::TypeExpr::Kinded { ty, .. } => {
            type_expr_has_row_or_record(ty)
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            type_expr_has_row_or_record(constructor) || type_expr_has_row_or_record(arg)
        }
        cst::TypeExpr::Function { from, to, .. } => {
            type_expr_has_row_or_record(from) || type_expr_has_row_or_record(to)
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            constraints
                .iter()
                .any(|c| c.args.iter().any(type_expr_has_row_or_record))
                || type_expr_has_row_or_record(ty)
        }
        _ => false,
    }
}

/// Structural equality of two `TypeExpr`s, modulo Parens wrappers.
/// Doesn't handle alpha-renaming under foralls — adequate for the
/// current `InstanceSigs` fixtures whose member sigs are
/// monomorphic post-substitution.
/// Alpha-eq with zero-parameter alias resolution: a `Constructor`
/// reference X is treated as Y when the module declares `type X
/// = Y`. Used by `detect_value_decl_sig_alias_mismatch` so a
/// sig of `… -> String` paired with a body `f :: … -> Path`
/// (where Path is a local `type Path = String` alias) doesn't
/// false-flag as a mismatch.
fn type_expr_alpha_eq_modulo_aliases(
    a: &cst::TypeExpr,
    b: &cst::TypeExpr,
    aliases: &HashMap<Symbol, Symbol>,
) -> bool {
    fn resolve_ctor(name: Symbol, aliases: &HashMap<Symbol, Symbol>) -> Symbol {
        let mut cur = name;
        let mut seen: std::collections::HashSet<Symbol> =
            std::collections::HashSet::new();
        while let Some(next) = aliases.get(&cur) {
            if !seen.insert(cur) {
                break;
            }
            cur = *next;
        }
        cur
    }
    let a = peel_parens(a);
    let b = peel_parens(b);
    match (a, b) {
        (
            cst::TypeExpr::Var { name: n1, .. },
            cst::TypeExpr::Var { name: n2, .. },
        ) => n1.value.symbol() == n2.value.symbol(),
        (
            cst::TypeExpr::Constructor { name: n1, .. },
            cst::TypeExpr::Constructor { name: n2, .. },
        ) => {
            let q1 = n1.to_qi();
            let q2 = n2.to_qi();
            resolve_ctor(q1.name, aliases) == resolve_ctor(q2.name, aliases)
        }
        (
            cst::TypeExpr::App { constructor: c1, arg: a1, .. },
            cst::TypeExpr::App { constructor: c2, arg: a2, .. },
        ) => {
            type_expr_alpha_eq_modulo_aliases(c1, c2, aliases)
                && type_expr_alpha_eq_modulo_aliases(a1, a2, aliases)
        }
        (
            cst::TypeExpr::Function { from: f1, to: t1, .. },
            cst::TypeExpr::Function { from: f2, to: t2, .. },
        ) => {
            type_expr_alpha_eq_modulo_aliases(f1, f2, aliases)
                && type_expr_alpha_eq_modulo_aliases(t1, t2, aliases)
        }
        (
            cst::TypeExpr::StringLiteral { value: v1, .. },
            cst::TypeExpr::StringLiteral { value: v2, .. },
        ) => v1 == v2,
        (
            cst::TypeExpr::IntLiteral { value: v1, .. },
            cst::TypeExpr::IntLiteral { value: v2, .. },
        ) => v1 == v2,
        (cst::TypeExpr::Wildcard { .. }, cst::TypeExpr::Wildcard { .. }) => true,
        _ => false,
    }
}

fn type_expr_alpha_eq(a: &cst::TypeExpr, b: &cst::TypeExpr) -> bool {
    let a = peel_parens(a);
    let b = peel_parens(b);
    match (a, b) {
        (
            cst::TypeExpr::Var { name: n1, .. },
            cst::TypeExpr::Var { name: n2, .. },
        ) => n1.value.symbol() == n2.value.symbol(),
        (
            cst::TypeExpr::Constructor { name: n1, .. },
            cst::TypeExpr::Constructor { name: n2, .. },
        ) => {
            let q1 = n1.to_qi();
            let q2 = n2.to_qi();
            q1.name == q2.name
        }
        (
            cst::TypeExpr::App { constructor: c1, arg: a1, .. },
            cst::TypeExpr::App { constructor: c2, arg: a2, .. },
        ) => type_expr_alpha_eq(c1, c2) && type_expr_alpha_eq(a1, a2),
        (
            cst::TypeExpr::Function { from: f1, to: t1, .. },
            cst::TypeExpr::Function { from: f2, to: t2, .. },
        ) => type_expr_alpha_eq(f1, f2) && type_expr_alpha_eq(t1, t2),
        (
            cst::TypeExpr::StringLiteral { value: v1, .. },
            cst::TypeExpr::StringLiteral { value: v2, .. },
        ) => v1 == v2,
        (
            cst::TypeExpr::IntLiteral { value: v1, .. },
            cst::TypeExpr::IntLiteral { value: v2, .. },
        ) => v1 == v2,
        (cst::TypeExpr::Wildcard { .. }, cst::TypeExpr::Wildcard { .. }) => true,
        _ => false,
    }
}

/// IncorrectConstructorArity. Pattern uses a constructor with the
/// wrong number of arguments. Walk every binder in every value
/// decl / instance member; for each `Binder::Constructor` resolve
/// the local arity and compare.
fn detect_incorrect_constructor_arity(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut local_ctor_arity: HashMap<Symbol, usize> = HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Data { constructors, .. } => {
                for c in constructors {
                    local_ctor_arity.insert(c.name.value.symbol(), c.fields.len());
                }
            }
            cst::Decl::Newtype { constructor, .. } => {
                // Newtype ctor has exactly 1 field.
                local_ctor_arity.insert(constructor.value.symbol(), 1);
            }
            _ => {}
        }
    }
    for d in decls {
        match d {
            cst::Decl::Value { binders, guarded, where_clause, .. } => {
                for b in binders {
                    walk_binder_for_ctor_arity(b, &local_ctor_arity, errors);
                }
                walk_guarded_for_ctor_arity(guarded, &local_ctor_arity, errors);
                for b in where_clause {
                    if let cst::LetBinding::Value { binder, expr, .. } = b {
                        walk_binder_for_ctor_arity(binder, &local_ctor_arity, errors);
                        walk_expr_for_ctor_arity(expr, &local_ctor_arity, errors);
                    }
                }
            }
            cst::Decl::Instance { members, .. } => {
                detect_incorrect_constructor_arity(members, errors);
            }
            _ => {}
        }
    }
}

fn walk_binder_for_ctor_arity(
    b: &cst::Binder,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match b {
        cst::Binder::Constructor { name, args, span } => {
            if name.module.is_none() {
                if let Some(&expected) = arities.get(&name.name.symbol()) {
                    let got = args.len();
                    if got != expected {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::IncorrectConstructorArity {
                                ctor: resolve(name.name.symbol()),
                                expected,
                                got,
                            },
                        });
                    }
                }
            }
            for a in args {
                walk_binder_for_ctor_arity(a, arities, errors);
            }
        }
        cst::Binder::Record { fields, .. } => {
            for f in fields {
                if let Some(inner) = &f.binder {
                    walk_binder_for_ctor_arity(inner, arities, errors);
                }
            }
        }
        cst::Binder::As { binder, .. }
        | cst::Binder::Parens { binder, .. }
        | cst::Binder::Typed { binder, .. } => {
            walk_binder_for_ctor_arity(binder, arities, errors);
        }
        cst::Binder::Array { elements, .. } => {
            for e in elements {
                walk_binder_for_ctor_arity(e, arities, errors);
            }
        }
        cst::Binder::Op { left, right, .. } => {
            walk_binder_for_ctor_arity(left, arities, errors);
            walk_binder_for_ctor_arity(right, arities, errors);
        }
        _ => {}
    }
}

fn walk_guarded_for_ctor_arity(
    g: &cst::GuardedExpr,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_ctor_arity(e, arities, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(b, e) => {
                            walk_binder_for_ctor_arity(b, arities, errors);
                            walk_expr_for_ctor_arity(e, arities, errors);
                        }
                        cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_ctor_arity(e, arities, errors);
                        }
                    }
                }
                walk_expr_for_ctor_arity(&gd.expr, arities, errors);
            }
        }
    }
}

fn walk_expr_for_ctor_arity(
    expr: &cst::Expr,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match expr {
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_ctor_arity(func, arities, errors);
            walk_expr_for_ctor_arity(arg, arities, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_ctor_arity(func, arities, errors);
        }
        cst::Expr::Lambda { binders, body, .. } => {
            for b in binders {
                walk_binder_for_ctor_arity(b, arities, errors);
            }
            walk_expr_for_ctor_arity(body, arities, errors);
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_ctor_arity(left, arities, errors);
            walk_expr_for_ctor_arity(right, arities, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_ctor_arity(cond, arities, errors);
            walk_expr_for_ctor_arity(then_expr, arities, errors);
            walk_expr_for_ctor_arity(else_expr, arities, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_ctor_arity(e, arities, errors);
            }
            for alt in alts {
                for b in &alt.binders {
                    walk_binder_for_ctor_arity(b, arities, errors);
                }
                walk_guarded_for_ctor_arity(&alt.result, arities, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { binder, expr, .. } = b {
                    walk_binder_for_ctor_arity(binder, arities, errors);
                    walk_expr_for_ctor_arity(expr, arities, errors);
                }
            }
            walk_expr_for_ctor_arity(body, arities, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { binder, expr, .. } => {
                        walk_binder_for_ctor_arity(binder, arities, errors);
                        walk_expr_for_ctor_arity(expr, arities, errors);
                    }
                    cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_ctor_arity(expr, arities, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { binder, expr, .. } = b {
                                walk_binder_for_ctor_arity(binder, arities, errors);
                                walk_expr_for_ctor_arity(expr, arities, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_ctor_arity(result, arities, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_ctor_arity(v, arities, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_ctor_arity(expr, arities, errors);
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_ctor_arity(expr, arities, errors);
            for u in updates {
                walk_expr_for_ctor_arity(&u.value, arities, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => walk_expr_for_ctor_arity(expr, arities, errors),
        cst::Expr::TypeAnnotation { expr, .. } => {
            walk_expr_for_ctor_arity(expr, arities, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_ctor_arity(e, arities, errors);
            }
        }
        cst::Expr::Negate { expr, .. } => walk_expr_for_ctor_arity(expr, arities, errors),
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_ctor_arity(name, arities, errors);
            walk_expr_for_ctor_arity(pattern, arities, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_ctor_arity(func, arities, errors);
            walk_expr_for_ctor_arity(left, arities, errors);
            walk_expr_for_ctor_arity(right, arities, errors);
        }
        _ => {}
    }
}

/// UndefinedTypeVariable. Scoped at:
///   - Type alias body: free type vars must be in `type_vars` (or
///     locally bound by inner forall).
///   - Class superclass constraints: free type vars must be in
///     `class.type_vars`.
fn detect_undefined_type_variables(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::TypeAlias { type_vars, ty, .. } => {
                let mut bound: HashSet<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                check_free_type_vars(ty, &mut bound, errors);
            }
            cst::Decl::Class { type_vars, constraints, members, is_kind_sig, .. }
                if !*is_kind_sig =>
            {
                let mut bound: HashSet<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                for c in constraints {
                    for arg in &c.args {
                        let mut local = bound.clone();
                        check_free_type_vars(arg, &mut local, errors);
                    }
                    let _ = &mut bound;
                }
                // Class members: each member sig sees the class's
                // type-vars as bound (plus implicit quantification
                // for any other free vars in the member sig).
                for m in members {
                    check_signature_type(&m.ty, Some(&bound), errors);
                }
            }
            cst::Decl::TypeSignature { ty, .. } => {
                // Top-level signatures: implicit forall quantifies
                // every free type var. Inner explicit foralls still
                // need to declare vars before referencing them.
                check_signature_type(ty, None, errors);
            }
            cst::Decl::Foreign { ty, .. } => {
                check_signature_type(ty, None, errors);
            }
            cst::Decl::Instance { members, .. } => {
                detect_undefined_type_variables(members, errors);
            }
            _ => {}
        }
    }
}

/// Check a top-level / class-member / instance-member type
/// signature, treating all "outer-free" type vars as implicitly
/// quantified. `extra_bound` lets the caller pre-bind class
/// type-vars (so a class member sig sees them as in-scope).
fn check_signature_type(
    ty: &cst::TypeExpr,
    extra_bound: Option<&HashSet<Symbol>>,
    errors: &mut Vec<ValidationError>,
) {
    let mut all_free: HashSet<Symbol> = HashSet::new();
    collect_free_outer_type_vars(ty, &mut all_free);
    let mut bound = all_free;
    if let Some(extra) = extra_bound {
        for s in extra {
            bound.insert(*s);
        }
    }
    check_free_type_vars(ty, &mut bound, errors);
}

/// Collect type-vars that appear free at the OUTERMOST level —
/// i.e. NOT bound by any explicit `forall`. These are implicitly
/// quantified at the top of the signature, so they don't trigger
/// `UndefinedTypeVariable` when the outer scope walks them.
fn collect_free_outer_type_vars(
    te: &cst::TypeExpr,
    out: &mut HashSet<Symbol>,
) {
    fn go(te: &cst::TypeExpr, bound: &mut HashSet<Symbol>, out: &mut HashSet<Symbol>) {
        match te {
            cst::TypeExpr::Var { name, .. } => {
                let sym = name.value.symbol();
                if !bound.contains(&sym) {
                    out.insert(sym);
                }
            }
            cst::TypeExpr::Constructor { .. }
            | cst::TypeExpr::Hole { .. }
            | cst::TypeExpr::Wildcard { .. }
            | cst::TypeExpr::StringLiteral { .. }
            | cst::TypeExpr::IntLiteral { .. } => {}
            cst::TypeExpr::App { constructor, arg, .. } => {
                go(constructor, bound, out);
                go(arg, bound, out);
            }
            cst::TypeExpr::Function { from, to, .. } => {
                go(from, bound, out);
                go(to, bound, out);
            }
            cst::TypeExpr::Forall { vars, ty, .. } => {
                // Pre-bind all forall vars BEFORE walking kind
                // annotations: a forall's vars are scoped over the
                // whole forall, not left-to-right. Order issues
                // (referencing a sibling not yet declared) are
                // caught by `check_free_type_vars` later, not by
                // this "free outer var" pass.
                let mut new_bound = bound.clone();
                for (v, _, _) in vars {
                    new_bound.insert(v.value.symbol());
                }
                for (_, _, kind) in vars {
                    if let Some(k) = kind {
                        go(k, &mut new_bound, out);
                    }
                }
                go(ty, &mut new_bound, out);
            }
            cst::TypeExpr::Constrained { constraints, ty, .. } => {
                for c in constraints {
                    for arg in &c.args {
                        go(arg, bound, out);
                    }
                }
                go(ty, bound, out);
            }
            cst::TypeExpr::Record { fields, .. } => {
                for f in fields {
                    go(&f.ty, bound, out);
                }
            }
            cst::TypeExpr::Row { fields, tail, .. } => {
                for f in fields {
                    go(&f.ty, bound, out);
                }
                if let Some(t) = tail {
                    go(t, bound, out);
                }
            }
            cst::TypeExpr::Parens { ty, .. } => go(ty, bound, out),
            cst::TypeExpr::TypeOp { left, right, .. } => {
                go(left, bound, out);
                go(right, bound, out);
            }
            cst::TypeExpr::Kinded { ty, kind, .. } => {
                go(ty, bound, out);
                go(kind, bound, out);
            }
            _ => {}
        }
    }
    let mut bound = HashSet::new();
    go(te, &mut bound, out);
}

fn check_free_type_vars(
    te: &cst::TypeExpr,
    bound: &mut HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    match te {
        cst::TypeExpr::Var { name, span } => {
            let sym = name.value.symbol();
            if !bound.contains(&sym) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::UndefinedTypeVariable(resolve(sym)),
                });
            }
        }
        cst::TypeExpr::Constructor { .. }
        | cst::TypeExpr::Hole { .. }
        | cst::TypeExpr::Wildcard { .. }
        | cst::TypeExpr::StringLiteral { .. }
        | cst::TypeExpr::IntLiteral { .. } => {}
        cst::TypeExpr::App { constructor, arg, .. } => {
            check_free_type_vars(constructor, bound, errors);
            check_free_type_vars(arg, bound, errors);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            check_free_type_vars(from, bound, errors);
            check_free_type_vars(to, bound, errors);
        }
        cst::TypeExpr::Forall { vars, ty, .. } => {
            // `forall (a :: k) k.` — the kind annotation on `a`
            // refers to `k` but `k` is declared LATER in the same
            // forall. The reference compiler rejects this. We
            // process vars in source order: kind-annotation lookups
            // can only see the bound set BEFORE this var was added.
            let mut new_bound = bound.clone();
            for (v, _, kind) in vars {
                if let Some(k) = kind {
                    let mut k_bound = new_bound.clone();
                    check_free_type_vars(k, &mut k_bound, errors);
                }
                new_bound.insert(v.value.symbol());
            }
            check_free_type_vars(ty, &mut new_bound, errors);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for arg in &c.args {
                    let mut local = bound.clone();
                    check_free_type_vars(arg, &mut local, errors);
                }
            }
            check_free_type_vars(ty, bound, errors);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                check_free_type_vars(&f.ty, bound, errors);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                check_free_type_vars(&f.ty, bound, errors);
            }
            if let Some(t) = tail {
                check_free_type_vars(t, bound, errors);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => check_free_type_vars(ty, bound, errors),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            check_free_type_vars(left, bound, errors);
            check_free_type_vars(right, bound, errors);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            check_free_type_vars(ty, bound, errors);
            check_free_type_vars(kind, bound, errors);
        }
        _ => {}
    }
}

/// Direct self-referential let bindings: `let x = x in ...` (CAF
/// cycle without a lambda barrier). Walks every value decl + nested
/// expression for `LetBinding::Value` whose binder names a name `x`
/// AND whose body's only Var occurrence is `x` itself.
fn detect_let_self_cycle(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::Value { guarded, where_clause, .. } => {
                walk_guarded_for_let_self_cycle(guarded, errors);
                check_let_block_self_cycle(where_clause, errors);
                for b in where_clause {
                    if let cst::LetBinding::Value { expr, .. } = b {
                        walk_expr_for_let_self_cycle(expr, errors);
                    }
                }
            }
            cst::Decl::Instance { members, .. } => {
                detect_let_self_cycle(members, errors);
            }
            _ => {}
        }
    }
}

fn check_let_block_self_cycle(
    bindings: &[cst::LetBinding],
    errors: &mut Vec<ValidationError>,
) {
    for b in bindings {
        if let cst::LetBinding::Value { binder, expr, span } = b {
            if let cst::Binder::Var { name, .. } = peel_paren_binder(binder) {
                let sym = name.value.symbol();
                if expr_is_direct_self_ref(expr, sym) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::CycleInDeclaration(vec![
                            resolve(sym),
                        ]),
                    });
                }
            }
        }
    }
}

/// True iff the expression bottom-reduces to `Var { name }` without
/// crossing any lambda / case / record (i.e. without forming a
/// computation barrier). Conservative: only handles trivial Parens
/// / TypeAnnotation wrappers.
fn expr_is_direct_self_ref(expr: &cst::Expr, name: Symbol) -> bool {
    let mut cur = expr;
    loop {
        match cur {
            cst::Expr::Var { name: qn, .. } => {
                return qn.module.is_none() && qn.name.symbol() == name;
            }
            cst::Expr::Parens { expr, .. } => cur = expr,
            cst::Expr::TypeAnnotation { expr, .. } => cur = expr,
            _ => return false,
        }
    }
}

fn walk_guarded_for_let_self_cycle(
    g: &cst::GuardedExpr,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_let_self_cycle(e, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_let_self_cycle(e, errors);
                        }
                    }
                }
                walk_expr_for_let_self_cycle(&gd.expr, errors);
            }
        }
    }
}

fn walk_expr_for_let_self_cycle(
    expr: &cst::Expr,
    errors: &mut Vec<ValidationError>,
) {
    match expr {
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_let_self_cycle(func, errors);
            walk_expr_for_let_self_cycle(arg, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_let_self_cycle(func, errors);
        }
        cst::Expr::Lambda { body, .. } => walk_expr_for_let_self_cycle(body, errors),
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_let_self_cycle(left, errors);
            walk_expr_for_let_self_cycle(right, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_let_self_cycle(cond, errors);
            walk_expr_for_let_self_cycle(then_expr, errors);
            walk_expr_for_let_self_cycle(else_expr, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_let_self_cycle(e, errors);
            }
            for alt in alts {
                walk_guarded_for_let_self_cycle(&alt.result, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            check_let_block_self_cycle(bindings, errors);
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_let_self_cycle(expr, errors);
                }
            }
            walk_expr_for_let_self_cycle(body, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_let_self_cycle(expr, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        check_let_block_self_cycle(bindings, errors);
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_let_self_cycle(expr, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_let_self_cycle(result, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_let_self_cycle(v, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => walk_expr_for_let_self_cycle(expr, errors),
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_let_self_cycle(expr, errors);
            for u in updates {
                walk_expr_for_let_self_cycle(&u.value, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => walk_expr_for_let_self_cycle(expr, errors),
        cst::Expr::TypeAnnotation { expr, .. } => {
            walk_expr_for_let_self_cycle(expr, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_let_self_cycle(e, errors);
            }
        }
        cst::Expr::Negate { expr, .. } => walk_expr_for_let_self_cycle(expr, errors),
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_let_self_cycle(name, errors);
            walk_expr_for_let_self_cycle(pattern, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_let_self_cycle(func, errors);
            walk_expr_for_let_self_cycle(left, errors);
            walk_expr_for_let_self_cycle(right, errors);
        }
        _ => {}
    }
}

/// `do`-block whose final statement is a `<-` bind (`InvalidDoBind`)
/// or a `let` (`InvalidDoLet`). Walks every Decl::Value body + its
/// where-clause + instance-method bodies for nested do-blocks.
fn detect_invalid_do_terminal(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::Value { guarded, where_clause, .. } => {
                walk_guarded_for_invalid_do(guarded, errors);
                for b in where_clause {
                    if let cst::LetBinding::Value { expr, .. } = b {
                        walk_expr_for_invalid_do(expr, errors);
                    }
                }
            }
            cst::Decl::Instance { members, .. } => {
                detect_invalid_do_terminal(members, errors);
            }
            _ => {}
        }
    }
}

fn walk_guarded_for_invalid_do(
    g: &cst::GuardedExpr,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => walk_expr_for_invalid_do(e, errors),
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_invalid_do(e, errors);
                        }
                    }
                }
                walk_expr_for_invalid_do(&gd.expr, errors);
            }
        }
    }
}

fn walk_expr_for_invalid_do(
    expr: &cst::Expr,
    errors: &mut Vec<ValidationError>,
) {
    match expr {
        cst::Expr::Do { span, statements, .. } => {
            if let Some(last) = statements.last() {
                match last {
                    cst::DoStatement::Bind { .. } => {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::InvalidDoBind,
                        });
                    }
                    cst::DoStatement::Let { .. } => {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::InvalidDoLet,
                        });
                    }
                    cst::DoStatement::Discard { .. } => {}
                }
            }
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_invalid_do(expr, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_invalid_do(expr, errors);
                            }
                        }
                    }
                }
            }
        }
        cst::Expr::Ado { statements, result, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_invalid_do(expr, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_invalid_do(expr, errors);
                            }
                        }
                    }
                }
            }
            walk_expr_for_invalid_do(result, errors);
        }
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_invalid_do(func, errors);
            walk_expr_for_invalid_do(arg, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_invalid_do(func, errors);
        }
        cst::Expr::Lambda { body, .. } => walk_expr_for_invalid_do(body, errors),
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_invalid_do(left, errors);
            walk_expr_for_invalid_do(right, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_invalid_do(cond, errors);
            walk_expr_for_invalid_do(then_expr, errors);
            walk_expr_for_invalid_do(else_expr, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_invalid_do(e, errors);
            }
            for alt in alts {
                walk_guarded_for_invalid_do(&alt.result, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_invalid_do(expr, errors);
                }
            }
            walk_expr_for_invalid_do(body, errors);
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_invalid_do(v, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_invalid_do(expr, errors);
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_invalid_do(expr, errors);
            for u in updates {
                walk_expr_for_invalid_do(&u.value, errors);
            }
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_for_invalid_do(expr, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_invalid_do(e, errors);
            }
        }
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_invalid_do(name, errors);
            walk_expr_for_invalid_do(pattern, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_invalid_do(func, errors);
            walk_expr_for_invalid_do(left, errors);
            walk_expr_for_invalid_do(right, errors);
        }
        _ => {}
    }
}

/// `outer { a = { b = 42 } }` — a flat update field's value is
/// itself a record-update section. The section's type is a function
/// `forall r. { b :: ?, ... | r } -> { b :: ?, ... | r }`, but `a`'s
/// declared type is a record. Function vs record can't unify.
/// Reference compiler reports as `TypesDoNotUnify`.
/// Detect `data X = X (forall a. F a)` where F is a LOCAL polykinded
/// data type (its parameter is unused in any ctor field). This
/// matches `QuantificationCheckFailureInType` from the reference
/// compiler: the inner `a`'s kind isn't determined by anything in
/// scope, so the implicit kind quantifier would have to wrap the
/// rank-2 forall, which the reference compiler rejects.
/// Detect kind mismatches at the level of row labels. Specifically:
/// `data P :: R (x :: Type, y :: Type) -> Type; ... type T = P Z` where
/// Z's kind is `forall r. R (z :: Type | r)` — Z's open-row label `z`
/// isn't in P's expected closed `{x, y}`. Reference compiler reports
/// as `KindsDoNotUnify`.
///
/// CST-only: requires both sides to be locally declared with explicit
/// kind annotations whose row structure we can extract. Skipped for
/// imported types (we don't have their kinds in the registry).
fn detect_row_kind_label_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;
    // Step 1: collect each LOCAL type's "output row info":
    //   - its first-arg-position expected row labels (closed if no
    //     tail) — for `data P :: R (a, b) -> Type` style,
    //   - its OUTPUT kind row labels (open or closed) — for foreign
    //     import data Z :: forall r. R (z | r)`.
    #[derive(Debug)]
    struct RowInfo {
        head: Symbol,         // R, Row, etc.
        labels: Vec<Symbol>,
        closed: bool,
    }
    // first_param_row[t]: the expected row at t's first arg position.
    let mut first_param_row: Map<Symbol, RowInfo> = Map::new();
    // output_row[t]: the row of t's output kind (after stripping all
    // visible foralls and arrow args).
    let mut output_row: Map<Symbol, RowInfo> = Map::new();
    for d in decls {
        match d {
            cst::Decl::Data {
                name,
                kind_sig: cst::KindSigSource::Data,
                kind_type: Some(kt),
                ..
            } => {
                // Standalone `data P :: K` form. K = arg1 -> ... -> Type.
                // Extract first arg's row info.
                if let Some(info) = extract_first_param_row(kt) {
                    first_param_row.insert(name.value.symbol(), info);
                }
            }
            cst::Decl::ForeignData { name, kind, .. } => {
                if let Some(info) = extract_output_row(kind) {
                    output_row.insert(name.value.symbol(), info);
                }
            }
            _ => {}
        }
    }
    if first_param_row.is_empty() || output_row.is_empty() {
        return;
    }
    // Step 2: walk every type expression and look for `f a`
    // applications where f is in `first_param_row` and a is in
    // `output_row`. Compare row labels.
    let mut visit = |ty: &cst::TypeExpr, errors: &mut Vec<ValidationError>| {
        check_row_kind_app(ty, &first_param_row, &output_row, errors);
    };
    for d in decls {
        match d {
            cst::Decl::TypeAlias { ty, .. } => visit(ty, errors),
            cst::Decl::Data { constructors, .. } => {
                for c in constructors {
                    for f in &c.fields {
                        visit(f, errors);
                    }
                }
            }
            cst::Decl::Newtype { ty, .. } => visit(ty, errors),
            cst::Decl::TypeSignature { ty, .. } => visit(ty, errors),
            cst::Decl::Foreign { ty, .. } => visit(ty, errors),
            cst::Decl::ForeignData { kind, .. } => visit(kind, errors),
            _ => {}
        }
    }

    /// Walk every App-spine within `ty` looking for f-a pairs that
    /// belong to the local row-aware type set.
    fn check_row_kind_app(
        ty: &cst::TypeExpr,
        first_param_row: &Map<Symbol, RowInfo>,
        output_row: &Map<Symbol, RowInfo>,
        errors: &mut Vec<ValidationError>,
    ) {
        match ty {
            cst::TypeExpr::App { constructor, arg, span, .. } => {
                if let cst::TypeExpr::Constructor { name: f_name, .. } = peel_paren_te(constructor) {
                    if f_name.module.is_none() {
                        if let cst::TypeExpr::Constructor { name: a_name, .. } = peel_paren_te(arg) {
                            if a_name.module.is_none() {
                                if let (Some(p_row), Some(a_row)) = (
                                    first_param_row.get(&f_name.name.symbol()),
                                    output_row.get(&a_name.name.symbol()),
                                ) {
                                    // Heads must match for a row-vs-row comparison.
                                    if p_row.head == a_row.head {
                                        for lbl in &a_row.labels {
                                            if !p_row.labels.iter().any(|x| x == lbl) {
                                                errors.push(ValidationError {
                                                    span: *span,
                                                    kind: ValidationErrorKind::KindsDoNotUnify(
                                                        resolve(*lbl),
                                                    ),
                                                });
                                                return;
                                            }
                                        }
                                        // Closed-vs-closed must match exactly.
                                        if p_row.closed && a_row.closed {
                                            for lbl in &p_row.labels {
                                                if !a_row.labels.iter().any(|x| x == lbl) {
                                                    errors.push(ValidationError {
                                                        span: *span,
                                                        kind: ValidationErrorKind::KindsDoNotUnify(
                                                            resolve(*lbl),
                                                        ),
                                                    });
                                                    return;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                check_row_kind_app(constructor, first_param_row, output_row, errors);
                check_row_kind_app(arg, first_param_row, output_row, errors);
            }
            cst::TypeExpr::Function { from, to, .. } => {
                check_row_kind_app(from, first_param_row, output_row, errors);
                check_row_kind_app(to, first_param_row, output_row, errors);
            }
            cst::TypeExpr::Forall { ty, .. } => {
                check_row_kind_app(ty, first_param_row, output_row, errors);
            }
            cst::TypeExpr::Constrained { ty, .. } => {
                check_row_kind_app(ty, first_param_row, output_row, errors);
            }
            cst::TypeExpr::Parens { ty, .. } => {
                check_row_kind_app(ty, first_param_row, output_row, errors);
            }
            cst::TypeExpr::Kinded { ty, kind, .. } => {
                check_row_kind_app(ty, first_param_row, output_row, errors);
                check_row_kind_app(kind, first_param_row, output_row, errors);
            }
            cst::TypeExpr::Record { fields, .. } | cst::TypeExpr::Row { fields, .. } => {
                for f in fields {
                    check_row_kind_app(&f.ty, first_param_row, output_row, errors);
                }
            }
            _ => {}
        }
    }

    /// Peel arrows/foralls from `K = T1 -> T2 -> ... -> Output` and
    /// extract the FIRST arg's row info. The arg shape we recognize
    /// is `App(Con(R), Row { fields, tail })`.
    fn extract_first_param_row(kind: &cst::TypeExpr) -> Option<RowInfo> {
        let mut cur = kind;
        loop {
            match peel_paren_te(cur) {
                cst::TypeExpr::Forall { ty, .. } => cur = ty,
                cst::TypeExpr::Function { from, .. } => return row_info_of(from),
                _ => return None,
            }
        }
    }

    /// Peel foralls from a type expr and extract the output row info.
    /// The output shape we recognize is `App(Con(R), Row { fields,
    /// tail })`.
    fn extract_output_row(kind: &cst::TypeExpr) -> Option<RowInfo> {
        let mut cur = kind;
        loop {
            match peel_paren_te(cur) {
                cst::TypeExpr::Forall { ty, .. } => cur = ty,
                cst::TypeExpr::Function { to, .. } => cur = to,
                other => return row_info_of(other),
            }
        }
    }

    /// If `ty` is `App(Con(R), Row { fields, tail })`, return RowInfo.
    fn row_info_of(ty: &cst::TypeExpr) -> Option<RowInfo> {
        let cur = peel_paren_te(ty);
        let cst::TypeExpr::App { constructor, arg, .. } = cur else {
            return None;
        };
        let cst::TypeExpr::Constructor { name: head_name, .. } = peel_paren_te(constructor) else {
            return None;
        };
        let cst::TypeExpr::Row { fields, tail, .. } = peel_paren_te(arg) else {
            return None;
        };
        let labels: Vec<Symbol> =
            fields.iter().map(|f| f.label.value.symbol()).collect();
        Some(RowInfo {
            head: head_name.name.symbol(),
            labels,
            closed: tail.is_none(),
        })
    }
}

/// Detect `type T ... = (X :: K)` where X is a foreign-import-data
/// declaration whose kind has 2+ forall-bound kind variables. The
/// annotation can't visibly bind all of them. Reference compiler
/// reports as `VisibleQuantificationCheckFailureInType`.
fn detect_visible_quant_kind_ann(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;
    // Map: foreign-import-data name → number of forall vars in its
    // kind annotation. Counts only top-level forall (visible).
    let mut multi_forall_foreign_data: Map<Symbol, usize> = Map::new();
    for d in decls {
        if let cst::Decl::ForeignData { name, kind, .. } = d {
            let n = count_top_forall_vars(kind);
            if n >= 2 {
                multi_forall_foreign_data.insert(name.value.symbol(), n);
            }
        }
    }
    if multi_forall_foreign_data.is_empty() {
        return;
    }
    for d in decls {
        if let cst::Decl::TypeAlias { ty, span, .. } = d {
            // Body must be a Kinded TypeExpr.
            let peeled = peel_paren_te_local(ty);
            let cst::TypeExpr::Kinded { ty: inner, .. } = peeled else {
                continue;
            };
            // Inner must be a single Constructor of one of our
            // multi-forall foreign-data types.
            let cur = peel_paren_te_local(inner);
            let cst::TypeExpr::Constructor { name, .. } = cur else {
                continue;
            };
            if name.module.is_some() {
                continue;
            }
            if multi_forall_foreign_data.contains_key(&name.name.symbol()) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::VisibleQuantificationCheckFailureInType(
                        resolve(name.name.symbol()),
                    ),
                });
            }
        }
    }
}

fn count_top_forall_vars(ty: &cst::TypeExpr) -> usize {
    let mut count = 0;
    let mut cur = ty;
    loop {
        match cur {
            cst::TypeExpr::Forall { vars, ty, .. } => {
                count += vars.len();
                cur = ty;
            }
            cst::TypeExpr::Parens { ty, .. } => cur = ty,
            _ => return count,
        }
    }
}

/// Detect chain ambiguity in a where-binding's recursive call:
/// `go :: forall i. C i => Proxy i -> ...` and the body recursively
/// calls `go (Proxy :: Proxy (Cons i)) ...` where C has a chain
/// instance `C x => C (Cons x)` (recursive on Cons). The
/// recursive constraint can't be discharged at inference time,
/// leading to `NoInstanceFound`.
fn detect_where_binding_chain_ambiguity(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashSet as Set;
    // Step 1: identify recursive chain instances. For each chain
    // class, collect the constructor heads `Cons` such that
    // `C x => C (Cons x)` exists in the chain.
    let mut recursive_chain_cons: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for d in decls {
        let cst::Decl::Instance { class_name, types, constraints, .. } = d else {
            continue;
        };
        let cqi = class_name.to_qi();
        if cqi.module.is_some() {
            continue;
        }
        // Check if instance head is `C (Cons x)` and constraint
        // includes `C x` for the same x.
        if types.len() != 1 {
            continue;
        }
        let head = peel_paren_te_local(&types[0]);
        let cst::TypeExpr::App { constructor, arg, .. } = head else {
            continue;
        };
        let cst::TypeExpr::Constructor { name: cons_name, .. } =
            peel_paren_te_local(constructor)
        else {
            continue;
        };
        if cons_name.module.is_some() {
            continue;
        }
        let cst::TypeExpr::Var { name: var_name, .. } = peel_paren_te_local(arg)
        else {
            continue;
        };
        let var_sym = var_name.value.symbol();
        // Constraint includes `C var` for same var.
        let has_recursive_constraint = constraints.iter().any(|c| {
            let c_qi = c.class.to_qi();
            if c_qi.module.is_some() || c_qi.name != cqi.name {
                return false;
            }
            c.args.len() == 1
                && match peel_paren_te_local(&c.args[0]) {
                    cst::TypeExpr::Var { name, .. } => {
                        name.value.symbol() == var_sym
                    }
                    _ => false,
                }
        });
        if has_recursive_constraint {
            recursive_chain_cons
                .entry(cqi.name)
                .or_default()
                .insert(cons_name.name.symbol());
        }
    }
    if recursive_chain_cons.is_empty() {
        return;
    }
    // Step 2: walk Decl::Value where-clauses for bindings with
    // sig `forall i. C i => ...` whose body recursively calls
    // itself with `Proxy (Cons _)` annotation.
    for d in decls {
        if let cst::Decl::Value { where_clause, span, .. } = d {
            check_where_chain_ambiguity(
                where_clause,
                &recursive_chain_cons,
                *span,
                errors,
            );
        }
    }
}

fn check_where_chain_ambiguity(
    bindings: &[cst::LetBinding],
    recursive_chain_cons: &HashMap<Symbol, HashSet<Symbol>>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;
    // Build per-name sig info: which binding has `C i` constraint.
    let mut sigs_with_constraint: Map<Symbol, Symbol> = Map::new(); // name -> class
    for b in bindings {
        if let cst::LetBinding::Signature { name, ty, .. } = b {
            if let Some(cls) = single_constraint_class_var(ty) {
                if recursive_chain_cons.contains_key(&cls) {
                    sigs_with_constraint.insert(name.value.symbol(), cls);
                }
            }
        }
    }
    if sigs_with_constraint.is_empty() {
        return;
    }
    // For each value binding whose name is in sigs_with_constraint,
    // walk the body for `name (Proxy :: Proxy (Cons _))` patterns.
    for b in bindings {
        if let cst::LetBinding::Value { binder, expr, .. } = b {
            let name = match peel_paren_binder(binder) {
                cst::Binder::Var { name, .. } => name.value.symbol(),
                _ => continue,
            };
            let Some(cls) = sigs_with_constraint.get(&name) else {
                continue;
            };
            let cons_set = match recursive_chain_cons.get(cls) {
                Some(s) => s,
                None => continue,
            };
            if recursive_call_with_proxy_cons(expr, name, cons_set) {
                errors.push(ValidationError {
                    span,
                    kind: ValidationErrorKind::NoInstanceFound(resolve(name)),
                });
                return;
            }
        }
    }
}

/// True iff `ty` is `forall <vars>. C <single_var> => ...` where
/// C is a single-arg class. Returns the class name if matched.
fn single_constraint_class_var(ty: &cst::TypeExpr) -> Option<Symbol> {
    let cur = peel_paren_te_local(ty);
    let cst::TypeExpr::Forall { ty, .. } = cur else {
        return None;
    };
    let body = peel_paren_te_local(ty);
    let cst::TypeExpr::Constrained { constraints, .. } = body else {
        return None;
    };
    if constraints.len() != 1 {
        return None;
    }
    let c = &constraints[0];
    if c.args.len() != 1 {
        return None;
    }
    let qi = c.class.to_qi();
    if qi.module.is_some() {
        return None;
    }
    if matches!(peel_paren_te_local(&c.args[0]), cst::TypeExpr::Var { .. }) {
        Some(qi.name)
    } else {
        None
    }
}

/// True if `expr` contains a recursive call `name (Proxy :: Proxy
/// (Cons _))` where Cons is in `cons_set`.
fn recursive_call_with_proxy_cons(
    expr: &cst::Expr,
    name: Symbol,
    cons_set: &HashSet<Symbol>,
) -> bool {
    let cur = peel_paren_expr(expr);
    if let cst::Expr::App { func, arg, .. } = cur {
        // Peel App spine.
        let mut tip = cur;
        let mut args: Vec<&cst::Expr> = Vec::new();
        while let cst::Expr::App { func, arg, .. } = tip {
            args.push(arg);
            tip = func;
        }
        args.reverse();
        if let cst::Expr::Var { name: f_name, .. } = peel_paren_expr(tip) {
            if f_name.module.is_none() && f_name.name.symbol() == name {
                // Check any arg is `(Proxy :: Proxy (Cons _))`.
                for a in &args {
                    if proxy_annotation_with_cons(a, cons_set) {
                        return true;
                    }
                }
            }
        }
        if recursive_call_with_proxy_cons(func, name, cons_set) {
            return true;
        }
        if recursive_call_with_proxy_cons(arg, name, cons_set) {
            return true;
        }
    }
    match cur {
        cst::Expr::Lambda { body, .. } => {
            recursive_call_with_proxy_cons(body, name, cons_set)
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            recursive_call_with_proxy_cons(cond, name, cons_set)
                || recursive_call_with_proxy_cons(then_expr, name, cons_set)
                || recursive_call_with_proxy_cons(else_expr, name, cons_set)
        }
        cst::Expr::Case { exprs, alts, .. } => {
            exprs
                .iter()
                .any(|e| recursive_call_with_proxy_cons(e, name, cons_set))
                || alts.iter().any(|alt| {
                    walk_guarded_proxy_cons(&alt.result, name, cons_set)
                })
        }
        cst::Expr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| {
                if let cst::LetBinding::Value { expr, .. } = b {
                    recursive_call_with_proxy_cons(expr, name, cons_set)
                } else {
                    false
                }
            }) || recursive_call_with_proxy_cons(body, name, cons_set)
        }
        cst::Expr::TypeAnnotation { expr, .. } | cst::Expr::Negate { expr, .. } => {
            recursive_call_with_proxy_cons(expr, name, cons_set)
        }
        _ => false,
    }
}

fn walk_guarded_proxy_cons(
    g: &cst::GuardedExpr,
    name: Symbol,
    cons_set: &HashSet<Symbol>,
) -> bool {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            recursive_call_with_proxy_cons(e, name, cons_set)
        }
        cst::GuardedExpr::Guarded(gs) => gs.iter().any(|gd| {
            gd.patterns.iter().any(|p| {
                let e = match p {
                    cst::GuardPattern::Pattern(_, e) => e,
                    cst::GuardPattern::Boolean(e) => e,
                };
                recursive_call_with_proxy_cons(e, name, cons_set)
            }) || recursive_call_with_proxy_cons(&gd.expr, name, cons_set)
        }),
    }
}

/// True iff `expr` is `(Proxy :: Proxy (Cons _))` for some Cons
/// in `cons_set`.
fn proxy_annotation_with_cons(
    expr: &cst::Expr,
    cons_set: &HashSet<Symbol>,
) -> bool {
    let cur = peel_paren_expr(expr);
    let cst::Expr::TypeAnnotation { ty, .. } = cur else {
        return false;
    };
    // Annotation: `Proxy (Cons _)`. Peel.
    let ann = peel_paren_te_local(ty);
    let cst::TypeExpr::App { constructor, arg, .. } = ann else {
        return false;
    };
    // First constructor must be Proxy (any module).
    if let cst::TypeExpr::Constructor { name: pn, .. } = peel_paren_te_local(constructor) {
        let n = resolve(pn.name.symbol());
        if n != "Proxy" {
            return false;
        }
    } else {
        return false;
    }
    // arg must be `(Cons _)` where Cons is in cons_set.
    let arg_peeled = peel_paren_te_local(arg);
    let cst::TypeExpr::App { constructor: inner_c, .. } = arg_peeled else {
        return false;
    };
    let cst::TypeExpr::Constructor { name: cn, .. } = peel_paren_te_local(inner_c) else {
        return false;
    };
    cn.module.is_none() && cons_set.contains(&cn.name.symbol())
}

/// Detect nested record update assigning a primitive literal to a
/// field whose declared type (per a local type alias) is
/// `{ | row_param }` — a record with a row variable as tail. Such
/// fields expect record values; assigning a string/int/bool fails.
/// Reference compiler reports as `TypesDoNotUnify`.
fn detect_nested_update_row_field_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashSet as Set;
    // Step 1: collect field names whose declared type in some
    // local type alias is `{ | row_param }` (record with bare type
    // var as tail). These fields expect a record value.
    let mut row_param_field_names: Set<Symbol> = Set::new();
    for d in decls {
        if let cst::Decl::TypeAlias { type_vars, ty, .. } = d {
            let var_set: HashSet<Symbol> = type_vars
                .iter()
                .map(|v| v.value.symbol())
                .collect();
            collect_row_param_fields(ty, &var_set, &mut row_param_field_names);
        }
    }
    if row_param_field_names.is_empty() {
        return;
    }
    // Step 2: walk Decl::Value bodies for nested updates whose
    // leaf assigns a primitive literal to a row-param field.
    for d in decls {
        if let cst::Decl::Value { guarded, where_clause, span, .. } = d {
            walk_guarded_row_field(guarded, &row_param_field_names, *span, errors);
            for b in where_clause {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_row_field(expr, &row_param_field_names, *span, errors);
                }
            }
        }
    }
}

fn collect_row_param_fields(
    ty: &cst::TypeExpr,
    type_vars: &HashSet<Symbol>,
    out: &mut HashSet<Symbol>,
) {
    let cur = peel_paren_te_local(ty);
    match cur {
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                // Field type `{ | row_var }` is parsed as
                // `Row { fields: [], tail: Some(Var(row_var)),
                // is_record: true }`.
                let field_ty = peel_paren_te_local(&f.ty);
                if let cst::TypeExpr::Row {
                    fields: inner_fields,
                    tail: Some(tail),
                    is_record: true,
                    ..
                } = field_ty
                {
                    if inner_fields.is_empty() {
                        if let cst::TypeExpr::Var { name, .. } = peel_paren_te_local(tail) {
                            if type_vars.contains(&name.value.symbol()) {
                                out.insert(f.label.value.symbol());
                            }
                        }
                    }
                }
                collect_row_param_fields(&f.ty, type_vars, out);
            }
        }
        cst::TypeExpr::Row { fields, .. } => {
            for f in fields {
                collect_row_param_fields(&f.ty, type_vars, out);
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            collect_row_param_fields(constructor, type_vars, out);
            collect_row_param_fields(arg, type_vars, out);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            collect_row_param_fields(from, type_vars, out);
            collect_row_param_fields(to, type_vars, out);
        }
        cst::TypeExpr::Forall { ty, .. } => {
            collect_row_param_fields(ty, type_vars, out);
        }
        cst::TypeExpr::Constrained { ty, .. } => {
            collect_row_param_fields(ty, type_vars, out);
        }
        _ => {}
    }
}

fn walk_guarded_row_field(
    g: &cst::GuardedExpr,
    row_field_names: &HashSet<Symbol>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_row_field(e, row_field_names, span, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_row_field(e, row_field_names, span, errors);
                        }
                    }
                }
                walk_expr_row_field(&gd.expr, row_field_names, span, errors);
            }
        }
    }
}

fn walk_expr_row_field(
    expr: &cst::Expr,
    row_field_names: &HashSet<Symbol>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    // Look for App(_, Record { fields with is_update }).
    if let cst::Expr::App { func, arg, .. } = expr {
        if let cst::Expr::Record { fields, .. } = peel_paren_expr(arg) {
            if !fields.is_empty() && fields.iter().all(|f| f.is_update) {
                walk_record_update_for_row_field(fields, row_field_names, span, errors);
            }
        }
        walk_expr_row_field(func, row_field_names, span, errors);
        walk_expr_row_field(arg, row_field_names, span, errors);
        return;
    }
    if let cst::Expr::RecordUpdate { updates, .. } = expr {
        for u in updates {
            walk_expr_row_field(&u.value, row_field_names, span, errors);
        }
        return;
    }
    match expr {
        cst::Expr::Lambda { body, .. } => {
            walk_expr_row_field(body, row_field_names, span, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_row_field(cond, row_field_names, span, errors);
            walk_expr_row_field(then_expr, row_field_names, span, errors);
            walk_expr_row_field(else_expr, row_field_names, span, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_row_field(e, row_field_names, span, errors);
            }
            for alt in alts {
                walk_guarded_row_field(&alt.result, row_field_names, span, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_row_field(expr, row_field_names, span, errors);
                }
            }
            walk_expr_row_field(body, row_field_names, span, errors);
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_row_field(expr, row_field_names, span, errors);
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_row_field(v, row_field_names, span, errors);
                }
            }
        }
        _ => {}
    }
}

/// Walk update fields. For each update field, recurse into the
/// nested update structure. If we find a leaf assignment
/// `row_field_name = primitive_literal`, emit error.
fn walk_record_update_for_row_field(
    fields: &[cst::RecordField],
    row_field_names: &HashSet<Symbol>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    for f in fields {
        // For nested case (is_nested=true), recurse into the value
        // as another update record.
        if f.is_nested {
            if let Some(cst::Expr::Record { fields: inner, .. }) = f.value.as_ref() {
                walk_record_update_for_row_field(inner, row_field_names, span, errors);
            }
            continue;
        }
        // For flat case (is_nested=false): if the field name is a
        // row-param field AND value is primitive literal, emit.
        if row_field_names.contains(&f.label.value.symbol()) {
            if let Some(value) = &f.value {
                if is_primitive_literal_value(value) {
                    errors.push(ValidationError {
                        span,
                        kind: ValidationErrorKind::LiteralBodySigMismatch(
                            resolve(f.label.value.symbol()),
                        ),
                    });
                    return;
                }
            }
        }
    }
}

fn is_primitive_literal_value(expr: &cst::Expr) -> bool {
    let cur = peel_paren_expr(expr);
    matches!(
        cur,
        cst::Expr::Literal {
            lit: crate::cst::Literal::String(_)
                | crate::cst::Literal::Int(_)
                | crate::cst::Literal::Float(_)
                | crate::cst::Literal::Boolean(_)
                | crate::cst::Literal::Char(_),
            ..
        }
    )
}

/// Detect KindsDoNotUnify in a class-method call where one arg
/// is `(C :: _ Lit)` with a primitive type-level literal:
/// `f (\a -> "foo") (Proxy :: _ "foo")`. The surrounding `f` is
/// a local class method; the wildcard kind annotation forces a
/// non-Type kind that conflicts with the class method's
/// `f a -> f b` shape (where a and b are Type-kinded by default).
fn detect_polykind_class_method_kind_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashSet as Set;
    // Collect local class method names.
    let mut class_methods: Set<Symbol> = Set::new();
    for d in decls {
        if let cst::Decl::Class { members, is_kind_sig: false, .. } = d {
            for m in members {
                class_methods.insert(m.name.value.symbol());
            }
        }
    }
    if class_methods.is_empty() {
        return;
    }
    for d in decls {
        if let cst::Decl::Value { guarded, where_clause, span, .. } = d {
            walk_guarded_polykind_method(guarded, &class_methods, *span, errors);
            for b in where_clause {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_polykind_method(expr, &class_methods, *span, errors);
                }
            }
        }
    }
}

fn walk_guarded_polykind_method(
    g: &cst::GuardedExpr,
    class_methods: &HashSet<Symbol>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_polykind_method(e, class_methods, span, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_polykind_method(e, class_methods, span, errors);
                        }
                    }
                }
                walk_expr_polykind_method(&gd.expr, class_methods, span, errors);
            }
        }
    }
}

fn walk_expr_polykind_method(
    expr: &cst::Expr,
    class_methods: &HashSet<Symbol>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    // Peel App spine: f x y z → head=f, args=[x, y, z].
    if let cst::Expr::App { func, arg, .. } = expr {
        let mut tip = expr;
        let mut args: Vec<&cst::Expr> = Vec::new();
        while let cst::Expr::App { func, arg, .. } = tip {
            args.push(arg);
            tip = func;
        }
        args.reverse();
        // Check head is a local class method.
        if let cst::Expr::Var { name, .. } = peel_paren_expr(tip) {
            if name.module.is_none() && class_methods.contains(&name.name.symbol()) {
                // Look for any arg that's `(C :: _ Lit)`.
                for a in &args {
                    let a_peeled = peel_paren_expr(a);
                    if let cst::Expr::TypeAnnotation { ty, .. } = a_peeled {
                        if annotation_is_wildcard_with_primitive_lit(ty) {
                            errors.push(ValidationError {
                                span,
                                kind: ValidationErrorKind::KindsDoNotUnify(
                                    resolve(name.name.symbol()),
                                ),
                            });
                            return;
                        }
                    }
                }
            }
        }
        walk_expr_polykind_method(func, class_methods, span, errors);
        walk_expr_polykind_method(arg, class_methods, span, errors);
        return;
    }
    match expr {
        cst::Expr::Lambda { body, .. } => {
            walk_expr_polykind_method(body, class_methods, span, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_polykind_method(cond, class_methods, span, errors);
            walk_expr_polykind_method(then_expr, class_methods, span, errors);
            walk_expr_polykind_method(else_expr, class_methods, span, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_polykind_method(e, class_methods, span, errors);
            }
            for alt in alts {
                walk_guarded_polykind_method(&alt.result, class_methods, span, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_polykind_method(expr, class_methods, span, errors);
                }
            }
            walk_expr_polykind_method(body, class_methods, span, errors);
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_polykind_method(expr, class_methods, span, errors);
        }
        _ => {}
    }
}

/// True iff `ty` is `_ Lit` where Lit is a primitive type-level
/// literal (StringLit/IntLit).
fn annotation_is_wildcard_with_primitive_lit(ty: &cst::TypeExpr) -> bool {
    let cur = peel_paren_te_local(ty);
    let cst::TypeExpr::App { constructor, arg, .. } = cur else {
        return false;
    };
    if !matches!(peel_paren_te_local(constructor), cst::TypeExpr::Wildcard { .. }) {
        return false;
    }
    matches!(
        peel_paren_te_local(arg),
        cst::TypeExpr::StringLiteral { .. } | cst::TypeExpr::IntLiteral { .. }
    )
}

/// Detect chain-instance fall-through to Fail. Pattern:
/// * `class C x` declared locally.
/// * Chain instances where the FIRST head has repeated type vars
///   like `C (X x x)` and a SUBSEQUENT chain link has a `Fail`
///   constraint.
/// * A use site of the class method on a value whose type
///   signature uses the same data type with DIFFERENT vars at the
///   repeated positions (e.g. `X a Int`).
/// → Emit NoInstanceFound (chain falls through to the Fail link).
fn detect_chain_fail_fall_through(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;

    // Step 1: identify chains. A chain is a contiguous run of
    // Instance decls where every link after the first has
    // `chain: true`. We're interested in chains where:
    //   - The first link's head has `T x x` (repeated var at
    //     multiple positions) for some local data type T.
    //   - SOME link in the chain has a `Fail` constraint.
    //
    // For each such chain, record (class_name, T, repeated_positions).
    let mut chains: Vec<ChainInfo> = Vec::new();
    let mut i = 0;
    while i < decls.len() {
        let cst::Decl::Instance { class_name, types, chain, constraints, .. } =
            &decls[i]
        else {
            i += 1;
            continue;
        };
        if *chain {
            // Skip — chain continuations are processed with their
            // chain-start.
            i += 1;
            continue;
        }
        // The first link of a (potential) chain.
        let cqi = class_name.to_qi();
        if cqi.module.is_some() {
            i += 1;
            continue;
        }
        // Find chain links.
        let chain_class_name = cqi.name;
        let mut j = i + 1;
        let mut chain_links: Vec<&cst::Decl> = vec![&decls[i]];
        while j < decls.len() {
            if let cst::Decl::Instance { chain: true, class_name: c_name, .. } = &decls[j] {
                let cqj = c_name.to_qi();
                if cqj.module.is_none() && cqj.name == chain_class_name {
                    chain_links.push(&decls[j]);
                    j += 1;
                    continue;
                }
            }
            break;
        }
        if chain_links.len() < 2 {
            i = j;
            continue;
        }
        // Check: any chain link has Fail constraint.
        let has_fail = chain_links.iter().any(|d| {
            if let cst::Decl::Instance { constraints, .. } = d {
                constraints.iter().any(|c| {
                    let q = c.class.to_qi();
                    let n = resolve(q.name);
                    n == "Fail" || n.ends_with(".Fail")
                })
            } else {
                false
            }
        });
        if !has_fail {
            i = j;
            continue;
        }
        // Check: first link's head has `T x x` shape.
        // types is `Vec<TypeExpr>` for instance args; for
        // `instance C (X x x)`, types = [App(App(Con(X), Var(x)), Var(x))].
        // We need to peel and find repeated type vars in different
        // positions.
        let _ = constraints;
        if let Some((dt_sym, rep_positions)) = first_instance_repeated_vars(types) {
            chains.push(ChainInfo {
                class_name: chain_class_name,
                data_type: dt_sym,
                repeated_positions: rep_positions,
            });
        }
        i = j;
    }
    if chains.is_empty() {
        return;
    }

    // Step 2: build a map of class methods → class name (LOCAL only).
    let mut method_to_class: Map<Symbol, Symbol> = Map::new();
    for d in decls {
        if let cst::Decl::Class { name, members, is_kind_sig: false, .. } = d {
            for m in members {
                method_to_class.insert(m.name.value.symbol(), name.value.symbol());
            }
        }
    }
    // Step 3: build value name → its declared type signature.
    let mut value_sigs: Map<Symbol, &cst::TypeExpr> = Map::new();
    for d in decls {
        if let cst::Decl::TypeSignature { name, ty, .. } = d {
            value_sigs.insert(name.value.symbol(), ty);
        }
    }
    // Step 4: walk every Decl::Value's body looking for
    // App(Var(method), Var(value)) where value has a sig matching
    // a chain's data type with DIFFERENT vars at the chain's
    // repeated positions.
    for d in decls {
        if let cst::Decl::Value { guarded, where_clause, span, .. } = d {
            walk_guarded_chain(
                guarded,
                &method_to_class,
                &value_sigs,
                chains.as_slice(),
                *span,
                errors,
            );
            for b in where_clause {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_chain(
                        expr,
                        &method_to_class,
                        &value_sigs,
                        chains.as_slice(),
                        *span,
                        errors,
                    );
                }
            }
        }
    }
}

fn first_instance_repeated_vars(
    types: &[cst::TypeExpr],
) -> Option<(Symbol, Vec<usize>)> {
    if types.len() != 1 {
        return None;
    }
    let cur = peel_paren_te_local(&types[0]);
    let mut args: Vec<&cst::TypeExpr> = Vec::new();
    let mut tip = cur;
    while let cst::TypeExpr::App { constructor, arg, .. } = tip {
        args.push(arg);
        tip = constructor;
    }
    args.reverse();
    let cst::TypeExpr::Constructor { name, .. } = peel_paren_te_local(tip) else {
        return None;
    };
    if name.module.is_some() || args.len() < 2 {
        return None;
    }
    // Collect var names per position.
    let var_names: Vec<Option<Symbol>> = args
        .iter()
        .map(|a| match peel_paren_te_local(a) {
            cst::TypeExpr::Var { name, .. } => Some(name.value.symbol()),
            _ => None,
        })
        .collect();
    // Check if any var name appears at 2+ positions.
    use std::collections::HashMap as Map;
    let mut positions: Map<Symbol, Vec<usize>> = Map::new();
    for (i, v) in var_names.iter().enumerate() {
        if let Some(s) = v {
            positions.entry(*s).or_default().push(i);
        }
    }
    for (_, ps) in &positions {
        if ps.len() >= 2 {
            return Some((name.name.symbol(), ps.clone()));
        }
    }
    None
}

fn walk_guarded_chain(
    g: &cst::GuardedExpr,
    method_to_class: &std::collections::HashMap<Symbol, Symbol>,
    value_sigs: &std::collections::HashMap<Symbol, &cst::TypeExpr>,
    chains: &[ChainInfo],
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_chain(e, method_to_class, value_sigs, chains, span, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_chain(e, method_to_class, value_sigs, chains, span, errors);
                        }
                    }
                }
                walk_expr_chain(&gd.expr, method_to_class, value_sigs, chains, span, errors);
            }
        }
    }
}

fn walk_expr_chain(
    expr: &cst::Expr,
    method_to_class: &std::collections::HashMap<Symbol, Symbol>,
    value_sigs: &std::collections::HashMap<Symbol, &cst::TypeExpr>,
    chains: &[ChainInfo],
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::Expr::App { func, arg, .. } = expr {
        // Check pattern: App(Var(method), Var(value)).
        let method_sym = match peel_paren_expr(func) {
            cst::Expr::Var { name, .. } if name.module.is_none() => {
                Some(name.name.symbol())
            }
            _ => None,
        };
        let value_sym = match peel_paren_expr(arg) {
            cst::Expr::Var { name, .. } if name.module.is_none() => {
                Some(name.name.symbol())
            }
            _ => None,
        };
        if let (Some(method), Some(value)) = (method_sym, value_sym) {
            if let Some(class_name) = method_to_class.get(&method) {
                if let Some(value_ty) = value_sigs.get(&value) {
                    for chain in chains {
                        if &chain.class_name != class_name {
                            continue;
                        }
                        if value_sig_has_different_vars_at_positions(
                            value_ty,
                            chain.data_type,
                            &chain.repeated_positions,
                        ) {
                            errors.push(ValidationError {
                                span,
                                kind: ValidationErrorKind::NoInstanceFound(
                                    resolve(method),
                                ),
                            });
                            return;
                        }
                    }
                }
            }
        }
        walk_expr_chain(func, method_to_class, value_sigs, chains, span, errors);
        walk_expr_chain(arg, method_to_class, value_sigs, chains, span, errors);
        return;
    }
    match expr {
        cst::Expr::Lambda { body, .. } => {
            walk_expr_chain(body, method_to_class, value_sigs, chains, span, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_chain(cond, method_to_class, value_sigs, chains, span, errors);
            walk_expr_chain(then_expr, method_to_class, value_sigs, chains, span, errors);
            walk_expr_chain(else_expr, method_to_class, value_sigs, chains, span, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_chain(e, method_to_class, value_sigs, chains, span, errors);
            }
            for alt in alts {
                walk_guarded_chain(&alt.result, method_to_class, value_sigs, chains, span, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_chain(expr, method_to_class, value_sigs, chains, span, errors);
                }
            }
            walk_expr_chain(body, method_to_class, value_sigs, chains, span, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_chain(expr, method_to_class, value_sigs, chains, span, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_chain(expr, method_to_class, value_sigs, chains, span, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_chain(result, method_to_class, value_sigs, chains, span, errors);
            }
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_chain(expr, method_to_class, value_sigs, chains, span, errors);
        }
        _ => {}
    }
}

#[derive(Debug)]
struct ChainInfo {
    class_name: Symbol,
    data_type: Symbol,
    repeated_positions: Vec<usize>,
}

/// True iff `value_ty` (a type signature, possibly under `forall`)
/// applies `data_type` to args where the args at `repeated_positions`
/// are NOT all the same (different type expressions).
fn value_sig_has_different_vars_at_positions(
    value_ty: &cst::TypeExpr,
    data_type: Symbol,
    repeated_positions: &[usize],
) -> bool {
    let mut cur = value_ty;
    loop {
        match peel_paren_te_local(cur) {
            cst::TypeExpr::Forall { ty, .. } => cur = ty,
            cst::TypeExpr::Constrained { ty, .. } => cur = ty,
            other => {
                cur = other;
                break;
            }
        }
    }
    // Peel App spine.
    let mut args: Vec<&cst::TypeExpr> = Vec::new();
    let mut tip = cur;
    while let cst::TypeExpr::App { constructor, arg, .. } = tip {
        args.push(arg);
        tip = constructor;
    }
    args.reverse();
    let cst::TypeExpr::Constructor { name, .. } = peel_paren_te_local(tip) else {
        return false;
    };
    if name.module.is_some() || name.name.symbol() != data_type {
        return false;
    }
    if args.len() < 2 {
        return false;
    }
    // Compare args at `repeated_positions` — they should NOT all be
    // the same shape.
    let positions_args: Vec<&cst::TypeExpr> = repeated_positions
        .iter()
        .filter_map(|&i| args.get(i).copied())
        .collect();
    if positions_args.len() < 2 {
        return false;
    }
    // Check if any two args at repeated positions are structurally
    // different.
    for i in 1..positions_args.len() {
        if !type_expr_eq(positions_args[0], positions_args[i]) {
            return true;
        }
    }
    false
}

fn type_expr_eq(a: &cst::TypeExpr, b: &cst::TypeExpr) -> bool {
    match (peel_paren_te_local(a), peel_paren_te_local(b)) {
        (cst::TypeExpr::Var { name: n1, .. }, cst::TypeExpr::Var { name: n2, .. }) => {
            n1.value.symbol() == n2.value.symbol()
        }
        (
            cst::TypeExpr::Constructor { name: n1, .. },
            cst::TypeExpr::Constructor { name: n2, .. },
        ) => n1.name.symbol() == n2.name.symbol(),
        (
            cst::TypeExpr::App { constructor: f1, arg: a1, .. },
            cst::TypeExpr::App { constructor: f2, arg: a2, .. },
        ) => type_expr_eq(f1, f2) && type_expr_eq(a1, a2),
        _ => false,
    }
}

/// Detect QuantificationCheckFailureInKind:
/// `data T :: forall (a :: Type) (b :: a) (c :: a) d. Relate b d
/// -> Type` where `d` is unannotated and used at Relate's 2nd
/// position whose expected kind is `Proxy b'` (a complex applied
/// type). Implicit kind generalization for `d` would need to
/// introduce a kind variable BEFORE the explicit forall, but that
/// kind variable depends on `a` (which is bound in the explicit
/// forall) — ill-ordered.
fn detect_quant_check_failure_in_kind(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;

    // Build per-data-type's per-arg "expected kind shape": is it
    // `App(_, _)` (complex), or just bare Var/Constructor (simple)?
    // From standalone kind sigs, we extract each arrow's input.
    let mut kind_arg_shapes: Map<Symbol, Vec<KindArgShape>> = Map::new();
    for d in decls {
        let (name, kind_type) = match d {
            cst::Decl::Data {
                name,
                kind_sig: cst::KindSigSource::Data,
                kind_type: Some(kt),
                ..
            } => (name, kt.as_ref()),
            cst::Decl::ForeignData { name, kind, .. } => (name, kind),
            _ => continue,
        };
        let shapes = extract_arg_shapes(kind_type);
        if !shapes.is_empty() {
            kind_arg_shapes.insert(name.value.symbol(), shapes);
        }
    }
    if kind_arg_shapes.is_empty() {
        return;
    }
    // Walk each standalone data kind sig with unannotated forall
    // vars; for each, find applications where an unannotated var
    // is supplied to a complex-kind position.
    for d in decls {
        if let cst::Decl::Data {
            name,
            kind_sig: cst::KindSigSource::Data,
            kind_type: Some(kt),
            span,
            ..
        } = d
        {
            let unann = unannotated_top_forall_vars(kt);
            if unann.is_empty() {
                continue;
            }
            if check_app_at_complex_position(kt, &unann, &kind_arg_shapes) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::QuantificationCheckFailureInKind(
                        resolve(name.value.symbol()),
                    ),
                });
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum KindArgShape {
    /// Bare type variable like `k`, or a primitive constructor
    /// like `Type`.
    Simple,
    /// An applied type (`Proxy b`) — complex kind.
    Complex,
}

/// Walk a kind type expression's arrow chain and return the shape
/// of each function-arg input.
fn extract_arg_shapes(kind: &cst::TypeExpr) -> Vec<KindArgShape> {
    let mut out = Vec::new();
    let mut cur = kind;
    loop {
        let peeled = peel_paren_te_local(cur);
        match peeled {
            cst::TypeExpr::Forall { ty, .. } => cur = ty,
            cst::TypeExpr::Function { from, to, .. } => {
                let from_peeled = peel_paren_te_local(from);
                let shape = match from_peeled {
                    cst::TypeExpr::App { .. } => KindArgShape::Complex,
                    cst::TypeExpr::Var { .. } | cst::TypeExpr::Constructor { .. } => {
                        KindArgShape::Simple
                    }
                    _ => KindArgShape::Simple,
                };
                out.push(shape);
                cur = to;
            }
            _ => return out,
        }
    }
}

/// Collect names of forall vars in the OUTER (top-level) forall of
/// the kind sig that have NO kind annotation.
fn unannotated_top_forall_vars(kind: &cst::TypeExpr) -> HashSet<Symbol> {
    let mut out = HashSet::new();
    let cur = peel_paren_te_local(kind);
    if let cst::TypeExpr::Forall { vars, .. } = cur {
        for (n, _, ann) in vars {
            if ann.is_none() {
                out.insert(n.value.symbol());
            }
        }
    }
    out
}

/// Walk `kind` looking for App spines where an unannotated forall
/// var appears as an arg at a "complex" kind position of a known
/// constructor (per `kind_arg_shapes`).
fn check_app_at_complex_position(
    kind: &cst::TypeExpr,
    unannotated: &HashSet<Symbol>,
    kind_arg_shapes: &std::collections::HashMap<Symbol, Vec<KindArgShape>>,
) -> bool {
    fn check_te(
        ty: &cst::TypeExpr,
        unannotated: &HashSet<Symbol>,
        kind_arg_shapes: &std::collections::HashMap<Symbol, Vec<KindArgShape>>,
    ) -> bool {
        let cur = peel_paren_te_local(ty);
        match cur {
            cst::TypeExpr::App { .. } => {
                // Peel App spine.
                let mut args: Vec<&cst::TypeExpr> = Vec::new();
                let mut tip = cur;
                while let cst::TypeExpr::App { constructor, arg, .. } = tip {
                    args.push(arg);
                    tip = constructor;
                }
                args.reverse();
                if let cst::TypeExpr::Constructor { name, .. } = peel_paren_te_local(tip) {
                    if name.module.is_none() {
                        if let Some(shapes) = kind_arg_shapes.get(&name.name.symbol()) {
                            for (i, arg) in args.iter().enumerate() {
                                if let Some(KindArgShape::Complex) = shapes.get(i) {
                                    let arg_peeled = peel_paren_te_local(arg);
                                    if let cst::TypeExpr::Var { name: vn, .. } = arg_peeled {
                                        if unannotated.contains(&vn.value.symbol()) {
                                            return true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                for arg in &args {
                    if check_te(arg, unannotated, kind_arg_shapes) {
                        return true;
                    }
                }
            }
            cst::TypeExpr::Function { from, to, .. } => {
                if check_te(from, unannotated, kind_arg_shapes) {
                    return true;
                }
                if check_te(to, unannotated, kind_arg_shapes) {
                    return true;
                }
            }
            cst::TypeExpr::Forall { ty, .. } => {
                if check_te(ty, unannotated, kind_arg_shapes) {
                    return true;
                }
            }
            _ => {}
        }
        false
    }
    check_te(kind, unannotated, kind_arg_shapes)
}

/// Detect infinite-type via recursive wildcard wrap:
/// `go :: Array _ -> Int; go xs = go [xs]` — the recursive call
/// wraps the binder in an additional Array, forcing the wildcard
/// to satisfy `_ = Array _`. Reference compiler reports as
/// `InfiniteType`.
fn detect_recursive_wildcard_wrap(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        if let cst::Decl::Value { where_clause, .. } = d {
            check_let_block_for_wildcard_wrap(where_clause, errors);
        }
    }
}

fn check_let_block_for_wildcard_wrap(
    bindings: &[cst::LetBinding],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;
    // Build per-binding-name: sig_has_wildcard.
    let mut sig_has_wildcard: Map<Symbol, ()> = Map::new();
    for b in bindings {
        if let cst::LetBinding::Signature { name, ty, .. } = b {
            if type_has_wildcard(ty) {
                sig_has_wildcard.insert(name.value.symbol(), ());
            }
        }
    }
    if sig_has_wildcard.is_empty() {
        return;
    }
    for b in bindings {
        if let cst::LetBinding::Value { binder, expr, span } = b {
            let name = match peel_paren_binder(binder) {
                cst::Binder::Var { name, .. } => name.value.symbol(),
                _ => continue,
            };
            if !sig_has_wildcard.contains_key(&name) {
                continue;
            }
            // Multi-equation `go xs = go [xs]` becomes
            // `LetBinding::Value { binder: Var(go), expr:
            // Lambda([Var(xs)], App(Var(go), Array([Var(xs)]))) }`.
            // Inspect the lambda body for a recursive call wrapping
            // the binder in an Array literal.
            let cst::Expr::Lambda { binders, body, .. } = expr else {
                continue;
            };
            let bound_names: HashSet<Symbol> = binders
                .iter()
                .filter_map(|b| match peel_paren_binder(b) {
                    cst::Binder::Var { name, .. } => Some(name.value.symbol()),
                    _ => None,
                })
                .collect();
            if has_recursive_array_wrap(body, name, &bound_names) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::InfiniteType(resolve(name)),
                });
            }
        }
    }
}

/// Returns true if `expr` is a recursive call to `func_name` whose
/// argument wraps a binder in an Array literal.
fn has_recursive_array_wrap(
    expr: &cst::Expr,
    func_name: Symbol,
    binder_names: &HashSet<Symbol>,
) -> bool {
    let cur = match expr {
        cst::Expr::Parens { expr, .. } => expr,
        other => other,
    };
    if let cst::Expr::App { func, arg, .. } = cur {
        // Check if func is the recursive call.
        if let cst::Expr::Var { name, .. } = peel_paren_expr(func) {
            if name.module.is_none() && name.name.symbol() == func_name {
                // Check if arg is an Array literal containing a binder.
                if let cst::Expr::Array { elements, .. } = peel_paren_expr(arg) {
                    for e in elements {
                        if let cst::Expr::Var { name, .. } = peel_paren_expr(e) {
                            if name.module.is_none()
                                && binder_names.contains(&name.name.symbol())
                            {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

fn type_has_wildcard(ty: &cst::TypeExpr) -> bool {
    match ty {
        cst::TypeExpr::Wildcard { .. } => true,
        cst::TypeExpr::App { constructor, arg, .. } => {
            type_has_wildcard(constructor) || type_has_wildcard(arg)
        }
        cst::TypeExpr::Function { from, to, .. } => {
            type_has_wildcard(from) || type_has_wildcard(to)
        }
        cst::TypeExpr::Forall { ty, .. } => type_has_wildcard(ty),
        cst::TypeExpr::Constrained { ty, .. } => type_has_wildcard(ty),
        cst::TypeExpr::Parens { ty, .. } => type_has_wildcard(ty),
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            type_has_wildcard(ty) || type_has_wildcard(kind)
        }
        cst::TypeExpr::Record { fields, .. } | cst::TypeExpr::Row { fields, .. } => {
            fields.iter().any(|f| type_has_wildcard(&f.ty))
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            type_has_wildcard(left) || type_has_wildcard(right)
        }
        _ => false,
    }
}

/// Detect kind mismatches when calling a polymorphic-proxy function:
/// `put (SProxy :: SProxy "apple")` where put has signature
/// `forall proxy a. proxy a -> TProxy a`. The same `a` appears at
/// both `proxy a` (kind determined by proxy's expected kind) and
/// `TProxy a` (where TProxy requires `t :: Type`). When the arg's
/// type annotation `SProxy "apple"` forces a's kind to Symbol,
/// the Type-kinded use site mismatches. Reference compiler reports
/// as `KindsDoNotUnify`.
fn detect_polymorphic_proxy_kind_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;
    // Step 1: build a map of LOCAL data types whose first param has
    // an explicit non-Type kind annotation (Symbol / Int / Boolean).
    // E.g. `data SProxy (s :: Symbol) = SProxy` → SProxy : Symbol-
    // kinded first param.
    let mut nontype_param_data: Map<Symbol, &'static str> = Map::new();
    let mut type_param_data: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::Data { name, type_var_kind_anns, .. } = d {
            if let Some(Some(kt)) = type_var_kind_anns.first() {
                let prim = prim_kind_name(kt);
                match prim {
                    Some("Symbol") | Some("Int") | Some("Boolean") => {
                        nontype_param_data.insert(name.value.symbol(), prim.unwrap());
                    }
                    Some("Type") => {
                        type_param_data.insert(name.value.symbol());
                    }
                    _ => {}
                }
            }
        }
    }
    if nontype_param_data.is_empty() || type_param_data.is_empty() {
        return;
    }
    // Step 2: build a map of LOCAL value sigs of shape
    // `forall proxy a. proxy a -> TyApp1 ... a ...` where TyApp1
    // contains a Type-param data type applied to `a`.
    let mut polymorphic_proxies: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::TypeSignature { name, ty, .. } = d {
            if is_polymorphic_proxy_sig(ty, &type_param_data) {
                polymorphic_proxies.insert(name.value.symbol());
            }
        }
    }
    if polymorphic_proxies.is_empty() {
        return;
    }
    // Step 3: walk every value body for App(f, (C :: D Lit))
    // where f is a polymorphic proxy and (C :: D Lit) has D in
    // nontype_param_data and Lit is a primitive literal of matching
    // kind.
    for d in decls {
        if let cst::Decl::Value { guarded, where_clause, .. } = d {
            walk_guarded_polyproxy(
                guarded,
                &polymorphic_proxies,
                &nontype_param_data,
                errors,
            );
            for b in where_clause {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_polyproxy(
                        expr,
                        &polymorphic_proxies,
                        &nontype_param_data,
                        errors,
                    );
                }
            }
        }
    }
}

fn prim_kind_name(ty: &cst::TypeExpr) -> Option<&'static str> {
    let mut cur = ty;
    loop {
        match cur {
            cst::TypeExpr::Parens { ty, .. } => cur = ty,
            cst::TypeExpr::Constructor { name, .. } => {
                let n = resolve(name.name.symbol());
                return match n.as_str() {
                    "Type" => Some("Type"),
                    "Symbol" => Some("Symbol"),
                    "Int" => Some("Int"),
                    "Boolean" => Some("Boolean"),
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// True iff `ty` is `forall <vars>. proxy a -> R ... a ...` where
/// `proxy` and `a` are forall-bound vars, and R is a local Type-
/// parameterised data type applied to `a` directly.
fn is_polymorphic_proxy_sig(
    ty: &cst::TypeExpr,
    type_param_data: &HashSet<Symbol>,
) -> bool {
    let cur = peel_paren_te_local(ty);
    let cst::TypeExpr::Forall { vars, ty: body, .. } = cur else {
        return false;
    };
    let bound: HashSet<Symbol> = vars.iter().map(|(n, _, _)| n.value.symbol()).collect();
    if bound.len() < 2 {
        return false;
    }
    let cst::TypeExpr::Function { from, to, .. } = peel_paren_te_local(body) else {
        return false;
    };
    // Check `from` is `Var(proxy) Var(a)` where both are bound.
    let cst::TypeExpr::App { constructor, arg, .. } = peel_paren_te_local(from) else {
        return false;
    };
    let cst::TypeExpr::Var { name: proxy_n, .. } = peel_paren_te_local(constructor) else {
        return false;
    };
    let cst::TypeExpr::Var { name: a_n, .. } = peel_paren_te_local(arg) else {
        return false;
    };
    let a_sym = a_n.value.symbol();
    if !bound.contains(&proxy_n.value.symbol()) || !bound.contains(&a_sym) {
        return false;
    }
    // Check `to` contains an App spine ending in `Con(R) Var(a)`
    // where R is in `type_param_data`.
    type_expr_uses_var_in_type_param_position(to, a_sym, type_param_data)
}

fn type_expr_uses_var_in_type_param_position(
    ty: &cst::TypeExpr,
    var_sym: Symbol,
    type_param_data: &HashSet<Symbol>,
) -> bool {
    let cur = peel_paren_te_local(ty);
    if let cst::TypeExpr::App { constructor, arg, .. } = cur {
        if let cst::TypeExpr::Constructor { name: ctor_name, .. } =
            peel_paren_te_local(constructor)
        {
            if ctor_name.module.is_none()
                && type_param_data.contains(&ctor_name.name.symbol())
            {
                if let cst::TypeExpr::Var { name: arg_n, .. } =
                    peel_paren_te_local(arg)
                {
                    if arg_n.value.symbol() == var_sym {
                        return true;
                    }
                }
            }
        }
        // Also recurse into nested apps.
        if type_expr_uses_var_in_type_param_position(constructor, var_sym, type_param_data) {
            return true;
        }
        if type_expr_uses_var_in_type_param_position(arg, var_sym, type_param_data) {
            return true;
        }
    }
    match cur {
        cst::TypeExpr::Function { from, to, .. } => {
            type_expr_uses_var_in_type_param_position(from, var_sym, type_param_data)
                || type_expr_uses_var_in_type_param_position(to, var_sym, type_param_data)
        }
        cst::TypeExpr::Forall { ty, .. }
        | cst::TypeExpr::Parens { ty, .. } => {
            type_expr_uses_var_in_type_param_position(ty, var_sym, type_param_data)
        }
        cst::TypeExpr::Constrained { ty, .. } => {
            type_expr_uses_var_in_type_param_position(ty, var_sym, type_param_data)
        }
        _ => false,
    }
}

fn walk_guarded_polyproxy(
    g: &cst::GuardedExpr,
    polyproxies: &HashSet<Symbol>,
    nontype_param_data: &std::collections::HashMap<Symbol, &'static str>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_polyproxy(e, polyproxies, nontype_param_data, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_polyproxy(e, polyproxies, nontype_param_data, errors);
                        }
                    }
                }
                walk_expr_polyproxy(&gd.expr, polyproxies, nontype_param_data, errors);
            }
        }
    }
}

fn walk_expr_polyproxy(
    expr: &cst::Expr,
    polyproxies: &HashSet<Symbol>,
    nontype_param_data: &std::collections::HashMap<Symbol, &'static str>,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::Expr::App { func, arg, span } = expr {
        // f's name?
        let func_name = match peel_paren_expr(func) {
            cst::Expr::Var { name, .. } if name.module.is_none() => {
                Some(name.name.symbol())
            }
            _ => None,
        };
        if let Some(fname) = func_name {
            if polyproxies.contains(&fname) {
                // Check arg is `(C :: D Lit)` with D in nontype_param_data.
                let arg_peeled = peel_paren_expr(arg);
                if let cst::Expr::TypeAnnotation { ty: ann, .. } = arg_peeled {
                    if let Some(_kind) = annotation_forces_nontype_kind(ann, nontype_param_data) {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::KindsDoNotUnify(
                                resolve(fname),
                            ),
                        });
                        return;
                    }
                }
            }
        }
        walk_expr_polyproxy(func, polyproxies, nontype_param_data, errors);
        walk_expr_polyproxy(arg, polyproxies, nontype_param_data, errors);
        return;
    }
    match expr {
        cst::Expr::Lambda { body, .. } => {
            walk_expr_polyproxy(body, polyproxies, nontype_param_data, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_polyproxy(cond, polyproxies, nontype_param_data, errors);
            walk_expr_polyproxy(then_expr, polyproxies, nontype_param_data, errors);
            walk_expr_polyproxy(else_expr, polyproxies, nontype_param_data, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_polyproxy(e, polyproxies, nontype_param_data, errors);
            }
            for alt in alts {
                walk_guarded_polyproxy(&alt.result, polyproxies, nontype_param_data, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_polyproxy(expr, polyproxies, nontype_param_data, errors);
                }
            }
            walk_expr_polyproxy(body, polyproxies, nontype_param_data, errors);
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_polyproxy(expr, polyproxies, nontype_param_data, errors);
        }
        _ => {}
    }
}

fn peel_paren_expr(e: &cst::Expr) -> &cst::Expr {
    let mut cur = e;
    while let cst::Expr::Parens { expr, .. } = cur {
        cur = expr;
    }
    cur
}

/// True iff `ann` is `D Lit` where D is a nontype-param data type
/// AND Lit is a primitive literal of matching kind. Returns the
/// kind name on match.
fn annotation_forces_nontype_kind(
    ann: &cst::TypeExpr,
    nontype_param_data: &std::collections::HashMap<Symbol, &'static str>,
) -> Option<&'static str> {
    let cur = peel_paren_te_local(ann);
    let cst::TypeExpr::App { constructor, arg, .. } = cur else {
        return None;
    };
    let cst::TypeExpr::Constructor { name, .. } = peel_paren_te_local(constructor) else {
        return None;
    };
    if name.module.is_some() {
        return None;
    }
    let kind = nontype_param_data.get(&name.name.symbol())?;
    // Check arg is a primitive literal of matching kind.
    let arg_peeled = peel_paren_te_local(arg);
    let arg_kind = match arg_peeled {
        cst::TypeExpr::StringLiteral { .. } => "Symbol",
        cst::TypeExpr::IntLiteral { .. } => "Int",
        _ => return None,
    };
    if &arg_kind == kind {
        Some(kind)
    } else {
        None
    }
}

/// Detect skolem escape via rank-2 kind annotation. `data A (a ::
/// forall k. k -> Type) = A` declares A with a rank-2-kinded
/// parameter. Using A unapplied as an arg to a Type-expecting
/// constructor (like `Proxy A`) lets the rank-2 quantifier escape.
/// Reference compiler reports as `EscapedSkolem`.
fn detect_skolem_escape_via_rank2_kind(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashSet as Set;
    // Step 1: identify local data types whose first type-var has
    // a rank-2 kind annotation (kind contains `forall`).
    let mut rank2_param_types: Set<Symbol> = Set::new();
    for d in decls {
        if let cst::Decl::Data { name, type_var_kind_anns, .. } = d {
            if type_var_kind_anns.iter().any(|opt| {
                opt.as_ref()
                    .map(|kt| has_forall(kt))
                    .unwrap_or(false)
            }) {
                rank2_param_types.insert(name.value.symbol());
            }
        }
    }
    if rank2_param_types.is_empty() {
        return;
    }
    // Step 2: walk every type expression and find App spines
    // where the rank-2-paramed type appears UNAPPLIED as an arg.
    // For a type `Proxy A` (App(Proxy, A)), A is the arg.
    for d in decls {
        match d {
            cst::Decl::TypeAlias { ty, span, .. } => {
                walk_for_unapplied_rank2(ty, &rank2_param_types, *span, errors);
            }
            cst::Decl::Data { constructors, .. } => {
                for c in constructors {
                    for f in &c.fields {
                        walk_for_unapplied_rank2(f, &rank2_param_types, c.name.span, errors);
                    }
                }
            }
            cst::Decl::Newtype { ty, span, .. } => {
                walk_for_unapplied_rank2(ty, &rank2_param_types, *span, errors);
            }
            cst::Decl::TypeSignature { ty, span, .. } => {
                walk_for_unapplied_rank2(ty, &rank2_param_types, *span, errors);
            }
            _ => {}
        }
    }
}

fn has_forall(ty: &cst::TypeExpr) -> bool {
    match ty {
        cst::TypeExpr::Forall { .. } => true,
        cst::TypeExpr::Parens { ty, .. } => has_forall(ty),
        cst::TypeExpr::Function { from, to, .. } => has_forall(from) || has_forall(to),
        cst::TypeExpr::App { constructor, arg, .. } => {
            has_forall(constructor) || has_forall(arg)
        }
        _ => false,
    }
}

fn walk_for_unapplied_rank2(
    ty: &cst::TypeExpr,
    rank2_types: &std::collections::HashSet<Symbol>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::TypeExpr::App { constructor, arg, .. } = ty {
        // Check the arg position: is it a bare Constructor of a
        // rank2-paramed type?
        let arg_peeled = peel_paren_te_local(arg);
        if let cst::TypeExpr::Constructor { name, .. } = arg_peeled {
            if name.module.is_none() && rank2_types.contains(&name.name.symbol()) {
                errors.push(ValidationError {
                    span,
                    kind: ValidationErrorKind::EscapedSkolem(
                        resolve(name.name.symbol()),
                    ),
                });
            }
        }
        walk_for_unapplied_rank2(constructor, rank2_types, span, errors);
        walk_for_unapplied_rank2(arg, rank2_types, span, errors);
        return;
    }
    match ty {
        cst::TypeExpr::Function { from, to, .. } => {
            walk_for_unapplied_rank2(from, rank2_types, span, errors);
            walk_for_unapplied_rank2(to, rank2_types, span, errors);
        }
        cst::TypeExpr::Forall { ty, .. } => {
            walk_for_unapplied_rank2(ty, rank2_types, span, errors);
        }
        cst::TypeExpr::Constrained { ty, .. } => {
            walk_for_unapplied_rank2(ty, rank2_types, span, errors);
        }
        cst::TypeExpr::Parens { ty, .. } => {
            walk_for_unapplied_rank2(ty, rank2_types, span, errors);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_for_unapplied_rank2(ty, rank2_types, span, errors);
            walk_for_unapplied_rank2(kind, rank2_types, span, errors);
        }
        cst::TypeExpr::Record { fields, .. } | cst::TypeExpr::Row { fields, .. } => {
            for f in fields {
                walk_for_unapplied_rank2(&f.ty, rank2_types, span, errors);
            }
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_for_unapplied_rank2(left, rank2_types, span, errors);
            walk_for_unapplied_rank2(right, rank2_types, span, errors);
        }
        _ => {}
    }
}

/// Detect ScopedTypeVariable issues hidden by aliases:
/// `foo :: T; foo = bar where bar :: Array a` where `T = forall a.
/// Array a` (alias whose body has explicit forall). The inner `a`
/// in `bar :: Array a` should refer to outer scoped `a`, but the
/// outer's forall is hidden behind the alias. Reference compiler
/// reports as `UndefinedTypeVariable`.
fn detect_scoped_var_via_alias(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    use std::collections::HashMap as Map;
    let mut alias_has_forall: Map<Symbol, bool> = Map::new();
    for d in decls {
        if let cst::Decl::TypeAlias { name, ty, .. } = d {
            let body_has_forall = matches!(
                peel_paren_te_local(ty),
                cst::TypeExpr::Forall { .. }
            );
            if body_has_forall {
                alias_has_forall.insert(name.value.symbol(), true);
            }
        }
    }
    if alias_has_forall.is_empty() {
        return;
    }
    let mut alias_sig_value: Map<Symbol, ()> = Map::new();
    for d in decls {
        if let cst::Decl::TypeSignature { name, ty, .. } = d {
            let peeled = peel_paren_te_local(ty);
            if let cst::TypeExpr::Constructor { name: alias_name, .. } = peeled {
                if alias_name.module.is_none()
                    && alias_has_forall.contains_key(&alias_name.name.symbol())
                {
                    alias_sig_value.insert(name.value.symbol(), ());
                }
            }
        }
    }
    if alias_sig_value.is_empty() {
        return;
    }
    for d in decls {
        if let cst::Decl::Value { name, where_clause, .. } = d {
            if alias_sig_value.contains_key(&name.value.symbol()) {
                for b in where_clause {
                    if let cst::LetBinding::Signature { ty, span, .. } = b {
                        let unbound = collect_unbound_type_vars(ty);
                        for v in unbound {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::UndefinedTypeVariable(
                                    resolve(v),
                                ),
                            });
                        }
                    }
                }
            }
        }
    }
}

fn peel_paren_te_local(ty: &cst::TypeExpr) -> &cst::TypeExpr {
    let mut cur = ty;
    while let cst::TypeExpr::Parens { ty, .. } = cur {
        cur = ty;
    }
    cur
}

fn collect_unbound_type_vars(ty: &cst::TypeExpr) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    let mut bound: HashSet<Symbol> = HashSet::new();
    walk_unbound(ty, &mut bound, &mut out);
    out
}

fn walk_unbound(
    ty: &cst::TypeExpr,
    bound: &mut HashSet<Symbol>,
    out: &mut Vec<Symbol>,
) {
    match ty {
        cst::TypeExpr::Var { name, .. } => {
            let sym = name.value.symbol();
            if !bound.contains(&sym) && !out.iter().any(|s| *s == sym) {
                out.push(sym);
            }
        }
        cst::TypeExpr::Forall { vars, ty, .. } => {
            let added: Vec<Symbol> = vars
                .iter()
                .map(|(n, _, _)| n.value.symbol())
                .filter(|s| bound.insert(*s))
                .collect();
            walk_unbound(ty, bound, out);
            for s in added {
                bound.remove(&s);
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            walk_unbound(constructor, bound, out);
            walk_unbound(arg, bound, out);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_unbound(from, bound, out);
            walk_unbound(to, bound, out);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for a in &c.args {
                    walk_unbound(a, bound, out);
                }
            }
            walk_unbound(ty, bound, out);
        }
        cst::TypeExpr::Parens { ty, .. } => walk_unbound(ty, bound, out),
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_unbound(ty, bound, out);
            walk_unbound(kind, bound, out);
        }
        cst::TypeExpr::Record { fields, .. } | cst::TypeExpr::Row { fields, .. } => {
            for f in fields {
                walk_unbound(&f.ty, bound, out);
            }
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_unbound(left, bound, out);
            walk_unbound(right, bound, out);
        }
        _ => {}
    }
}

fn detect_polykinded_rank2_in_ctor(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Step 1: identify each LOCAL data type's polykinded var
    // positions. A `data D v1 v2 … = ctor1 fields1 | …` is
    // polykinded at position i iff `vi` doesn't appear in ANY
    // constructor field's type expression. Skip data types with
    // an explicit standalone kind sig (those have a known kind).
    let mut polykinded_local_types: HashMap<Symbol, HashSet<usize>> = HashMap::new();
    let mut has_standalone_sig: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::Data { name, kind_sig, .. } = d {
            if !matches!(kind_sig, cst::KindSigSource::None) {
                has_standalone_sig.insert(name.value.symbol());
            }
        }
    }
    for d in decls {
        let cst::Decl::Data { name, type_vars, constructors, .. } = d else {
            continue;
        };
        if has_standalone_sig.contains(&name.value.symbol()) {
            continue;
        }
        let mut polykinded: HashSet<usize> = HashSet::new();
        for (i, var) in type_vars.iter().enumerate() {
            let var_sym = var.value.symbol();
            let used = constructors.iter().any(|c| {
                c.fields.iter().any(|f| type_expr_uses_var(f, var_sym))
            });
            if !used {
                polykinded.insert(i);
            }
        }
        if !polykinded.is_empty() {
            polykinded_local_types.insert(name.value.symbol(), polykinded);
        }
    }
    if polykinded_local_types.is_empty() {
        return;
    }
    // Step 2: walk each Decl::Data's ctor field types looking for
    // `Forall { vars: [a], ty: App(Con(F), Var(a)) }` where F is
    // local polykinded at the position `a` is supplied.
    for d in decls {
        let cst::Decl::Data { constructors, span, .. } = d else {
            continue;
        };
        for c in constructors {
            for f in &c.fields {
                if let Some(bad_var) = polykinded_rank2_violation(f, &polykinded_local_types) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::QuantificationCheckFailureInType(
                            resolve(bad_var),
                        ),
                    });
                }
            }
        }
    }
}

/// True if `ty` mentions a type variable named `var`.
fn type_expr_uses_var(ty: &cst::TypeExpr, var: Symbol) -> bool {
    match ty {
        cst::TypeExpr::Var { name, .. } => name.value.symbol() == var,
        cst::TypeExpr::Constructor { .. } => false,
        cst::TypeExpr::App { constructor, arg, .. } => {
            type_expr_uses_var(constructor, var) || type_expr_uses_var(arg, var)
        }
        cst::TypeExpr::Function { from, to, .. } => {
            type_expr_uses_var(from, var) || type_expr_uses_var(to, var)
        }
        cst::TypeExpr::Forall { vars, ty, .. } => {
            // shadow check: inner forall might rebind the same name
            if vars.iter().any(|(n, _, _)| n.value.symbol() == var) {
                return false;
            }
            type_expr_uses_var(ty, var)
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            constraints.iter().any(|c| {
                c.args.iter().any(|a| type_expr_uses_var(a, var))
            }) || type_expr_uses_var(ty, var)
        }
        cst::TypeExpr::Record { fields, .. } | cst::TypeExpr::Row { fields, .. } => {
            fields.iter().any(|tf| type_expr_uses_var(&tf.ty, var))
        }
        cst::TypeExpr::Parens { ty, .. } => type_expr_uses_var(ty, var),
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            type_expr_uses_var(ty, var) || type_expr_uses_var(kind, var)
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            type_expr_uses_var(left, var) || type_expr_uses_var(right, var)
        }
        _ => false,
    }
}

/// If `ty` is `forall a. F a` (or `forall a b … . F a` etc.) where F
/// is a local polykinded data type AND `a` is supplied at a
/// polykinded position, return `a`'s symbol.
fn polykinded_rank2_violation(
    ty: &cst::TypeExpr,
    polykinded_local_types: &HashMap<Symbol, HashSet<usize>>,
) -> Option<Symbol> {
    let mut cur = ty;
    while let cst::TypeExpr::Parens { ty, .. } = cur {
        cur = ty;
    }
    let cst::TypeExpr::Forall { vars, ty: body, .. } = cur else {
        return None;
    };
    // Only fire on simple `forall a. F a` shapes — single var,
    // body is App(Con(F), Var(a)). Multi-var foralls likely
    // constrain through other positions.
    if vars.len() != 1 {
        return None;
    }
    let bound_var = vars[0].0.value.symbol();
    // Body: peel App spine: F a1 a2 … an → head=F, args=[a1, …, an].
    let (head, args) = peel_app_te(body);
    let cst::TypeExpr::Constructor { name, .. } = head else {
        return None;
    };
    if name.module.is_some() {
        return None;
    }
    let polykinded_positions =
        polykinded_local_types.get(&name.name.symbol())?;
    for (i, arg) in args.iter().enumerate() {
        if !polykinded_positions.contains(&i) {
            continue;
        }
        if let cst::TypeExpr::Var { name, .. } = peel_paren_te(arg) {
            if name.value.symbol() == bound_var {
                return Some(bound_var);
            }
        }
    }
    None
}

fn peel_app_te(ty: &cst::TypeExpr) -> (&cst::TypeExpr, Vec<&cst::TypeExpr>) {
    let mut args: Vec<&cst::TypeExpr> = Vec::new();
    let mut cur = ty;
    while let cst::TypeExpr::App { constructor, arg, .. } = cur {
        args.push(arg);
        cur = constructor;
    }
    args.reverse();
    (cur, args)
}

fn peel_paren_te(ty: &cst::TypeExpr) -> &cst::TypeExpr {
    let mut cur = ty;
    while let cst::TypeExpr::Parens { ty, .. } = cur {
        cur = ty;
    }
    cur
}

fn detect_record_update_section_as_value(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::Value { guarded, where_clause, .. } => {
                walk_guarded_for_section(guarded, errors);
                for b in where_clause {
                    if let cst::LetBinding::Value { expr, .. } = b {
                        walk_expr_for_section(expr, errors);
                    }
                }
            }
            cst::Decl::Instance { members, .. } => {
                detect_record_update_section_as_value(members, errors);
            }
            _ => {}
        }
    }
}

/// True if `expr` is a Record literal where every field has
/// `is_update == true` AND `is_nested == false` (i.e. the user wrote
/// `{ field = value, ... }` with no nesting).
fn is_record_update_section(expr: &cst::Expr) -> bool {
    let mut cur = expr;
    loop {
        match cur {
            cst::Expr::Parens { expr, .. } => cur = expr,
            cst::Expr::Record { fields, .. } => {
                return !fields.is_empty()
                    && fields.iter().all(|f| f.is_update && !f.is_nested);
            }
            _ => return false,
        }
    }
}

fn walk_guarded_for_section(
    g: &cst::GuardedExpr,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => walk_expr_for_section(e, errors),
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_section(e, errors);
                        }
                    }
                }
                walk_expr_for_section(&gd.expr, errors);
            }
        }
    }
}

fn walk_expr_for_section(
    expr: &cst::Expr,
    errors: &mut Vec<ValidationError>,
) {
    // Two parser shapes can carry an update:
    //   - `Expr::App { func, arg: Expr::Record { fields with is_update } }`
    //     for explicit `r { f = v }`
    //   - `Expr::RecordUpdate { expr, updates }` (legacy)
    // Inspect each update field's value for a record-update section.
    let check_field = |span: crate::span::Span, value: &cst::Expr,
                        is_nested: bool,
                        errors: &mut Vec<ValidationError>| {
        if !is_nested && is_record_update_section(value) {
            errors.push(ValidationError {
                span,
                kind: ValidationErrorKind::LiteralBodySigMismatch(String::new()),
            });
        }
    };
    match expr {
        cst::Expr::App { func, arg, span } => {
            // `r { f = v }` shape
            if let cst::Expr::Record { fields, .. } = arg.as_ref() {
                if !fields.is_empty()
                    && fields.iter().all(|f| f.is_update)
                {
                    for f in fields {
                        if let Some(v) = &f.value {
                            check_field(*span, v, f.is_nested, errors);
                            walk_expr_for_section(v, errors);
                        }
                    }
                    walk_expr_for_section(func, errors);
                    return;
                }
            }
            walk_expr_for_section(func, errors);
            walk_expr_for_section(arg, errors);
        }
        cst::Expr::RecordUpdate { expr, updates, span } => {
            walk_expr_for_section(expr, errors);
            for u in updates {
                check_field(*span, &u.value, false, errors);
                walk_expr_for_section(&u.value, errors);
            }
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_section(func, errors);
        }
        cst::Expr::Lambda { body, .. } => walk_expr_for_section(body, errors),
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_section(left, errors);
            walk_expr_for_section(right, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_section(cond, errors);
            walk_expr_for_section(then_expr, errors);
            walk_expr_for_section(else_expr, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_section(e, errors);
            }
            for alt in alts {
                walk_guarded_for_section(&alt.result, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_section(expr, errors);
                }
            }
            walk_expr_for_section(body, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_section(expr, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_section(expr, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_section(result, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_section(v, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_section(expr, errors);
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_for_section(expr, errors);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_section(e, errors);
            }
        }
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_section(name, errors);
            walk_expr_for_section(pattern, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_section(func, errors);
            walk_expr_for_section(left, errors);
            walk_expr_for_section(right, errors);
        }
        _ => {}
    }
}

/// Equations of the same value name must agree on binder count.
/// `f x y = ...; f = ...` is `ArgListLengthsDiffer`.
fn detect_arg_list_lengths_differ(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Walk consecutive `Decl::Value` runs, recording per-name the
    // (span, binder_count). At the end of each contiguous group of
    // the same name, if any pair of binder counts differs, emit
    // ArgListLengthsDiffer at every offending span.
    let mut runs: HashMap<Symbol, Vec<(Span, usize)>> = HashMap::new();
    let mut last_name: Option<Symbol> = None;
    for d in decls {
        if let cst::Decl::Value { span, name, binders, .. } = d {
            let sym = name.value.symbol();
            // Multi-equation runs are allowed only when ADJACENT.
            // Reset accumulation for non-adjacent re-encounters.
            if last_name != Some(sym) {
                runs.entry(sym).or_default().clear();
            }
            runs.entry(sym).or_default().push((*span, binders.len()));
            last_name = Some(sym);
        } else {
            last_name = None;
        }
    }
    emit_arg_list_diffs(&runs, errors);
    // Also walk into instance member bodies.
    for d in decls {
        if let cst::Decl::Instance { members, .. } = d {
            detect_arg_list_lengths_differ(members, errors);
        }
    }
}

fn emit_arg_list_diffs(
    runs: &HashMap<Symbol, Vec<(Span, usize)>>,
    errors: &mut Vec<ValidationError>,
) {
    for (sym, eqs) in runs {
        if eqs.len() < 2 {
            continue;
        }
        let first_count = eqs[0].1;
        for (span, count) in eqs.iter().skip(1) {
            if *count != first_count {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::ArgListLengthsDiffer(resolve(*sym)),
                });
            }
        }
    }
}

/// Two `instance i :: ...` decls sharing the same instance name.
fn detect_duplicate_instance(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut seen: HashMap<Symbol, Vec<Span>> = HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Instance { name: Some(n), span, .. }
            | cst::Decl::Derive { name: Some(n), span, .. } => {
                seen.entry(n.value.symbol()).or_default().push(*span);
            }
            _ => {}
        }
    }
    for (sym, spans) in seen {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::DuplicateInstance(resolve(sym)),
                });
            }
        }
    }
}

/// Walk the export list (if any) and emit `UnknownExport` for every
/// declared name that isn't visible in the module — neither defined
/// locally, imported under that name, nor re-exported via `module N`.
/// Class methods + ctors travel with their parent decl, so we
/// include them in the local-name set.
fn detect_unknown_exports(
    module: &cst::Module,
    errors: &mut Vec<ValidationError>,
) {
    let Some(spanned) = &module.exports else {
        return;
    };
    // Collect every name that the module either defines locally or
    // brings into scope via an import. For values, we include
    // explicit-list imports; open imports admit any name from the
    // target so we can't enumerate without registry access — those
    // are handled below by skipping the check when at least one
    // open import exists.
    let mut local_values: HashSet<Symbol> = HashSet::new();
    let mut local_classes: HashSet<Symbol> = HashSet::new();
    let mut local_types: HashSet<Symbol> = HashSet::new();
    let mut local_ctors: HashSet<Symbol> = HashSet::new();
    let mut local_value_ops: HashSet<Symbol> = HashSet::new();
    let mut local_type_ops: HashSet<Symbol> = HashSet::new();
    let mut data_ctors_of: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for d in &module.decls {
        match d {
            cst::Decl::Value { name, .. } | cst::Decl::Foreign { name, .. } => {
                local_values.insert(name.value.symbol());
            }
            cst::Decl::Class { name, members, is_kind_sig: false, .. } => {
                local_classes.insert(name.value.symbol());
                for m in members {
                    local_values.insert(m.name.value.symbol());
                }
            }
            cst::Decl::Data { name, constructors, kind_sig: cst::KindSigSource::None, is_role_decl: false, .. } => {
                local_types.insert(name.value.symbol());
                let mut ctor_set: HashSet<Symbol> = HashSet::new();
                for c in constructors {
                    let csym = c.name.value.symbol();
                    local_ctors.insert(csym);
                    ctor_set.insert(csym);
                }
                data_ctors_of.insert(name.value.symbol(), ctor_set);
            }
            cst::Decl::Newtype { name, constructor, .. } => {
                local_types.insert(name.value.symbol());
                let csym = constructor.value.symbol();
                local_ctors.insert(csym);
                let mut ctor_set: HashSet<Symbol> = HashSet::new();
                ctor_set.insert(csym);
                data_ctors_of.insert(name.value.symbol(), ctor_set);
            }
            cst::Decl::TypeAlias { name, .. } => {
                local_types.insert(name.value.symbol());
            }
            cst::Decl::ForeignData { name, .. } => {
                local_types.insert(name.value.symbol());
            }
            cst::Decl::Fixity { operator, is_type, .. } => {
                if *is_type {
                    local_type_ops.insert(operator.value.symbol());
                } else {
                    local_value_ops.insert(operator.value.symbol());
                }
            }
            _ => {}
        }
    }
    // Imports: any unqualified name referenced via `import M (foo)`
    // also counts as in-scope. Conservatively, for open imports
    // (`import M`) we BAIL OUT of the unknown-export check entirely
    // because we can't enumerate target's exports here.
    let mut has_open_import = false;
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue; // qualified imports don't put names in unqualified scope
        }
        match &imp.imports {
            None | Some(cst::ImportList::Hiding(_)) => {
                has_open_import = true;
            }
            Some(cst::ImportList::Explicit(items)) => {
                for item in items {
                    let n = item.name();
                    match item {
                        cst::Import::Value(_) => {
                            local_values.insert(n);
                            local_value_ops.insert(n);
                        }
                        cst::Import::Class(_) => {
                            local_classes.insert(n);
                        }
                        cst::Import::Type(_, members) => {
                            local_types.insert(n);
                            if let Some(m) = members {
                                match m {
                                    cst::DataMembers::All => {}
                                    cst::DataMembers::Explicit(cs) => {
                                        for c in cs {
                                            local_ctors
                                                .insert(c.value.symbol());
                                        }
                                    }
                                }
                            }
                        }
                        cst::Import::TypeOp(_) => {
                            local_type_ops.insert(n);
                        }
                    }
                }
            }
        }
    }
    if has_open_import {
        // Open imports may surface anything; play safe and only
        // check ctor-of-type membership (which is local-decl driven).
    }
    for e in &spanned.value.exports {
        match e {
            cst::Export::Value(vn) => {
                if has_open_import {
                    continue;
                }
                let sym = vn.symbol();
                if !local_values.contains(&sym) && !local_value_ops.contains(&sym) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(resolve(sym)),
                    });
                }
            }
            cst::Export::Class(cn) => {
                if has_open_import {
                    continue;
                }
                let sym = cn.symbol();
                if !local_classes.contains(&sym) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(resolve(sym)),
                    });
                }
            }
            cst::Export::TypeOp(on) => {
                if has_open_import {
                    continue;
                }
                let sym = on.symbol();
                if !local_type_ops.contains(&sym) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(resolve(sym)),
                    });
                }
            }
            cst::Export::Type(tn, members) => {
                let tsym = tn.symbol();
                if !has_open_import && !local_types.contains(&tsym) {
                    errors.push(ValidationError {
                        span: spanned.span,
                        kind: ValidationErrorKind::UnknownExport(resolve(tsym)),
                    });
                }
                // Constructor membership check: for `T(C1, C2)` each
                // C must be a constructor of T (or of any parent if
                // we don't know — checked locally only).
                if let Some(cst::DataMembers::Explicit(cs)) = members {
                    if let Some(allowed) = data_ctors_of.get(&tsym) {
                        for c in cs {
                            let csym = c.value.symbol();
                            if !allowed.contains(&csym) {
                                errors.push(ValidationError {
                                    span: spanned.span,
                                    kind:
                                        ValidationErrorKind::UnknownExportDataConstructor(
                                            resolve(csym),
                                        ),
                                });
                            }
                        }
                    }
                }
            }
            cst::Export::Module(_) => {}
        }
    }
}

/// Refined orphan-kind detection. A `type Foo :: Type` standalone
/// kind sig (KindSigSource::Type) followed by a `data Foo = …`
/// declaration is an orphan kind: the source of the kind sig
/// (TypeAlias) doesn't match the actual decl shape (Data).
fn detect_orphan_kind_source_mismatch(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Map each kind sig name → its source variant.
    let mut kind_source: HashMap<Symbol, (cst::KindSigSource, Span)> =
        HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Data { name, kind_sig: src, span, .. }
                if !matches!(src, cst::KindSigSource::None) =>
            {
                kind_source.insert(name.value.symbol(), (*src, *span));
            }
            cst::Decl::Class { name, is_kind_sig: true, span, .. } => {
                kind_source
                    .insert(name.value.symbol(), (cst::KindSigSource::Class, *span));
            }
            _ => {}
        }
    }
    // For each declaration's actual shape, find the matching kind
    // sig and check the source matches.
    for d in decls {
        let (sym, span, expected_src) = match d {
            cst::Decl::Data { name, kind_sig: cst::KindSigSource::None, is_role_decl: false, span, .. } => {
                (name.value.symbol(), *span, cst::KindSigSource::Data)
            }
            cst::Decl::Newtype { name, span, .. } => {
                (name.value.symbol(), *span, cst::KindSigSource::Newtype)
            }
            cst::Decl::TypeAlias { name, span, .. } => {
                (name.value.symbol(), *span, cst::KindSigSource::Type)
            }
            cst::Decl::Class { name, is_kind_sig: false, span, .. } => {
                (name.value.symbol(), *span, cst::KindSigSource::Class)
            }
            _ => continue,
        };
        let _ = sym;
        if let Some((src, sig_span)) = kind_source.get(&sym) {
            // Newtype may use `data Foo :: Kind` OR `newtype Foo ::
            // Kind` interchangeably — the original compiler accepts
            // both. Likewise data may use `data` only. Type aliases
            // need `type`. Classes need `class`.
            let ok = match (expected_src, src) {
                (cst::KindSigSource::Newtype, cst::KindSigSource::Newtype)
                | (cst::KindSigSource::Newtype, cst::KindSigSource::Data)
                | (cst::KindSigSource::Data, cst::KindSigSource::Data)
                | (cst::KindSigSource::Type, cst::KindSigSource::Type)
                | (cst::KindSigSource::Class, cst::KindSigSource::Class) => true,
                _ => false,
            };
            if !ok {
                errors.push(ValidationError {
                    span: *sig_span,
                    kind: ValidationErrorKind::OrphanKindDeclaration(resolve(sym)),
                });
            }
        }
        let _ = span;
    }
}

/// Inside an instance body, a `TypeSignature` for a name without a
/// matching `Value` definition becomes `OrphanTypeDeclaration`.
fn detect_instance_orphan_type_signatures(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        if let cst::Decl::Instance { members, .. } = d {
            let mut value_names: HashSet<Symbol> = HashSet::new();
            for m in members {
                if let cst::Decl::Value { name, .. } = m {
                    value_names.insert(name.value.symbol());
                }
            }
            for m in members {
                if let cst::Decl::TypeSignature { name, span, .. } = m {
                    let sym = name.value.symbol();
                    if !value_names.contains(&sym) {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::OrphanTypeDeclaration(
                                resolve(sym),
                            ),
                        });
                    }
                }
            }
        }
    }
}

/// `derive newtype instance ...` validation. Two failure modes:
///   - `derive newtype instance Nullary` — class is nullary so
///     there's no head to derive over.
///   - `derive newtype instance functorX :: Functor X` — the
///     instance head's type isn't a saturated newtype application,
///     so newtype-coercion can't produce the required instance.
///     Rule we fire on: head is a bare local newtype constructor
///     (zero args) but the class has arity 1 expecting `f a`.
///     Original compiler reports as `InvalidNewtypeInstance`.
fn detect_invalid_newtype_derive(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Build: newtype-name → (type-vars, body)
    let mut local_newtypes: HashMap<Symbol, (Vec<Symbol>, &cst::TypeExpr)> =
        HashMap::new();
    for d in decls {
        if let cst::Decl::Newtype { name, type_vars, ty, .. } = d {
            let vs: Vec<Symbol> =
                type_vars.iter().map(|v| v.value.symbol()).collect();
            local_newtypes.insert(name.value.symbol(), (vs, ty));
        }
    }
    for d in decls {
        if let cst::Decl::Derive { newtype: true, types, class_name, span, .. } = d
        {
            // Nullary classes: `derive newtype instance Nullary` —
            // no head to derive over.
            if types.is_empty() {
                let display = resolve(class_name.to_qi().name);
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::InvalidNewtypeInstance(display),
                });
                continue;
            }
            // `derive newtype instance Functor X` for
            // `newtype X a = X a`: the newtype's representation
            // body is a bare type variable, so newtype-coercion
            // can't pull a `Functor a` instance out of thin air
            // (`a` is universally quantified at the instance).
            // Reference compiler reports as InvalidNewtypeInstance.
            //
            // Fires only when the head is a bare local newtype
            // constructor with no args (the class is expected to
            // have arity 1, like `Functor`, hence X is passed
            // unsaturated).
            let head = types.last().unwrap();
            let head_sym = match peel_parens(head) {
                cst::TypeExpr::Constructor { name, .. } => {
                    let qi = name.to_qi();
                    if qi.module.is_some() {
                        continue;
                    }
                    qi.name
                }
                _ => continue,
            };
            let (nt_vars, nt_body) = match local_newtypes.get(&head_sym) {
                Some(p) => p,
                None => continue,
            };
            // Body must be a bare Var that is the LAST nt-var.
            let body_inner = peel_parens(nt_body);
            if let cst::TypeExpr::Var { name, .. } = body_inner {
                if let Some(last) = nt_vars.last() {
                    if name.value.symbol() == *last {
                        let display = resolve(class_name.to_qi().name);
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::InvalidNewtypeInstance(
                                display,
                            ),
                        });
                    }
                }
            }
        }
    }
}

/// `foreign import a' :: …` — apostrophe in an FFI declaration name
/// is deprecated.
fn detect_deprecated_ffi_prime(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        if let cst::Decl::Foreign { name, span, .. } = d {
            let s = resolve(name.value.symbol());
            if s.contains('\'') {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::DeprecatedFFIPrime(s),
                });
            }
        }
    }
}

/// `foo n x = x <> bar n x` (mutually recursive with `bar`,
/// no top-level signature): the body uses `<>` on parameter
/// `x`, so generalization would need to introduce a `Semigroup`
/// constraint on the recursive function's quantified type-var.
/// Reference compiler reports as `CannotGeneralizeRecursiveFunction`.
///
/// Detection (CST-only heuristic):
/// 1. Build local-value names + signed names + ref-graph from
///    each Decl::Value's body (top-level only — no descent into
///    where / let / case bodies, since those scopes have their
///    own binders).
/// 2. Run Tarjan SCC. A decl is recursive iff in an SCC with
///    size > 1 OR it self-references.
/// 3. Per-decl: collect its parameter-binder names. Walk the
///    top-level body for `Op` with at least one operand that
///    bottom-resolves to a Var of one of its parameter binders.
///    If found and the decl is recursive + unsigned → emit.
fn detect_cannot_generalize_recursive_function(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut local_values: HashSet<Symbol> = HashSet::new();
    let mut signed: HashSet<Symbol> = HashSet::new();
    for d in decls {
        match d {
            cst::Decl::Value { name, .. } => {
                local_values.insert(name.value.symbol());
            }
            cst::Decl::TypeSignature { name, .. } => {
                signed.insert(name.value.symbol());
            }
            _ => {}
        }
    }
    if local_values.is_empty() {
        return;
    }
    // Build per-decl ref set and (per-decl, per-equation) the set
    // of parameter binder names. We aggregate across all equations
    // for the same decl name.
    let mut refs: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    let mut name_spans: HashMap<Symbol, Span> = HashMap::new();
    let mut params_for: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    let mut bodies_for: HashMap<Symbol, Vec<&cst::GuardedExpr>> = HashMap::new();
    for d in decls {
        if let cst::Decl::Value { name, binders, guarded, .. } = d {
            let n = name.value.symbol();
            name_spans.entry(n).or_insert(name.span);
            let mut seen: HashSet<Symbol> = HashSet::new();
            let mut dummy_op = false;
            walk_guarded_for_recur_check(
                guarded,
                &local_values,
                &mut seen,
                &mut dummy_op,
            );
            refs.entry(n).or_default().extend(seen);
            // Collect parameter binder names.
            let p_set = params_for.entry(n).or_default();
            for b in binders {
                collect_binder_var_names(b, p_set);
            }
            bodies_for.entry(n).or_default().push(guarded);
        }
    }
    // SCC.
    let nodes: Vec<Symbol> = refs.keys().copied().collect();
    let mut idx_of: HashMap<Symbol, usize> = HashMap::new();
    for (i, n) in nodes.iter().enumerate() {
        idx_of.insert(*n, i);
    }
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
    for (n, succ) in &refs {
        if let Some(&i) = idx_of.get(n) {
            for s in succ {
                if let Some(&j) = idx_of.get(s) {
                    adj[i].push(j);
                }
            }
        }
    }
    let sccs = tarjan_scc(&adj);
    let mut recursive: HashSet<Symbol> = HashSet::new();
    for scc in &sccs {
        let size = scc.len();
        for &i in scc {
            let n = nodes[i];
            let self_loop = adj[i].contains(&i);
            if size > 1 || self_loop {
                recursive.insert(n);
            }
        }
    }
    let mut emitted: HashSet<Symbol> = HashSet::new();
    for n in &nodes {
        if signed.contains(n) || !recursive.contains(n) {
            continue;
        }
        let params = match params_for.get(n) {
            Some(p) if !p.is_empty() => p,
            _ => continue,
        };
        let bodies = match bodies_for.get(n) {
            Some(bs) => bs,
            None => continue,
        };
        let mut hit = false;
        for body in bodies {
            if guarded_has_param_op(body, params) {
                hit = true;
                break;
            }
        }
        if !hit {
            continue;
        }
        if !emitted.insert(*n) {
            continue;
        }
        let span = name_spans.get(n).copied().unwrap_or(crate::span::Span {
            start: 0,
            end: 0,
        });
        errors.push(ValidationError {
            span,
            kind: ValidationErrorKind::CannotGeneralizeRecursiveFunction(
                resolve(*n),
            ),
        });
    }
}

fn collect_binder_var_names(b: &cst::Binder, out: &mut HashSet<Symbol>) {
    match b {
        cst::Binder::Var { name, .. } => {
            out.insert(name.value.symbol());
        }
        cst::Binder::Parens { binder, .. }
        | cst::Binder::Typed { binder, .. } => {
            collect_binder_var_names(binder, out);
        }
        cst::Binder::As { name, binder, .. } => {
            out.insert(name.value.symbol());
            collect_binder_var_names(binder, out);
        }
        cst::Binder::Constructor { args, .. } => {
            for a in args {
                collect_binder_var_names(a, out);
            }
        }
        cst::Binder::Record { fields, .. } => {
            for f in fields {
                if let Some(b) = &f.binder {
                    collect_binder_var_names(b, out);
                }
            }
        }
        cst::Binder::Array { elements, .. } => {
            for e in elements {
                collect_binder_var_names(e, out);
            }
        }
        cst::Binder::Op { left, right, .. } => {
            collect_binder_var_names(left, out);
            collect_binder_var_names(right, out);
        }
        _ => {}
    }
}

fn guarded_has_param_op(
    g: &cst::GuardedExpr,
    params: &HashSet<Symbol>,
) -> bool {
    match g {
        cst::GuardedExpr::Unconditional(expr) => {
            expr_has_param_op(expr, params)
        }
        cst::GuardedExpr::Guarded(guards) => {
            guards.iter().any(|g| expr_has_param_op(&g.expr, params))
        }
    }
}

fn expr_has_param_op(e: &cst::Expr, params: &HashSet<Symbol>) -> bool {
    match e {
        cst::Expr::Op { left, right, .. } => {
            let l = peel_expr_parens(left);
            let r = peel_expr_parens(right);
            let is_param_var = |e: &cst::Expr| {
                if let cst::Expr::Var { name, .. } = e {
                    let qi = name.to_qi();
                    return qi.module.is_none() && params.contains(&qi.name);
                }
                false
            };
            // Flag iff at least one operand is a param-Var AND
            // no operand is a primitive-type-pinning literal. A
            // literal like `0.0` pins its operand's type to a
            // concrete type (Number), eliminating the constraint
            // generalization issue. `passes_MutRec`'s `g x = f
            // (x / 0.0)` falls in this safe category.
            if (is_param_var(l) || is_param_var(r))
                && !is_pinning_literal(l)
                && !is_pinning_literal(r)
            {
                return true;
            }
            expr_has_param_op(left, params) || expr_has_param_op(right, params)
        }
        cst::Expr::App { func, arg, .. } => {
            expr_has_param_op(func, params) || expr_has_param_op(arg, params)
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => expr_has_param_op(expr, params),
        cst::Expr::Lambda { body, .. } => expr_has_param_op(body, params),
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            expr_has_param_op(cond, params)
                || expr_has_param_op(then_expr, params)
                || expr_has_param_op(else_expr, params)
        }
        cst::Expr::Case { exprs, alts, .. } => {
            exprs.iter().any(|e| expr_has_param_op(e, params))
                || alts
                    .iter()
                    .any(|a| guarded_has_param_op(&a.result, params))
        }
        cst::Expr::Record { fields, .. } => fields.iter().any(|f| {
            f.value.as_ref().map_or(false, |v| expr_has_param_op(v, params))
        }),
        cst::Expr::Array { elements, .. } => {
            elements.iter().any(|e| expr_has_param_op(e, params))
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            expr_has_param_op(expr, params)
                || updates.iter().any(|u| expr_has_param_op(&u.value, params))
        }
        _ => false,
    }
}

fn is_pinning_literal(e: &cst::Expr) -> bool {
    match e {
        cst::Expr::Literal { lit, .. } => matches!(
            lit,
            cst::Literal::Int(_)
                | cst::Literal::Float(_)
                | cst::Literal::String(_)
                | cst::Literal::Char(_)
                | cst::Literal::Boolean(_)
        ),
        cst::Expr::Negate { expr, .. } => is_pinning_literal(expr),
        cst::Expr::Parens { expr, .. } => is_pinning_literal(expr),
        _ => false,
    }
}

fn peel_expr_parens(e: &cst::Expr) -> &cst::Expr {
    let mut cur = e;
    loop {
        match cur {
            cst::Expr::Parens { expr, .. }
            | cst::Expr::TypeAnnotation { expr, .. } => cur = expr,
            _ => return cur,
        }
    }
}

fn tarjan_scc(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = adj.len();
    let mut idx = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut index_counter: usize = 0;
    let mut sccs: Vec<Vec<usize>> = Vec::new();

    fn strong(
        v: usize,
        adj: &[Vec<usize>],
        idx: &mut Vec<usize>,
        low: &mut Vec<usize>,
        on_stack: &mut Vec<bool>,
        stack: &mut Vec<usize>,
        index_counter: &mut usize,
        sccs: &mut Vec<Vec<usize>>,
    ) {
        idx[v] = *index_counter;
        low[v] = *index_counter;
        *index_counter += 1;
        stack.push(v);
        on_stack[v] = true;
        for &w in &adj[v] {
            if idx[w] == usize::MAX {
                strong(w, adj, idx, low, on_stack, stack, index_counter, sccs);
                low[v] = low[v].min(low[w]);
            } else if on_stack[w] {
                low[v] = low[v].min(idx[w]);
            }
        }
        if low[v] == idx[v] {
            let mut comp: Vec<usize> = Vec::new();
            loop {
                let w = stack.pop().unwrap();
                on_stack[w] = false;
                comp.push(w);
                if w == v {
                    break;
                }
            }
            sccs.push(comp);
        }
    }

    for v in 0..n {
        if idx[v] == usize::MAX {
            strong(
                v,
                adj,
                &mut idx,
                &mut low,
                &mut on_stack,
                &mut stack,
                &mut index_counter,
                &mut sccs,
            );
        }
    }
    sccs
}

fn walk_guarded_for_recur_check(
    g: &cst::GuardedExpr,
    local_values: &HashSet<Symbol>,
    seen: &mut HashSet<Symbol>,
    op_used: &mut bool,
) {
    match g {
        cst::GuardedExpr::Unconditional(expr) => {
            walk_expr_for_recur_check(expr, local_values, seen, op_used);
        }
        cst::GuardedExpr::Guarded(guards) => {
            for gd in guards {
                for p in &gd.patterns {
                    if let cst::GuardPattern::Boolean(e) = p {
                        walk_expr_for_recur_check(
                            e,
                            local_values,
                            seen,
                            op_used,
                        );
                    } else if let cst::GuardPattern::Pattern(_, e) = p {
                        walk_expr_for_recur_check(
                            e,
                            local_values,
                            seen,
                            op_used,
                        );
                    }
                }
                walk_expr_for_recur_check(
                    &gd.expr,
                    local_values,
                    seen,
                    op_used,
                );
            }
        }
    }
}

fn walk_expr_for_recur_check(
    e: &cst::Expr,
    local_values: &HashSet<Symbol>,
    seen: &mut HashSet<Symbol>,
    op_used: &mut bool,
) {
    match e {
        cst::Expr::Var { name, .. } => {
            let qi = name.to_qi();
            if qi.module.is_none() && local_values.contains(&qi.name) {
                seen.insert(qi.name);
            }
        }
        cst::Expr::Op { left, right, .. } => {
            *op_used = true;
            walk_expr_for_recur_check(left, local_values, seen, op_used);
            walk_expr_for_recur_check(right, local_values, seen, op_used);
        }
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_recur_check(func, local_values, seen, op_used);
            walk_expr_for_recur_check(arg, local_values, seen, op_used);
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_for_recur_check(expr, local_values, seen, op_used);
        }
        cst::Expr::Lambda { body, .. } => {
            walk_expr_for_recur_check(body, local_values, seen, op_used);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_recur_check(cond, local_values, seen, op_used);
            walk_expr_for_recur_check(then_expr, local_values, seen, op_used);
            walk_expr_for_recur_check(else_expr, local_values, seen, op_used);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for ex in exprs {
                walk_expr_for_recur_check(ex, local_values, seen, op_used);
            }
            for alt in alts {
                walk_guarded_for_recur_check(
                    &alt.result,
                    local_values,
                    seen,
                    op_used,
                );
            }
        }
        _ => {}
    }
}

/// `module M (a) where data A = A; a = A`: exporting `a` exposes
/// hidden type `A`. Reference compiler reports as
/// `TransitiveExportError`.
///
/// CST-only approximation: for every locally-declared exported
/// value, walk its body collecting referenced data constructors,
/// look up each ctor's parent data type, and flag if the parent
/// type is locally declared but NOT in the export list.
fn detect_transitive_export_via_hidden_type(
    module: &cst::Module,
    errors: &mut Vec<ValidationError>,
) {
    let export_list: &Vec<cst::Export> = match &module.exports {
        Some(es) => &es.value.exports,
        None => return,
    };
    // Local data/newtype/alias name set, plus a map ctor →
    // (parent type symbol). Type aliases don't have ctors but
    // we still track their names in `local_types` to know what's
    // "ours".
    let mut local_types: HashSet<Symbol> = HashSet::new();
    let mut ctor_to_type: HashMap<Symbol, Symbol> = HashMap::new();
    for d in &module.decls {
        match d {
            cst::Decl::Data { name, constructors, .. } => {
                let tsym = name.value.symbol();
                local_types.insert(tsym);
                for c in constructors {
                    ctor_to_type.insert(c.name.value.symbol(), tsym);
                }
            }
            cst::Decl::Newtype { name, constructor, .. } => {
                let tsym = name.value.symbol();
                local_types.insert(tsym);
                ctor_to_type.insert(constructor.value.symbol(), tsym);
            }
            cst::Decl::TypeAlias { name, .. }
            | cst::Decl::ForeignData { name, .. } => {
                local_types.insert(name.value.symbol());
            }
            _ => {}
        }
    }
    // Build the exported-types set from the export list.
    let mut exported_types: HashSet<Symbol> = HashSet::new();
    let mut exported_values: HashSet<Symbol> = HashSet::new();
    let mut wild_module_export = false;
    for e in export_list {
        match e {
            cst::Export::Type(t, _) => {
                exported_types.insert(t.symbol());
            }
            cst::Export::Value(n) => {
                exported_values.insert(n.symbol());
            }
            cst::Export::Module(_) => {
                wild_module_export = true;
            }
            _ => {}
        }
    }
    if wild_module_export {
        // `module X` re-exports may bring more types into scope —
        // we'd need the registry to know what they cover. Bail.
        return;
    }
    if exported_values.is_empty() {
        return;
    }
    // For each exported, locally-defined value decl, look at its
    // body. To stay sound without inference, only flag when the
    // body's TOP-LEVEL expression is a bare Constructor (modulo
    // Parens / TypeAnnotation wrappers). This catches the
    // simple `a = A` fixture pattern without false-positiving on
    // helpers that USE local ctors internally but expose only
    // public types in their result type.
    for d in &module.decls {
        if let cst::Decl::Value { name, binders, guarded, .. } = d {
            // Only no-arg value bindings. With binders the value
            // is a function — its result type isn't determinable
            // from a syntactic scan.
            if !binders.is_empty() {
                continue;
            }
            let vsym = name.value.symbol();
            if !exported_values.contains(&vsym) {
                continue;
            }
            let body_expr = match guarded {
                cst::GuardedExpr::Unconditional(e) => e.as_ref(),
                _ => continue,
            };
            let inner = peel_parens_typeann(body_expr);
            if let cst::Expr::Constructor { name: ctor_name, .. } = inner {
                let qi = ctor_name.to_qi();
                if qi.module.is_none() {
                    if let Some(parent) = ctor_to_type.get(&qi.name) {
                        if local_types.contains(parent)
                            && !exported_types.contains(parent)
                        {
                            errors.push(ValidationError {
                                span: name.span,
                                kind: ValidationErrorKind::TransitiveExportError(
                                    resolve(*parent),
                                ),
                            });
                        }
                    }
                }
            }
        }
    }
}

fn peel_parens_typeann(e: &cst::Expr) -> &cst::Expr {
    let mut cur = e;
    loop {
        match cur {
            cst::Expr::Parens { expr, .. }
            | cst::Expr::TypeAnnotation { expr, .. } => cur = expr,
            _ => return cur,
        }
    }
}

/// `f x | 1 <- x = x` — every equation of `f` has only guarded
/// branches with no `| true` / `| otherwise` / pattern-only
/// fallback. The function may not match every input, so the
/// reference compiler treats it as non-exhaustive. Emit
/// `NonExhaustiveGuardOnlyDecl` (codes as `NonExhaustivePattern`).
///
/// Skips decls whose top-level signature carries a `Partial =>`
/// constraint — the user has explicitly opted out of
/// exhaustiveness.
fn detect_non_exhaustive_guard_only_decl(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Build local data-decl info: ctor → number-of-siblings. A
    // pattern `C x` is irrefutable iff `C` is the only ctor of
    // its parent. (We don't see imported types here; pattern
    // guards involving imported single-ctor types fall through to
    // upstream exhaustiveness checks.)
    let mut ctor_sibling_count: HashMap<Symbol, usize> = HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Data { constructors, .. } => {
                let n = constructors.len();
                for c in constructors {
                    ctor_sibling_count.insert(c.name.value.symbol(), n);
                }
            }
            cst::Decl::Newtype { constructor, .. } => {
                ctor_sibling_count.insert(constructor.value.symbol(), 1);
            }
            _ => {}
        }
    }

    let mut partial_decls: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::TypeSignature { name, ty, .. } = d {
            if type_has_partial(ty) {
                partial_decls.insert(name.value.symbol());
            }
        }
    }
    let mut by_name: HashMap<Symbol, Vec<(&cst::GuardedExpr, Span)>> =
        HashMap::new();
    let mut name_spans: HashMap<Symbol, Span> = HashMap::new();
    for d in decls {
        if let cst::Decl::Value { name, guarded, span, .. } = d {
            let n = name.value.symbol();
            name_spans.entry(n).or_insert(name.span);
            by_name.entry(n).or_default().push((guarded, *span));
        }
    }
    for (n, eqs) in by_name {
        if partial_decls.contains(&n) {
            continue;
        }
        let any_uncond = eqs
            .iter()
            .any(|(g, _)| guarded_has_fallback(g, &ctor_sibling_count));
        if any_uncond {
            continue;
        }
        let span = name_spans.get(&n).copied().unwrap_or_else(|| {
            eqs.first().map(|(_, s)| *s).unwrap_or(crate::span::Span {
                start: 0,
                end: 0,
            })
        });
        errors.push(ValidationError {
            span,
            kind: ValidationErrorKind::NonExhaustiveGuardOnlyDecl(resolve(n)),
        });
    }
}

/// True iff a `GuardedExpr` has at least one unconditional branch
/// (Unconditional, or a `Guarded` with a `| true` / `| otherwise`
/// / irrefutable-pattern fallback).
fn guarded_has_fallback(
    g: &cst::GuardedExpr,
    ctor_sibling_count: &HashMap<Symbol, usize>,
) -> bool {
    match g {
        cst::GuardedExpr::Unconditional(_) => true,
        cst::GuardedExpr::Guarded(guards) => guards
            .iter()
            .any(|g| guard_is_uncond(g, ctor_sibling_count)),
    }
}

fn guard_is_uncond(
    g: &cst::Guard,
    ctor_sibling_count: &HashMap<Symbol, usize>,
) -> bool {
    if g.patterns.len() != 1 {
        return false;
    }
    match &g.patterns[0] {
        cst::GuardPattern::Boolean(expr) => is_true_or_otherwise(expr),
        cst::GuardPattern::Pattern(binder, _) => {
            binder_is_irrefutable(binder, ctor_sibling_count)
        }
    }
}

fn is_true_or_otherwise(e: &cst::Expr) -> bool {
    match e {
        cst::Expr::Literal { lit: cst::Literal::Boolean(true), .. } => true,
        cst::Expr::Var { name, .. } => {
            let qi = name.to_qi();
            resolve(qi.name) == "otherwise"
        }
        cst::Expr::Parens { expr, .. } => is_true_or_otherwise(expr),
        _ => false,
    }
}

fn binder_is_irrefutable(
    b: &cst::Binder,
    ctor_sibling_count: &HashMap<Symbol, usize>,
) -> bool {
    match b {
        cst::Binder::Wildcard { .. } | cst::Binder::Var { .. } => true,
        cst::Binder::Parens { binder, .. } => {
            binder_is_irrefutable(binder, ctor_sibling_count)
        }
        cst::Binder::As { binder, .. } => {
            binder_is_irrefutable(binder, ctor_sibling_count)
        }
        cst::Binder::Typed { binder, .. } => {
            binder_is_irrefutable(binder, ctor_sibling_count)
        }
        cst::Binder::Record { fields, .. } => fields.iter().all(|f| {
            f.binder
                .as_ref()
                .map_or(true, |b| binder_is_irrefutable(b, ctor_sibling_count))
        }),
        cst::Binder::Literal { .. } => false,
        cst::Binder::Constructor { name, args, .. } => {
            let qi = name.to_qi();
            // Local single-ctor types: irrefutable. Multi-ctor or
            // unknown (imported / undeclared): refutable.
            let solo = qi.module.is_none()
                && ctor_sibling_count.get(&qi.name).copied() == Some(1);
            if !solo {
                return false;
            }
            args.iter()
                .all(|a| binder_is_irrefutable(a, ctor_sibling_count))
        }
        cst::Binder::Op { .. } | cst::Binder::Array { .. } => false,
    }
}

fn type_has_partial(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            constraints.iter().any(|c| {
                let qi = c.class.to_qi();
                resolve(qi.name) == "Partial"
            }) || type_has_partial(ty)
        }
        cst::TypeExpr::Forall { ty, .. } => type_has_partial(ty),
        cst::TypeExpr::Parens { ty, .. } => type_has_partial(ty),
        _ => false,
    }
}

/// `f @Int` where `f`'s declared sig either has no top-level
/// `forall` or its outer forall is INVISIBLE (`forall a.` not
/// `forall @a.`). Reference compiler reports as
/// `CannotApplyExpressionOfTypeOnType`.
///
/// CST-only approximation: build a map from local value name to
/// its TypeSignature's outer-forall visibility (None = no forall,
/// Some(false) = invisible, Some(true) = visible). Then walk
/// every `Expr::VisibleTypeApp`, resolve the func to a local
/// signed value, and flag if the visibility check fails.
fn detect_visible_type_app_on_non_visible_forall(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut sig_visibility: HashMap<Symbol, Option<bool>> = HashMap::new();
    for d in decls {
        if let cst::Decl::TypeSignature { name, ty, .. } = d {
            let vis = outer_forall_visible(ty);
            sig_visibility.insert(name.value.symbol(), vis);
        }
    }
    if sig_visibility.is_empty() {
        return;
    }
    for d in decls {
        if let cst::Decl::Value { binders, guarded, where_clause, .. } = d {
            for b in binders {
                walk_binder_for_vta_check(b, &sig_visibility, errors);
            }
            walk_guarded_for_vta_check(guarded, &sig_visibility, errors);
            for w in where_clause {
                walk_let_for_vta_check(w, &sig_visibility, errors);
            }
        }
    }
}

/// Returns:
///   `None` if the type has no outer-level `Forall` (after
///   peeling Parens / Constrained).
///   `Some(false)` if the outer forall exists but ALL of its
///   vars are invisible — VTA can't reach any of them.
///   `Some(true)` if the outer forall has AT LEAST ONE visible
///   (`@a`) var. PureScript VTA skips leading invisible vars to
///   apply to the next visible one.
fn outer_forall_visible(ty: &cst::TypeExpr) -> Option<bool> {
    let mut cur = ty;
    loop {
        match cur {
            cst::TypeExpr::Parens { ty: inner, .. }
            | cst::TypeExpr::Constrained { ty: inner, .. } => cur = inner,
            cst::TypeExpr::Forall { vars, .. } => {
                let any_visible = vars.iter().any(|(_, v, _)| *v);
                return Some(any_visible);
            }
            _ => return None,
        }
    }
}

fn walk_binder_for_vta_check(
    b: &cst::Binder,
    sig_visibility: &HashMap<Symbol, Option<bool>>,
    errors: &mut Vec<ValidationError>,
) {
    match b {
        cst::Binder::Typed { binder, .. } | cst::Binder::Parens { binder, .. } => {
            walk_binder_for_vta_check(binder, sig_visibility, errors);
        }
        cst::Binder::Constructor { args, .. } => {
            for a in args {
                walk_binder_for_vta_check(a, sig_visibility, errors);
            }
        }
        cst::Binder::Record { fields, .. } => {
            for f in fields {
                if let Some(b) = &f.binder {
                    walk_binder_for_vta_check(b, sig_visibility, errors);
                }
            }
        }
        cst::Binder::Array { elements, .. } => {
            for e in elements {
                walk_binder_for_vta_check(e, sig_visibility, errors);
            }
        }
        cst::Binder::As { binder, .. } => {
            walk_binder_for_vta_check(binder, sig_visibility, errors);
        }
        cst::Binder::Op { left, right, .. } => {
            walk_binder_for_vta_check(left, sig_visibility, errors);
            walk_binder_for_vta_check(right, sig_visibility, errors);
        }
        _ => {}
    }
}

fn walk_guarded_for_vta_check(
    g: &cst::GuardedExpr,
    sig_visibility: &HashMap<Symbol, Option<bool>>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(expr) => {
            walk_expr_for_vta_check(expr, sig_visibility, errors);
        }
        cst::GuardedExpr::Guarded(guards) => {
            for gd in guards {
                walk_expr_for_vta_check(&gd.expr, sig_visibility, errors);
            }
        }
    }
}

fn walk_expr_for_vta_check(
    e: &cst::Expr,
    sig_visibility: &HashMap<Symbol, Option<bool>>,
    errors: &mut Vec<ValidationError>,
) {
    match e {
        cst::Expr::VisibleTypeApp { func, span, .. } => {
            // Find the underlying var (peel Parens / TypeAnnotation).
            let mut cur: &cst::Expr = func;
            loop {
                match cur {
                    cst::Expr::Parens { expr, .. }
                    | cst::Expr::TypeAnnotation { expr, .. } => cur = expr,
                    _ => break,
                }
            }
            if let cst::Expr::Var { name, .. } = cur {
                let qi = name.to_qi();
                if qi.module.is_none() {
                    if let Some(vis) = sig_visibility.get(&qi.name) {
                        let bad = match vis {
                            None => true,
                            Some(false) => true,
                            Some(true) => false,
                        };
                        if bad {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind
                                    ::CannotApplyExpressionOfTypeOnType(
                                    resolve(qi.name),
                                ),
                            });
                        }
                    }
                }
            }
            walk_expr_for_vta_check(func, sig_visibility, errors);
        }
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_vta_check(func, sig_visibility, errors);
            walk_expr_for_vta_check(arg, sig_visibility, errors);
        }
        cst::Expr::Parens { expr, .. }
        | cst::Expr::TypeAnnotation { expr, .. }
        | cst::Expr::Negate { expr, .. } => {
            walk_expr_for_vta_check(expr, sig_visibility, errors);
        }
        cst::Expr::Lambda { body, .. } => {
            walk_expr_for_vta_check(body, sig_visibility, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_vta_check(cond, sig_visibility, errors);
            walk_expr_for_vta_check(then_expr, sig_visibility, errors);
            walk_expr_for_vta_check(else_expr, sig_visibility, errors);
        }
        cst::Expr::Let { bindings, body, .. } => {
            for lb in bindings {
                walk_let_for_vta_check(lb, sig_visibility, errors);
            }
            walk_expr_for_vta_check(body, sig_visibility, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for ex in exprs {
                walk_expr_for_vta_check(ex, sig_visibility, errors);
            }
            for alt in alts {
                walk_guarded_for_vta_check(&alt.result, sig_visibility, errors);
            }
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_vta_check(left, sig_visibility, errors);
            walk_expr_for_vta_check(right, sig_visibility, errors);
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_vta_check(v, sig_visibility, errors);
                }
            }
        }
        cst::Expr::Array { elements, .. } => {
            for el in elements {
                walk_expr_for_vta_check(el, sig_visibility, errors);
            }
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_vta_check(expr, sig_visibility, errors);
            for u in updates {
                walk_expr_for_vta_check(&u.value, sig_visibility, errors);
            }
        }
        cst::Expr::Do { statements, .. } => {
            for s in statements {
                walk_do_for_vta_check(s, sig_visibility, errors);
            }
        }
        cst::Expr::Ado { statements, result, .. } => {
            for s in statements {
                walk_do_for_vta_check(s, sig_visibility, errors);
            }
            walk_expr_for_vta_check(result, sig_visibility, errors);
        }
        _ => {}
    }
}

fn walk_let_for_vta_check(
    lb: &cst::LetBinding,
    sig_visibility: &HashMap<Symbol, Option<bool>>,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::LetBinding::Value { expr, .. } = lb {
        walk_expr_for_vta_check(expr, sig_visibility, errors);
    }
}

fn walk_do_for_vta_check(
    s: &cst::DoStatement,
    sig_visibility: &HashMap<Symbol, Option<bool>>,
    errors: &mut Vec<ValidationError>,
) {
    match s {
        cst::DoStatement::Bind { expr, .. }
        | cst::DoStatement::Discard { expr, .. } => {
            walk_expr_for_vta_check(expr, sig_visibility, errors);
        }
        cst::DoStatement::Let { bindings, .. } => {
            for lb in bindings {
                walk_let_for_vta_check(lb, sig_visibility, errors);
            }
        }
    }
}

/// `foreign import data X :: C => K` — kind signatures can't
/// carry constraint arrows. Walks each `ForeignData`'s kind and
/// flags any `Constrained` shape. Reference compiler reports as
/// `UnsupportedTypeInKind`.
fn detect_unsupported_type_in_kind(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        if let cst::Decl::ForeignData { name, kind, span, .. } = d {
            if kind_contains_constraint(kind) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::UnsupportedTypeInKind(resolve(
                        name.value.symbol(),
                    )),
                });
            }
        }
    }
}

fn kind_contains_constraint(te: &cst::TypeExpr) -> bool {
    match te {
        cst::TypeExpr::Constrained { .. } => true,
        cst::TypeExpr::Forall { ty, .. } => kind_contains_constraint(ty),
        cst::TypeExpr::Function { from, to, .. } => {
            kind_contains_constraint(from) || kind_contains_constraint(to)
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            kind_contains_constraint(constructor)
                || kind_contains_constraint(arg)
        }
        cst::TypeExpr::Parens { ty, .. } => kind_contains_constraint(ty),
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            kind_contains_constraint(ty) || kind_contains_constraint(kind)
        }
        _ => false,
    }
}

/// Walks every `Binder::Typed` and every `Expr::TypeAnnotation` in
/// the module, flagging annotations whose type is a bare local
/// data/newtype/alias constructor with non-zero arity (`(x :: F)`
/// where `data F a = …`). The reference compiler emits
/// `ExpectedType` for these — the annotation requires a
/// `Type`-kinded type, but `F` has kind `Type -> Type`.
fn detect_expected_type_in_annotations(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut local_higher_arity: HashMap<Symbol, usize> = HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Data { name, type_vars, .. }
            | cst::Decl::Newtype { name, type_vars, .. } => {
                let n = type_vars.len();
                if n > 0 {
                    local_higher_arity.insert(name.value.symbol(), n);
                }
            }
            cst::Decl::TypeAlias { name, type_vars, .. } => {
                let n = type_vars.len();
                if n > 0 {
                    local_higher_arity.insert(name.value.symbol(), n);
                }
            }
            _ => {}
        }
    }
    if local_higher_arity.is_empty() {
        return;
    }
    for d in decls {
        match d {
            cst::Decl::Value { binders, guarded, where_clause, .. } => {
                for b in binders {
                    walk_binder_for_expected_type(
                        b,
                        &local_higher_arity,
                        errors,
                    );
                }
                walk_guarded_expr_for_expected_type(
                    guarded,
                    &local_higher_arity,
                    errors,
                );
                for w in where_clause {
                    walk_let_binding_for_expected_type(
                        w,
                        &local_higher_arity,
                        errors,
                    );
                }
            }
            // `test :: List` where `List` is a bare arity-1
            // constructor — the sig itself is the annotation.
            cst::Decl::TypeSignature { ty, span, .. } => {
                check_type_annotation_for_expected_type(
                    ty,
                    *span,
                    &local_higher_arity,
                    errors,
                );
            }
            _ => {}
        }
    }
}

fn check_type_annotation_for_expected_type(
    ty: &cst::TypeExpr,
    span: Span,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    let inner = peel_parens(ty);
    if let cst::TypeExpr::Constructor { name, .. } = inner {
        let qi = name.to_qi();
        if qi.module.is_none() {
            if arities.contains_key(&qi.name) {
                errors.push(ValidationError {
                    span,
                    kind: ValidationErrorKind::ExpectedType(resolve(qi.name)),
                });
            }
        }
    }
}

fn walk_binder_for_expected_type(
    b: &cst::Binder,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match b {
        cst::Binder::Typed { binder, ty, span } => {
            check_type_annotation_for_expected_type(ty, *span, arities, errors);
            walk_binder_for_expected_type(binder, arities, errors);
        }
        cst::Binder::Parens { binder, .. } => {
            walk_binder_for_expected_type(binder, arities, errors);
        }
        cst::Binder::Constructor { args, .. } => {
            for a in args {
                walk_binder_for_expected_type(a, arities, errors);
            }
        }
        cst::Binder::Record { fields, .. } => {
            for f in fields {
                if let Some(b) = &f.binder {
                    walk_binder_for_expected_type(b, arities, errors);
                }
            }
        }
        cst::Binder::Array { elements, .. } => {
            for e in elements {
                walk_binder_for_expected_type(e, arities, errors);
            }
        }
        cst::Binder::As { binder, .. } => {
            walk_binder_for_expected_type(binder, arities, errors);
        }
        cst::Binder::Op { left, right, .. } => {
            walk_binder_for_expected_type(left, arities, errors);
            walk_binder_for_expected_type(right, arities, errors);
        }
        _ => {}
    }
}

fn walk_guarded_expr_for_expected_type(
    g: &cst::GuardedExpr,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(expr) => {
            walk_expr_for_expected_type(expr, arities, errors);
        }
        cst::GuardedExpr::Guarded(guards) => {
            for g in guards {
                walk_expr_for_expected_type(&g.expr, arities, errors);
            }
        }
    }
}

fn walk_expr_for_expected_type(
    e: &cst::Expr,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match e {
        cst::Expr::TypeAnnotation { expr, ty, span } => {
            check_type_annotation_for_expected_type(ty, *span, arities, errors);
            walk_expr_for_expected_type(expr, arities, errors);
        }
        cst::Expr::Lambda { binders, body, .. } => {
            for b in binders {
                walk_binder_for_expected_type(b, arities, errors);
            }
            walk_expr_for_expected_type(body, arities, errors);
        }
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_expected_type(func, arities, errors);
            walk_expr_for_expected_type(arg, arities, errors);
        }
        cst::Expr::Parens { expr, .. } => {
            walk_expr_for_expected_type(expr, arities, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_expected_type(cond, arities, errors);
            walk_expr_for_expected_type(then_expr, arities, errors);
            walk_expr_for_expected_type(else_expr, arities, errors);
        }
        cst::Expr::Let { bindings, body, .. } => {
            for lb in bindings {
                walk_let_binding_for_expected_type(lb, arities, errors);
            }
            walk_expr_for_expected_type(body, arities, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for s in exprs {
                walk_expr_for_expected_type(s, arities, errors);
            }
            for alt in alts {
                for b in &alt.binders {
                    walk_binder_for_expected_type(b, arities, errors);
                }
                walk_guarded_expr_for_expected_type(
                    &alt.result,
                    arities,
                    errors,
                );
            }
        }
        cst::Expr::Do { statements, .. } => {
            for s in statements {
                walk_do_statement_for_expected_type(s, arities, errors);
            }
        }
        cst::Expr::Ado { statements, result, .. } => {
            for s in statements {
                walk_do_statement_for_expected_type(s, arities, errors);
            }
            walk_expr_for_expected_type(result, arities, errors);
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_expected_type(v, arities, errors);
                }
            }
        }
        cst::Expr::Array { elements, .. } => {
            for el in elements {
                walk_expr_for_expected_type(el, arities, errors);
            }
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_expected_type(expr, arities, errors);
            for u in updates {
                walk_expr_for_expected_type(&u.value, arities, errors);
            }
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_expected_type(left, arities, errors);
            walk_expr_for_expected_type(right, arities, errors);
        }
        cst::Expr::Negate { expr, .. } => {
            walk_expr_for_expected_type(expr, arities, errors);
        }
        _ => {}
    }
}

fn walk_let_binding_for_expected_type(
    lb: &cst::LetBinding,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match lb {
        cst::LetBinding::Value { binder, expr, .. } => {
            walk_binder_for_expected_type(binder, arities, errors);
            walk_expr_for_expected_type(expr, arities, errors);
        }
        cst::LetBinding::Signature { .. } => {}
    }
}

fn walk_do_statement_for_expected_type(
    s: &cst::DoStatement,
    arities: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    match s {
        cst::DoStatement::Bind { binder, expr, .. } => {
            walk_binder_for_expected_type(binder, arities, errors);
            walk_expr_for_expected_type(expr, arities, errors);
        }
        cst::DoStatement::Discard { expr, .. } => {
            walk_expr_for_expected_type(expr, arities, errors);
        }
        cst::DoStatement::Let { bindings, .. } => {
            for lb in bindings {
                walk_let_binding_for_expected_type(lb, arities, errors);
            }
        }
    }
}

/// Instance method CAF cycle. `instance C T where g = f` — when
/// `g` is a 0-binder method body that references another method
/// of the same class WITHOUT a lambda barrier, the dictionary
/// record can't be constructed (each field would need to be ready
/// for the other). Reference compiler reports as
/// `CycleInDeclaration`.
fn detect_instance_method_caf_cycle(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Map class name → its method set. Only local classes are
    // tracked here; imported classes' member sigs aren't reachable
    // without registry access.
    let mut class_methods: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for d in decls {
        if let cst::Decl::Class { name, members, is_kind_sig: false, .. } = d {
            let ms: HashSet<Symbol> =
                members.iter().map(|m| m.name.value.symbol()).collect();
            class_methods.insert(name.value.symbol(), ms);
        }
    }
    for d in decls {
        let cst::Decl::Instance { class_name, members, constraints, .. } = d else {
            continue;
        };
        let cqi = class_name.to_qi();
        // Local classes only — imported instance methods would need
        // registry-aware analysis.
        if cqi.module.is_some() {
            continue;
        }
        let Some(methods) = class_methods.get(&cqi.name) else {
            continue;
        };
        // Whether this instance has a constraint with the SAME class
        // as the instance head. If so, sibling method references in
        // method bodies could legitimately come through that
        // constraint's dictionary (e.g. `instance Eq a => Eq (Array
        // a) where eq = eqArrayImpl eq`). If not, sibling references
        // MUST come from the current dict — a CAF cycle.
        let has_same_class_constraint = constraints.iter().any(|c| {
            let qi = c.class.to_qi();
            qi.module.is_none() && qi.name == cqi.name
        });
        for m in members {
            if let cst::Decl::Value { name, binders, guarded, span, .. } = m {
                if !binders.is_empty() {
                    continue;
                }
                let body = match guarded {
                    cst::GuardedExpr::Unconditional(e) => e.as_ref(),
                    _ => continue,
                };
                // Direct rename `g = f` always flags.
                if let Some(sym) = direct_var_ref(body) {
                    if methods.contains(&sym) {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::CycleInDeclaration(vec![
                                resolve(name.value.symbol()),
                            ]),
                        });
                        continue;
                    }
                }
                // Cross-method head reference: `size = fold (...) 0.0`
                // where the HEAD of the body's App chain IS a sibling
                // method. The sibling is immediately called at dictionary
                // construction time (partial application in JS). Only
                // fire when there's no same-class constraint (which would
                // mean `fold` comes from the constraint, not the dict).
                // Note: `exl = linearPropagation exl exl` is OK because
                // `linearPropagation` is the head (external), and `exl`
                // appears only in argument position — the closure captures
                // it lazily.
                if !has_same_class_constraint {
                    let head = peel_app_head_for_method_ref(body);
                    if let Some(sym) = head {
                        if methods.contains(&sym) {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::CycleInDeclaration(vec![
                                    resolve(name.value.symbol()),
                                ]),
                            });
                        }
                    }
                }
            }
        }
    }
}

/// True if the expression is a direct unqualified `Var` reference
/// (through Parens / TypeAnnotation only — NO App / Lambda / Case
/// / etc.). Used to detect `g = f` direct renames.
fn direct_var_ref(expr: &cst::Expr) -> Option<crate::interner::Symbol> {
    let mut cur = expr;
    loop {
        match cur {
            cst::Expr::Parens { expr, .. } => cur = expr,
            cst::Expr::TypeAnnotation { expr, .. } => cur = expr,
            cst::Expr::Var { name, .. } if name.module.is_none() => {
                return Some(name.name.symbol());
            }
            _ => return None,
        }
    }
}

/// Peel Parens/TypeAnnotation/App to find the unqualified Var head of
/// an expression's App chain. Returns `Some(sym)` if the outermost
/// function position is a bare variable, `None` otherwise.
fn peel_app_head_for_method_ref(expr: &cst::Expr) -> Option<crate::interner::Symbol> {
    let mut cur = expr;
    loop {
        match cur {
            cst::Expr::Parens { expr, .. } => cur = expr,
            cst::Expr::TypeAnnotation { expr, .. } => cur = expr,
            cst::Expr::App { func, .. } => cur = func,
            cst::Expr::VisibleTypeApp { func, .. } => cur = func,
            cst::Expr::Var { name, .. } if name.module.is_none() => {
                return Some(name.name.symbol());
            }
            _ => return None,
        }
    }
}

#[allow(dead_code)]
fn walk_guarded_for_caf_method_ref(
    g: &cst::GuardedExpr,
    methods: &HashSet<Symbol>,
    found: &mut Option<Symbol>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_caf_method_ref(e, methods, found);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_caf_method_ref(e, methods, found);
                        }
                    }
                }
                walk_expr_for_caf_method_ref(&gd.expr, methods, found);
            }
        }
    }
}

fn walk_expr_for_caf_method_ref(
    expr: &cst::Expr,
    methods: &HashSet<Symbol>,
    found: &mut Option<Symbol>,
) {
    if found.is_some() {
        return;
    }
    match expr {
        cst::Expr::Var { name, .. } => {
            if name.module.is_none() {
                let sym = name.name.symbol();
                if methods.contains(&sym) {
                    *found = Some(sym);
                }
            }
        }
        cst::Expr::Constructor { .. }
        | cst::Expr::Literal { .. }
        | cst::Expr::OpParens { .. }
        | cst::Expr::Wildcard { .. }
        | cst::Expr::Hole { .. } => {}
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_caf_method_ref(func, methods, found);
            walk_expr_for_caf_method_ref(arg, methods, found);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_caf_method_ref(func, methods, found);
        }
        cst::Expr::Lambda { .. } => {
            // Lambda is a barrier — its body doesn't trigger.
        }
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_caf_method_ref(left, methods, found);
            walk_expr_for_caf_method_ref(right, methods, found);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_caf_method_ref(cond, methods, found);
            walk_expr_for_caf_method_ref(then_expr, methods, found);
            walk_expr_for_caf_method_ref(else_expr, methods, found);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_caf_method_ref(e, methods, found);
            }
            for alt in alts {
                walk_guarded_for_caf_method_ref(&alt.result, methods, found);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_caf_method_ref(expr, methods, found);
                }
            }
            walk_expr_for_caf_method_ref(body, methods, found);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_caf_method_ref(expr, methods, found);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_caf_method_ref(expr, methods, found);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_caf_method_ref(result, methods, found);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_caf_method_ref(v, methods, found);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            walk_expr_for_caf_method_ref(expr, methods, found);
        }
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_caf_method_ref(expr, methods, found);
            for u in updates {
                walk_expr_for_caf_method_ref(&u.value, methods, found);
            }
        }
        cst::Expr::Parens { expr, .. } => {
            walk_expr_for_caf_method_ref(expr, methods, found);
        }
        cst::Expr::TypeAnnotation { expr, .. } => {
            walk_expr_for_caf_method_ref(expr, methods, found);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_caf_method_ref(e, methods, found);
            }
        }
        cst::Expr::Negate { expr, .. } => {
            walk_expr_for_caf_method_ref(expr, methods, found);
        }
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_caf_method_ref(name, methods, found);
            walk_expr_for_caf_method_ref(pattern, methods, found);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_caf_method_ref(func, methods, found);
            walk_expr_for_caf_method_ref(left, methods, found);
            walk_expr_for_caf_method_ref(right, methods, found);
        }
    }
}

/// Walks every place a class name can appear (instance class_name,
/// instance constraints, derive class_name, derive constraints,
/// class superclass constraints) and emits `UnknownName` for any
/// unqualified class name that isn't declared locally and isn't
/// imported via an unqualified import. Skips qualified references
/// (`Foo.Bar.Baz a`) — those resolve through the registry by
/// module qualifier.
fn detect_unknown_class_references(
    decls: &[cst::Decl],
    imported_class_arity: &HashMap<Symbol, usize>,
    errors: &mut Vec<ValidationError>,
) {
    let mut local_classes: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::Class { name, is_kind_sig: false, .. } = d {
            local_classes.insert(name.value.symbol());
        }
    }
    let mut seen: HashSet<Symbol> = HashSet::new();
    let class_known = |sym: Symbol| -> bool {
        local_classes.contains(&sym) || imported_class_arity.contains_key(&sym)
    };
    for d in decls {
        match d {
            cst::Decl::Instance { class_name, constraints, span, .. }
            | cst::Decl::Derive { class_name, constraints, span, .. } => {
                if class_name.module.is_none() {
                    let n = class_name.name.symbol();
                    if !class_known(n) && seen.insert(n) {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::UnknownName(resolve(n)),
                        });
                    }
                }
                for c in constraints {
                    let cqi = c.class.to_qi();
                    if cqi.module.is_none() {
                        let n = cqi.name;
                        if !class_known(n) && seen.insert(n) {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::UnknownName(resolve(n)),
                            });
                        }
                    }
                }
            }
            cst::Decl::Class { constraints, span, is_kind_sig: false, members, .. } => {
                for c in constraints {
                    let cqi = c.class.to_qi();
                    if cqi.module.is_none() {
                        let n = cqi.name;
                        if !class_known(n) && seen.insert(n) {
                            errors.push(ValidationError {
                                span: *span,
                                kind: ValidationErrorKind::UnknownName(resolve(n)),
                            });
                        }
                    }
                }
                for m in members {
                    let mut classes_used: HashSet<Symbol> = HashSet::new();
                    collect_unqualified_constraint_classes(&m.ty, &mut classes_used);
                    for sym in classes_used {
                        if !class_known(sym) && seen.insert(sym) {
                            errors.push(ValidationError {
                                span: m.span,
                                kind: ValidationErrorKind::UnknownName(resolve(sym)),
                            });
                        }
                    }
                }
            }
            cst::Decl::TypeSignature { ty, span, .. }
            | cst::Decl::Foreign { ty, span, .. } => {
                let mut classes_used: HashSet<Symbol> = HashSet::new();
                collect_unqualified_constraint_classes(ty, &mut classes_used);
                for sym in classes_used {
                    if !class_known(sym) && seen.insert(sym) {
                        errors.push(ValidationError {
                            span: *span,
                            kind: ValidationErrorKind::UnknownName(resolve(sym)),
                        });
                    }
                }
            }
            _ => {}
        }
    }
}

/// Collect every unqualified class name referenced as a constraint
/// inside `te` (transitively walking Forall / Constrained / etc.).
fn collect_unqualified_constraint_classes(
    te: &cst::TypeExpr,
    out: &mut HashSet<Symbol>,
) {
    match te {
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                let cqi = c.class.to_qi();
                if cqi.module.is_none() {
                    out.insert(cqi.name);
                }
            }
            collect_unqualified_constraint_classes(ty, out);
        }
        cst::TypeExpr::Forall { ty, .. } => {
            collect_unqualified_constraint_classes(ty, out);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            collect_unqualified_constraint_classes(from, out);
            collect_unqualified_constraint_classes(to, out);
        }
        cst::TypeExpr::Parens { ty, .. } => {
            collect_unqualified_constraint_classes(ty, out);
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            collect_unqualified_constraint_classes(constructor, out);
            collect_unqualified_constraint_classes(arg, out);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                collect_unqualified_constraint_classes(&f.ty, out);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                collect_unqualified_constraint_classes(&f.ty, out);
            }
            if let Some(t) = tail {
                collect_unqualified_constraint_classes(t, out);
            }
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            collect_unqualified_constraint_classes(ty, out);
            collect_unqualified_constraint_classes(kind, out);
        }
        _ => {}
    }
}

/// Detect type-variables applied to themselves
/// (`data F a = F (a a)`). The kind unifier would need
/// `kind(a) = kind(a) -> _` — an occurs failure (`InfiniteKind`).
fn detect_infinite_kind(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    for d in decls {
        match d {
            cst::Decl::Data { name, type_vars, constructors, .. } => {
                let self_name = name.value.symbol();
                let self_vars: HashSet<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                for c in constructors {
                    for f in &c.fields {
                        scan_for_self_app(f, errors);
                        scan_for_data_self_app(f, self_name, &self_vars, errors);
                    }
                }
            }
            cst::Decl::Newtype { name, type_vars, ty, .. } => {
                let self_name = name.value.symbol();
                let self_vars: HashSet<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                scan_for_self_app(ty, errors);
                scan_for_data_self_app(ty, self_name, &self_vars, errors);
            }
            cst::Decl::TypeAlias { ty, .. } => {
                scan_for_self_app(ty, errors);
            }
            cst::Decl::TypeSignature { ty, .. } => {
                scan_for_self_app(ty, errors);
            }
            cst::Decl::Foreign { ty, .. } => {
                scan_for_self_app(ty, errors);
            }
            _ => {}
        }
    }
}

/// `data Tree m = Tree (m Tree)` — a data ctor field has the form
/// `App(Var(v), Constructor(SelfName))` where `v` is one of the
/// data's type-vars AND `SelfName` is BARE (unsaturated). The kind
/// unifier would require `kind(v) = (kind(SelfName) -> _)` but
/// SelfName itself takes `v` as arg, producing the infinite cycle
/// the reference compiler reports as `InfiniteKind`.
///
/// Saturated forms (`In (f (Mu f))` where `Mu f` IS the recursive
/// reference) are valid fixed-point newtypes/data and not flagged.
fn scan_for_data_self_app(
    te: &cst::TypeExpr,
    self_name: Symbol,
    self_vars: &HashSet<Symbol>,
    errors: &mut Vec<ValidationError>,
) {
    match te {
        cst::TypeExpr::App { constructor, arg, span } => {
            let l = peel_parens(constructor);
            let r = peel_parens(arg);
            if let cst::TypeExpr::Var { name: ln, .. } = l {
                if self_vars.contains(&ln.value.symbol())
                    && is_bare_self_ctor(r, self_name)
                {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::InfiniteKind(resolve(
                            ln.value.symbol(),
                        )),
                    });
                }
            }
            scan_for_data_self_app(constructor, self_name, self_vars, errors);
            scan_for_data_self_app(arg, self_name, self_vars, errors);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            scan_for_data_self_app(from, self_name, self_vars, errors);
            scan_for_data_self_app(to, self_name, self_vars, errors);
        }
        cst::TypeExpr::Forall { ty, .. } => {
            scan_for_data_self_app(ty, self_name, self_vars, errors);
        }
        cst::TypeExpr::Constrained { ty, .. } => {
            scan_for_data_self_app(ty, self_name, self_vars, errors);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                scan_for_data_self_app(&f.ty, self_name, self_vars, errors);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                scan_for_data_self_app(&f.ty, self_name, self_vars, errors);
            }
            if let Some(t) = tail {
                scan_for_data_self_app(t, self_name, self_vars, errors);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => {
            scan_for_data_self_app(ty, self_name, self_vars, errors);
        }
        cst::TypeExpr::Kinded { ty, .. } => {
            scan_for_data_self_app(ty, self_name, self_vars, errors);
        }
        _ => {}
    }
}

/// True iff `te` is exactly the bare unqualified Constructor
/// `self_name` (peeling Parens). NOT true for App-wrapped forms
/// (`Mu f` is a saturated application, not bare).
fn is_bare_self_ctor(te: &cst::TypeExpr, self_name: Symbol) -> bool {
    match te {
        cst::TypeExpr::Constructor { name, .. } => {
            name.module.is_none() && name.name.symbol() == self_name
        }
        cst::TypeExpr::Parens { ty, .. } => is_bare_self_ctor(ty, self_name),
        _ => false,
    }
}

/// Non-associative operator chained with itself.
///
/// `a == b == c` (where `==` is declared `infix` not `infixl`/r)
/// or the type-level analogue `a >> b >> a` (with `infix 6 type
/// Function as >>`). Both produce `NonAssociativeError`.
///
/// Detection: walk every Op (value-level) and TypeOp (type-level)
/// in the module. For each whose operator has `Associativity::None`
/// (locally declared), check whether either child uses the SAME
/// operator. If so, fire.
fn detect_non_associative_chain(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    detect_non_associative_chain_with_imports(
        decls,
        &HashMap::new(),
        &HashMap::new(),
        errors,
    );
}

pub(crate) fn detect_non_associative_chain_with_imports(
    decls: &[cst::Decl],
    imported_value_op_assoc: &HashMap<Symbol, cst::Associativity>,
    imported_type_op_assoc: &HashMap<Symbol, cst::Associativity>,
    errors: &mut Vec<ValidationError>,
) {
    let mut value_op_assoc: HashMap<Symbol, cst::Associativity> =
        imported_value_op_assoc.clone();
    let mut type_op_assoc: HashMap<Symbol, cst::Associativity> =
        imported_type_op_assoc.clone();
    for d in decls {
        if let cst::Decl::Fixity { operator, associativity, is_type, .. } = d {
            let map = if *is_type { &mut type_op_assoc } else { &mut value_op_assoc };
            map.insert(operator.value.symbol(), *associativity);
        }
    }
    // Walk type expressions for TypeOp chains.
    for d in decls {
        match d {
            cst::Decl::TypeAlias { ty, .. }
            | cst::Decl::TypeSignature { ty, .. }
            | cst::Decl::Foreign { ty, .. } => {
                walk_type_for_non_assoc_chain(ty, &type_op_assoc, errors);
            }
            cst::Decl::Class { members, .. } => {
                for m in members {
                    walk_type_for_non_assoc_chain(&m.ty, &type_op_assoc, errors);
                }
            }
            cst::Decl::Data { constructors, .. } => {
                for c in constructors {
                    for f in &c.fields {
                        walk_type_for_non_assoc_chain(f, &type_op_assoc, errors);
                    }
                }
            }
            cst::Decl::Newtype { ty, .. } => {
                walk_type_for_non_assoc_chain(ty, &type_op_assoc, errors);
            }
            _ => {}
        }
    }
    // Walk value expressions for Op chains.
    for d in decls {
        match d {
            cst::Decl::Value { guarded, where_clause, .. } => {
                walk_guarded_for_non_assoc(guarded, &value_op_assoc, errors);
                for b in where_clause {
                    if let cst::LetBinding::Value { expr, .. } = b {
                        walk_expr_for_non_assoc(expr, &value_op_assoc, errors);
                    }
                }
            }
            cst::Decl::Instance { members, .. } => {
                detect_non_associative_chain(members, errors);
            }
            _ => {}
        }
    }
}

fn walk_type_for_non_assoc_chain(
    te: &cst::TypeExpr,
    assoc: &HashMap<Symbol, cst::Associativity>,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::TypeExpr::TypeOp { left, op, right, span } = te {
        if op.value.module.is_none() {
            let op_sym = op.value.name.symbol();
            if let Some(cst::Associativity::None) = assoc.get(&op_sym) {
                if type_uses_op(left, op_sym) || type_uses_op(right, op_sym) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::NonAssociativeError(resolve(op_sym)),
                    });
                }
            }
        }
    }
    match te {
        cst::TypeExpr::App { constructor, arg, .. } => {
            walk_type_for_non_assoc_chain(constructor, assoc, errors);
            walk_type_for_non_assoc_chain(arg, assoc, errors);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_type_for_non_assoc_chain(from, assoc, errors);
            walk_type_for_non_assoc_chain(to, assoc, errors);
        }
        cst::TypeExpr::Forall { ty, .. } => {
            walk_type_for_non_assoc_chain(ty, assoc, errors);
        }
        cst::TypeExpr::Constrained { ty, .. } => {
            walk_type_for_non_assoc_chain(ty, assoc, errors);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_type_for_non_assoc_chain(&f.ty, assoc, errors);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_type_for_non_assoc_chain(&f.ty, assoc, errors);
            }
            if let Some(t) = tail {
                walk_type_for_non_assoc_chain(t, assoc, errors);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => {
            walk_type_for_non_assoc_chain(ty, assoc, errors);
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_type_for_non_assoc_chain(left, assoc, errors);
            walk_type_for_non_assoc_chain(right, assoc, errors);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_type_for_non_assoc_chain(ty, assoc, errors);
            walk_type_for_non_assoc_chain(kind, assoc, errors);
        }
        _ => {}
    }
}

/// True iff `te` is an immediate TypeOp using `op_sym`. Same
/// rationale as `expr_uses_op` — no recursion into children.
fn type_uses_op(te: &cst::TypeExpr, op_sym: Symbol) -> bool {
    if let cst::TypeExpr::TypeOp { op, .. } = te {
        op.value.module.is_none() && op.value.name.symbol() == op_sym
    } else {
        false
    }
}

fn walk_guarded_for_non_assoc(
    g: &cst::GuardedExpr,
    assoc: &HashMap<Symbol, cst::Associativity>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => {
            walk_expr_for_non_assoc(e, assoc, errors);
        }
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_non_assoc(e, assoc, errors);
                        }
                    }
                }
                walk_expr_for_non_assoc(&gd.expr, assoc, errors);
            }
        }
    }
}

fn walk_expr_for_non_assoc(
    expr: &cst::Expr,
    assoc: &HashMap<Symbol, cst::Associativity>,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::Expr::Op { left, op, right, span } = expr {
        if op.value.module.is_none() {
            let op_sym = op.value.name.symbol();
            if let Some(cst::Associativity::None) = assoc.get(&op_sym) {
                if expr_uses_op(left, op_sym) || expr_uses_op(right, op_sym) {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::NonAssociativeError(resolve(op_sym)),
                    });
                }
            }
        }
    }
    match expr {
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_non_assoc(func, assoc, errors);
            walk_expr_for_non_assoc(arg, assoc, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            walk_expr_for_non_assoc(func, assoc, errors);
        }
        cst::Expr::Lambda { body, .. } => walk_expr_for_non_assoc(body, assoc, errors),
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_non_assoc(left, assoc, errors);
            walk_expr_for_non_assoc(right, assoc, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_non_assoc(cond, assoc, errors);
            walk_expr_for_non_assoc(then_expr, assoc, errors);
            walk_expr_for_non_assoc(else_expr, assoc, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_non_assoc(e, assoc, errors);
            }
            for alt in alts {
                walk_guarded_for_non_assoc(&alt.result, assoc, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_non_assoc(expr, assoc, errors);
                }
            }
            walk_expr_for_non_assoc(body, assoc, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_non_assoc(expr, assoc, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_non_assoc(expr, assoc, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_non_assoc(result, assoc, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_non_assoc(v, assoc, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => walk_expr_for_non_assoc(expr, assoc, errors),
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_non_assoc(expr, assoc, errors);
            for u in updates {
                walk_expr_for_non_assoc(&u.value, assoc, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => walk_expr_for_non_assoc(expr, assoc, errors),
        cst::Expr::TypeAnnotation { expr, .. } => walk_expr_for_non_assoc(expr, assoc, errors),
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_non_assoc(e, assoc, errors);
            }
        }
        cst::Expr::Negate { expr, .. } => walk_expr_for_non_assoc(expr, assoc, errors),
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_non_assoc(name, assoc, errors);
            walk_expr_for_non_assoc(pattern, assoc, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_non_assoc(func, assoc, errors);
            walk_expr_for_non_assoc(left, assoc, errors);
            walk_expr_for_non_assoc(right, assoc, errors);
        }
        _ => {}
    }
}

/// True iff `expr` is an immediate `Op` node using `op_sym`. Does
/// NOT recurse into children — only the OUTERMOST shape counts.
/// Parens explicitly disambiguate; deeper nested ops with the
/// same name (after the rebracketer settles) are a separate
/// concern. We only want to catch direct chains like
/// `Op(Op(a, ==, b), ==, c)` or `Op(a, ==, Op(b, ==, c))`.
fn expr_uses_op(expr: &cst::Expr, op_sym: Symbol) -> bool {
    if let cst::Expr::Op { op, .. } = expr {
        op.value.module.is_none() && op.value.name.symbol() == op_sym
    } else {
        false
    }
}

/// MixedAssociativityError. Two operators at the same precedence
/// with different associativity chained without explicit grouping
/// — e.g. `f <$> x == f <$> y` mixes `<$>` (left, prec 4) with
/// `==` (none, prec 4). Fires only on the OUTERMOST mismatch
/// (immediate child Op of same precedence + different assoc, no
/// Parens between).
pub(crate) fn detect_mixed_associativity(
    decls: &[cst::Decl],
    imported_value_op_fixity: &HashMap<Symbol, (u8, cst::Associativity)>,
    imported_type_op_fixity: &HashMap<Symbol, (u8, cst::Associativity)>,
    errors: &mut Vec<ValidationError>,
) {
    let mut value_fix: HashMap<Symbol, (u8, cst::Associativity)> =
        imported_value_op_fixity.clone();
    let mut type_fix: HashMap<Symbol, (u8, cst::Associativity)> =
        imported_type_op_fixity.clone();
    for d in decls {
        if let cst::Decl::Fixity {
            operator,
            associativity,
            precedence,
            is_type,
            ..
        } = d
        {
            let map = if *is_type { &mut type_fix } else { &mut value_fix };
            map.insert(operator.value.symbol(), (*precedence, *associativity));
        }
    }
    for d in decls {
        match d {
            cst::Decl::Value { guarded, where_clause, .. } => {
                walk_guarded_for_mixed(guarded, &value_fix, errors);
                for b in where_clause {
                    if let cst::LetBinding::Value { expr, .. } = b {
                        walk_expr_for_mixed(expr, &value_fix, errors);
                    }
                }
            }
            cst::Decl::Instance { members, .. } => {
                detect_mixed_associativity(members, &value_fix, &type_fix, errors);
            }
            cst::Decl::TypeAlias { ty, .. }
            | cst::Decl::TypeSignature { ty, .. }
            | cst::Decl::Foreign { ty, .. } => {
                walk_type_for_mixed(ty, &type_fix, errors);
            }
            _ => {}
        }
    }
}

fn check_op_mixed(
    outer_op_sym: Symbol,
    outer_module_none: bool,
    child: Option<(Symbol, bool)>,
    fix: &HashMap<Symbol, (u8, cst::Associativity)>,
    span: Span,
    errors: &mut Vec<ValidationError>,
) {
    if !outer_module_none {
        return;
    }
    let Some((outer_prec, outer_assoc)) = fix.get(&outer_op_sym).copied() else {
        return;
    };
    let Some((child_sym, child_module_none)) = child else { return };
    if !child_module_none {
        return;
    }
    let Some((child_prec, child_assoc)) = fix.get(&child_sym).copied() else {
        return;
    };
    if outer_prec != child_prec {
        return;
    }
    if outer_assoc == child_assoc {
        return;
    }
    // The same-op same-prec chain is `NonAssociativeError`'s
    // territory (when both are None). A mixed-assoc chain at the
    // same precedence with DIFFERENT operators (or one None and
    // the other L/R) is the MixedAssociativityError case.
    if outer_op_sym == child_sym {
        return;
    }
    errors.push(ValidationError {
        span,
        kind: ValidationErrorKind::MixedAssociativityError(resolve(outer_op_sym)),
    });
}

fn walk_guarded_for_mixed(
    g: &cst::GuardedExpr,
    fix: &HashMap<Symbol, (u8, cst::Associativity)>,
    errors: &mut Vec<ValidationError>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => walk_expr_for_mixed(e, fix, errors),
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            walk_expr_for_mixed(e, fix, errors);
                        }
                    }
                }
                walk_expr_for_mixed(&gd.expr, fix, errors);
            }
        }
    }
}

fn walk_expr_for_mixed(
    expr: &cst::Expr,
    fix: &HashMap<Symbol, (u8, cst::Associativity)>,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::Expr::Op { left, op, right, span } = expr {
        let outer_sym = op.value.name.symbol();
        let outer_mod_none = op.value.module.is_none();
        let child_info = |c: &cst::Expr| -> Option<(Symbol, bool)> {
            if let cst::Expr::Op { op, .. } = c {
                Some((op.value.name.symbol(), op.value.module.is_none()))
            } else {
                None
            }
        };
        check_op_mixed(outer_sym, outer_mod_none, child_info(left), fix, *span, errors);
        check_op_mixed(outer_sym, outer_mod_none, child_info(right), fix, *span, errors);
    }
    match expr {
        cst::Expr::App { func, arg, .. } => {
            walk_expr_for_mixed(func, fix, errors);
            walk_expr_for_mixed(arg, fix, errors);
        }
        cst::Expr::VisibleTypeApp { func, .. } => walk_expr_for_mixed(func, fix, errors),
        cst::Expr::Lambda { body, .. } => walk_expr_for_mixed(body, fix, errors),
        cst::Expr::Op { left, right, .. } => {
            walk_expr_for_mixed(left, fix, errors);
            walk_expr_for_mixed(right, fix, errors);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr_for_mixed(cond, fix, errors);
            walk_expr_for_mixed(then_expr, fix, errors);
            walk_expr_for_mixed(else_expr, fix, errors);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr_for_mixed(e, fix, errors);
            }
            for alt in alts {
                walk_guarded_for_mixed(&alt.result, fix, errors);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    walk_expr_for_mixed(expr, fix, errors);
                }
            }
            walk_expr_for_mixed(body, fix, errors);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        walk_expr_for_mixed(expr, fix, errors);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                walk_expr_for_mixed(expr, fix, errors);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                walk_expr_for_mixed(result, fix, errors);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    walk_expr_for_mixed(v, fix, errors);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => walk_expr_for_mixed(expr, fix, errors),
        cst::Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr_for_mixed(expr, fix, errors);
            for u in updates {
                walk_expr_for_mixed(&u.value, fix, errors);
            }
        }
        cst::Expr::Parens { expr, .. } => walk_expr_for_mixed(expr, fix, errors),
        cst::Expr::TypeAnnotation { expr, .. } => walk_expr_for_mixed(expr, fix, errors),
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr_for_mixed(e, fix, errors);
            }
        }
        cst::Expr::Negate { expr, .. } => walk_expr_for_mixed(expr, fix, errors),
        cst::Expr::AsPattern { name, pattern, .. } => {
            walk_expr_for_mixed(name, fix, errors);
            walk_expr_for_mixed(pattern, fix, errors);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            walk_expr_for_mixed(func, fix, errors);
            walk_expr_for_mixed(left, fix, errors);
            walk_expr_for_mixed(right, fix, errors);
        }
        _ => {}
    }
}

fn walk_type_for_mixed(
    te: &cst::TypeExpr,
    fix: &HashMap<Symbol, (u8, cst::Associativity)>,
    errors: &mut Vec<ValidationError>,
) {
    if let cst::TypeExpr::TypeOp { left, op, right, span } = te {
        let outer_sym = op.value.name.symbol();
        let outer_mod_none = op.value.module.is_none();
        let child_info = |c: &cst::TypeExpr| -> Option<(Symbol, bool)> {
            if let cst::TypeExpr::TypeOp { op, .. } = c {
                Some((op.value.name.symbol(), op.value.module.is_none()))
            } else {
                None
            }
        };
        check_op_mixed(outer_sym, outer_mod_none, child_info(left), fix, *span, errors);
        check_op_mixed(outer_sym, outer_mod_none, child_info(right), fix, *span, errors);
    }
    match te {
        cst::TypeExpr::App { constructor, arg, .. } => {
            walk_type_for_mixed(constructor, fix, errors);
            walk_type_for_mixed(arg, fix, errors);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_type_for_mixed(from, fix, errors);
            walk_type_for_mixed(to, fix, errors);
        }
        cst::TypeExpr::Forall { ty, .. } => walk_type_for_mixed(ty, fix, errors),
        cst::TypeExpr::Constrained { ty, .. } => walk_type_for_mixed(ty, fix, errors),
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_type_for_mixed(&f.ty, fix, errors);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_type_for_mixed(&f.ty, fix, errors);
            }
            if let Some(t) = tail {
                walk_type_for_mixed(t, fix, errors);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => walk_type_for_mixed(ty, fix, errors),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_type_for_mixed(left, fix, errors);
            walk_type_for_mixed(right, fix, errors);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_type_for_mixed(ty, fix, errors);
            walk_type_for_mixed(kind, fix, errors);
        }
        _ => {}
    }
}

/// OverlappingInstances. Walk pairs of instances of the same
/// class; flag pairs whose heads can match the same type.
///
/// "Can match" = one head is at least as general as the other:
///   - Var / Wildcard matches anything
///   - Same Constructor matches itself
///   - Function/App/Record match component-wise
///
/// Type aliases are expanded one level (local aliases only) before
/// comparison so `Convert String Bar` and `Convert String String`
/// (where `type Bar = String`) collide.
fn detect_overlapping_instances(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    let mut alias_body: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
    for d in decls {
        if let cst::Decl::TypeAlias { name, ty, .. } = d {
            alias_body.insert(name.value.symbol(), ty);
        }
    }
    // Group instance heads by class name. Instance chains (with
    // `chain: true` for any non-head member) are explicitly
    // ordered overlap and not an error; we drop ANY chain-member
    // from the comparison set entirely (along with the head it's
    // attached to, since chain semantics make ordering deliberate).
    let mut chain_classes: HashSet<Symbol> = HashSet::new();
    for d in decls {
        if let cst::Decl::Instance { class_name, chain: true, .. } = d {
            let cqi = class_name.to_qi();
            if cqi.module.is_none() {
                chain_classes.insert(cqi.name);
            }
        }
    }
    let mut by_class: HashMap<Symbol, Vec<(Vec<&cst::TypeExpr>, Span)>> =
        HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Instance { class_name, types, span, chain, .. } => {
                let cqi = class_name.to_qi();
                if cqi.module.is_some() {
                    continue;
                }
                if *chain || chain_classes.contains(&cqi.name) {
                    continue;
                }
                by_class
                    .entry(cqi.name)
                    .or_default()
                    .push((types.iter().collect(), *span));
            }
            cst::Decl::Derive { class_name, types, span, .. } => {
                let cqi = class_name.to_qi();
                if cqi.module.is_some() {
                    continue;
                }
                if chain_classes.contains(&cqi.name) {
                    continue;
                }
                by_class
                    .entry(cqi.name)
                    .or_default()
                    .push((types.iter().collect(), *span));
            }
            _ => {}
        }
    }
    let mut emitted: HashSet<(Symbol, usize, usize)> = HashSet::new();
    for (class, instances) in &by_class {
        for i in 0..instances.len() {
            for j in (i + 1)..instances.len() {
                let (a_types, _a_span) = &instances[i];
                let (b_types, b_span) = &instances[j];
                if a_types.len() != b_types.len() {
                    continue;
                }
                let a_matches_b = a_types
                    .iter()
                    .zip(b_types.iter())
                    .all(|(a, b)| head_at_least_as_general(a, b, &alias_body));
                let b_matches_a = b_types
                    .iter()
                    .zip(a_types.iter())
                    .all(|(b, a)| head_at_least_as_general(b, a, &alias_body));
                if a_matches_b || b_matches_a {
                    let key = (*class, i, j);
                    if emitted.insert(key) {
                        errors.push(ValidationError {
                            span: *b_span,
                            kind: ValidationErrorKind::OverlappingInstances(
                                resolve(*class),
                            ),
                        });
                    }
                }
            }
        }
    }
}

/// True iff `a` can match `b` by substituting `a`'s type-vars with
/// arbitrary types — i.e. `a`'s pattern is at least as general as
/// `b`'s.
fn head_at_least_as_general(
    a: &cst::TypeExpr,
    b: &cst::TypeExpr,
    aliases: &HashMap<Symbol, &cst::TypeExpr>,
) -> bool {
    head_at_least_as_general_seen(a, b, aliases, &mut HashSet::new())
}

fn head_at_least_as_general_seen(
    a: &cst::TypeExpr,
    b: &cst::TypeExpr,
    aliases: &HashMap<Symbol, &cst::TypeExpr>,
    seen: &mut HashSet<Symbol>,
) -> bool {
    let a = peel_parens(a);
    let b = peel_parens(b);
    // Var / Wildcard matches anything.
    if matches!(a, cst::TypeExpr::Var { .. } | cst::TypeExpr::Wildcard { .. }) {
        return true;
    }
    // Expand a one-level alias on `a` if applicable.
    if let cst::TypeExpr::Constructor { name, .. } = a {
        if name.module.is_none() {
            if let Some(body) = aliases.get(&name.name.symbol()) {
                if seen.insert(name.name.symbol()) {
                    return head_at_least_as_general_seen(body, b, aliases, seen);
                }
            }
        }
    }
    if let cst::TypeExpr::Constructor { name, .. } = b {
        if name.module.is_none() {
            if let Some(body) = aliases.get(&name.name.symbol()) {
                if seen.insert(name.name.symbol()) {
                    return head_at_least_as_general_seen(a, body, aliases, seen);
                }
            }
        }
    }
    match (a, b) {
        (
            cst::TypeExpr::Constructor { name: an, .. },
            cst::TypeExpr::Constructor { name: bn, .. },
        ) => {
            // Name AND module must match. Different import aliases
            // (e.g. `Uncurried.ReaderT` vs bare `ReaderT`) represent
            // different types and must not be considered overlapping.
            an.name.symbol() == bn.name.symbol() && an.module == bn.module
        }
        (
            cst::TypeExpr::App { constructor: a1, arg: a2, .. },
            cst::TypeExpr::App { constructor: b1, arg: b2, .. },
        ) => {
            head_at_least_as_general_seen(a1, b1, aliases, seen)
                && head_at_least_as_general_seen(a2, b2, aliases, seen)
        }
        (
            cst::TypeExpr::Function { from: a1, to: a2, .. },
            cst::TypeExpr::Function { from: b1, to: b2, .. },
        ) => {
            head_at_least_as_general_seen(a1, b1, aliases, seen)
                && head_at_least_as_general_seen(a2, b2, aliases, seen)
        }
        (
            cst::TypeExpr::StringLiteral { value: av, .. },
            cst::TypeExpr::StringLiteral { value: bv, .. },
        ) => av == bv,
        (
            cst::TypeExpr::IntLiteral { value: av, .. },
            cst::TypeExpr::IntLiteral { value: bv, .. },
        ) => av == bv,
        (
            cst::TypeExpr::Kinded { ty: at, kind: ak, .. },
            cst::TypeExpr::Kinded { ty: bt, kind: bk, .. },
        ) => {
            // Both kind-annotated — kind annotations participate
            // in matching. `(a :: Type)` vs `(a :: Symbol)` are
            // NOT overlapping.
            head_at_least_as_general_seen(at, bt, aliases, seen)
                && head_at_least_as_general_seen(ak, bk, aliases, seen)
        }
        // Mixed Kinded vs non-Kinded: peel and compare. The
        // unannotated side is treated as the more general one.
        (cst::TypeExpr::Kinded { ty: at, .. }, _) => {
            head_at_least_as_general_seen(at, b, aliases, seen)
        }
        (_, cst::TypeExpr::Kinded { ty: bt, .. }) => {
            head_at_least_as_general_seen(a, bt, aliases, seen)
        }
        _ => false,
    }
}

/// Module names containing apostrophes or underscores are rejected
/// by the reference compiler's parser. We catch them post-parse
/// since our lexer is more permissive.
fn detect_invalid_module_name(
    module: &cst::Module,
    errors: &mut Vec<ValidationError>,
) {
    for part in &module.name.value.parts {
        let s = crate::interner::resolve(*part).unwrap_or_default();
        if s.contains('\'') || s.contains('_') {
            errors.push(ValidationError {
                span: module.name.span,
                kind: ValidationErrorKind::InvalidModuleName(s.to_string()),
            });
            return;
        }
    }
}

fn scan_for_self_app(te: &cst::TypeExpr, errors: &mut Vec<ValidationError>) {
    match te {
        cst::TypeExpr::App { constructor, arg, span } => {
            if let (cst::TypeExpr::Var { name: ln, .. }, cst::TypeExpr::Var { name: rn, .. }) =
                (peel_parens(constructor), peel_parens(arg))
            {
                if ln.value.symbol() == rn.value.symbol() {
                    errors.push(ValidationError {
                        span: *span,
                        kind: ValidationErrorKind::InfiniteKind(resolve(
                            ln.value.symbol(),
                        )),
                    });
                }
            }
            scan_for_self_app(constructor, errors);
            scan_for_self_app(arg, errors);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            scan_for_self_app(from, errors);
            scan_for_self_app(to, errors);
        }
        cst::TypeExpr::Forall { ty, .. } => scan_for_self_app(ty, errors),
        cst::TypeExpr::Constrained { ty, .. } => scan_for_self_app(ty, errors),
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                scan_for_self_app(&f.ty, errors);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                scan_for_self_app(&f.ty, errors);
            }
            if let Some(t) = tail {
                scan_for_self_app(t, errors);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => scan_for_self_app(ty, errors),
        cst::TypeExpr::TypeOp { left, right, .. } => {
            scan_for_self_app(left, errors);
            scan_for_self_app(right, errors);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            scan_for_self_app(ty, errors);
            scan_for_self_app(kind, errors);
        }
        _ => {}
    }
}

