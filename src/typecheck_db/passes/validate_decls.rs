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
    // match the class's parameter count (local classes only — imported
    // classes aren't accessible from this CST-only pass).
    detect_class_instance_arity(&module.decls, &mut errors);

    // RoleDeclarationArityMismatch: `type role Foo r1 r2 …` must match the
    // arity of the matching data/newtype/foreign-data.
    detect_role_arity_mismatches(&module.decls, &mut errors);

    // DeclConflict: cross-namespace name collisions at the type level
    // (e.g. `class Fail` + `data Fail`), plus duplicate data-constructor
    // names inside one decl or across data decls in the module.
    detect_decl_conflicts(&module.decls, &mut errors);

    // Orphan instances: declared where neither the class nor any type
    // constructor in the instance head is defined locally.
    detect_orphan_instances(&module.decls, &mut errors);

    detect_partially_applied_synonyms(&module.decls, imported_alias_arity, &mut errors);
    detect_invalid_instance_heads(&module.decls, &mut errors);

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
    errors: &mut Vec<ValidationError>,
) {
    // Build a map of local type-alias name → body, so we can look
    // through one level of aliasing for the record/row check.
    let mut alias_body: HashMap<Symbol, &cst::TypeExpr> = HashMap::new();
    // Local classes that declare any fundep — these allow record/row
    // literals in determined positions and we conservatively skip
    // record-checking for any instance of such a class. (A precise
    // "is position i determined" rule would be better but requires
    // imported fundep visibility too; classes-with-fundeps is the
    // common case.)
    let mut classes_with_fundeps: HashSet<Symbol> = HashSet::new();
    for d in decls {
        match d {
            cst::Decl::TypeAlias { name, ty, .. } => {
                alias_body.insert(name.value.symbol(), ty);
            }
            cst::Decl::Class { name, fundeps, .. } if !fundeps.is_empty() => {
                classes_with_fundeps.insert(name.value.symbol());
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
                    // record) is record-headed. We can't reliably
                    // distinguish open from closed records when the
                    // alias body is a Row (open records can be made
                    // closed by row composition with `()` —
                    // `type Env = { | EnvRow () }`), so we skip Row
                    // here.
                    matches!(peel_parens(body), cst::TypeExpr::Record { .. })
                        || walk_to_record_alias(body, alias_body, seen)
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
            // type. Empty row `()` is fine (it's Row { fields: [] }
            // under our parser, distinct from Record), so we don't
            // flag rows here.
            cst::TypeExpr::Record { .. } => true,
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
        // Skip classes with fundeps — records in determined
        // positions are legitimate (`class Simple a b | a -> b;
        // instance Simple Empty {}`). Imported classes whose
        // fundeps we can't see are also skipped, since we can't
        // distinguish `Foo Empty {}` from `Foo Unit {}` without
        // them.
        let cqi = class_name.to_qi();
        if cqi.module.is_some() {
            continue;
        }
        if classes_with_fundeps.contains(&cqi.name) {
            continue;
        }
        for t in types {
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
    for d in &module.decls {
        match d {
            cst::Decl::Data { name, .. }
            | cst::Decl::Newtype { name, .. }
            | cst::Decl::TypeAlias { name, .. }
            | cst::Decl::ForeignData { name, .. } => {
                local_types.insert(name.value.symbol());
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
                    ..
                } => {
                    let n = name.value.symbol();
                    newtype_decl_span.insert(n, *span);
                    newtype_decl_field.insert(n, ty);
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
        // `owner_sym` if the body references a local-but-unexported
        // type / class.
        let mut check_ty_refs = |
            owner_sym: Symbol,
            owner_span: Span,
            ty: &cst::TypeExpr,
            errors: &mut Vec<ValidationError>,
            reported: &mut HashSet<Symbol>,
        | {
            collect_type_refs(ty, &mut |name: Symbol, _is_class| {
                if !local_types.contains(&name) {
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

        // Exported value with type referring to a non-exported local type.
        for v in &exported_values {
            if let Some(ty) = value_decl_ty.get(v) {
                let span = value_decl_span.get(v).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                check_ty_refs(*v, span, ty, errors, &mut reported_decl);
            }
        }

        // Exported alias with body referring to a non-exported local type.
        for t in &exported_types {
            if let Some(body) = alias_decl_body.get(t) {
                let span = alias_decl_span.get(t).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                check_ty_refs(*t, span, body, errors, &mut reported_decl);
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
                        check_ty_refs(parent, span, f, errors, &mut reported_decl);
                    }
                }
            }
        }
        for t in &exported_types {
            if let Some(anns) = data_decl_kind_anns.get(t) {
                let span = data_decl_span.get(t).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                for ann in anns {
                    check_ty_refs(*t, span, ann, errors, &mut reported_decl);
                }
            }
            if let Some(anns) = newtype_decl_kind_anns.get(t) {
                let span = newtype_decl_span.get(t).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                for ann in anns {
                    check_ty_refs(*t, span, ann, errors, &mut reported_decl);
                }
            }
            if let Some(body) = newtype_decl_field.get(t) {
                let span = newtype_decl_span.get(t).copied()
                    .unwrap_or(crate::span::Span::new(0, 0));
                check_ty_refs(*t, span, body, errors, &mut reported_decl);
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
    errors: &mut Vec<ValidationError>,
) {
    let mut class_arity: HashMap<Symbol, usize> = HashMap::new();
    for d in decls {
        if let cst::Decl::Class { name, type_vars, is_kind_sig: false, .. } = d {
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
fn detect_orphan_instances(decls: &[cst::Decl], errors: &mut Vec<ValidationError>) {
    // Collect local class and data/newtype/foreign-data names.
    let mut local_classes: HashSet<Symbol> = HashSet::new();
    let mut local_data: HashSet<Symbol> = HashSet::new();
    let mut local_aliases: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    for d in decls {
        match d {
            cst::Decl::Class { name, is_kind_sig: false, .. } => {
                local_classes.insert(name.value.symbol());
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

        // Walk each type in the head, extract constructor heads, check if any
        // is locally defined as data/newtype/foreign-data — OR is a local
        // alias whose expansion anchors locally.
        let mut head_is_local = false;
        for t in types {
            for sym in head_type_cons(t) {
                if local_data.contains(&sym) || alias_anchors_locally.contains(&sym) {
                    head_is_local = true;
                    break;
                }
            }
            if head_is_local {
                break;
            }
        }
        if head_is_local {
            continue;
        }

        // Neither the class nor any head type is local — orphan.
        let class_display = resolve(class_name.name.symbol());
        errors.push(ValidationError {
            span,
            kind: ValidationErrorKind::OrphanInstance(class_display),
        });
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
        cst::TypeExpr::TypeOp { left, right, .. } => {
            collect_all_cons(left, out);
            collect_all_cons(right, out);
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
    errors: &mut Vec<ValidationError>,
) {
    // Start with imported aliases (and operator aliases) as the
    // baseline. Local declarations override these on collision.
    let mut alias_arity: HashMap<Symbol, usize> = imported_alias_arity.clone();
    for d in decls {
        if let cst::Decl::TypeAlias { name, type_vars, .. } = d {
            alias_arity.insert(name.value.symbol(), type_vars.len());
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
        walk_partial_apps(te, &alias_arity, errors, &mut reported);
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
    errors: &mut Vec<ValidationError>,
    reported: &mut HashSet<(Symbol, usize)>,
) {
    match te {
        cst::TypeExpr::Constructor { span, name } => {
            if name.module.is_none() {
                let sym = name.name.symbol();
                if let Some(&n) = alias_arity.get(&sym) {
                    if n > 0 {
                        // Zero arguments applied.
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
                    walk_partial_apps(a, alias_arity, errors, reported);
                }
            }
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_partial_apps(from, alias_arity, errors, reported);
            walk_partial_apps(to, alias_arity, errors, reported);
        }
        cst::TypeExpr::Forall { ty, vars, .. } => {
            for (_, _, k) in vars {
                if let Some(k) = k {
                    walk_partial_apps(k, alias_arity, errors, reported);
                }
            }
            walk_partial_apps(ty, alias_arity, errors, reported);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for a in &c.args {
                    walk_partial_apps(a, alias_arity, errors, reported);
                }
            }
            walk_partial_apps(ty, alias_arity, errors, reported);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_partial_apps(&f.ty, alias_arity, errors, reported);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_partial_apps(&f.ty, alias_arity, errors, reported);
            }
            if let Some(t) = tail {
                walk_partial_apps(t, alias_arity, errors, reported);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => {
            walk_partial_apps(ty, alias_arity, errors, reported);
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_partial_apps(left, alias_arity, errors, reported);
            walk_partial_apps(right, alias_arity, errors, reported);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_partial_apps(ty, alias_arity, errors, reported);
            walk_partial_apps(kind, alias_arity, errors, reported);
        }
        cst::TypeExpr::ArrayPattern { elements, .. } => {
            for e in elements {
                walk_partial_apps(e, alias_arity, errors, reported);
            }
        }
        cst::TypeExpr::AsPattern { ty, .. } => {
            walk_partial_apps(ty, alias_arity, errors, reported);
        }
        _ => {}
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
            cst::Decl::Class { type_vars, constraints, is_kind_sig, .. }
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
            }
            _ => {}
        }
    }
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

