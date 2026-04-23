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
        }
    }
}

/// Top-level entry point. Walks the module's decls once, emitting
/// every structural issue it finds.
pub fn validate_module(module: &cst::Module) -> Vec<ValidationError> {
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
            cst::Decl::Value { span, name, .. } => {
                let sym = name.value.symbol();
                value_has_any.insert(sym);
                // Start a new group unless this equation is adjacent
                // to the previous one with the same name.
                if last_value_name != Some(sym) {
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
            cst::Decl::Instance { .. } | cst::Decl::Derive { .. } => {
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

    // Duplicate type decls
    for (sym, spans) in &type_decls {
        if spans.len() > 1 {
            for span in spans.iter().skip(1) {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::DuplicateTypeDeclaration(resolve(*sym)),
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

    // Orphan role decls: role targeting a type that doesn't exist locally.
    for (sym, spans) in &role_decls {
        if !type_decls.contains_key(sym) {
            for span in spans {
                errors.push(ValidationError {
                    span: *span,
                    kind: ValidationErrorKind::OrphanRoleDeclaration(resolve(*sym)),
                });
            }
        }
    }

    // Cycle detection --------------------------------------------------
    detect_alias_cycles(&module.decls, &mut errors);
    detect_class_cycles(&module.decls, &mut errors);
    detect_kind_sig_cycles(&module.decls, &mut errors);
    detect_value_cycles(&module.decls, &mut errors);

    // DeclConflict: cross-namespace name collisions at the type level
    // (e.g. `class Fail` + `data Fail`), plus duplicate data-constructor
    // names inside one decl or across data decls in the module.
    detect_decl_conflicts(&module.decls, &mut errors);

    // Orphan instances: declared where neither the class nor any type
    // constructor in the instance head is defined locally.
    detect_orphan_instances(&module.decls, &mut errors);

    // NOTE: Partially-applied type synonyms are detected conservatively
    // via `detect_partially_applied_synonyms` below, but disabled here —
    // without kind information we can't distinguish `type Identity a = a;
    // type Patch = Template Identity` (valid HKT argument) from
    // `newtype N = N S where type S a = D a` (actual partial). Enable
    // once Bucket 3 (kind checker) lands kind-aware detection.
    let _ = detect_partially_applied_synonyms;

    errors
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
            }
            cst::Decl::TypeAlias { span, name, .. } => {
                emit_conflict(&mut type_level_names, name.value.symbol(), "type", *span, errors);
            }
            cst::Decl::Class { span, name, is_kind_sig: false, .. } => {
                emit_conflict(&mut type_level_names, name.value.symbol(), "class", *span, errors);
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

/// Flag any use of a local type alias with fewer arguments than its
/// declared parameter count. Only catches LOCAL aliases; imported
/// aliases aren't accessible from this CST-only pass.
fn detect_partially_applied_synonyms(
    decls: &[cst::Decl],
    errors: &mut Vec<ValidationError>,
) {
    // Collect arity of every local alias.
    let mut alias_arity: HashMap<Symbol, usize> = HashMap::new();
    for d in decls {
        if let cst::Decl::TypeAlias { name, type_vars, .. } = d {
            alias_arity.insert(name.value.symbol(), type_vars.len());
        }
    }
    if alias_arity.is_empty() {
        return;
    }

    // Helper used on every TypeExpr site.
    let mut reported: HashSet<(Symbol, usize)> = HashSet::new();
    let mut check = |te: &cst::TypeExpr, errors: &mut Vec<ValidationError>| {
        walk_partial_apps(te, &alias_arity, errors, &mut reported);
    };

    for d in decls {
        match d {
            cst::Decl::TypeAlias { ty, .. } => check(ty, errors),
            cst::Decl::TypeSignature { ty, .. } => check(ty, errors),
            cst::Decl::Foreign { ty, .. } => check(ty, errors),
            cst::Decl::ForeignData { kind, .. } => check(kind, errors),
            cst::Decl::Data { constructors, kind_type, .. } => {
                for c in constructors {
                    for f in &c.fields {
                        check(f, errors);
                    }
                }
                if let Some(k) = kind_type {
                    check(k, errors);
                }
            }
            cst::Decl::Newtype { ty, .. } => check(ty, errors),
            cst::Decl::Class { members, constraints, kind_type, .. } => {
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
            if let cst::TypeExpr::Constructor { name, .. } = head {
                if name.module.is_none() {
                    let sym = name.name.symbol();
                    if let Some(&n) = alias_arity.get(&sym) {
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
            // Recurse into args regardless — nested apps may have their
            // own partial alias applications.
            for a in &args {
                walk_partial_apps(a, alias_arity, errors, reported);
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
