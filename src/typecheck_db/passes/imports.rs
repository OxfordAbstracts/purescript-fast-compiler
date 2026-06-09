//! Cross-module import resolution.
//!
//! Given a parsed `cst::Module` and a populated `ModuleRegistry`,
//! produce the pre-populated `Env` and `InstanceIndex` that the
//! single-module pipeline (`infer_value_scc_with_all`) needs.
//!
//! The resolver mirrors legacy `src/typechecker/check/imports.rs`
//! but lives inside the new pipeline shape:
//!
//! * `Prim` is always implicitly imported unqualified. The
//!   corresponding `Prim.*` submodules are not implicit — users
//!   write `import Prim.Row` explicitly when they want those.
//! * Every explicit `import M (...)` adds its listed items into
//!   the env. `import M as Q` adds a qualified prefix; an
//!   unqualified import also makes the items findable by their
//!   bare name.
//! * Instances travel globally: every successfully-resolved
//!   import contributes that module's entire `instances` list to
//!   the built `InstanceIndex`, regardless of the import
//!   filter. Classes travel with their instances.

use crate::cst::{self, DataMembers, Decl, ImportDecl, ImportList};
use crate::typecheck_db::env::Env;
use crate::typecheck_db::module_registry::{ModuleExports, ModuleRegistry};
use crate::typecheck_db::passes::instance_index::InstanceIndex;
use crate::typecheck_db::prim::prim_exports;
use crate::typecheck_db::types::QName;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportError {
    pub span: crate::span::Span,
    pub kind: ImportErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportErrorKind {
    /// `import M` where `M` isn't known to the registry.
    UnknownModule(String),
    /// `import M (foo)` where `foo` isn't in M's exports.
    UnknownValue { module: String, name: String },
    /// `import M (Bar(..))` where `Bar` isn't in M's types.
    UnknownType { module: String, name: String },
    /// `import M (Bar(C1))` where `C1` isn't one of Bar's ctors.
    UnknownConstructor {
        module: String,
        type_name: String,
        ctor: String,
    },
    /// `import M (class C)` where `C` isn't in M's classes.
    UnknownClass { module: String, name: String },
    /// `import M ((<>))` where `<>` isn't in M's fixities.
    UnknownOperator { module: String, name: String },
    /// Two imports bring the same name into scope from different
    /// modules. Triggered when `import A (thing); import B (thing)`
    /// (both expose `thing` unqualified) or
    /// `import A as X; import B as X` (both share alias `X`),
    /// matching the reference compiler's `ScopeConflict` failure.
    ScopeConflict {
        name: String,
        first_module: String,
        second_module: String,
        first_import: crate::span::Span,
        second_import: crate::span::Span,
    },
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

/// Build the pre-populated `Env` + `InstanceIndex` a single
/// module's check should start from. The returned `Vec` carries
/// any non-fatal import errors — callers can surface them to the
/// user and still proceed with inference.
pub fn build_env_from_imports(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> (Env, InstanceIndex, Vec<ImportError>) {
    let mut env = Env::new();
    let mut ix = InstanceIndex::new();
    let mut errors: Vec<ImportError> = Vec::new();

    // Every user module implicitly sees `Prim` unqualified.
    let prims = prim_exports();
    if let Some(prim) = prims.get("Prim") {
        import_all("Prim", prim, /*qualifier=*/ None, &mut env, &mut ix);
    }
    // The solver looks up class_info by simple name. Prim
    // sub-modules (Prim.RowList, Prim.Row, Prim.Symbol, Prim.Coerce,
    // …) carry the fundeps the solver needs to fire fundep-
    // improvement on their classes. Their VALUES/TYPES aren't
    // auto-imported (user code must qualify them), but their CLASSES'
    // metadata must be available to the solver regardless of import
    // status — otherwise a transitively-induced constraint like
    // `RowToList r rl` (from an imported instance's context) defers
    // forever because `class_info` returns None and the solver
    // falls back to "any bare unif defers" with no determined set
    // to consult. This mirrors the reference compiler, which treats
    // Prim fundeps as built-in.
    for (mod_name, exp) in &prims {
        if mod_name == "Prim" {
            continue;
        }
        for (class_name, info) in &exp.classes {
            ix.insert_class(class_name.clone(), info.clone());
        }
    }

    // Track each (qualifier, name) pair against the *origin* module
    // (the module that declared the value, not the re-exporter).
    // Re-exports through Prelude that wrap a name from Control.Apply
    // share the same origin, so importing both `Prelude` and
    // `Control.Apply` doesn't false-positive on shared re-exports.
    //
    // The reference compiler's ScopeConflict is fundamentally
    // *use-site* (only fires when an unqualified reference resolves
    // ambiguously), but most fixtures we care about either:
    // (a) explicitly list both imports — `import A (thing); import
    //     B (thing)` — the user has clearly committed to both being
    //     in scope; or
    // (b) reference the conflicted name in body code.
    // We approximate (a) by only emitting ScopeConflict when BOTH
    // sides flagged a name explicitly — open `import A; import B`
    // doesn't flag (matches `passing/PendingConflictingImports.purs`).
    let mut name_origins: std::collections::HashMap<
        (Option<String>, String),
        (String, bool, crate::span::Span),
    > = std::collections::HashMap::new();
    // Qualified-import-only conflicts deferred to use-site. The
    // reference compiler defers `import A as X; import B as X` (no
    // explicit list either side) to the actual `X.thing` reference
    // — if the conflicted name is never used, no error.
    let mut deferred_qualified_conflicts: Vec<(
        crate::span::Span,
        Option<String>,
        String,
        String,
        String,
        crate::span::Span,
    )> = Vec::new();
    for imp in &module.imports {
        let target_name = module_name_string(&imp.module);
        // Prim and its submodules are resolved from the static
        // `prim_exports` map first; user modules come from the
        // registry.
        let target: Option<&ModuleExports> = prims
            .get(&target_name)
            .or_else(|| registry.get(&target_name));
        let target = match target {
            Some(t) => t,
            None => {
                errors.push(ImportError {
                    span: imp.span,
                    kind: ImportErrorKind::UnknownModule(target_name.clone()),
                });
                continue;
            }
        };

        let qualifier: Option<String> = imp
            .qualified
            .as_ref()
            .map(|q| module_name_string(q));

        // Detect conflicts before applying: collect every
        // (qualifier, name) this import would bring in (filtered
        // by explicit / hiding lists). Resolve each name's origin
        // module via `value_origins`; if it's a re-export, the
        // origin points to the declaring module, so two imports of
        // the same re-exported name don't false-positive.
        let is_explicit_list =
            matches!(imp.imports, Some(ImportList::Explicit(_)));
        let imported_names = compute_imported_names(target, &imp.imports);
        for n in imported_names {
            let key = (qualifier.clone(), n.clone());
            let origin = target
                .value_origins
                .get(&n)
                .cloned()
                .unwrap_or_else(|| target_name.clone());
            match name_origins.get(&key) {
                Some((prev_origin, prev_explicit, prev_span))
                    if *prev_origin != origin
                        && *prev_explicit
                        && is_explicit_list =>
                {
                    // Both sides explicitly listed — user committed
                    // to both. Flag at import time.
                    errors.push(ImportError {
                        span: imp.span,
                        kind: ImportErrorKind::ScopeConflict {
                            name: n,
                            first_module: prev_origin.clone(),
                            second_module: origin.clone(),
                            first_import: *prev_span,
                            second_import: imp.span,
                        },
                    });
                }
                Some((prev_origin, _, prev_span))
                    if *prev_origin != origin && qualifier.is_some() =>
                {
                    // Qualified conflict — defer to use-site. Only
                    // emit if `Q.n` is actually referenced in the
                    // module body.
                    deferred_qualified_conflicts.push((
                        imp.span,
                        qualifier.clone(),
                        n,
                        prev_origin.clone(),
                        origin.clone(),
                        *prev_span,
                    ));
                }
                _ => {
                    name_origins.insert(key, (origin, is_explicit_list, imp.span));
                }
            }
        }

        apply_import(&target_name, target, &imp, qualifier, &mut env, &mut ix, &mut errors);
    }

    // Local-decl-vs-explicit-import scope conflict: a `type T = ...`
    // or `data T` (or value) when `T` was also imported via
    // `import M (T)`. Reference compiler reports as ScopeConflict.
    detect_local_explicit_import_conflicts(module, registry, &prims, &mut errors);

    // Use-site filter for deferred qualified conflicts. Walk every
    // decl body and collect `Q.x` references; emit ScopeConflict
    // only for the deferred entries whose qualified pair is
    // actually referenced — OR whose qualifier appears as a
    // `module Q` re-export clause (a wholesale re-export touches
    // every name in Q's scope, so any conflict under Q fires).
    if !deferred_qualified_conflicts.is_empty() {
        let mut referenced: std::collections::HashSet<(Option<String>, String)> =
            std::collections::HashSet::new();
        collect_qualified_refs(module, &mut referenced);
        let mut reexported_qualifiers: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        if let Some(exports) = &module.exports {
            for e in &exports.value.exports {
                if let cst::Export::Module(q) = e {
                    reexported_qualifiers.insert(module_name_string(q));
                }
            }
        }
        for (span, q, n, m1, m2, first_span) in deferred_qualified_conflicts {
            let q_re_exported = q
                .as_ref()
                .map_or(false, |qn| reexported_qualifiers.contains(qn));
            if q_re_exported
                || referenced.contains(&(q.clone(), n.clone()))
            {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::ScopeConflict {
                        name: n,
                        first_module: m1,
                        second_module: m2,
                        first_import: first_span,
                        second_import: span,
                    },
                });
            }
        }
    }

    (env, ix, errors)
}

fn collect_qualified_refs(
    module: &cst::Module,
    out: &mut std::collections::HashSet<(Option<String>, String)>,
) {
    for d in &module.decls {
        collect_qualified_refs_decl(d, out);
    }
}

fn collect_qualified_refs_decl(
    d: &cst::Decl,
    out: &mut std::collections::HashSet<(Option<String>, String)>,
) {
    match d {
        cst::Decl::Value { guarded, where_clause, .. } => {
            collect_qualified_refs_guarded(guarded, out);
            for b in where_clause {
                if let cst::LetBinding::Value { expr, .. } = b {
                    collect_qualified_refs_expr(expr, out);
                }
            }
        }
        cst::Decl::Instance { members, .. } => {
            for m in members {
                collect_qualified_refs_decl(m, out);
            }
        }
        _ => {}
    }
}

fn collect_qualified_refs_guarded(
    g: &cst::GuardedExpr,
    out: &mut std::collections::HashSet<(Option<String>, String)>,
) {
    match g {
        cst::GuardedExpr::Unconditional(e) => collect_qualified_refs_expr(e, out),
        cst::GuardedExpr::Guarded(gs) => {
            for gd in gs {
                for p in &gd.patterns {
                    match p {
                        cst::GuardPattern::Pattern(_, e)
                        | cst::GuardPattern::Boolean(e) => {
                            collect_qualified_refs_expr(e, out)
                        }
                    }
                }
                collect_qualified_refs_expr(&gd.expr, out);
            }
        }
    }
}

fn collect_qualified_refs_expr(
    expr: &cst::Expr,
    out: &mut std::collections::HashSet<(Option<String>, String)>,
) {
    match expr {
        cst::Expr::Var { name, .. } => {
            if let Some(m) = &name.module {
                let q = crate::typecheck_db::util::resolve_symbol(m.symbol());
                let n = crate::typecheck_db::util::resolve_symbol(name.name.symbol());
                out.insert((Some(q), n));
            }
        }
        cst::Expr::Constructor { name, .. } => {
            if let Some(m) = &name.module {
                let q = crate::typecheck_db::util::resolve_symbol(m.symbol());
                let n = crate::typecheck_db::util::resolve_symbol(name.name.symbol());
                out.insert((Some(q), n));
            }
        }
        cst::Expr::App { func, arg, .. } => {
            collect_qualified_refs_expr(func, out);
            collect_qualified_refs_expr(arg, out);
        }
        cst::Expr::VisibleTypeApp { func, .. } => {
            collect_qualified_refs_expr(func, out);
        }
        cst::Expr::Lambda { body, .. } => collect_qualified_refs_expr(body, out),
        cst::Expr::Op { left, right, .. } => {
            collect_qualified_refs_expr(left, out);
            collect_qualified_refs_expr(right, out);
        }
        cst::Expr::BacktickApp { func, left, right, .. } => {
            collect_qualified_refs_expr(func, out);
            collect_qualified_refs_expr(left, out);
            collect_qualified_refs_expr(right, out);
        }
        cst::Expr::If { cond, then_expr, else_expr, .. } => {
            collect_qualified_refs_expr(cond, out);
            collect_qualified_refs_expr(then_expr, out);
            collect_qualified_refs_expr(else_expr, out);
        }
        cst::Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                collect_qualified_refs_expr(e, out);
            }
            for alt in alts {
                collect_qualified_refs_guarded(&alt.result, out);
            }
        }
        cst::Expr::Let { bindings, body, .. } => {
            for b in bindings {
                if let cst::LetBinding::Value { expr, .. } = b {
                    collect_qualified_refs_expr(expr, out);
                }
            }
            collect_qualified_refs_expr(body, out);
        }
        cst::Expr::Do { statements, .. } | cst::Expr::Ado { statements, .. } => {
            for s in statements {
                match s {
                    cst::DoStatement::Bind { expr, .. }
                    | cst::DoStatement::Discard { expr, .. } => {
                        collect_qualified_refs_expr(expr, out);
                    }
                    cst::DoStatement::Let { bindings, .. } => {
                        for b in bindings {
                            if let cst::LetBinding::Value { expr, .. } = b {
                                collect_qualified_refs_expr(expr, out);
                            }
                        }
                    }
                }
            }
            if let cst::Expr::Ado { result, .. } = expr {
                collect_qualified_refs_expr(result, out);
            }
        }
        cst::Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    collect_qualified_refs_expr(v, out);
                }
            }
        }
        cst::Expr::RecordAccess { expr, .. } => {
            collect_qualified_refs_expr(expr, out);
        }
        cst::Expr::RecordUpdate { expr: rec, updates, .. } => {
            collect_qualified_refs_expr(rec, out);
            for u in updates {
                collect_qualified_refs_expr(&u.value, out);
            }
        }
        cst::Expr::TypeAnnotation { expr, .. } => {
            collect_qualified_refs_expr(expr, out);
        }
        cst::Expr::Negate { expr, .. } => {
            collect_qualified_refs_expr(expr, out);
        }
        cst::Expr::Parens { expr, .. } => {
            collect_qualified_refs_expr(expr, out);
        }
        cst::Expr::Array { elements, .. } => {
            for e in elements {
                collect_qualified_refs_expr(e, out);
            }
        }
        _ => {}
    }
}


fn detect_local_explicit_import_conflicts(
    module: &cst::Module,
    registry: &ModuleRegistry,
    prims: &std::collections::HashMap<String, ModuleExports>,
    errors: &mut Vec<ImportError>,
) {
    use std::collections::HashMap as Map;
    #[derive(Hash, Eq, PartialEq, Clone, Copy)]
    enum Ns {
        Value,
        Type,
        Class,
    }
    // Collect (namespace, name → source module) from unqualified
    // explicit imports. Qualified imports (`import M as Q`) don't
    // bring names into the unqualified namespace.
    let mut imported: Map<(Ns, String), (String, crate::span::Span)> = Map::new();
    for imp in &module.imports {
        if imp.qualified.is_some() {
            continue;
        }
        let target_name = module_name_string(&imp.module);
        let target: Option<&ModuleExports> = prims
            .get(&target_name)
            .or_else(|| registry.get(&target_name));
        let target = match target {
            Some(t) => t,
            None => continue,
        };
        if let Some(ImportList::Explicit(items)) = &imp.imports {
            for item in items {
                let (ns, name) = match item {
                    cst::Import::Value(n) => (
                        Ns::Value,
                        crate::typecheck_db::util::resolve_symbol(
                            n.value.symbol(),
                        ),
                    ),
                    cst::Import::Type(n, _) => (
                        Ns::Type,
                        crate::typecheck_db::util::resolve_symbol(
                            n.value.symbol(),
                        ),
                    ),
                    cst::Import::Class(n) => (
                        Ns::Class,
                        crate::typecheck_db::util::resolve_symbol(
                            n.value.symbol(),
                        ),
                    ),
                    _ => continue,
                };
                let _ = target;
                imported.insert((ns, name), (target_name.clone(), imp.span));
            }
        }
    }
    if imported.is_empty() {
        return;
    }
    // Walk local decls; collect any whose (namespace, name) is in
    // `imported` as a CANDIDATE conflict. A `data Cons` (type)
    // doesn't conflict with an `import M (class Cons)` (class)
    // because they're in different namespaces.
    //
    // The reference compiler has a quirk: a local type/class decl
    // that collides with an unqualified explicit import is OK so
    // long as the conflicting name is NEVER referenced unqualified
    // in the module body. The conflict only matters at the use
    // site — without a use, there's no ambiguity to resolve. So we
    // collect candidates here, then check use-sites below, and
    // only emit ScopeConflict for candidates that ARE used.
    let mut candidates: Vec<(Ns, String, String, crate::span::Span, crate::span::Span)> =
        Vec::new();
    for d in &module.decls {
        let (ns, decl_name, span) = match d {
            cst::Decl::TypeAlias { name, span, .. }
            | cst::Decl::Data { name, span, .. }
            | cst::Decl::Newtype { name, span, .. } => (
                Ns::Type,
                crate::typecheck_db::util::resolve_symbol(name.value.symbol()),
                *span,
            ),
            cst::Decl::Class { name, span, .. } => (
                Ns::Class,
                crate::typecheck_db::util::resolve_symbol(name.value.symbol()),
                *span,
            ),
            // Value declarations shadow explicit imports silently in
            // PureScript — the local definition wins. Only type and class
            // declarations cause ScopeConflict when they collide with an
            // explicit import. Skip value / foreign decls here.
            _ => continue,
        };
        if let Some((src, src_span)) = imported.get(&(ns, decl_name.clone())) {
            candidates.push((ns, decl_name, src.clone(), *src_span, span));
        }
    }
    if candidates.is_empty() {
        return;
    }
    // Collect unqualified type-constructor references and
    // unqualified constraint-class references from every type
    // expression in the module's decls. The declaration's own LHS
    // (the binder name on `data X`, `type X`, etc.) is NOT a
    // reference and is excluded by virtue of only visiting
    // TypeExpr positions, not Decl-name positions.
    let mut type_refs: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut class_refs: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for d in &module.decls {
        collect_unqualified_refs_decl(d, &mut type_refs, &mut class_refs);
    }
    for (ns, name, src, src_span, span) in candidates {
        let referenced = match ns {
            Ns::Type => type_refs.contains(&name),
            Ns::Class => class_refs.contains(&name),
            Ns::Value => false,
        };
        if !referenced {
            continue;
        }
        errors.push(ImportError {
            span,
            kind: ImportErrorKind::ScopeConflict {
                name,
                first_module: src,
                second_module: module_name_string(&module.name.value),
                first_import: src_span,
                second_import: span,
            },
        });
    }
}

/// Walk a decl's type expressions, collecting unqualified
/// references — split by namespace. Type-constructor refs go in
/// `type_refs`; constraint class refs go in `class_refs`. The
/// decl's own LHS-bound name is skipped automatically (we only
/// visit TypeExpr nodes, never Decl.name).
fn collect_unqualified_refs_decl(
    d: &cst::Decl,
    type_refs: &mut std::collections::HashSet<String>,
    class_refs: &mut std::collections::HashSet<String>,
) {
    match d {
        cst::Decl::TypeAlias { ty, .. } => {
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        cst::Decl::Data { constructors, .. } => {
            for ctor in constructors {
                for f in &ctor.fields {
                    walk_typeexpr_unqualified(f, type_refs, class_refs);
                }
            }
        }
        cst::Decl::Newtype { ty, .. } => {
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        cst::Decl::Class { constraints, members, .. } => {
            for c in constraints {
                if c.class.module.is_none() {
                    class_refs.insert(
                        crate::typecheck_db::util::resolve_symbol(c.class.name.symbol()),
                    );
                }
                for arg in &c.args {
                    walk_typeexpr_unqualified(arg, type_refs, class_refs);
                }
            }
            for m in members {
                walk_typeexpr_unqualified(&m.ty, type_refs, class_refs);
            }
        }
        cst::Decl::TypeSignature { ty, .. } => {
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        cst::Decl::Foreign { ty, .. } => {
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        cst::Decl::Instance { class_name, types, constraints, members, .. } => {
            if class_name.module.is_none() {
                class_refs.insert(
                    crate::typecheck_db::util::resolve_symbol(
                        class_name.name.symbol(),
                    ),
                );
            }
            for t in types {
                walk_typeexpr_unqualified(t, type_refs, class_refs);
            }
            for c in constraints {
                if c.class.module.is_none() {
                    class_refs.insert(
                        crate::typecheck_db::util::resolve_symbol(c.class.name.symbol()),
                    );
                }
                for arg in &c.args {
                    walk_typeexpr_unqualified(arg, type_refs, class_refs);
                }
            }
            for m in members {
                collect_unqualified_refs_decl(m, type_refs, class_refs);
            }
        }
        _ => {}
    }
}

fn walk_typeexpr_unqualified(
    te: &cst::TypeExpr,
    type_refs: &mut std::collections::HashSet<String>,
    class_refs: &mut std::collections::HashSet<String>,
) {
    match te {
        cst::TypeExpr::Constructor { name, .. } => {
            if name.module.is_none() {
                type_refs.insert(
                    crate::typecheck_db::util::resolve_symbol(name.name.symbol()),
                );
            }
        }
        cst::TypeExpr::App { constructor, arg, .. } => {
            walk_typeexpr_unqualified(constructor, type_refs, class_refs);
            walk_typeexpr_unqualified(arg, type_refs, class_refs);
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_typeexpr_unqualified(from, type_refs, class_refs);
            walk_typeexpr_unqualified(to, type_refs, class_refs);
        }
        cst::TypeExpr::Forall { vars, ty, .. } => {
            for (_, _, k) in vars {
                if let Some(k) = k {
                    walk_typeexpr_unqualified(k, type_refs, class_refs);
                }
            }
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                if c.class.module.is_none() {
                    class_refs.insert(
                        crate::typecheck_db::util::resolve_symbol(c.class.name.symbol()),
                    );
                }
                for arg in &c.args {
                    walk_typeexpr_unqualified(arg, type_refs, class_refs);
                }
            }
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_typeexpr_unqualified(&f.ty, type_refs, class_refs);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_typeexpr_unqualified(&f.ty, type_refs, class_refs);
            }
            if let Some(t) = tail {
                walk_typeexpr_unqualified(t, type_refs, class_refs);
            }
        }
        cst::TypeExpr::Parens { ty, .. } => {
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        cst::TypeExpr::Kinded { ty, kind, .. } => {
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
            walk_typeexpr_unqualified(kind, type_refs, class_refs);
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_typeexpr_unqualified(left, type_refs, class_refs);
            walk_typeexpr_unqualified(right, type_refs, class_refs);
        }
        cst::TypeExpr::ArrayPattern { elements, .. } => {
            for e in elements {
                walk_typeexpr_unqualified(e, type_refs, class_refs);
            }
        }
        cst::TypeExpr::AsPattern { ty, .. } => {
            walk_typeexpr_unqualified(ty, type_refs, class_refs);
        }
        _ => {}
    }
}

/// Compute the set of unqualified VALUE names that an import would
/// bring into the importer's scope, respecting any explicit-list /
/// hiding-list filter. Restricted to values (not types/classes/ctors)
/// because the ScopeConflict detector relies on
/// `ModuleExports.value_origins` to dedupe re-exports — types and
/// classes lack origin tracking, so attempting to detect their
/// conflicts here would false-positive on Prelude re-exports of
/// Data.Eq's `Eq1`, etc.
fn compute_imported_names(
    target: &ModuleExports,
    list: &Option<ImportList>,
) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let push_all = |out: &mut Vec<String>, target: &ModuleExports, hidden: &HideFilter| {
        for n in target.values.keys() {
            if !hidden.values.contains(n.as_str()) {
                out.push(n.clone());
            }
        }
    };
    match list {
        None => push_all(&mut out, target, &HideFilter::default()),
        Some(ImportList::Hiding(hidden)) => {
            let mut filter = HideFilter::default();
            for item in hidden {
                filter.insert(item);
            }
            push_all(&mut out, target, &filter);
        }
        Some(ImportList::Explicit(items)) => {
            for item in items {
                if let cst::Import::Value(n) = item {
                    out.push(
                        crate::typecheck_db::util::resolve_symbol(n.value.symbol()),
                    );
                }
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Import application helpers
// ---------------------------------------------------------------------------

fn apply_import(
    target_name: &str,
    target: &ModuleExports,
    imp: &ImportDecl,
    qualifier: Option<String>,
    env: &mut Env,
    ix: &mut InstanceIndex,
    errors: &mut Vec<ImportError>,
) {
    match &imp.imports {
        None => {
            // `import M` or `import M as Q` — take everything.
            import_all(target_name, target, qualifier.clone(), env, ix);
        }
        Some(ImportList::Explicit(items)) => {
            for item in items {
                apply_explicit(target_name, target, item, qualifier.clone(), env, ix, errors, imp.span);
            }
            // Instances still travel with any non-empty import.
            merge_instances_and_classes(target, ix);
        }
        Some(ImportList::Hiding(hidden)) => {
            let mut filter = HideFilter::default();
            for item in hidden {
                filter.insert(item);
            }
            import_all_except(target_name, target, qualifier.clone(), &filter, env, ix);
        }
    }
}

fn import_all(
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<String>,
    env: &mut Env,
    ix: &mut InstanceIndex,
) {
    import_all_except(target_name, target, qualifier, &HideFilter::default(), env, ix)
}

fn import_all_except(
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<String>,
    hidden: &HideFilter,
    env: &mut Env,
    ix: &mut InstanceIndex,
) {
    // Values. Bind each scheme under both the import-chosen
    // qualifier key (`qualifier.name`) AND an origin-module key
    // (`target.value_origins[name].name`, falling back to the
    // importee itself). The origin key is what rebracket-time
    // fixity lowering looks up when a fixity decl's target has
    // been canonicalized to its defining module — without it,
    // `Var("Data.Function.apply")` would not resolve when the
    // module was imported unqualified through a re-exporter.
    for (name, scheme) in &target.values {
        let is_hidden = hidden.values.contains(name.as_str());
        // `target.values` already stores `Arc<Scheme>`. Each
        // binding is a pure `Arc::clone` (one atomic increment), no
        // deep `Scheme::clone` and no fresh heap allocation. Each
        // importer of Prelude binds 200+ values under two keys each
        // — that's ~400 atomic increments per Prelude importer
        // instead of ~400 deep `Type` tree clones.
        let origin = target
            .value_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| target_name.to_string());
        if !is_hidden {
            let key = QName { module: qualifier.clone(), name: name.clone() };
            env.bind_scheme_arc(key, std::sync::Arc::clone(scheme));
        }
        env.bind_scheme_arc(
            QName { module: Some(origin), name: name.clone() },
            std::sync::Arc::clone(scheme),
        );
    }
    // Also bind every extra origin-qualified scheme the
    // re-exporter surfaced — e.g. `Prelude.qualified_values`
    // holds `Data.Function.apply` even when its primary `values`
    // entry was won by `Control.Apply.apply`. Origin-qualified
    // bindings ignore `hidden` for the same reason as above.
    for ((origin, name), scheme) in &target.qualified_values {
        env.bind_scheme_arc(
            QName { module: Some(origin.clone()), name: name.clone() },
            std::sync::Arc::clone(scheme),
        );
    }
    // Data constructors: synthesize each one's value scheme
    // (`forall a b. f1 -> f2 -> … -> T a b …`) and bind it
    // under both the import qualifier and the origin module.
    // The origin-qualified key lets a rebracketer-produced
    // `Expr::Constructor { name: Lib.Tuple }` resolve even when
    // `Lib` was imported unqualified (i.e. `qualifier: None`).
    for (ctor_name, info) in &target.ctors {
        if hidden.ctors.contains(ctor_name.as_str()) {
            continue;
        }
        let arc = std::sync::Arc::new(synth_ctor_scheme(info));
        let key = QName { module: qualifier.clone(), name: ctor_name.clone() };
        env.bind_scheme_arc(key, std::sync::Arc::clone(&arc));
        // Bind under BOTH the import-target module AND the ctor's
        // DEFINING module (when they differ — re-export chain).
        // Post-resolve_pass refs carry the defining module; the
        // import-target key stays as a transition belt-and-braces.
        let target_key = QName {
            module: Some(target_name.to_string()),
            name: ctor_name.clone(),
        };
        env.bind_scheme_arc(target_key, std::sync::Arc::clone(&arc));
        if let Some(origin) = target.ctor_origins.get(ctor_name) {
            if origin != target_name {
                let origin_key = QName {
                    module: Some(origin.clone()),
                    name: ctor_name.clone(),
                };
                env.bind_scheme_arc(origin_key, arc);
            }
        }
    }
    // Instances + class info: always propagated.
    merge_instances_and_classes(target, ix);
}

fn apply_explicit(
    target_name: &str,
    target: &ModuleExports,
    item: &cst::Import,
    qualifier: Option<String>,
    env: &mut Env,
    _ix: &mut InstanceIndex,
    errors: &mut Vec<ImportError>,
    span: crate::span::Span,
) {
    match item {
        cst::Import::Value(vn) => {
            let name = crate::typecheck_db::util::resolve_symbol(vn.value.symbol());
            match target.values.get(&name) {
                Some(scheme) => {
                    let key = QName { module: qualifier.clone(), name: name.clone() };
                    env.bind_scheme_arc(key, std::sync::Arc::clone(scheme));
                    // Also bind under the origin module's qualified
                    // key so a rebracketer-produced `Var("A.foo")`
                    // can resolve even when `foo` was imported
                    // unqualified. Matches the `import_all_except`
                    // path — every imported scheme is findable both
                    // by the user's chosen qualifier and by its
                    // defining module.
                    let origin = target
                        .value_origins
                        .get(&name)
                        .cloned()
                        .unwrap_or_else(|| target_name.to_string());
                    env.bind_scheme_arc(
                        QName {
                            module: Some(origin),
                            name: name.clone(),
                        },
                        std::sync::Arc::clone(scheme),
                    );
                    // If this Value-import is actually an operator
                    // alias (e.g. `import M ((==))` where `==` aliases
                    // `eq`), also bring the underlying target into
                    // scope. After desugar, call-site code references
                    // the target directly, not the operator, so the
                    // target must be resolvable.
                    if let Some(fx) = target.value_fixities.get(&name) {
                        if let Some(target_scheme) = target.values.get(&fx.target_name) {
                            env.bind_scheme_arc(
                                QName {
                                    module: qualifier.clone(),
                                    name: fx.target_name.clone(),
                                },
                                std::sync::Arc::clone(target_scheme),
                            );
                            // Mirror under the fixity's own
                            // origin-module (may differ from
                            // `target_name` when a re-export chain
                            // is at play).
                            let fixity_origin = fx
                                .target_module
                                .clone()
                                .unwrap_or_else(|| target_name.to_string());
                            env.bind_scheme_arc(
                                QName {
                                    module: Some(fixity_origin),
                                    name: fx.target_name.clone(),
                                },
                                std::sync::Arc::clone(target_scheme),
                            );
                        }
                        // Constructor-operator alias: `infixr 6
                        // Tuple as /\` — fixity target is in
                        // `target.ctors`, not `target.values`.
                        // Synthesize the ctor's value scheme and
                        // bind under qualifier + origin keys so
                        // rebracketed `a /\ b` → `Constructor
                        // A.Tuple` resolves.
                        if let Some(info) = target.ctors.get(&fx.target_name) {
                            let ctor_scheme = std::sync::Arc::new(synth_ctor_scheme(info));
                            env.bind_scheme_arc(
                                QName {
                                    module: qualifier.clone(),
                                    name: fx.target_name.clone(),
                                },
                                std::sync::Arc::clone(&ctor_scheme),
                            );
                            let fixity_origin = fx
                                .target_module
                                .clone()
                                .unwrap_or_else(|| target_name.to_string());
                            env.bind_scheme_arc(
                                QName {
                                    module: Some(fixity_origin),
                                    name: fx.target_name.clone(),
                                },
                                ctor_scheme,
                            );
                        } else if let Some(origin) = fx.target_module.clone() {
                            // Re-exporter path: the fixity's
                            // target lives in `qualified_values`
                            // because it was resolved through an
                            // imported module's exports rather
                            // than this one. Bind both the
                            // unqualified form (for the common
                            // fallback lookup) and the
                            // origin-qualified form.
                            if let Some(scheme) = target
                                .qualified_values
                                .get(&(origin.clone(), fx.target_name.clone()))
                            {
                                env.bind_scheme_arc(
                                    QName {
                                        module: qualifier.clone(),
                                        name: fx.target_name.clone(),
                                    },
                                    std::sync::Arc::clone(scheme),
                                );
                                env.bind_scheme_arc(
                                    QName {
                                        module: Some(origin),
                                        name: fx.target_name.clone(),
                                    },
                                    std::sync::Arc::clone(scheme),
                                );
                            }
                        }
                    }
                }
                None => errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownValue {
                        module: target_name.into(),
                        name,
                    },
                }),
            }
        }
        cst::Import::Type(tn, members) => {
            let name = crate::typecheck_db::util::resolve_symbol(tn.value.symbol());
            let type_known = target.type_arities.contains_key(&name)
                || target.data_constructors.contains_key(&name)
                || target.type_aliases.contains_key(&name);
            if !type_known {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownType {
                        module: target_name.into(),
                        name: name.clone(),
                    },
                });
                return;
            }
            // Which ctors travel with the type?
            if let Some(all_ctors) = target.data_constructors.get(&name) {
                let wanted: Vec<String> = match members {
                    None => Vec::new(),
                    Some(DataMembers::All) => all_ctors.clone(),
                    Some(DataMembers::Explicit(list)) => list
                        .iter()
                        .map(|c| {
                            crate::typecheck_db::util::resolve_symbol(c.value.symbol())
                        })
                        .collect(),
                };
                for ctor in wanted {
                    if !all_ctors.contains(&ctor) {
                        errors.push(ImportError {
                            span,
                            kind: ImportErrorKind::UnknownConstructor {
                                module: target_name.into(),
                                type_name: name.clone(),
                                ctor,
                            },
                        });
                        continue;
                    }
                    if let Some(info) = target.ctors.get(&ctor) {
                        let scheme = synth_ctor_scheme(info);
                        let key = QName {
                            module: qualifier.clone(),
                            name: ctor.clone(),
                        };
                        env.bind_scheme(key, scheme.clone());
                        let target_key = QName {
                            module: Some(target_name.to_string()),
                            name: ctor.clone(),
                        };
                        env.bind_scheme(target_key, scheme.clone());
                        // Also bind under the DEFINING module so
                        // post-resolve_pass refs resolve.
                        if let Some(origin) = target.ctor_origins.get(&ctor) {
                            if origin != target_name {
                                let origin_key = QName {
                                    module: Some(origin.clone()),
                                    name: ctor.clone(),
                                };
                                env.bind_scheme(origin_key, scheme);
                            }
                        }
                    }
                }
            }
        }
        cst::Import::Class(cn) => {
            let name = crate::typecheck_db::util::resolve_symbol(cn.value.symbol());
            if !target.classes.contains_key(&name) {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownClass {
                        module: target_name.into(),
                        name,
                    },
                });
            }
            // Class import doesn't automatically pull in methods
            // at this layer — the class's methods live in
            // `target.values` and must be explicitly listed OR
            // brought in via `import M (class C)` + the method's
            // own import. Legacy pulls methods along with the
            // class; we can add that here once a fixture needs it.
        }
        cst::Import::TypeOp(on) => {
            let name = crate::typecheck_db::util::resolve_symbol(on.value.symbol());
            if !target.type_fixities.contains_key(&name) {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownOperator {
                        module: target_name.into(),
                        name,
                    },
                });
            }
        }
    }
}

fn merge_instances_and_classes(target: &ModuleExports, ix: &mut InstanceIndex) {
    for (class_name, info) in &target.classes {
        ix.insert_class(class_name.clone(), info.clone());
    }
    for inst in &target.instances {
        ix.insert(inst.clone());
    }
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

/// Synthesize the value-level `Scheme` for a constructor:
/// `forall <type_vars>. f1 -> f2 -> … -> Parent <type_vars>`.
pub(crate) fn synth_ctor_scheme(
    info: &crate::typecheck_db::passes::exhaustiveness::CtorInfo,
) -> crate::typecheck_db::types::Scheme {
    use crate::typecheck_db::types::{Scheme, Type};
    // Use the defining module if known so the synthesized ctor
    // scheme's result type aligns with resolver-rewritten use-site
    // qualifiers. Legacy entries (no parent_module) still produce
    // unqualified Type::Con and rely on the lenient unify rule.
    let head_qname = match &info.parent_module {
        Some(m) => QName::qualified(m, &info.parent_type),
        None => QName::unqualified(&info.parent_type),
    };
    let head = Type::Con(head_qname);
    let mut result = head;
    for v in &info.type_vars {
        result = Type::app(result, Type::Var(v.clone()));
    }
    let mut ty = result;
    for field in info.fields.iter().rev() {
        ty = Type::fun(field.clone(), ty);
    }
    Scheme::new(info.type_vars.clone(), ty)
}

fn module_name_string(m: &cst::ModuleName) -> String {
    m.parts
        .iter()
        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
        .collect::<Vec<_>>()
        .join(".")
}

#[derive(Debug, Clone, Default)]
struct HideFilter<'a> {
    values: std::collections::HashSet<&'a str>,
    ctors: std::collections::HashSet<&'a str>,
    types: std::collections::HashSet<&'a str>,
    classes: std::collections::HashSet<&'a str>,
    ops: std::collections::HashSet<&'a str>,
}

impl<'a> HideFilter<'a> {
    fn insert(&mut self, item: &'a cst::Import) {
        // For hiding, we only need to keep name strings; clone
        // them out of the interner as owned strings. But we
        // store string slices — the CST outlives this filter so
        // we can use short-lived refs through a boxed leak.
        let name_owned: String = match item {
            cst::Import::Value(n) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
            cst::Import::Type(n, _) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
            cst::Import::Class(n) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
            cst::Import::TypeOp(n) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
        };
        // Leak to 'static since this filter is short-lived per
        // import resolution. An import list is typically <100
        // names, so this is a small, bounded leak.
        let s: &'static str = Box::leak(name_owned.into_boxed_str());
        match item {
            cst::Import::Value(_) => {
                self.values.insert(s);
            }
            cst::Import::Type(_, members) => {
                self.types.insert(s);
                if let Some(DataMembers::All) = members {
                    // Hide all ctors of this type too.
                }
                // Specific ctor hiding not supported in hiding
                // lists by legacy either.
            }
            cst::Import::Class(_) => {
                self.classes.insert(s);
            }
            cst::Import::TypeOp(_) => {
                self.ops.insert(s);
            }
        }
    }
}

// Silence: unused Decl variant would hint at Decl import not being needed
// in this module; we keep the `cst::Import` / `cst::Module` paths.
#[allow(dead_code)]
fn _touch_decl(_: &Decl) {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::env::Lookup;
    use crate::typecheck_db::module_registry::ModuleExports;
    use crate::typecheck_db::passes::instance_index::{ClassInfo, Instance};
    use crate::typecheck_db::types::{Scheme, Type};

    fn int_ty() -> Type {
        crate::typecheck_db::types::prim_int()
    }

    fn parse_mod(src: &str) -> cst::Module {
        parse(src).unwrap()
    }

    /// Register a fake module with a single value `foo :: Int`.
    fn registry_with_foo() -> ModuleRegistry {
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.values.insert("foo".into(), std::sync::Arc::new(Scheme::mono(int_ty())));
        r.insert("Data.Foo", exp);
        r
    }

    // =================================================================
    // Prim is always visible
    // =================================================================

    #[test]
    fn prim_is_implicitly_imported() {
        let module = parse_mod("module M where\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert!(errs.is_empty());
        // `Int` is a Prim type; after implicit Prim import, the
        // env should know about Prim's classes at least.
        let _ = env;
    }

    #[test]
    fn prim_auto_import_provides_partial_class() {
        let module = parse_mod("module M where\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert!(errs.is_empty());
        assert!(ix.class_info("Partial").is_some());
        assert!(ix.class_info("IsSymbol").is_some());
    }

    // =================================================================
    // import all / qualified / hiding
    // =================================================================

    #[test]
    fn import_all_unqualified_makes_values_available() {
        let module = parse_mod("module M where\nimport Data.Foo\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert!(errs.is_empty(), "got: {errs:?}");
        match env.lookup_unqualified("foo") {
            Lookup::Scheme(s) => assert_eq!(s.ty, int_ty()),
            other => panic!("expected scheme, got {other:?}"),
        }
    }

    #[test]
    fn import_as_qualifies_all_values() {
        let module = parse_mod("module M where\nimport Data.Foo as F\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert!(errs.is_empty());
        let qualified = QName { module: Some("F".into()), name: "foo".into() };
        assert!(env.lookup_qualified(&qualified).is_some());
    }

    #[test]
    fn import_explicit_value() {
        let module = parse_mod("module M where\nimport Data.Foo (foo)\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert!(errs.is_empty());
        match env.lookup_unqualified("foo") {
            Lookup::Scheme(_) => {}
            other => panic!("expected scheme, got {other:?}"),
        }
    }

    #[test]
    fn import_unknown_value_reports_error() {
        let module = parse_mod("module M where\nimport Data.Foo (bar)\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert_eq!(errs.len(), 1);
        match &errs[0].kind {
            ImportErrorKind::UnknownValue { module, name } => {
                assert_eq!(module, "Data.Foo");
                assert_eq!(name, "bar");
            }
            other => panic!("wrong error: {other:?}"),
        }
    }

    #[test]
    fn import_unknown_module_reports_error() {
        let module = parse_mod("module M where\nimport Data.DoesNotExist\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert_eq!(errs.len(), 1);
        assert!(matches!(
            errs[0].kind,
            ImportErrorKind::UnknownModule(ref m) if m == "Data.DoesNotExist"
        ));
    }

    #[test]
    fn import_hiding_excludes_listed_value() {
        // Register a module with both foo + bar.
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.values.insert("foo".into(), std::sync::Arc::new(Scheme::mono(int_ty())));
        exp.values.insert("bar".into(), std::sync::Arc::new(Scheme::mono(int_ty())));
        r.insert("Data.Mix", exp);
        let module = parse_mod("module M where\nimport Data.Mix hiding (bar)\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &r);
        assert!(errs.is_empty());
        assert!(matches!(env.lookup_unqualified("foo"), Lookup::Scheme(_)));
        assert!(matches!(env.lookup_unqualified("bar"), Lookup::Missing));
    }

    // =================================================================
    // Instance propagation
    // =================================================================

    #[test]
    fn imports_propagate_instances_and_class_info() {
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.classes.insert(
            "Eq".into(),
            ClassInfo { type_vars: vec!["a".into()], fundeps: vec![], superclasses: vec![] },
        );
        exp.instances.push(Instance {
            class: QName::unqualified("Eq"),
            types: vec![int_ty()],
            context: vec![],
            vars: vec![],
            chained: false,
        });
        r.insert("Data.Eq", exp);
        let module = parse_mod("module M where\nimport Data.Eq\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &r);
        assert!(errs.is_empty());
        assert!(ix.class_info("Eq").is_some());
        assert_eq!(ix.candidates("Eq").len(), 1);
    }

    #[test]
    fn explicit_imports_still_propagate_instances() {
        // PureScript: even `import M (foo)` pulls in M's instances.
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.values.insert("foo".into(), std::sync::Arc::new(Scheme::mono(int_ty())));
        exp.instances.push(Instance {
            class: QName::unqualified("Eq"),
            types: vec![int_ty()],
            context: vec![],
            vars: vec![],
            chained: false,
        });
        r.insert("Data.Foo", exp);
        let module = parse_mod("module M where\nimport Data.Foo (foo)\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &r);
        assert!(errs.is_empty());
        assert_eq!(ix.candidates("Eq").len(), 1);
    }

    // =================================================================
    // Class / operator / type import errors
    // =================================================================

    #[test]
    fn import_unknown_class_reports_error() {
        let mut r = ModuleRegistry::new();
        r.insert("Data.Foo", ModuleExports::default());
        let module =
            parse_mod("module M where\nimport Data.Foo (class NoSuch)\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &r);
        assert_eq!(errs.len(), 1);
        assert!(matches!(errs[0].kind, ImportErrorKind::UnknownClass { .. }));
    }

    #[test]
    fn import_unknown_type_reports_error() {
        let mut r = ModuleRegistry::new();
        r.insert("Data.Foo", ModuleExports::default());
        let module = parse_mod("module M where\nimport Data.Foo (NoSuchType)\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &r);
        assert_eq!(errs.len(), 1);
        assert!(matches!(errs[0].kind, ImportErrorKind::UnknownType { .. }));
    }

    #[test]
    fn import_prim_submodule_by_name() {
        // `import Prim.Row` is a real thing; resolver should
        // pick it up from the static prim_exports map.
        let module = parse_mod("module M where\nimport Prim.Row\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert!(errs.is_empty());
        assert!(ix.class_info("Cons").is_some());
        assert!(ix.class_info("Union").is_some());
    }
}
