//! Name resolution pass.
//!
//! Runs before typechecking to resolve every name reference in a module to its
//! definition location. Produces a `ResolvedResult` containing:
//! - A sorted list of resolutions mapping usage spans to definition sites
//! - Any name resolution errors (undefined variables, unknown types, etc.)
//!
//! The resolutions are sorted by span start, enabling:
//! - Binary search by span (for typechecker lookup)
//! - Binary search by byte offset (for IDE go-to-definition)

use std::collections::{HashMap, HashSet};

use crate::ast::span::Span;
use crate::cst::{
    Binder, CaseAlternative, Decl, DoStatement, Expr, GuardPattern, GuardedExpr, ImportList,
    LetBinding, Literal, Module, QualifiedIdent, TypeExpr,
};
use crate::interner::{self, Symbol};
use crate::typechecker::check::{ModuleExports, ModuleRegistry};
use crate::typechecker::error::TypeError;

// ===== Public types =====

/// Result of name resolution for a module.
pub struct ResolvedResult {
    /// Name resolution errors (unresolved names, scope conflicts, etc.)
    pub errors: Vec<TypeError>,
    /// All resolutions, sorted by `src_span.start` for binary search.
    resolutions: Vec<ResolvedName>,
    /// Resolutions keyed by source span for direct lookup (index into `resolutions`).
    resolution_map: HashMap<Span, usize>,
}

impl ResolvedResult {
    /// Look up the resolution for a given byte offset (e.g. cursor position).
    /// Returns the resolution whose span contains the offset, if any.
    pub fn lookup_at(&self, offset: usize) -> Option<&ResolvedName> {
        // Binary search for the last span whose start <= offset
        let idx = self.resolutions.partition_point(|r| r.src_span.start <= offset);
        if idx == 0 {
            return None;
        }
        let r = &self.resolutions[idx - 1];
        if offset < r.src_span.end {
            Some(r)
        } else {
            None
        }
    }

    /// Look up the resolution for an exact source span.
    pub fn lookup_at_span(&self, span: Span) -> Option<&ResolvedName> {
        self.resolution_map.get(&span).map(|&idx| &self.resolutions[idx])
    }
}

/// A single name resolution: maps a usage site to its definition.
#[derive(Clone)]
pub struct ResolvedName {
    /// Span of the name at the usage site
    pub src_span: Span,
    /// The symbol as written at the usage site
    pub src_symbol: Symbol,
    /// The namespace of the name
    pub namespace: Namespace,
    /// Where the definition lives
    pub definition: DefinitionSite,
}

/// What kind of name this is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Namespace {
    Value,
    Type,
    Class,
    TypeOperator,
}

/// Where a name is defined.
#[derive(Debug, Clone)]
pub enum DefinitionSite {
    /// Defined in the current module at this span
    Local(Span),
    /// Imported from another module
    Imported(Symbol),
    /// Built-in from Prim
    Prim,
    /// Local variable (lambda param, let binding, case binder, etc.)
    LocalVar(Span),
}

// ===== Internal types =====

/// Origin of a name in the scope.
#[derive(Clone)]
enum NameOrigin {
    /// Defined locally in this module at this declaration span
    Local(Span),
    /// Imported from module (module name as symbol e.g. "Data.Array")
    Imported(Symbol),
    /// Built-in from Prim
    Prim,
}

impl NameOrigin {
    fn to_definition_site(&self) -> DefinitionSite {
        match self {
            NameOrigin::Local(span) => DefinitionSite::Local(*span),
            NameOrigin::Imported(module) => DefinitionSite::Imported(*module),
            NameOrigin::Prim => DefinitionSite::Prim,
        }
    }
}

/// Names available at module scope, partitioned by namespace.
/// Each name maps to its origin (where it was defined).
struct NameScope {
    values: HashMap<Symbol, NameOrigin>,
    types: HashMap<Symbol, NameOrigin>,
    classes: HashMap<Symbol, NameOrigin>,
    type_operators: HashMap<Symbol, NameOrigin>,
    scope_conflicts: HashSet<Symbol>,
}

impl NameScope {
    fn new() -> Self {
        NameScope {
            values: HashMap::new(),
            types: HashMap::new(),
            classes: HashMap::new(),
            type_operators: HashMap::new(),
            scope_conflicts: HashSet::new(),
        }
    }
}

/// Local variable scope: name → span where introduced.
type LocalScope = HashMap<Symbol, Span>;

/// Context for the resolution walk.
struct Resolver<'a> {
    scope: &'a NameScope,
    resolutions: Vec<ResolvedName>,
    errors: Vec<TypeError>,
}

// ===== Helpers =====

fn qualified_symbol(module: Symbol, name: Symbol) -> Symbol {
    let mod_str = interner::resolve(module).unwrap_or_default();
    let name_str = interner::resolve(name).unwrap_or_default();
    interner::intern(&format!("{}.{}", mod_str, name_str))
}

fn is_prim_module(module: &crate::cst::ModuleName) -> bool {
    module.parts.len() == 1
        && interner::resolve(module.parts[0]).unwrap_or_default() == "Prim"
}

fn is_prim_submodule(module: &crate::cst::ModuleName) -> bool {
    module.parts.len() > 1
        && interner::resolve(module.parts[0]).unwrap_or_default() == "Prim"
}

fn module_name_to_symbol(module: &crate::cst::ModuleName) -> Symbol {
    let parts: Vec<String> = module
        .parts
        .iter()
        .map(|s| interner::resolve(*s).unwrap_or_default().to_string())
        .collect();
    interner::intern(&parts.join("."))
}

fn import_name(item: &crate::cst::Import) -> Symbol {
    match item {
        crate::cst::Import::Value(n) => *n,
        crate::cst::Import::Type(n, _) => *n,
        crate::cst::Import::TypeOp(n) => *n,
        crate::cst::Import::Class(n) => *n,
    }
}

fn maybe_qualify(name: Symbol, qualifier: Option<Symbol>) -> Symbol {
    match qualifier {
        Some(q) => qualified_symbol(q, name),
        None => name,
    }
}

// ===== Scope building =====

fn import_all_to_scope(
    exports: &ModuleExports,
    scope: &mut NameScope,
    qualifier: Option<Symbol>,
    origin: NameOrigin,
) {
    for name in exports.values.keys() {
        scope.values.insert(maybe_qualify(*name, qualifier), origin.clone());
    }
    for name in exports.data_constructors.keys() {
        scope.types.insert(maybe_qualify(*name, qualifier), origin.clone());
    }
    for (op, _) in &exports.type_operators {
        scope.type_operators.insert(*op, origin.clone());
    }
    for op in exports.value_fixities.keys() {
        scope.values.insert(maybe_qualify(*op, qualifier), origin.clone());
    }
    for name in exports.class_methods.keys() {
        scope.classes.insert(*name, origin.clone());
    }
    for name in exports.class_param_counts.keys() {
        scope.classes.insert(*name, origin.clone());
    }
    for name in exports.type_aliases.keys() {
        scope.types.insert(maybe_qualify(*name, qualifier), origin.clone());
    }
    for ctors in exports.data_constructors.values() {
        for ctor in ctors {
            scope.values.insert(maybe_qualify(*ctor, qualifier), origin.clone());
        }
    }
    for name in exports.type_con_arities.keys() {
        scope.types.insert(maybe_qualify(*name, qualifier), origin.clone());
    }
}

fn import_item_to_scope(
    item: &crate::cst::Import,
    exports: &ModuleExports,
    scope: &mut NameScope,
    qualifier: Option<Symbol>,
    origin: NameOrigin,
) {
    match item {
        crate::cst::Import::Value(name) => {
            scope.values.insert(maybe_qualify(*name, qualifier), origin);
        }
        crate::cst::Import::Type(name, members) => {
            scope.types.insert(maybe_qualify(*name, qualifier), origin.clone());
            if let Some(ctors) = exports.data_constructors.get(name) {
                match members {
                    Some(crate::cst::DataMembers::All) => {
                        for ctor in ctors {
                            scope.values.insert(maybe_qualify(*ctor, qualifier), origin.clone());
                        }
                    }
                    Some(crate::cst::DataMembers::Explicit(names)) => {
                        for n in names {
                            scope.values.insert(maybe_qualify(*n, qualifier), origin.clone());
                        }
                    }
                    None => {}
                }
            }
        }
        crate::cst::Import::TypeOp(name) => {
            scope.type_operators.insert(*name, origin);
        }
        crate::cst::Import::Class(name) => {
            scope.classes.insert(*name, origin.clone());
            for (method, (class, _)) in &exports.class_methods {
                if *class == *name {
                    scope.values.insert(maybe_qualify(*method, qualifier), origin.clone());
                }
            }
        }
    }
}

fn import_all_except_to_scope(
    exports: &ModuleExports,
    hidden: &HashSet<Symbol>,
    scope: &mut NameScope,
    qualifier: Option<Symbol>,
    origin: NameOrigin,
) {
    for name in exports.values.keys() {
        if !hidden.contains(name) {
            scope.values.insert(maybe_qualify(*name, qualifier), origin.clone());
        }
    }
    for name in exports.data_constructors.keys() {
        if !hidden.contains(name) {
            scope.types.insert(maybe_qualify(*name, qualifier), origin.clone());
        }
    }
    for (op, _) in &exports.type_operators {
        if !hidden.contains(op) {
            scope.type_operators.insert(*op, origin.clone());
        }
    }
    for op in exports.value_fixities.keys() {
        if !hidden.contains(op) {
            scope.values.insert(maybe_qualify(*op, qualifier), origin.clone());
        }
    }
    for name in exports.class_methods.keys() {
        if !hidden.contains(name) {
            scope.classes.insert(*name, origin.clone());
        }
    }
    for name in exports.class_param_counts.keys() {
        if !hidden.contains(name) {
            scope.classes.insert(*name, origin.clone());
        }
    }
    for name in exports.type_aliases.keys() {
        if !hidden.contains(name) {
            scope.types.insert(maybe_qualify(*name, qualifier), origin.clone());
        }
    }
    for ctors in exports.data_constructors.values() {
        for ctor in ctors {
            if !hidden.contains(ctor) {
                scope.values.insert(maybe_qualify(*ctor, qualifier), origin.clone());
            }
        }
    }
    for name in exports.type_con_arities.keys() {
        if !hidden.contains(name) {
            scope.types.insert(maybe_qualify(*name, qualifier), origin.clone());
        }
    }
}

fn build_scope_conflicts(module: &Module, registry: &ModuleRegistry, scope: &mut NameScope) {
    let mut import_origins: HashMap<Symbol, (Symbol, bool)> = HashMap::new();

    for import_decl in &module.imports {
        let prim_sub;
        let module_exports = if is_prim_module(&import_decl.module) {
            super::check::prim_exports()
        } else if is_prim_submodule(&import_decl.module) {
            prim_sub = super::check::prim_submodule_exports(&import_decl.module);
            &prim_sub
        } else {
            match registry.lookup(&import_decl.module.parts) {
                Some(exports) => exports,
                None => continue,
            }
        };

        let qualifier = import_decl.qualified.as_ref().map(module_name_to_symbol);
        let mod_sym = module_name_to_symbol(&import_decl.module);
        let is_explicit = matches!(&import_decl.imports, Some(ImportList::Explicit(_)));

        let imported_names: Vec<Symbol> = match (&import_decl.imports, qualifier) {
            (None, Some(q)) => module_exports
                .values
                .keys()
                .map(|n| maybe_qualify(*n, Some(q)))
                .collect(),
            (None, None) => module_exports.values.keys().copied().collect(),
            (Some(ImportList::Explicit(items)), _) => items
                .iter()
                .map(|i| maybe_qualify(import_name(i), qualifier))
                .collect(),
            (Some(ImportList::Hiding(items)), _) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                module_exports
                    .values
                    .keys()
                    .copied()
                    .filter(|n| !hidden.contains(n))
                    .map(|n| maybe_qualify(n, qualifier))
                    .collect()
            }
        };

        for name in &imported_names {
            let unqual = if qualifier.is_some() {
                let name_str = interner::resolve(*name).unwrap_or_default();
                if let Some(pos) = name_str.find('.') {
                    interner::intern(&name_str[pos + 1..])
                } else {
                    *name
                }
            } else {
                *name
            };
            let found_origin = module_exports.value_origins.get(&unqual).copied();
            let origin = found_origin.unwrap_or(mod_sym);
            if let Some(&(existing_origin, existing_explicit)) = import_origins.get(name) {
                if existing_origin != origin {
                    if (is_explicit && existing_explicit) || (!is_explicit && !existing_explicit) {
                        scope.scope_conflicts.insert(*name);
                    }
                }
            } else {
                import_origins.insert(*name, (origin, is_explicit));
            }
        }
    }
}

fn build_module_scope(module: &Module, registry: &ModuleRegistry) -> NameScope {
    let mut scope = NameScope::new();

    // Import Prim (unless module has explicit Prim import)
    let has_explicit_prim = module.imports.iter().any(|imp| {
        is_prim_module(&imp.module) && imp.imports.is_some() && imp.qualified.is_none()
    });
    if !has_explicit_prim {
        let prim = super::check::prim_exports();
        import_all_to_scope(prim, &mut scope, None, NameOrigin::Prim);
    }

    // Process imports
    for import_decl in &module.imports {
        let prim_sub;
        let module_exports = if is_prim_module(&import_decl.module) {
            super::check::prim_exports()
        } else if is_prim_submodule(&import_decl.module) {
            prim_sub = super::check::prim_submodule_exports(&import_decl.module);
            &prim_sub
        } else {
            match registry.lookup(&import_decl.module.parts) {
                Some(exports) => exports,
                None => continue,
            }
        };

        let qualifier = import_decl.qualified.as_ref().map(module_name_to_symbol);
        let mod_sym = module_name_to_symbol(&import_decl.module);
        let origin = if is_prim_module(&import_decl.module) || is_prim_submodule(&import_decl.module) {
            NameOrigin::Prim
        } else {
            NameOrigin::Imported(mod_sym)
        };

        match &import_decl.imports {
            None => {
                import_all_to_scope(module_exports, &mut scope, qualifier, origin);
            }
            Some(ImportList::Explicit(items)) => {
                for item in items {
                    import_item_to_scope(item, module_exports, &mut scope, qualifier, origin.clone());
                }
            }
            Some(ImportList::Hiding(items)) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                import_all_except_to_scope(module_exports, &hidden, &mut scope, qualifier, origin);
            }
        }
    }

    // Register local declarations
    for decl in &module.decls {
        match decl {
            Decl::Value { name, span, .. } => {
                scope.values.insert(name.value, NameOrigin::Local(*span));
            }
            Decl::Data {
                name,
                span,
                constructors,
                kind_sig,
                is_role_decl,
                ..
            } => {
                scope.types.insert(name.value, NameOrigin::Local(*span));
                if *kind_sig == crate::cst::KindSigSource::None && !*is_role_decl {
                    for ctor in constructors {
                        scope.values.insert(ctor.name.value, NameOrigin::Local(ctor.span));
                    }
                }
            }
            Decl::Newtype {
                name,
                span,
                constructor,
                ..
            } => {
                scope.types.insert(name.value, NameOrigin::Local(*span));
                scope.values.insert(constructor.value, NameOrigin::Local(*span));
            }
            Decl::TypeAlias { name, span, .. } => {
                scope.types.insert(name.value, NameOrigin::Local(*span));
            }
            Decl::ForeignData { name, span, .. } => {
                scope.types.insert(name.value, NameOrigin::Local(*span));
            }
            Decl::Foreign { name, span, .. } => {
                scope.values.insert(name.value, NameOrigin::Local(*span));
            }
            Decl::Class {
                name,
                span,
                members,
                ..
            } => {
                scope.classes.insert(name.value, NameOrigin::Local(*span));
                for member in members {
                    scope.values.insert(member.name.value, NameOrigin::Local(member.span));
                }
            }
            Decl::Fixity {
                is_type,
                operator,
                span,
                ..
            } => {
                if *is_type {
                    scope.type_operators.insert(operator.value, NameOrigin::Local(*span));
                } else {
                    scope.values.insert(operator.value, NameOrigin::Local(*span));
                }
            }
            Decl::Instance { .. } | Decl::Derive { .. } | Decl::TypeSignature { .. } => {}
        }
    }

    build_scope_conflicts(module, registry, &mut scope);
    scope
}

// ===== Resolution methods =====

impl<'a> Resolver<'a> {
    fn new(scope: &'a NameScope) -> Self {
        Resolver {
            scope,
            resolutions: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Resolve a value name (variable, constructor, operator).
    fn resolve_value(
        &mut self,
        name: &QualifiedIdent,
        locals: &LocalScope,
        span: Span,
    ) {
        let resolved = match name.module {
            Some(module) => qualified_symbol(module, name.name),
            None => name.name,
        };

        if self.scope.scope_conflicts.contains(&resolved) {
            self.errors.push(TypeError::ScopeConflict { span, name: resolved });
            return;
        }

        // Check locals first (unqualified only)
        if name.module.is_none() {
            if let Some(&local_span) = locals.get(&name.name) {
                self.resolutions.push(ResolvedName {
                    src_span: span,
                    src_symbol: name.name,
                    namespace: Namespace::Value,
                    definition: DefinitionSite::LocalVar(local_span),
                });
                return;
            }
        }

        // Check module scope
        if let Some(origin) = self.scope.values.get(&resolved) {
            self.resolutions.push(ResolvedName {
                src_span: span,
                src_symbol: resolved,
                namespace: Namespace::Value,
                definition: origin.to_definition_site(),
            });
        } else {
            self.errors.push(TypeError::UndefinedVariable { span, name: resolved });
        }
    }

    /// Resolve a type name.
    fn resolve_type(&mut self, name: &QualifiedIdent, span: Span) {
        let resolved = match name.module {
            Some(module) => qualified_symbol(module, name.name),
            None => name.name,
        };

        if let Some(origin) = self.scope.types.get(&resolved) {
            self.resolutions.push(ResolvedName {
                src_span: span,
                src_symbol: resolved,
                namespace: Namespace::Type,
                definition: origin.to_definition_site(),
            });
        } else {
            self.errors.push(TypeError::UnknownType { span, name: resolved });
        }
    }

    /// Resolve a class name.
    fn resolve_class(&mut self, name: &QualifiedIdent, span: Span) {
        let class_sym = name.name;
        if let Some(origin) = self.scope.classes.get(&class_sym) {
            self.resolutions.push(ResolvedName {
                src_span: span,
                src_symbol: class_sym,
                namespace: Namespace::Class,
                definition: origin.to_definition_site(),
            });
        } else {
            self.errors.push(TypeError::UnknownClass { span, name: class_sym });
        }
    }

    /// Resolve a type operator.
    fn resolve_type_op(&mut self, name: &QualifiedIdent, span: Span) {
        if let Some(origin) = self.scope.type_operators.get(&name.name) {
            self.resolutions.push(ResolvedName {
                src_span: span,
                src_symbol: name.name,
                namespace: Namespace::TypeOperator,
                definition: origin.to_definition_site(),
            });
        } else {
            self.errors.push(TypeError::UnknownType { span, name: name.name });
        }
    }
}

// ===== CST walking =====

fn walk_expr(
    r: &mut Resolver,
    expr: &Expr,
    locals: &LocalScope,
    type_vars: &HashSet<Symbol>,
) {
    match expr {
        Expr::Var { span, name } => {
            r.resolve_value(name, locals, *span);
        }
        Expr::Constructor { span, name } => {
            r.resolve_value(name, locals, *span);
        }
        Expr::Literal { lit, .. } => {
            walk_literal(r, lit, locals, type_vars);
        }
        Expr::App { func, arg, .. } => {
            walk_expr(r, func, locals, type_vars);
            walk_expr(r, arg, locals, type_vars);
        }
        Expr::VisibleTypeApp { func, ty, .. } => {
            walk_expr(r, func, locals, type_vars);
            walk_type_expr(r, ty, type_vars);
        }
        Expr::Lambda { binders, body, .. } => {
            let mut inner = locals.clone();
            for binder in binders {
                collect_binder_names(binder, &mut inner);
                walk_binder(r, binder, locals, type_vars);
            }
            walk_expr(r, body, &inner, type_vars);
        }
        Expr::Op { left, op, right, .. } => {
            walk_expr(r, left, locals, type_vars);
            r.resolve_value(&op.value, locals, op.span);
            walk_expr(r, right, locals, type_vars);
        }
        Expr::OpParens { op, .. } => {
            r.resolve_value(&op.value, locals, op.span);
        }
        Expr::If { cond, then_expr, else_expr, .. } => {
            walk_expr(r, cond, locals, type_vars);
            walk_expr(r, then_expr, locals, type_vars);
            walk_expr(r, else_expr, locals, type_vars);
        }
        Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                walk_expr(r, e, locals, type_vars);
            }
            for alt in alts {
                walk_case_alt(r, alt, locals, type_vars);
            }
        }
        Expr::Let { bindings, body, .. } => {
            let mut inner = locals.clone();
            for binding in bindings {
                collect_let_binding_names(binding, &mut inner);
            }
            for binding in bindings {
                walk_let_binding(r, binding, &inner, type_vars);
            }
            walk_expr(r, body, &inner, type_vars);
        }
        Expr::Do { statements, .. } => {
            walk_do_statements(r, statements, locals, type_vars);
        }
        Expr::Ado { statements, result, .. } => {
            let mut inner = locals.clone();
            for stmt in statements {
                collect_do_statement_names(stmt, &mut inner);
            }
            walk_do_statements(r, statements, locals, type_vars);
            walk_expr(r, result, &inner, type_vars);
        }
        Expr::Record { fields, .. } => {
            for field in fields {
                match &field.value {
                    None => {
                        // Punned field: { x } uses x as a value
                        let qi = QualifiedIdent { module: None, name: field.label.value };
                        r.resolve_value(&qi, locals, field.label.span);
                    }
                    Some(value_expr) => {
                        walk_expr(r, value_expr, locals, type_vars);
                    }
                }
            }
        }
        Expr::RecordAccess { expr, .. } => {
            walk_expr(r, expr, locals, type_vars);
        }
        Expr::RecordUpdate { expr, updates, .. } => {
            walk_expr(r, expr, locals, type_vars);
            for update in updates {
                walk_expr(r, &update.value, locals, type_vars);
            }
        }
        Expr::Parens { expr, .. } => {
            walk_expr(r, expr, locals, type_vars);
        }
        Expr::TypeAnnotation { expr, ty, .. } => {
            walk_expr(r, expr, locals, type_vars);
            walk_type_expr(r, ty, type_vars);
        }
        Expr::Hole { .. } => {}
        Expr::Array { elements, .. } => {
            for e in elements {
                walk_expr(r, e, locals, type_vars);
            }
        }
        Expr::Negate { expr, .. } => {
            walk_expr(r, expr, locals, type_vars);
        }
        Expr::AsPattern { name, pattern, .. } => {
            walk_expr(r, name, locals, type_vars);
            walk_expr(r, pattern, locals, type_vars);
        }
    }
}

fn walk_literal(
    r: &mut Resolver,
    lit: &Literal,
    locals: &LocalScope,
    type_vars: &HashSet<Symbol>,
) {
    if let Literal::Array(exprs) = lit {
        for e in exprs {
            walk_expr(r, e, locals, type_vars);
        }
    }
}

fn walk_type_expr(
    r: &mut Resolver,
    ty: &TypeExpr,
    type_vars: &HashSet<Symbol>,
) {
    match ty {
        TypeExpr::Var { .. } => {
            // Type variables — implicitly bound in PureScript, no resolution needed
        }
        TypeExpr::Constructor { span, name } => {
            r.resolve_type(name, *span);
        }
        TypeExpr::App { constructor, arg, .. } => {
            walk_type_expr(r, constructor, type_vars);
            walk_type_expr(r, arg, type_vars);
        }
        TypeExpr::Function { from, to, .. } => {
            walk_type_expr(r, from, type_vars);
            walk_type_expr(r, to, type_vars);
        }
        TypeExpr::Forall { vars, ty, .. } => {
            let mut inner_tvs = type_vars.clone();
            for (var, _, kind) in vars {
                inner_tvs.insert(var.value);
                if let Some(kind_expr) = kind {
                    walk_type_expr(r, kind_expr, &inner_tvs);
                }
            }
            walk_type_expr(r, ty, &inner_tvs);
        }
        TypeExpr::Constrained { constraints, ty, .. } => {
            for constraint in constraints {
                r.resolve_class(&constraint.class, constraint.span);
                for arg in &constraint.args {
                    walk_type_expr(r, arg, type_vars);
                }
            }
            walk_type_expr(r, ty, type_vars);
        }
        TypeExpr::Record { fields, .. } => {
            for field in fields {
                walk_type_expr(r, &field.ty, type_vars);
            }
        }
        TypeExpr::Row { fields, tail, .. } => {
            for field in fields {
                walk_type_expr(r, &field.ty, type_vars);
            }
            if let Some(tail) = tail {
                walk_type_expr(r, tail, type_vars);
            }
        }
        TypeExpr::Parens { ty, .. } => {
            walk_type_expr(r, ty, type_vars);
        }
        TypeExpr::Hole { .. } | TypeExpr::Wildcard { .. } => {}
        TypeExpr::TypeOp { left, op, right, .. } => {
            walk_type_expr(r, left, type_vars);
            r.resolve_type_op(&op.value, op.span);
            walk_type_expr(r, right, type_vars);
        }
        TypeExpr::Kinded { ty, kind, .. } => {
            walk_type_expr(r, ty, type_vars);
            walk_type_expr(r, kind, type_vars);
        }
        TypeExpr::StringLiteral { .. } | TypeExpr::IntLiteral { .. } => {}
    }
}

// ===== Binder helpers =====

/// Collect names introduced by a binder into the local scope.
fn collect_binder_names(binder: &Binder, locals: &mut LocalScope) {
    match binder {
        Binder::Var { name, .. } => {
            locals.insert(name.value, name.span);
        }
        Binder::Constructor { args, .. } => {
            for arg in args {
                collect_binder_names(arg, locals);
            }
        }
        Binder::As { name, binder, .. } => {
            locals.insert(name.value, name.span);
            collect_binder_names(binder, locals);
        }
        Binder::Parens { binder, .. } => {
            collect_binder_names(binder, locals);
        }
        Binder::Array { elements, .. } => {
            for e in elements {
                collect_binder_names(e, locals);
            }
        }
        Binder::Record { fields, .. } => {
            for field in fields {
                match &field.binder {
                    None => {
                        locals.insert(field.label.value, field.label.span);
                    }
                    Some(binder) => {
                        collect_binder_names(binder, locals);
                    }
                }
            }
        }
        Binder::Op { left, right, .. } => {
            collect_binder_names(left, locals);
            collect_binder_names(right, locals);
        }
        Binder::Typed { binder, .. } => {
            collect_binder_names(binder, locals);
        }
        Binder::Wildcard { .. } | Binder::Literal { .. } => {}
    }
}

fn walk_binder(
    r: &mut Resolver,
    binder: &Binder,
    locals: &LocalScope,
    type_vars: &HashSet<Symbol>,
) {
    match binder {
        Binder::Constructor { span, name, args } => {
            r.resolve_value(name, locals, *span);
            for arg in args {
                walk_binder(r, arg, locals, type_vars);
            }
        }
        Binder::Op { left, op, right, .. } => {
            walk_binder(r, left, locals, type_vars);
            r.resolve_value(&op.value, locals, op.span);
            walk_binder(r, right, locals, type_vars);
        }
        Binder::Typed { binder, ty, .. } => {
            walk_binder(r, binder, locals, type_vars);
            walk_type_expr(r, ty, type_vars);
        }
        Binder::As { binder, .. } | Binder::Parens { binder, .. } => {
            walk_binder(r, binder, locals, type_vars);
        }
        Binder::Array { elements, .. } => {
            for e in elements {
                walk_binder(r, e, locals, type_vars);
            }
        }
        Binder::Record { fields, .. } => {
            for field in fields {
                if let Some(binder) = &field.binder {
                    walk_binder(r, binder, locals, type_vars);
                }
            }
        }
        Binder::Literal { lit, .. } => {
            if let Literal::Array(exprs) = lit {
                for e in exprs {
                    walk_expr(r, e, locals, type_vars);
                }
            }
        }
        Binder::Var { .. } | Binder::Wildcard { .. } => {}
    }
}

// ===== Case / guard =====

fn walk_case_alt(
    r: &mut Resolver,
    alt: &CaseAlternative,
    locals: &LocalScope,
    type_vars: &HashSet<Symbol>,
) {
    let mut inner = locals.clone();
    for binder in &alt.binders {
        collect_binder_names(binder, &mut inner);
        walk_binder(r, binder, locals, type_vars);
    }
    walk_guarded(r, &alt.result, &inner, type_vars);
}

fn walk_guarded(
    r: &mut Resolver,
    guarded: &GuardedExpr,
    locals: &LocalScope,
    type_vars: &HashSet<Symbol>,
) {
    match guarded {
        GuardedExpr::Unconditional(expr) => {
            walk_expr(r, expr, locals, type_vars);
        }
        GuardedExpr::Guarded(guards) => {
            for guard in guards {
                let mut guard_locals = locals.clone();
                for pattern in &guard.patterns {
                    match pattern {
                        GuardPattern::Boolean(e) => {
                            walk_expr(r, e, &guard_locals, type_vars);
                        }
                        GuardPattern::Pattern(binder, e) => {
                            walk_expr(r, e, &guard_locals, type_vars);
                            collect_binder_names(binder, &mut guard_locals);
                            walk_binder(r, binder, locals, type_vars);
                        }
                    }
                }
                walk_expr(r, &guard.expr, &guard_locals, type_vars);
            }
        }
    }
}

// ===== Let / do =====

fn collect_let_binding_names(binding: &LetBinding, locals: &mut LocalScope) {
    if let LetBinding::Value { binder, .. } = binding {
        collect_binder_names(binder, locals);
    }
}

fn walk_let_binding(
    r: &mut Resolver,
    binding: &LetBinding,
    locals: &LocalScope,
    type_vars: &HashSet<Symbol>,
) {
    match binding {
        LetBinding::Value { binder, expr, .. } => {
            walk_binder(r, binder, locals, type_vars);
            walk_expr(r, expr, locals, type_vars);
        }
        LetBinding::Signature { ty, .. } => {
            walk_type_expr(r, ty, type_vars);
        }
    }
}

fn collect_do_statement_names(stmt: &DoStatement, locals: &mut LocalScope) {
    match stmt {
        DoStatement::Bind { binder, .. } => {
            collect_binder_names(binder, locals);
        }
        DoStatement::Let { bindings, .. } => {
            for binding in bindings {
                collect_let_binding_names(binding, locals);
            }
        }
        DoStatement::Discard { .. } => {}
    }
}

fn walk_do_statements(
    r: &mut Resolver,
    statements: &[DoStatement],
    locals: &LocalScope,
    type_vars: &HashSet<Symbol>,
) {
    let mut current = locals.clone();
    for stmt in statements {
        match stmt {
            DoStatement::Bind { binder, expr, .. } => {
                walk_expr(r, expr, &current, type_vars);
                walk_binder(r, binder, &current, type_vars);
                collect_binder_names(binder, &mut current);
            }
            DoStatement::Let { bindings, .. } => {
                for binding in bindings {
                    collect_let_binding_names(binding, &mut current);
                }
                for binding in bindings {
                    walk_let_binding(r, binding, &current, type_vars);
                }
            }
            DoStatement::Discard { expr, .. } => {
                walk_expr(r, expr, &current, type_vars);
            }
        }
    }
}

// ===== Declaration walking =====

fn walk_decl(r: &mut Resolver, decl: &Decl) {
    let type_vars = HashSet::new();
    let locals = LocalScope::new();

    match decl {
        Decl::Value {
            binders,
            guarded,
            where_clause,
            ..
        } => {
            let mut body_locals = locals.clone();
            for binder in binders {
                collect_binder_names(binder, &mut body_locals);
                walk_binder(r, binder, &locals, &type_vars);
            }
            for binding in where_clause {
                collect_let_binding_names(binding, &mut body_locals);
            }
            for binding in where_clause {
                walk_let_binding(r, binding, &body_locals, &type_vars);
            }
            walk_guarded(r, guarded, &body_locals, &type_vars);
        }
        Decl::TypeSignature { ty, .. } => {
            walk_type_expr(r, ty, &type_vars);
        }
        Decl::Data {
            constructors,
            type_vars: tvs,
            kind_type,
            type_var_kind_anns,
            ..
        } => {
            let bound_tvs: HashSet<Symbol> = tvs.iter().map(|tv| tv.value).collect();
            for ann in type_var_kind_anns {
                if let Some(kind_expr) = ann {
                    walk_type_expr(r, kind_expr, &bound_tvs);
                }
            }
            if let Some(kind_ty) = kind_type {
                walk_type_expr(r, kind_ty, &bound_tvs);
            }
            for ctor in constructors {
                for field in &ctor.fields {
                    walk_type_expr(r, field, &bound_tvs);
                }
            }
        }
        Decl::Newtype {
            type_vars: tvs,
            ty,
            type_var_kind_anns,
            ..
        } => {
            let bound_tvs: HashSet<Symbol> = tvs.iter().map(|tv| tv.value).collect();
            for ann in type_var_kind_anns {
                if let Some(kind_expr) = ann {
                    walk_type_expr(r, kind_expr, &bound_tvs);
                }
            }
            walk_type_expr(r, ty, &bound_tvs);
        }
        Decl::TypeAlias {
            type_vars: tvs,
            ty,
            type_var_kind_anns,
            ..
        } => {
            let bound_tvs: HashSet<Symbol> = tvs.iter().map(|tv| tv.value).collect();
            for ann in type_var_kind_anns {
                if let Some(kind_expr) = ann {
                    walk_type_expr(r, kind_expr, &bound_tvs);
                }
            }
            walk_type_expr(r, ty, &bound_tvs);
        }
        Decl::Class {
            constraints,
            type_vars: tvs,
            members,
            type_var_kind_anns,
            ..
        } => {
            let bound_tvs: HashSet<Symbol> = tvs.iter().map(|tv| tv.value).collect();
            for ann in type_var_kind_anns {
                if let Some(kind_expr) = ann {
                    walk_type_expr(r, kind_expr, &bound_tvs);
                }
            }
            for constraint in constraints {
                r.resolve_class(&constraint.class, constraint.span);
                for arg in &constraint.args {
                    walk_type_expr(r, arg, &bound_tvs);
                }
            }
            for member in members {
                walk_type_expr(r, &member.ty, &bound_tvs);
            }
        }
        Decl::Instance {
            constraints,
            class_name,
            types,
            members,
            span,
            ..
        } => {
            r.resolve_class(class_name, *span);
            for constraint in constraints {
                r.resolve_class(&constraint.class, constraint.span);
                for arg in &constraint.args {
                    walk_type_expr(r, arg, &type_vars);
                }
            }
            for ty in types {
                walk_type_expr(r, ty, &type_vars);
            }
            for member in members {
                walk_decl(r, member);
            }
        }
        Decl::Derive {
            constraints,
            class_name,
            types,
            span,
            ..
        } => {
            r.resolve_class(class_name, *span);
            for constraint in constraints {
                r.resolve_class(&constraint.class, constraint.span);
                for arg in &constraint.args {
                    walk_type_expr(r, arg, &type_vars);
                }
            }
            for ty in types {
                walk_type_expr(r, ty, &type_vars);
            }
        }
        Decl::Fixity { target, span, .. } => {
            let resolved = match target.module {
                Some(module) => qualified_symbol(module, target.name),
                None => target.name,
            };
            if !r.scope.values.contains_key(&resolved) && !r.scope.types.contains_key(&resolved) {
                r.errors.push(TypeError::UndefinedVariable { span: *span, name: resolved });
            }
        }
        Decl::Foreign { ty, .. } => {
            walk_type_expr(r, ty, &type_vars);
        }
        Decl::ForeignData { kind, .. } => {
            walk_type_expr(r, kind, &type_vars);
        }
    }
}

// ===== Public API =====

/// Resolve all names in a module.
///
/// Returns a `ResolvedResult` containing:
/// - All name resolutions (usage span → definition site), sorted by span start
/// - Any name resolution errors
pub fn resolve_names(module: &Module, registry: &ModuleRegistry) -> ResolvedResult {
    let scope = build_module_scope(module, registry);
    let mut resolver = Resolver::new(&scope);

    for decl in &module.decls {
        walk_decl(&mut resolver, decl);
    }

    // Sort resolutions by span start for binary search
    resolver.resolutions.sort_by_key(|r| r.src_span.start);

    let resolution_map: HashMap<Span, usize> = resolver
        .resolutions
        .iter()
        .enumerate()
        .map(|(i, r)| (r.src_span, i))
        .collect();

    ResolvedResult {
        errors: resolver.errors,
        resolutions: resolver.resolutions,
        resolution_map,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner;
    use crate::parser;
    use crate::typechecker::check::{ModuleExports, ModuleRegistry};
    use crate::typechecker::types::{Scheme, Type};

    /// Parse a module and resolve names with an empty registry.
    fn resolve(source: &str) -> ResolvedResult {
        let module = parser::parse(source).expect("parsing failed");
        let registry = ModuleRegistry::new();
        resolve_names(&module, &registry)
    }

    /// Parse a module and resolve names with a pre-populated registry.
    fn resolve_with_registry(source: &str, registry: &ModuleRegistry) -> ResolvedResult {
        let module = parser::parse(source).expect("parsing failed");
        resolve_names(&module, registry)
    }

    /// Build a simple ModuleExports with the given value names (monomorphic Int).
    fn make_exports_with_values(names: &[&str]) -> ModuleExports {
        let mut exports = ModuleExports::default();
        for name in names {
            let sym = interner::intern(name);
            exports.values.insert(sym, Scheme::mono(Type::int()));
        }
        exports
    }

    /// Build a ModuleExports with given type constructor names (arity 0).
    fn make_exports_with_types(names: &[&str]) -> ModuleExports {
        let mut exports = ModuleExports::default();
        for name in names {
            let sym = interner::intern(name);
            exports.type_con_arities.insert(sym, 0);
        }
        exports
    }

    /// Build a ModuleExports with given data constructors.
    fn make_exports_with_data(type_name: &str, ctor_names: &[&str]) -> ModuleExports {
        let mut exports = ModuleExports::default();
        let type_sym = interner::intern(type_name);
        let ctors: Vec<Symbol> = ctor_names.iter().map(|n| interner::intern(n)).collect();
        exports.data_constructors.insert(type_sym, ctors.clone());
        exports.type_con_arities.insert(type_sym, 0);
        for ctor in &ctors {
            exports.values.insert(*ctor, Scheme::mono(Type::Con(type_sym)));
        }
        exports
    }

    /// Build a ModuleExports with a class and its methods.
    fn make_exports_with_class(class_name: &str, methods: &[&str]) -> ModuleExports {
        let mut exports = ModuleExports::default();
        let class_sym = interner::intern(class_name);
        exports.class_param_counts.insert(class_sym, 1);
        for method in methods {
            let method_sym = interner::intern(method);
            exports.class_methods.insert(method_sym, (class_sym, vec![]));
            exports.values.insert(method_sym, Scheme::mono(Type::int()));
        }
        exports
    }

    /// Build a ModuleExports with a value fixity operator.
    fn make_exports_with_value_op(op: &str, target: &str) -> ModuleExports {
        let mut exports = ModuleExports::default();
        let op_sym = interner::intern(op);
        let target_sym = interner::intern(target);
        exports.value_fixities.insert(op_sym, (crate::cst::Associativity::Left, 5));
        exports.values.insert(target_sym, Scheme::mono(Type::int()));
        exports
    }

    /// Build a ModuleExports with a type operator.
    fn make_exports_with_type_op(op: &str, target: &str) -> ModuleExports {
        let mut exports = ModuleExports::default();
        let op_sym = interner::intern(op);
        let target_sym = interner::intern(target);
        exports.type_operators.insert(op_sym, target_sym);
        exports
    }

    /// Register a module in the registry by module name parts.
    fn register_module(registry: &mut ModuleRegistry, module_parts: &[&str], exports: ModuleExports) {
        let parts: Vec<Symbol> = module_parts.iter().map(|p| interner::intern(p)).collect();
        registry.register(&parts, exports);
    }

    /// Find resolutions matching a given symbol name.
    fn find_resolutions<'a>(result: &'a ResolvedResult, name: &str) -> Vec<&'a ResolvedName> {
        let sym = interner::intern(name);
        result.resolutions.iter().filter(|r| r.src_symbol == sym).collect()
    }

    /// Check if any error is an UndefinedVariable for the given name.
    fn has_undefined_variable(result: &ResolvedResult, name: &str) -> bool {
        let sym = interner::intern(name);
        result.errors.iter().any(|e| matches!(e, TypeError::UndefinedVariable { name: n, .. } if *n == sym))
    }

    /// Check if any error is an UnknownType for the given name.
    fn has_unknown_type(result: &ResolvedResult, name: &str) -> bool {
        let sym = interner::intern(name);
        result.errors.iter().any(|e| matches!(e, TypeError::UnknownType { name: n, .. } if *n == sym))
    }

    /// Check if any error is an UnknownClass for the given name.
    fn has_unknown_class(result: &ResolvedResult, name: &str) -> bool {
        let sym = interner::intern(name);
        result.errors.iter().any(|e| matches!(e, TypeError::UnknownClass { name: n, .. } if *n == sym))
    }

    /// Check if any error is a ScopeConflict for the given name.
    fn has_scope_conflict(result: &ResolvedResult, name: &str) -> bool {
        let sym = interner::intern(name);
        result.errors.iter().any(|e| matches!(e, TypeError::ScopeConflict { name: n, .. } if *n == sym))
    }

    // ===== Error cases =====

    #[test]
    fn test_error_undefined_variable() {
        let result = resolve("module T where\nx = unknownVar");
        assert!(has_undefined_variable(&result, "unknownVar"),
            "expected UndefinedVariable for unknownVar, got errors: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_error_unknown_type_in_signature() {
        let result = resolve("module T where\nx :: UnknownType\nx = 42");
        assert!(has_unknown_type(&result, "UnknownType"),
            "expected UnknownType for UnknownType, got errors: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_error_unknown_class_in_constraint() {
        let result = resolve("module T where\nx :: UnknownClass a => a -> a\nx y = y");
        assert!(has_unknown_class(&result, "UnknownClass"),
            "expected UnknownClass, got errors: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_error_unknown_constructor_in_case() {
        let result = resolve("module T where\nf x = case x of\n  UnknownCtor -> 1");
        assert!(has_undefined_variable(&result, "UnknownCtor"),
            "expected UndefinedVariable for UnknownCtor, got errors: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_error_undefined_in_lambda() {
        let result = resolve("module T where\nf = \\x -> unknownFn x");
        assert!(has_undefined_variable(&result, "unknownFn"));
    }

    #[test]
    fn test_error_undefined_in_let() {
        let result = resolve("module T where\nx = let\n  y = unknownFn\nin y");
        assert!(has_undefined_variable(&result, "unknownFn"));
    }

    // ===== No-error cases =====

    #[test]
    fn test_no_errors_simple_value() {
        let result = resolve("module T where\nx = 42");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_data_and_constructor_use() {
        let result = resolve("module T where\ndata MyBool = MyTrue | MyFalse\nx = MyTrue");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_prim_types() {
        let result = resolve("module T where\nx :: Int\nx = 42\ny :: String\ny = \"hello\"");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_function_with_binders() {
        let result = resolve("module T where\nf x y = x");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_let_and_where() {
        let result = resolve("module T where\nf = let\n  x = 1\nin x");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_case_with_data() {
        let result = resolve("module T where\ndata AB = A | B\nf x = case x of\n  A -> 1\n  B -> 2");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_type_alias() {
        let result = resolve("module T where\ntype MyInt = Int\nx :: MyInt\nx = 42");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_class_and_instance() {
        let result = resolve("module T where\nclass MyClass a where\n  myMethod :: a -> a\ndata Foo = Foo\ninstance MyClass Foo where\n  myMethod x = x");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_newtype() {
        let result = resolve("module T where\nnewtype Wrapper = Wrapper Int\nx = Wrapper 42");
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_no_errors_lambda() {
        let result = resolve("module T where\nf = \\x -> x");
        assert!(result.errors.is_empty());
    }

    // ===== Top-level declaration references =====

    #[test]
    fn test_top_level_value_reference() {
        let result = resolve("module T where\nf x = x\ng = f 42");
        assert!(result.errors.is_empty());
        let f_refs = find_resolutions(&result, "f");
        assert!(!f_refs.is_empty(), "expected resolution for 'f'");
        // The reference to f in g should resolve to a local definition
        let f_ref = f_refs.iter().find(|r| r.namespace == Namespace::Value).unwrap();
        assert!(matches!(f_ref.definition, DefinitionSite::Local(_)),
            "expected local definition for f, got {:?}", f_ref.definition);
    }

    #[test]
    fn test_top_level_constructor_reference() {
        let result = resolve("module T where\ndata Color = Red | Green | Blue\nx = Red");
        assert!(result.errors.is_empty());
        let red_refs = find_resolutions(&result, "Red");
        assert!(!red_refs.is_empty(), "expected resolution for 'Red'");
        let red_ref = red_refs.iter().find(|r| r.namespace == Namespace::Value).unwrap();
        assert!(matches!(red_ref.definition, DefinitionSite::Local(_)));
    }

    #[test]
    fn test_top_level_type_reference_in_sig() {
        let result = resolve("module T where\ndata Foo = Foo\nx :: Foo\nx = Foo");
        assert!(result.errors.is_empty());
        let foo_type_refs: Vec<_> = find_resolutions(&result, "Foo")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Type)
            .collect();
        assert!(!foo_type_refs.is_empty(), "expected type resolution for 'Foo'");
        assert!(matches!(foo_type_refs[0].definition, DefinitionSite::Local(_)));
    }

    #[test]
    fn test_top_level_class_reference() {
        let result = resolve("module T where\nclass MyShow a where\n  myShow :: a -> Int\ndata Bar = Bar\ninstance MyShow Bar where\n  myShow _ = 1");
        assert!(result.errors.is_empty());
        let class_refs: Vec<_> = find_resolutions(&result, "MyShow")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Class)
            .collect();
        // Class is referenced in the instance declaration
        assert!(!class_refs.is_empty(), "expected class resolution for 'MyShow'");
        assert!(matches!(class_refs[0].definition, DefinitionSite::Local(_)));
    }

    #[test]
    fn test_top_level_mutual_reference() {
        let result = resolve("module T where\nf x = g x\ng x = f x");
        assert!(result.errors.is_empty());
        // f references g
        let g_refs = find_resolutions(&result, "g");
        assert!(!g_refs.is_empty(), "expected resolution for 'g'");
        assert!(matches!(g_refs[0].definition, DefinitionSite::Local(_)));
        // g references f
        let f_refs = find_resolutions(&result, "f");
        assert!(!f_refs.is_empty(), "expected resolution for 'f'");
    }

    // ===== Local declaration references =====

    #[test]
    fn test_local_let_binding_reference() {
        let result = resolve("module T where\nf = let\n  x = 1\nin x");
        assert!(result.errors.is_empty());
        let x_refs = find_resolutions(&result, "x");
        // The reference to x in the let body should resolve to LocalVar
        let body_ref = x_refs.iter().find(|r| matches!(r.definition, DefinitionSite::LocalVar(_)));
        assert!(body_ref.is_some(), "expected LocalVar reference for let-bound 'x'");
    }

    #[test]
    fn test_local_lambda_param_reference() {
        let result = resolve("module T where\nf = \\x -> x");
        assert!(result.errors.is_empty());
        let x_refs = find_resolutions(&result, "x");
        let param_ref = x_refs.iter().find(|r| matches!(r.definition, DefinitionSite::LocalVar(_)));
        assert!(param_ref.is_some(), "expected LocalVar reference for lambda param 'x'");
    }

    #[test]
    fn test_local_case_binder_reference() {
        let result = resolve("module T where\ndata Maybe a = Just a | Nothing\nf mx = case mx of\n  Just x -> x\n  Nothing -> 0");
        assert!(result.errors.is_empty());
        let x_refs = find_resolutions(&result, "x");
        let binder_ref = x_refs.iter().find(|r| matches!(r.definition, DefinitionSite::LocalVar(_)));
        assert!(binder_ref.is_some(), "expected LocalVar reference for case-bound 'x'");
    }

    #[test]
    fn test_local_function_binder_reference() {
        let result = resolve("module T where\nf x = x");
        assert!(result.errors.is_empty());
        let x_refs = find_resolutions(&result, "x");
        let binder_ref = x_refs.iter().find(|r| matches!(r.definition, DefinitionSite::LocalVar(_)));
        assert!(binder_ref.is_some(), "expected LocalVar reference for function binder 'x'");
    }

    #[test]
    fn test_local_shadows_top_level() {
        // Lambda param 'x' should shadow the top-level 'x'
        let result = resolve("module T where\nx = 1\nf = \\x -> x");
        assert!(result.errors.is_empty());
        // The 'x' in the lambda body should resolve to LocalVar, not Local
        let x_refs = find_resolutions(&result, "x");
        let local_var_ref = x_refs.iter().find(|r| matches!(r.definition, DefinitionSite::LocalVar(_)));
        assert!(local_var_ref.is_some(), "expected lambda param to shadow top-level 'x'");
    }

    // ===== Imported value declaration references =====

    #[test]
    fn test_imported_value_reference() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_values(&["bar"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo (bar)\nx = bar",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let bar_refs = find_resolutions(&result, "bar");
        assert!(!bar_refs.is_empty(), "expected resolution for imported 'bar'");
        assert!(matches!(bar_refs[0].definition, DefinitionSite::Imported(_)));
    }

    #[test]
    fn test_imported_open_import() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_values(&["bar", "baz"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo\nx = bar\ny = baz",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_imported_hiding() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_values(&["bar", "baz"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo hiding (baz)\nx = bar",
            &registry,
        );
        assert!(result.errors.is_empty());

        // baz should be hidden
        let result2 = resolve_with_registry(
            "module T where\nimport Data.Foo hiding (baz)\nx = baz",
            &registry,
        );
        assert!(has_undefined_variable(&result2, "baz"));
    }

    #[test]
    fn test_imported_constructor_reference() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Maybe"], make_exports_with_data("Maybe", &["Just", "Nothing"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Maybe (Maybe(..))\nx = Just 42",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let just_refs = find_resolutions(&result, "Just");
        assert!(!just_refs.is_empty(), "expected resolution for imported 'Just'");
        assert!(matches!(just_refs[0].definition, DefinitionSite::Imported(_)));
    }

    // ===== Imported value operator references =====

    #[test]
    fn test_imported_value_operator() {
        let mut registry = ModuleRegistry::new();
        let mut exports = make_exports_with_value_op("<>", "append");
        // Also add append as a value
        exports.values.insert(interner::intern("append"), Scheme::mono(Type::int()));
        register_module(&mut registry, &["Data", "Semigroup"], exports);

        let result = resolve_with_registry(
            "module T where\nimport Data.Semigroup (append)\nx = append",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors for imported operator, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    // ===== Qualified imported value references =====

    #[test]
    fn test_qualified_imported_value() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_values(&["bar"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo as Foo\nx = Foo.bar",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let qbar_refs = find_resolutions(&result, "Foo.bar");
        assert!(!qbar_refs.is_empty(), "expected resolution for qualified 'Foo.bar'");
        assert!(matches!(qbar_refs[0].definition, DefinitionSite::Imported(_)));
    }

    #[test]
    fn test_qualified_unresolved_value() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_values(&["bar"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo as Foo\nx = Foo.nonexistent",
            &registry,
        );
        assert!(has_undefined_variable(&result, "Foo.nonexistent"),
            "expected UndefinedVariable for Foo.nonexistent, got errors: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    // ===== Qualified imported type references =====

    #[test]
    fn test_qualified_imported_type() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_types(&["Bar"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo as Foo\nx :: Foo.Bar\nx = 42",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let qbar_refs: Vec<_> = find_resolutions(&result, "Foo.Bar")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Type)
            .collect();
        assert!(!qbar_refs.is_empty(), "expected type resolution for 'Foo.Bar'");
        assert!(matches!(qbar_refs[0].definition, DefinitionSite::Imported(_)));
    }

    #[test]
    fn test_qualified_unknown_type() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_types(&["Bar"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo as Foo\nx :: Foo.Nonexistent\nx = 42",
            &registry,
        );
        assert!(has_unknown_type(&result, "Foo.Nonexistent"),
            "expected UnknownType for Foo.Nonexistent, got errors: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    // ===== Qualified imported constructor references =====

    #[test]
    fn test_qualified_imported_constructor() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Maybe"], make_exports_with_data("Maybe", &["Just", "Nothing"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Maybe as M\nx = M.Just 42",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        let qjust_refs = find_resolutions(&result, "M.Just");
        assert!(!qjust_refs.is_empty(), "expected resolution for 'M.Just'");
        assert!(matches!(qjust_refs[0].definition, DefinitionSite::Imported(_)));
    }

    // ===== Qualified imported operator references =====

    #[test]
    fn test_local_type_operator_reference() {
        // Define a type operator locally and use it in a type signature
        let result = resolve(
            "module T where\ndata TypeApply f a = TypeApply (f a)\ninfixr 0 type TypeApply as $\nx :: Int $ String\nx = TypeApply 42",
        );
        // The type operator $ should resolve
        let op_refs: Vec<_> = find_resolutions(&result, "$")
            .into_iter()
            .filter(|r| r.namespace == Namespace::TypeOperator)
            .collect();
        assert!(!op_refs.is_empty(), "expected type operator resolution for '$'");
        assert!(matches!(op_refs[0].definition, DefinitionSite::Local(_)));
    }

    // ===== Local type declaration overriding imported type =====

    #[test]
    fn test_local_type_alias_overrides_imported_type() {
        let mut registry = ModuleRegistry::new();
        let mut exports = make_exports_with_types(&["Codec"]);
        // Also add Codec as a type alias to simulate the real Codec module
        let codec_sym = interner::intern("Codec");
        exports.type_aliases.insert(codec_sym, (vec![interner::intern("a")], Type::int()));
        register_module(&mut registry, &["Data", "Codec"], exports);

        let result = resolve_with_registry(
            "module T where\nimport Data.Codec (Codec)\ntype Codec a = Int\nx :: Codec Int\nx = 42",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());

        // The Codec in the type signature should resolve to Local (the local alias), not Imported
        let codec_type_refs: Vec<_> = find_resolutions(&result, "Codec")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Type)
            .collect();
        assert!(!codec_type_refs.is_empty(), "expected type resolution for 'Codec'");
        // The local type alias should override the import
        let has_local = codec_type_refs.iter().any(|r| matches!(r.definition, DefinitionSite::Local(_)));
        assert!(has_local,
            "expected local Codec alias to override imported Codec. Definitions: {:?}",
            codec_type_refs.iter().map(|r| &r.definition).collect::<Vec<_>>());
    }

    #[test]
    fn test_local_data_overrides_imported_type() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Foo"], make_exports_with_types(&["Bar"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Foo (Bar)\ndata Bar = MkBar\nx :: Bar\nx = MkBar",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());

        // Bar should resolve to Local (local data decl overrides import)
        let bar_type_refs: Vec<_> = find_resolutions(&result, "Bar")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Type)
            .collect();
        assert!(!bar_type_refs.is_empty());
        assert!(bar_type_refs.iter().all(|r| matches!(r.definition, DefinitionSite::Local(_))),
            "expected local data Bar to override imported Bar");
    }

    // ===== lookup_at (IDE support) =====

    #[test]
    fn test_lookup_at_returns_resolution() {
        let result = resolve("module T where\nx = 42");
        // There may or may not be resolutions for literals, but at least verify no panic
        // and that lookup_at works for valid offsets
        let _ = result.lookup_at(0);
        let _ = result.lookup_at(100);
    }

    #[test]
    fn test_lookup_at_finds_correct_resolution() {
        let result = resolve("module T where\ndata Foo = Foo\nx = Foo");
        // Find the span of a resolution and verify lookup_at returns it
        if let Some(r) = result.resolutions.first() {
            let found = result.lookup_at(r.src_span.start);
            assert!(found.is_some(), "expected lookup_at to find resolution at span start");
            assert_eq!(found.unwrap().src_span.start, r.src_span.start);
        }
    }

    #[test]
    fn test_lookup_at_out_of_range() {
        let result = resolve("module T where\nx = 42");
        assert!(result.lookup_at(99999).is_none());
    }

    // ===== Resolutions are sorted =====

    #[test]
    fn test_resolutions_sorted_by_span() {
        let result = resolve("module T where\ndata Foo = A | B\nf x = case x of\n  A -> 1\n  B -> 2");
        for window in result.resolutions.windows(2) {
            assert!(window[0].src_span.start <= window[1].src_span.start,
                "resolutions not sorted: {} > {}", window[0].src_span.start, window[1].src_span.start);
        }
    }

    // ===== Prim references =====

    #[test]
    fn test_prim_type_resolves_to_prim() {
        let result = resolve("module T where\nx :: Int\nx = 42");
        assert!(result.errors.is_empty());
        let int_refs: Vec<_> = find_resolutions(&result, "Int")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Type)
            .collect();
        assert!(!int_refs.is_empty(), "expected type resolution for 'Int'");
        assert!(matches!(int_refs[0].definition, DefinitionSite::Prim),
            "expected Prim definition for Int, got {:?}", int_refs[0].definition);
    }

    #[test]
    fn test_prim_boolean_type() {
        let result = resolve("module T where\nx :: Boolean\nx = true");
        assert!(result.errors.is_empty());
        let bool_refs: Vec<_> = find_resolutions(&result, "Boolean")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Type)
            .collect();
        assert!(!bool_refs.is_empty(), "expected type resolution for 'Boolean'");
        assert!(matches!(bool_refs[0].definition, DefinitionSite::Prim));
    }

    // ===== Complex scenarios =====

    #[test]
    fn test_nested_let_scoping() {
        let result = resolve("module T where\nf = let\n  x = 1\n  y = let\n    z = x\n  in z\nin y");
        assert!(result.errors.is_empty(),
            "expected no errors in nested let, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_where_clause_reference() {
        let result = resolve("module T where\nf x = g x\n  where\n  g y = y");
        assert!(result.errors.is_empty(),
            "expected no errors with where clause, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_multiple_imports_same_name_no_conflict() {
        // Same name from same origin should not conflict
        let mut registry = ModuleRegistry::new();
        let mut exports1 = make_exports_with_values(&["foo"]);
        let foo_sym = interner::intern("foo");
        let origin_sym = interner::intern("Original.Module");
        exports1.value_origins.insert(foo_sym, origin_sym);
        register_module(&mut registry, &["Data", "A"], exports1);

        let mut exports2 = make_exports_with_values(&["foo"]);
        exports2.value_origins.insert(foo_sym, origin_sym);
        register_module(&mut registry, &["Data", "B"], exports2);

        let result = resolve_with_registry(
            "module T where\nimport Data.A (foo)\nimport Data.B (foo)\nx = foo",
            &registry,
        );
        // Same origin, so no conflict
        assert!(!has_scope_conflict(&result, "foo"),
            "expected no scope conflict for same-origin 'foo'");
    }

    #[test]
    fn test_record_pun_resolves() {
        let result = resolve("module T where\nf x = { x }");
        assert!(result.errors.is_empty(),
            "expected no errors for record pun, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        // x in { x } should resolve as a value
        let x_refs = find_resolutions(&result, "x");
        assert!(!x_refs.is_empty(), "expected resolution for record pun 'x'");
    }

    #[test]
    fn test_imported_class_methods_in_scope() {
        let mut registry = ModuleRegistry::new();
        register_module(&mut registry, &["Data", "Show"],
            make_exports_with_class("Show", &["show"]));

        let result = resolve_with_registry(
            "module T where\nimport Data.Show (class Show)\nx = show",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_imported_type_operator() {
        let mut registry = ModuleRegistry::new();
        let mut exports = make_exports_with_type_op("~>", "NaturalTransformation");
        // Also add NaturalTransformation as a type so the fixity target resolves
        let nt_sym = interner::intern("NaturalTransformation");
        exports.type_con_arities.insert(nt_sym, 2);
        register_module(&mut registry, &["Data", "NaturalTransformation"], exports);

        let result = resolve_with_registry(
            "module T where\nimport Data.NaturalTransformation (type (~>))\nx :: forall f g. (f ~> g) -> Int\nx _ = 42",
            &registry,
        );
        assert!(result.errors.is_empty(),
            "expected no errors for imported type operator, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());

        let op_refs: Vec<_> = find_resolutions(&result, "~>")
            .into_iter()
            .filter(|r| r.namespace == Namespace::TypeOperator)
            .collect();
        assert!(!op_refs.is_empty(), "expected type operator resolution for '~>'");
        assert!(matches!(op_refs[0].definition, DefinitionSite::Imported(_)),
            "expected imported definition for '~>', got {:?}", op_refs[0].definition);
    }

    #[test]
    fn test_forall_type_in_signature() {
        let result = resolve("module T where\nid :: forall a. a -> a\nid x = x");
        assert!(result.errors.is_empty(),
            "expected no errors for forall type, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn test_type_annotation_in_expr() {
        let result = resolve("module T where\nx = (42 :: Int)");
        assert!(result.errors.is_empty(),
            "expected no errors for type annotation, got: {:?}",
            result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        // Int should be resolved
        let int_refs: Vec<_> = find_resolutions(&result, "Int")
            .into_iter()
            .filter(|r| r.namespace == Namespace::Type)
            .collect();
        assert!(!int_refs.is_empty(), "expected type resolution for Int in annotation");
    }

    #[test]
    fn test_if_then_else_resolves_all_branches() {
        let result = resolve("module T where\ndata B = T | F\nf b = if true then T else F");
        assert!(result.errors.is_empty());
        assert!(!find_resolutions(&result, "T").is_empty());
        assert!(!find_resolutions(&result, "F").is_empty());
    }

    #[test]
    fn test_array_elements_resolved() {
        let result = resolve("module T where\ndata X = A | B | C\nxs = [A, B, C]");
        assert!(result.errors.is_empty());
        assert!(!find_resolutions(&result, "A").is_empty());
        assert!(!find_resolutions(&result, "B").is_empty());
        assert!(!find_resolutions(&result, "C").is_empty());
    }
}
