use std::collections::HashMap;

use crate::cst::*;
use crate::interner::Symbol;
use crate::span::Span;

/// What kind of reference we found at the cursor
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefKind {
    Value,
    Constructor,
    Type,
}

/// A reference found at the cursor position
#[derive(Debug, Clone)]
pub struct IdentAtCursor {
    pub name: QualifiedIdent,
    pub kind: RefKind,
    pub span: Span,
}

/// A definition location in a source file
#[derive(Debug, Clone)]
pub struct DefLocation {
    pub file_path: String,
    pub span: Span,
}

/// Index of definitions across all loaded modules.
/// Keys are (module_name_string, unqualified_name_symbol).
#[derive(Debug, Clone, Default)]
pub struct DefinitionIndex {
    pub values: HashMap<(String, Symbol), DefLocation>,
    pub types: HashMap<(String, Symbol), DefLocation>,
    pub constructors: HashMap<(String, Symbol), DefLocation>,
}

impl DefinitionIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Collect definitions from a parsed module and add them to the index.
    pub fn add_module(&mut self, module: &Module, file_path: &str) {
        let module_name = format!("{}", module.name.value);

        for decl in &module.decls {
            match decl {
                Decl::TypeSignature { name, .. } => {
                    // Type signatures take precedence — insert first
                    self.values.insert(
                        (module_name.clone(), name.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span: name.span,
                        },
                    );
                }
                Decl::Value { name, .. } => {
                    // Don't overwrite TypeSignature entry
                    self.values.entry((module_name.clone(), name.value))
                        .or_insert(DefLocation {
                            file_path: file_path.to_string(),
                            span: name.span,
                        });
                }
                Decl::Data {
                    name,
                    constructors,
                    kind_sig,
                    is_role_decl,
                    ..
                } => {
                    if *kind_sig == KindSigSource::None && !is_role_decl {
                        self.types.insert(
                            (module_name.clone(), name.value),
                            DefLocation {
                                file_path: file_path.to_string(),
                                span: name.span,
                            },
                        );
                        for ctor in constructors {
                            self.constructors.insert(
                                (module_name.clone(), ctor.name.value),
                                DefLocation {
                                    file_path: file_path.to_string(),
                                    span: ctor.name.span,
                                },
                            );
                        }
                    }
                }
                Decl::TypeAlias { name, .. } => {
                    self.types.insert(
                        (module_name.clone(), name.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span: name.span,
                        },
                    );
                }
                Decl::Newtype {
                    name, constructor, ..
                } => {
                    self.types.insert(
                        (module_name.clone(), name.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span: name.span,
                        },
                    );
                    self.constructors.insert(
                        (module_name.clone(), constructor.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span: constructor.span,
                        },
                    );
                }
                Decl::Class { name, members, .. } => {
                    self.types.insert(
                        (module_name.clone(), name.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span: name.span,
                        },
                    );
                    for member in members {
                        self.values.insert(
                            (module_name.clone(), member.name.value),
                            DefLocation {
                                file_path: file_path.to_string(),
                                span: member.name.span,
                            },
                        );
                    }
                }
                Decl::Foreign { name, .. } => {
                    self.values.insert(
                        (module_name.clone(), name.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span: name.span,
                        },
                    );
                }
                Decl::ForeignData { name, .. } => {
                    self.types.insert(
                        (module_name.clone(), name.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span: name.span,
                        },
                    );
                }
                Decl::Fixity { operator, target, is_type, .. } => {
                    // For operators, try to resolve to the target function's definition
                    let target_key = (module_name.clone(), target.name);
                    let target_span = if *is_type {
                        self.types.get(&target_key).map(|l| l.span)
                    } else {
                        self.values.get(&target_key).map(|l| l.span)
                    };
                    let span = target_span.unwrap_or(operator.span);
                    let map = if *is_type { &mut self.types } else { &mut self.values };
                    map.insert(
                        (module_name.clone(), operator.value),
                        DefLocation {
                            file_path: file_path.to_string(),
                            span,
                        },
                    );
                }
                _ => {}
            }
        }
    }

    /// Look up a definition for a reference found at the cursor.
    /// `current_module` is the module name of the file being edited.
    /// `imports` maps qualified/unqualified names to their source module.
    pub fn find(
        &self,
        ident: &IdentAtCursor,
        current_module: &str,
        import_map: &ImportMap,
    ) -> Option<&DefLocation> {
        let name = ident.name.name;

        // If qualified (e.g. Data.Maybe.Just), resolve the qualifier
        if let Some(qualifier) = ident.name.module {
            // Look up what module this qualifier maps to
            if let Some(real_module) = import_map.qualifier_to_module.get(&qualifier) {
                let key = (real_module.clone(), name);
                return match ident.kind {
                    RefKind::Value => self.values.get(&key),
                    RefKind::Constructor => self.constructors.get(&key),
                    RefKind::Type => self.types.get(&key),
                };
            }
        }

        // Try current module first
        let local_key = (current_module.to_string(), name);
        let result = match ident.kind {
            RefKind::Value => self.values.get(&local_key),
            RefKind::Constructor => self.constructors.get(&local_key),
            RefKind::Type => self.types.get(&local_key),
        };
        if result.is_some() {
            return result;
        }

        // Try imported modules
        let candidates = match ident.kind {
            RefKind::Value => import_map.value_modules.get(&name),
            RefKind::Constructor => import_map.ctor_modules.get(&name),
            RefKind::Type => import_map.type_modules.get(&name),
        };
        if let Some(module_name) = candidates {
            let key = (module_name.clone(), name);
            return match ident.kind {
                RefKind::Value => self.values.get(&key),
                RefKind::Constructor => self.constructors.get(&key),
                RefKind::Type => self.types.get(&key),
            };
        }

        None
    }

    /// Search all modules for a symbol definition. Used as fallback when the
    /// import source module doesn't directly define the symbol (re-exports).
    pub fn find_reexport(
        &self,
        symbol: Symbol,
        namespace: crate::lsp::utils::resolve::Namespace,
    ) -> Option<(&String, &DefLocation)> {
        use crate::lsp::utils::resolve::Namespace;
        match namespace {
            Namespace::Value => self
                .values
                .iter()
                .find(|((_, s), _)| *s == symbol)
                .map(|((m, _), loc)| (m, loc))
                .or_else(|| {
                    self.constructors
                        .iter()
                        .find(|((_, s), _)| *s == symbol)
                        .map(|((m, _), loc)| (m, loc))
                }),
            Namespace::Type | Namespace::Class | Namespace::TypeOperator => self
                .types
                .iter()
                .find(|((_, s), _)| *s == symbol)
                .map(|((m, _), loc)| (m, loc))
                .or_else(|| {
                    self.constructors
                        .iter()
                        .find(|((_, s), _)| *s == symbol)
                        .map(|((m, _), loc)| (m, loc))
                }),
        }
    }
}

/// Maps imported names to their source modules.
#[derive(Debug, Clone, Default)]
pub struct ImportMap {
    /// qualifier symbol → full module name string (e.g. intern("M") → "Data.Maybe")
    pub qualifier_to_module: HashMap<Symbol, String>,
    /// unqualified value name → source module name
    pub value_modules: HashMap<Symbol, String>,
    /// unqualified constructor name → source module name
    pub ctor_modules: HashMap<Symbol, String>,
    /// unqualified type name → source module name
    pub type_modules: HashMap<Symbol, String>,
}

impl ImportMap {
    /// Build an import map from a module's import declarations and the definition index.
    pub fn from_imports(imports: &[ImportDecl], index: &DefinitionIndex) -> Self {
        let mut map = ImportMap::default();

        for import in imports {
            let module_name = format!("{}", import.module);

            // Record qualifier mapping
            if let Some(ref qual) = import.qualified {
                // `import Data.Maybe as M` → qualifier is M's first part
                if let Some(q) = qual.parts.first() {
                    map.qualifier_to_module.insert(*q, module_name.clone());
                }
            }

            // For unqualified imports, record which names come from which module.
            // If it's `import X as Y` (qualified-only), skip unqualified registration.
            let is_qualified_only = import.qualified.is_some();
            if is_qualified_only {
                // Still need to register for qualified lookups, but not unqualified
                // unless there's an explicit import list
                if import.imports.is_none() {
                    continue;
                }
            }

            match &import.imports {
                None => {
                    // `import Data.Maybe` — all exports are available unqualified
                    for ((mod_name, sym), _) in &index.values {
                        if mod_name == &module_name {
                            map.value_modules.insert(*sym, module_name.clone());
                        }
                    }
                    for ((mod_name, sym), _) in &index.types {
                        if mod_name == &module_name {
                            map.type_modules.insert(*sym, module_name.clone());
                        }
                    }
                    for ((mod_name, sym), _) in &index.constructors {
                        if mod_name == &module_name {
                            map.ctor_modules.insert(*sym, module_name.clone());
                        }
                    }
                }
                Some(ImportList::Explicit(items)) => {
                    for item in items {
                        register_import_item(&mut map, item, &module_name, index);
                    }
                }
                Some(ImportList::Hiding(items)) => {
                    // Import everything except the hidden items
                    let mut hidden_values = std::collections::HashSet::new();
                    let mut hidden_types = std::collections::HashSet::new();
                    let hidden_ctors: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
                    for item in items {
                        match item {
                            Import::Value(name) => { hidden_values.insert(name.value); }
                            Import::Type(name, _) => {
                                hidden_types.insert(name.value);
                            }
                            Import::Class(name) => { hidden_types.insert(name.value); }
                            Import::TypeOp(name) => { hidden_types.insert(name.value); }
                        }
                    }
                    for ((mod_name, sym), _) in &index.values {
                        if mod_name == &module_name && !hidden_values.contains(sym) {
                            map.value_modules.insert(*sym, module_name.clone());
                        }
                    }
                    for ((mod_name, sym), _) in &index.types {
                        if mod_name == &module_name && !hidden_types.contains(sym) {
                            map.type_modules.insert(*sym, module_name.clone());
                        }
                    }
                    for ((mod_name, sym), _) in &index.constructors {
                        if mod_name == &module_name && !hidden_ctors.contains(sym) {
                            map.ctor_modules.insert(*sym, module_name.clone());
                        }
                    }
                }
            }
        }

        map
    }
}

fn register_import_item(
    map: &mut ImportMap,
    item: &Import,
    module_name: &str,
    index: &DefinitionIndex,
) {
    match item {
        Import::Value(name) => {
            map.value_modules
                .insert(name.value, module_name.to_string());
        }
        Import::Type(name, data_members) => {
            map.type_modules
                .insert(name.value, module_name.to_string());
            if let Some(DataMembers::All) = data_members {
                // Import all constructors for this type from this module
                for ((mod_name, sym), _) in &index.constructors {
                    if mod_name == module_name {
                        map.ctor_modules.insert(*sym, module_name.to_string());
                    }
                }
            }
        }
        Import::Class(name) => {
            map.type_modules
                .insert(name.value, module_name.to_string());
        }
        Import::TypeOp(name) => {
            map.type_modules
                .insert(name.value, module_name.to_string());
        }
    }
}

/// Find the identifier at the given byte offset in a module's CST.
pub fn find_ident_at_offset(module: &Module, offset: usize) -> Option<IdentAtCursor> {
    let mut best: Option<IdentAtCursor> = None;

    for decl in &module.decls {
        if let Some(found) = find_in_decl(decl, offset) {
            if best
                .as_ref()
                .map_or(true, |b| span_len(found.span) < span_len(b.span))
            {
                best = Some(found);
            }
        }
    }

    best
}

fn span_len(s: Span) -> usize {
    s.end.saturating_sub(s.start)
}

fn contains(span: Span, offset: usize) -> bool {
    if span.end == 0 || span.end <= span.start {
        // Span has no valid end — treat as containing everything from start onward
        offset >= span.start
    } else {
        offset >= span.start && offset < span.end
    }
}

fn find_in_decl(decl: &Decl, offset: usize) -> Option<IdentAtCursor> {
    if !contains(decl.span(), offset) {
        return None;
    }

    match decl {
        Decl::Value {
            guarded,
            binders,
            where_clause,
            ..
        } => {
            for b in binders {
                if let Some(r) = find_in_binder(b, offset) {
                    return Some(r);
                }
            }
            if let Some(r) = find_in_guarded(guarded, offset) {
                return Some(r);
            }
            for lb in where_clause {
                if let Some(r) = find_in_let_binding(lb, offset) {
                    return Some(r);
                }
            }
            None
        }
        Decl::TypeSignature { ty, .. } => find_in_type_expr(ty, offset),
        Decl::Data { constructors, .. } => {
            for ctor in constructors {
                for field in &ctor.fields {
                    if let Some(r) = find_in_type_expr(field, offset) {
                        return Some(r);
                    }
                }
            }
            None
        }
        Decl::TypeAlias { ty, .. } => find_in_type_expr(ty, offset),
        Decl::Newtype { ty, .. } => find_in_type_expr(ty, offset),
        Decl::Class { members, .. } => {
            for m in members {
                if let Some(r) = find_in_type_expr(&m.ty, offset) {
                    return Some(r);
                }
            }
            None
        }
        Decl::Instance { members, types, .. } => {
            for ty in types {
                if let Some(r) = find_in_type_expr(ty, offset) {
                    return Some(r);
                }
            }
            for d in members {
                if let Some(r) = find_in_decl(d, offset) {
                    return Some(r);
                }
            }
            None
        }
        Decl::Foreign { ty, .. } => find_in_type_expr(ty, offset),
        Decl::ForeignData { .. } => None,
        Decl::Fixity { .. } => None,
        Decl::Derive { types, .. } => {
            for ty in types {
                if let Some(r) = find_in_type_expr(ty, offset) {
                    return Some(r);
                }
            }
            None
        }
    }
}

fn find_in_expr(expr: &Expr, offset: usize) -> Option<IdentAtCursor> {
    if !contains(expr.span(), offset) {
        return None;
    }

    match expr {
        Expr::Var { span, name, .. } => {
            if contains(*span, offset) {
                Some(IdentAtCursor {
                    name: *name,
                    kind: RefKind::Value,
                    span: *span,
                })
            } else {
                None
            }
        }
        Expr::Constructor { span, name, .. } => {
            if contains(*span, offset) {
                Some(IdentAtCursor {
                    name: *name,
                    kind: RefKind::Constructor,
                    span: *span,
                })
            } else {
                None
            }
        }
        Expr::Op { left, op, right, .. } => {
            if let Some(r) = find_in_expr(left, offset) {
                return Some(r);
            }
            if contains(op.span, offset) {
                return Some(IdentAtCursor {
                    name: op.value,
                    kind: RefKind::Value,
                    span: op.span,
                });
            }
            find_in_expr(right, offset)
        }
        Expr::OpParens { op, .. } => {
            if contains(op.span, offset) {
                Some(IdentAtCursor {
                    name: op.value,
                    kind: RefKind::Value,
                    span: op.span,
                })
            } else {
                None
            }
        }
        Expr::App { func, arg, .. } => {
            find_in_expr(func, offset).or_else(|| find_in_expr(arg, offset))
        }
        Expr::VisibleTypeApp { func, ty, .. } => {
            find_in_expr(func, offset).or_else(|| find_in_type_expr(ty, offset))
        }
        Expr::Lambda {
            binders, body, ..
        } => {
            for b in binders {
                if let Some(r) = find_in_binder(b, offset) {
                    return Some(r);
                }
            }
            find_in_expr(body, offset)
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => find_in_expr(cond, offset)
            .or_else(|| find_in_expr(then_expr, offset))
            .or_else(|| find_in_expr(else_expr, offset)),
        Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                if let Some(r) = find_in_expr(e, offset) {
                    return Some(r);
                }
            }
            for alt in alts {
                for b in &alt.binders {
                    if let Some(r) = find_in_binder(b, offset) {
                        return Some(r);
                    }
                }
                if let Some(r) = find_in_guarded(&alt.result, offset) {
                    return Some(r);
                }
            }
            None
        }
        Expr::Let {
            bindings, body, ..
        } => {
            for lb in bindings {
                if let Some(r) = find_in_let_binding(lb, offset) {
                    return Some(r);
                }
            }
            find_in_expr(body, offset)
        }
        Expr::Do { statements, .. } | Expr::Ado { statements, .. } => {
            for stmt in statements {
                if let Some(r) = find_in_do_statement(stmt, offset) {
                    return Some(r);
                }
            }
            if let Expr::Ado { result, .. } = expr {
                return find_in_expr(result, offset);
            }
            None
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(ref val) = f.value {
                    if let Some(r) = find_in_expr(val, offset) {
                        return Some(r);
                    }
                }
            }
            None
        }
        Expr::RecordAccess { expr: inner, .. } => find_in_expr(inner, offset),
        Expr::RecordUpdate {
            expr: inner,
            updates,
            ..
        } => {
            if let Some(r) = find_in_expr(inner, offset) {
                return Some(r);
            }
            for u in updates {
                if let Some(r) = find_in_expr(&u.value, offset) {
                    return Some(r);
                }
            }
            None
        }
        Expr::Parens { expr: inner, .. } => find_in_expr(inner, offset),
        Expr::TypeAnnotation {
            expr: inner, ty, ..
        } => find_in_expr(inner, offset).or_else(|| find_in_type_expr(ty, offset)),
        Expr::Literal { lit, .. } => find_in_literal(lit, offset),
        Expr::Array { elements, .. } => {
            for e in elements {
                if let Some(r) = find_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        Expr::Negate { expr: inner, .. } => find_in_expr(inner, offset),
        Expr::AsPattern { name, pattern, .. } => {
            find_in_expr(name, offset).or_else(|| find_in_expr(pattern, offset))
        }
        Expr::BacktickApp {
            func, left, right, ..
        } => find_in_expr(left, offset)
            .or_else(|| find_in_expr(func, offset))
            .or_else(|| find_in_expr(right, offset)),
        Expr::Wildcard { .. } | Expr::Hole { .. } => None,
    }
}

fn find_in_literal(lit: &Literal, offset: usize) -> Option<IdentAtCursor> {
    match lit {
        Literal::Array(exprs) => {
            for e in exprs {
                if let Some(r) = find_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        _ => None,
    }
}

fn find_in_type_expr(ty: &TypeExpr, offset: usize) -> Option<IdentAtCursor> {
    match ty {
        TypeExpr::Constructor { span, name } => {
            if contains(*span, offset) {
                Some(IdentAtCursor {
                    name: *name,
                    kind: RefKind::Type,
                    span: *span,
                })
            } else {
                None
            }
        }
        TypeExpr::App {
            constructor, arg, ..
        } => find_in_type_expr(constructor, offset).or_else(|| find_in_type_expr(arg, offset)),
        TypeExpr::Function { from, to, .. } => {
            find_in_type_expr(from, offset).or_else(|| find_in_type_expr(to, offset))
        }
        TypeExpr::Forall { vars, ty: inner, .. } => {
            for (_, _, kind) in vars {
                if let Some(k) = kind {
                    if let Some(r) = find_in_type_expr(k, offset) {
                        return Some(r);
                    }
                }
            }
            find_in_type_expr(inner, offset)
        }
        TypeExpr::Constrained {
            constraints,
            ty: inner,
            ..
        } => {
            for c in constraints {
                if contains(c.span, offset) {
                    if let Some(r) = find_in_constraint(c, offset) {
                        return Some(r);
                    }
                }
            }
            find_in_type_expr(inner, offset)
        }
        TypeExpr::Record { fields, .. } => {
            for f in fields {
                if let Some(r) = find_in_type_expr(&f.ty, offset) {
                    return Some(r);
                }
            }
            None
        }
        TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                if let Some(r) = find_in_type_expr(&f.ty, offset) {
                    return Some(r);
                }
            }
            if let Some(t) = tail {
                return find_in_type_expr(t, offset);
            }
            None
        }
        TypeExpr::Parens { ty: inner, .. } => find_in_type_expr(inner, offset),
        TypeExpr::TypeOp {
            left, op, right, ..
        } => {
            if let Some(r) = find_in_type_expr(left, offset) {
                return Some(r);
            }
            if contains(op.span, offset) {
                return Some(IdentAtCursor {
                    name: op.value,
                    kind: RefKind::Type,
                    span: op.span,
                });
            }
            find_in_type_expr(right, offset)
        }
        TypeExpr::Kinded { ty: inner, kind, .. } => {
            find_in_type_expr(inner, offset).or_else(|| find_in_type_expr(kind, offset))
        }
        TypeExpr::Var { .. }
        | TypeExpr::Hole { .. }
        | TypeExpr::Wildcard { .. }
        | TypeExpr::StringLiteral { .. }
        | TypeExpr::IntLiteral { .. }
        | TypeExpr::ArrayPattern { .. }
        | TypeExpr::AsPattern { .. } => None,
    }
}

fn find_in_constraint(c: &Constraint, offset: usize) -> Option<IdentAtCursor> {
    // The class name in the constraint
    // We don't have an exact span for just the class name in a Constraint,
    // so use the constraint's span as approximation
    for arg in &c.args {
        if let Some(r) = find_in_type_expr(arg, offset) {
            return Some(r);
        }
    }
    // If not in args, it's probably on the class name
    Some(IdentAtCursor {
        name: c.class,
        kind: RefKind::Type,
        span: c.span,
    })
}

fn find_in_binder(binder: &Binder, offset: usize) -> Option<IdentAtCursor> {
    match binder {
        Binder::Constructor {
            span, name, args, ..
        } => {
            if contains(*span, offset) {
                // Check args first (tighter match)
                for a in args {
                    if let Some(r) = find_in_binder(a, offset) {
                        return Some(r);
                    }
                }
                Some(IdentAtCursor {
                    name: *name,
                    kind: RefKind::Constructor,
                    span: *span,
                })
            } else {
                None
            }
        }
        Binder::Record { fields, .. } => {
            for f in fields {
                if let Some(ref b) = f.binder {
                    if let Some(r) = find_in_binder(b, offset) {
                        return Some(r);
                    }
                }
            }
            None
        }
        Binder::As { binder: inner, .. } => find_in_binder(inner, offset),
        Binder::Parens { binder: inner, .. } => find_in_binder(inner, offset),
        Binder::Array { elements, .. } => {
            for e in elements {
                if let Some(r) = find_in_binder(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        Binder::Op {
            left, op, right, ..
        } => {
            if let Some(r) = find_in_binder(left, offset) {
                return Some(r);
            }
            if contains(op.span, offset) {
                return Some(IdentAtCursor {
                    name: op.value,
                    kind: RefKind::Value,
                    span: op.span,
                });
            }
            find_in_binder(right, offset)
        }
        Binder::Typed {
            binder: inner,
            ty,
            ..
        } => find_in_binder(inner, offset).or_else(|| find_in_type_expr(ty, offset)),
        Binder::Wildcard { .. } | Binder::Var { .. } | Binder::Literal { .. } => None,
    }
}

fn find_in_guarded(guarded: &GuardedExpr, offset: usize) -> Option<IdentAtCursor> {
    match guarded {
        GuardedExpr::Unconditional(expr) => find_in_expr(expr, offset),
        GuardedExpr::Guarded(guards) => {
            for g in guards {
                for pat in &g.patterns {
                    match pat {
                        GuardPattern::Boolean(e) => {
                            if let Some(r) = find_in_expr(e, offset) {
                                return Some(r);
                            }
                        }
                        GuardPattern::Pattern(b, e) => {
                            if let Some(r) = find_in_binder(b, offset) {
                                return Some(r);
                            }
                            if let Some(r) = find_in_expr(e, offset) {
                                return Some(r);
                            }
                        }
                    }
                }
                if let Some(r) = find_in_expr(&g.expr, offset) {
                    return Some(r);
                }
            }
            None
        }
    }
}

fn find_in_let_binding(lb: &LetBinding, offset: usize) -> Option<IdentAtCursor> {
    match lb {
        LetBinding::Value { binder, expr, .. } => {
            find_in_binder(binder, offset).or_else(|| find_in_expr(expr, offset))
        }
        LetBinding::Signature { ty, .. } => find_in_type_expr(ty, offset),
    }
}

fn find_in_do_statement(stmt: &DoStatement, offset: usize) -> Option<IdentAtCursor> {
    match stmt {
        DoStatement::Bind { binder, expr, .. } => {
            find_in_binder(binder, offset).or_else(|| find_in_expr(expr, offset))
        }
        DoStatement::Let { bindings, .. } => {
            for lb in bindings {
                if let Some(r) = find_in_let_binding(lb, offset) {
                    return Some(r);
                }
            }
            None
        }
        DoStatement::Discard { expr, .. } => find_in_expr(expr, offset),
    }
}

/// Convert an LSP Position (0-indexed line/col) to a byte offset in source.
pub fn position_to_offset(source: &str, line: u32, character: u32) -> Option<usize> {
    let mut current_line = 0u32;
    let mut current_col = 0u32;

    for (i, c) in source.char_indices() {
        if current_line == line && current_col == character {
            return Some(i);
        }
        if c == '\n' {
            if current_line == line {
                // Past end of this line
                return Some(i);
            }
            current_line += 1;
            current_col = 0;
        } else {
            current_col += 1;
        }
    }

    // Handle position at end of file
    if current_line == line && current_col == character {
        return Some(source.len());
    }

    None
}

/// Find definition of a local variable within the same module.
/// Returns the span of the binding site if found.
pub fn find_local_definition(module: &Module, name: Symbol) -> Option<Span> {
    for decl in &module.decls {
        if let Some(span) = find_name_in_decl(decl, name) {
            return Some(span);
        }
    }
    None
}

fn find_name_in_decl(decl: &Decl, name: Symbol) -> Option<Span> {
    match decl {
        Decl::Value {
            name: decl_name, ..
        } => {
            if decl_name.value == name {
                Some(decl_name.span)
            } else {
                None
            }
        }
        Decl::Data {
            name: decl_name,
            constructors,
            ..
        } => {
            if decl_name.value == name {
                return Some(decl_name.span);
            }
            for ctor in constructors {
                if ctor.name.value == name {
                    return Some(ctor.name.span);
                }
            }
            None
        }
        Decl::TypeAlias {
            name: decl_name, ..
        } => {
            if decl_name.value == name {
                Some(decl_name.span)
            } else {
                None
            }
        }
        Decl::Newtype {
            name: decl_name,
            constructor,
            ..
        } => {
            if decl_name.value == name {
                return Some(decl_name.span);
            }
            if constructor.value == name {
                return Some(constructor.span);
            }
            None
        }
        Decl::Class {
            name: decl_name,
            members,
            ..
        } => {
            if decl_name.value == name {
                return Some(decl_name.span);
            }
            for m in members {
                if m.name.value == name {
                    return Some(m.name.span);
                }
            }
            None
        }
        Decl::Foreign {
            name: decl_name, ..
        } => {
            if decl_name.value == name {
                Some(decl_name.span)
            } else {
                None
            }
        }
        Decl::ForeignData {
            name: decl_name, ..
        } => {
            if decl_name.value == name {
                Some(decl_name.span)
            } else {
                None
            }
        }
        Decl::Instance { members, .. } => {
            for d in members {
                if let Some(span) = find_name_in_decl(d, name) {
                    return Some(span);
                }
            }
            None
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner::intern;

    #[test]
    fn test_position_to_offset() {
        let src = "hello\nworld\nfoo";
        assert_eq!(position_to_offset(src, 0, 0), Some(0));
        assert_eq!(position_to_offset(src, 0, 3), Some(3));
        assert_eq!(position_to_offset(src, 1, 0), Some(6));
        assert_eq!(position_to_offset(src, 1, 5), Some(11));
        assert_eq!(position_to_offset(src, 2, 0), Some(12));
        assert_eq!(position_to_offset(src, 2, 3), Some(15));
    }

    #[test]
    fn test_find_ident_at_offset_var() {
        let src = "module Test where\n\nfoo = bar";
        let module = crate::parser::parse(src).expect("parse");
        let bar_offset = src.find("bar").unwrap();
        let result = find_ident_at_offset(&module, bar_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Value);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "bar"
        );
    }

    #[test]
    fn test_find_ident_at_offset_constructor() {
        let src = "module Test where\n\nfoo = Just 1";
        let module = crate::parser::parse(src).expect("parse");
        // "Just" starts somewhere around offset 24
        let just_offset = src.find("Just").unwrap();
        let result = find_ident_at_offset(&module, just_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Constructor);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "Just"
        );
    }

    #[test]
    fn test_find_ident_at_offset_type() {
        let src = "module Test where\n\nfoo :: Int -> String\nfoo x = \"\"";
        let module = crate::parser::parse(src).expect("parse");
        let int_offset = src.find("Int").unwrap();
        let result = find_ident_at_offset(&module, int_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Type);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "Int"
        );
    }

    #[test]
    fn test_find_local_definition() {
        let src = "module Test where\n\nfoo = 1\n\nbar = foo";
        let module = crate::parser::parse(src).expect("parse");
        let foo_sym = intern("foo");
        let result = find_local_definition(&module, foo_sym);
        assert!(result.is_some());
    }

    #[test]
    fn test_definition_index_collect() {
        let src = "module Test where\n\ndata Color = Red | Green | Blue\n\nfoo = 1";
        let module = crate::parser::parse(src).expect("parse");
        let mut index = DefinitionIndex::new();
        index.add_module(&module, "test.purs");

        let foo_sym = intern("foo");
        let color_sym = intern("Color");
        let red_sym = intern("Red");

        assert!(index.values.contains_key(&("Test".to_string(), foo_sym)));
        assert!(index.types.contains_key(&("Test".to_string(), color_sym)));
        assert!(index
            .constructors
            .contains_key(&("Test".to_string(), red_sym)));
    }

    #[test]
    fn test_find_ident_in_case_expr() {
        let src = "module Test where\n\nfoo x = case x of\n  Just y -> y\n  Nothing -> 0";
        let module = crate::parser::parse(src).expect("parse");
        let nothing_offset = src.find("Nothing").unwrap();
        let result = find_ident_at_offset(&module, nothing_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Constructor);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "Nothing"
        );
    }

    /// Helper: simulate the goto-definition flow for a cursor position in source.
    /// Returns the resolved DefLocation if found.
    fn goto_def_in_source(
        src: &str,
        file_path: &str,
        line: u32,
        character: u32,
        index: &DefinitionIndex,
    ) -> Option<DefLocation> {
        let offset = position_to_offset(src, line, character)?;
        let module = crate::parser::parse(src).ok()?;
        let ident = find_ident_at_offset(&module, offset)?;
        let current_module = format!("{}", module.name.value);

        // Try local first
        if ident.name.module.is_none() {
            if let Some(span) = find_local_definition(&module, ident.name.name) {
                return Some(DefLocation {
                    file_path: file_path.to_string(),
                    span,
                });
            }
        }

        // Try cross-module
        let import_map = ImportMap::from_imports(&module.imports, index);
        index.find(&ident, &current_module, &import_map).cloned()
    }

    #[test]
    fn test_goto_def_local_value() {
        let src = "module Test where\n\nfoo = 1\n\nbar = foo";
        // Click on "foo" in "bar = foo" (line 4, col 6)
        let foo_in_bar = src.rfind("foo").unwrap();
        let line = src[..foo_in_bar].matches('\n').count() as u32;
        let col = (foo_in_bar - src[..foo_in_bar].rfind('\n').unwrap() - 1) as u32;

        let index = DefinitionIndex::new();
        let result = goto_def_in_source(src, "test.purs", line, col, &index);
        assert!(result.is_some(), "should find local definition of foo");
        let loc = result.unwrap();
        assert_eq!(loc.file_path, "test.purs");
        // The span should point to the definition of foo (line 3, "foo = 1")
        let (start, _) = loc.span.to_pos(src).unwrap();
        assert_eq!(start.line, 3); // 1-indexed: module=1, blank=2, foo=3
    }

    #[test]
    fn test_goto_def_local_data_constructor() {
        let src = "module Test where\n\ndata Color = Red | Green | Blue\n\nfoo = Red";
        // Click on "Red" in "foo = Red"
        let red_in_foo = src.rfind("Red").unwrap();
        let line = src[..red_in_foo].matches('\n').count() as u32;
        let col = (red_in_foo - src[..red_in_foo].rfind('\n').unwrap() - 1) as u32;

        let index = DefinitionIndex::new();
        let result = goto_def_in_source(src, "test.purs", line, col, &index);
        assert!(result.is_some(), "should find local constructor Red");
        let loc = result.unwrap();
        let (start, _) = loc.span.to_pos(src).unwrap();
        assert_eq!(start.line, 3); // data Color = Red is on line 3
    }

    #[test]
    fn test_goto_def_local_type_in_signature() {
        let src = "module Test where\n\ndata Foo = MkFoo\n\nbar :: Foo\nbar = MkFoo";
        // Click on "Foo" in the type signature "bar :: Foo"
        let foo_in_sig = src.find("bar :: Foo").unwrap() + "bar :: ".len();
        let line = src[..foo_in_sig].matches('\n').count() as u32;
        let col = (foo_in_sig - src[..foo_in_sig].rfind('\n').unwrap() - 1) as u32;

        let index = DefinitionIndex::new();
        let result = goto_def_in_source(src, "test.purs", line, col, &index);
        assert!(result.is_some(), "should find local type Foo");
        let loc = result.unwrap();
        let (start, _) = loc.span.to_pos(src).unwrap();
        assert_eq!(start.line, 3); // data Foo on line 3
    }

    #[test]
    fn test_goto_def_cross_module_value() {
        // Module A defines "helper"
        let src_a = "module ModA where\n\nhelper = 1";
        // Module B imports and uses it
        let src_b = "module ModB where\n\nimport ModA\n\nfoo = helper";

        let mut index = DefinitionIndex::new();
        let mod_a = crate::parser::parse(src_a).unwrap();
        index.add_module(&mod_a, "/src/ModA.purs");

        // Click on "helper" in ModB
        let helper_offset = src_b.find("helper").unwrap();
        let line = src_b[..helper_offset].matches('\n').count() as u32;
        let col = (helper_offset - src_b[..helper_offset].rfind('\n').unwrap() - 1) as u32;

        let result = goto_def_in_source(src_b, "/src/ModB.purs", line, col, &index);
        assert!(result.is_some(), "should find cross-module definition of helper");
        let loc = result.unwrap();
        assert_eq!(loc.file_path, "/src/ModA.purs");
        let (start, _) = loc.span.to_pos(src_a).unwrap();
        assert_eq!(start.line, 3);
    }

    #[test]
    fn test_goto_def_cross_module_type() {
        let src_a = "module ModA where\n\ndata Widget = W";
        let src_b = "module ModB where\n\nimport ModA (Widget(..))\n\nfoo :: Widget\nfoo = W";

        let mut index = DefinitionIndex::new();
        let mod_a = crate::parser::parse(src_a).unwrap();
        index.add_module(&mod_a, "/src/ModA.purs");

        // Click on "Widget" in the type signature
        let widget_offset = src_b.find("foo :: Widget").unwrap() + "foo :: ".len();
        let line = src_b[..widget_offset].matches('\n').count() as u32;
        let col = (widget_offset - src_b[..widget_offset].rfind('\n').unwrap() - 1) as u32;

        let result = goto_def_in_source(src_b, "/src/ModB.purs", line, col, &index);
        assert!(result.is_some(), "should find cross-module type Widget");
        let loc = result.unwrap();
        assert_eq!(loc.file_path, "/src/ModA.purs");
    }

    #[test]
    fn test_goto_def_cross_module_constructor() {
        let src_a = "module ModA where\n\ndata Maybe a = Nothing | Just a";
        let src_b = "module ModB where\n\nimport ModA (Maybe(..))\n\nfoo = Just 1";

        let mut index = DefinitionIndex::new();
        let mod_a = crate::parser::parse(src_a).unwrap();
        index.add_module(&mod_a, "/src/ModA.purs");

        // Click on "Just" in "foo = Just 1"
        let just_offset = src_b.find("Just").unwrap();
        let line = src_b[..just_offset].matches('\n').count() as u32;
        let col = (just_offset - src_b[..just_offset].rfind('\n').unwrap() - 1) as u32;

        let result = goto_def_in_source(src_b, "/src/ModB.purs", line, col, &index);
        assert!(result.is_some(), "should find cross-module constructor Just");
        let loc = result.unwrap();
        assert_eq!(loc.file_path, "/src/ModA.purs");
    }

    #[test]
    fn test_goto_def_no_result_for_unknown() {
        let src = "module Test where\n\nfoo = unknownThing";
        let offset = src.find("unknownThing").unwrap();
        let line = src[..offset].matches('\n').count() as u32;
        let col = (offset - src[..offset].rfind('\n').unwrap() - 1) as u32;

        let index = DefinitionIndex::new();
        let result = goto_def_in_source(src, "test.purs", line, col, &index);
        // unknownThing is not defined anywhere — should return None
        assert!(result.is_none());
    }

    #[test]
    fn test_goto_def_not_ready_returns_none_for_whitespace() {
        let src = "module Test where\n\nfoo = 1";
        // Click on whitespace (line 1, col 0 = blank line)
        let index = DefinitionIndex::new();
        let result = goto_def_in_source(src, "test.purs", 1, 0, &index);
        assert!(result.is_none());
    }

    #[test]
    fn test_find_ident_in_where_clause() {
        let src = "module Test where\n\nfoo = bar\n  where\n  bar = 1";
        let module = crate::parser::parse(src).expect("parse");
        let bar_offset = src.find("foo = bar").unwrap() + "foo = ".len();
        let result = find_ident_at_offset(&module, bar_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Value);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "bar"
        );
        assert_eq!(ident.span.start, bar_offset);
        assert_eq!(ident.span.end, bar_offset + "bar".len());
    }

    #[test]
    fn test_find_ident_in_where_clause_definition() {
        // Click on the reference inside the where binding's RHS
        let src = "module Test where\n\nbaz = 1\n\nfoo = bar\n  where\n  bar = baz";
        let module = crate::parser::parse(src).expect("parse");
        let baz_offset = src.rfind("baz").unwrap();
        let result = find_ident_at_offset(&module, baz_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Value);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "baz"
        );
        assert_eq!(ident.span.start, baz_offset);
        assert_eq!(ident.span.end, baz_offset + "baz".len());
    }

    #[test]
    fn test_find_ident_in_let_expr() {
        let src = "module Test where\n\nfoo = let x = 1 in x";
        let module = crate::parser::parse(src).expect("parse");
        // Click on the "x" after "in"
        let x_offset = src.rfind("x").unwrap();
        let result = find_ident_at_offset(&module, x_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Value);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "x"
        );
        assert_eq!(ident.span.start, x_offset);
        assert_eq!(ident.span.end, x_offset + "x".len());
    }

    #[test]
    fn test_find_ident_in_do_bind_rhs() {
        let src = "module Test where\n\nfoo = do\n  x <- bar\n  pure x";
        let module = crate::parser::parse(src).expect("parse");
        // Click on "bar" (RHS of bind arrow)
        let bar_offset = src.find("bar").unwrap();
        let result = find_ident_at_offset(&module, bar_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Value);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "bar"
        );
        assert_eq!(ident.span.start, bar_offset);
        assert_eq!(ident.span.end, bar_offset + "bar".len());
    }

    #[test]
    fn test_find_ident_in_do_discard() {
        let src = "module Test where\n\nfoo = do\n  bar\n  baz";
        let module = crate::parser::parse(src).expect("parse");
        let baz_offset = src.find("baz").unwrap();
        let result = find_ident_at_offset(&module, baz_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Value);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "baz"
        );
        assert_eq!(ident.span.start, baz_offset);
        assert_eq!(ident.span.end, baz_offset + "baz".len());
    }

    #[test]
    fn test_find_ident_value_operator() {
        let src = "module Test where\n\nfoo = 1 + 2";
        let module = crate::parser::parse(src).expect("parse");
        let plus_offset = src.find('+').unwrap();
        let result = find_ident_at_offset(&module, plus_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Value);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "+"
        );
        assert_eq!(ident.span.start, plus_offset);
        assert_eq!(ident.span.end, plus_offset + "+".len());
    }

    #[test]
    fn test_find_ident_value_operator_operands() {
        let src = "module Test where\n\nfoo = bar + baz";
        let module = crate::parser::parse(src).expect("parse");
        // Click on "bar" (left operand)
        let bar_offset = src.find("bar").unwrap();
        let result = find_ident_at_offset(&module, bar_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "bar"
        );
        assert_eq!(ident.span.start, bar_offset);
        assert_eq!(ident.span.end, bar_offset + "bar".len());
        // Click on "baz" (right operand)
        let baz_offset = src.find("baz").unwrap();
        let result = find_ident_at_offset(&module, baz_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "baz"
        );
        assert_eq!(ident.span.start, baz_offset);
        assert_eq!(ident.span.end, baz_offset + "baz".len());
    }

    #[test]
    fn test_find_ident_type_operator() {
        let src = "module Test where\n\nfoo :: Int ~> String\nfoo = bar";
        let module = crate::parser::parse(src).expect("parse");
        let op_offset = src.find("~>").unwrap();
        let result = find_ident_at_offset(&module, op_offset);
        assert!(result.is_some());
        let ident = result.unwrap();
        assert_eq!(ident.kind, RefKind::Type);
        assert_eq!(
            crate::interner::resolve(ident.name.name).unwrap(),
            "~>"
        );
        assert_eq!(ident.span.start, op_offset);
        assert_eq!(ident.span.end, op_offset + "~>".len());
    }
}
