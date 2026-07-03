use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use crate::cst::{self, Comment, Decl};
use crate::interner;
use crate::lsp::utils::find_definition::position_to_offset;
use crate::lsp::utils::resolve::{self, DefinitionSite, Namespace};
use crate::typecheck_db::driver_multi::{check_module_ide, ModuleInput};
use crate::typecheck_db::types::Type;

fn fmt_ty(ty: &Type) -> String {
    ty.to_string()
}

/// Render a constructor's type from its `CtorInfo`: the fields as an arrow
/// chain ending in the parent type applied to its type vars. Constructors are
/// not stored in `ModuleExports.values`, so hover synthesizes their type here.
fn ctor_type_string(info: &crate::typecheck_db::passes::exhaustiveness::CtorInfo) -> String {
    let mut result = info.parent_type.clone();
    for v in &info.type_vars {
        result.push(' ');
        result.push_str(v);
    }
    for field in info.fields.iter().rev() {
        result = format!("{} -> {result}", field);
    }
    result
}

/// Format a `name :: type` line, wrapping long types onto a new indented line
/// so the type stays readable in hover popovers.
fn format_sig(name: &str, ty: &str) -> String {
    if ty.chars().count() > 32 || ty.contains('(') || ty.contains('{') {
        let indented = ty
            .lines()
            .map(|line| format!("  {line}"))
            .collect::<Vec<_>>()
            .join("\n");
        format!("{name} ::\n{indented}")
    } else {
        format!("{name} :: {ty}")
    }
}

use super::super::Backend;

/// Info about what the cursor is on: either a resolved reference or a declaration name.
enum HoverTarget {
    /// Cursor is on a reference to a name (resolved by resolve_names).
    Reference(resolve::ResolvedName),
    /// Cursor is on a value declaration name (the definition site itself).
    ValueDeclaration(interner::Symbol),
    /// Cursor is on a type/data declaration name.
    TypeDeclaration(interner::Symbol),
}

impl Backend {
    pub(crate) async fn handle_hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        if !self.is_ready() {
            return Ok(None);
        }

        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;

        let source = {
            let files = self.files.read().await;
            files.get(&uri.to_string()).map(|f| f.source.clone())
        };
        let source = match source {
            Some(s) => s,
            None => return Ok(None),
        };

        let offset = match position_to_offset(&source, pos.line, pos.character) {
            Some(o) => o,
            None => return Ok(None),
        };

        let module = match crate::parser::parse(&source) {
            Ok(m) => m,
            Err(_) => return Ok(None),
        };

        // Check if cursor is on an import item
        if let Some(hover) = self.hover_import_item(&module, offset).await {
            return Ok(Some(hover));
        }

        // Try resolve_names first (for references), then check declaration sites
        let exports = self.resolution_exports.read().await;
        let resolved = resolve::resolve_names(&module, &exports);
        drop(exports);

        let target = if let Some(r) = resolved.lookup_at(offset) {
            HoverTarget::Reference(r.clone())
        } else if let Some((sym, is_type)) = find_decl_name_at_offset(&module.decls, offset) {
            if is_type {
                HoverTarget::TypeDeclaration(sym)
            } else {
                HoverTarget::ValueDeclaration(sym)
            }
        } else {
            // Fallback: check span_types for record labels and other spans
            // that resolve_names doesn't track
            return self.hover_span_type(&module, &source, offset).await;
        };

        let (symbol, name_str, type_str, namespace) = match &target {
            HoverTarget::Reference(resolved_name) => {
                let full_name_str = interner::resolve(resolved_name.src_symbol).unwrap_or_default();
                // Strip qualifier prefix for registry lookups (e.g., "Lib.times2" → "times2")
                let name_str = match &resolved_name.definition {
                    DefinitionSite::Imported(_) => {
                        full_name_str.rsplit('.').next().unwrap_or(&full_name_str).to_string()
                    }
                    _ => full_name_str.to_string(),
                };

                let type_str = match &resolved_name.definition {
                    DefinitionSite::Local(_) => {
                        let ty = self.get_local_type(&module, resolved_name.src_symbol, &source).await;
                        if ty.is_none() && matches!(resolved_name.namespace, Namespace::Type | Namespace::Class) {
                            let sym = interner::intern(&name_str);
                            self.get_local_kind(&module, sym).await
                                .or_else(|| Some("Type".to_string()))
                        } else {
                            ty
                        }
                    }
                    DefinitionSite::LocalVar(local_span) => {
                        self.get_local_var_type(&module, &source, *local_span).await
                    }
                    DefinitionSite::Imported(module_sym) => {
                        let ty = self.get_imported_type(*module_sym, &name_str).await;
                        if ty.is_none() && matches!(resolved_name.namespace, Namespace::Type | Namespace::Class) {
                            // For imported types/classes, show kind from source module CST
                            self.get_imported_kind(*module_sym, &name_str).await
                        } else {
                            ty
                        }
                    }
                    DefinitionSite::Prim => match resolved_name.namespace {
                        Namespace::Type | Namespace::Class => Some("Type".to_string()),
                        _ => None,
                    },
                };

                match type_str {
                    Some(s) => (resolved_name.src_symbol, name_str, s, resolved_name.namespace),
                    None => return Ok(None),
                }
            }
            HoverTarget::ValueDeclaration(sym) => {
                let name_str = interner::resolve(*sym).unwrap_or_default();
                let type_str = self.get_local_type(&module, *sym, &source).await;
                match type_str {
                    Some(s) => (*sym, name_str, s, Namespace::Value),
                    None => return Ok(None),
                }
            }
            HoverTarget::TypeDeclaration(sym) => {
                let name_str = interner::resolve(*sym).unwrap_or_default();
                let kind_str = self.get_local_kind(&module, *sym).await
                    .unwrap_or_else(|| "Type".to_string());
                (*sym, name_str, kind_str, Namespace::Type)
            }
        };

        // Look up doc-comments: local CST first, then imported module.
        // For qualified imports, use the unqualified name to match against declarations.
        let unqualified_symbol = interner::intern(&name_str);
        let doc_comments = find_doc_comments(&module.decls, unqualified_symbol);
        let imported_docs = if doc_comments.is_empty() {
            if let HoverTarget::Reference(resolved_name) = &target {
                if let DefinitionSite::Imported(module_sym) = &resolved_name.definition {
                    let module_name = interner::resolve(*module_sym).unwrap_or_default();
                    self.get_imported_doc_comments(&module_name, unqualified_symbol).await
                } else {
                    Vec::new()
                }
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // For types/classes, include the source definition (first 1000 chars).
        let definition_text = self
            .get_type_definition_text(&module, &source, &target)
            .await;

        // Build markdown content
        let sig = format_sig(&name_str, &type_str);
        let mut markdown = format!("```purescript\n{sig}\n```");

        if let Some(def) = &definition_text {
            markdown.push_str("\n\n---\n\n```purescript\n");
            markdown.push_str(def);
            markdown.push_str("\n```");
        }

        if !doc_comments.is_empty() {
            markdown.push_str("\n\n---\n\n");
            for comment in &doc_comments {
                if let Comment::Doc(text) = comment {
                    markdown.push_str(text.trim());
                    markdown.push('\n');
                }
            }
        } else if !imported_docs.is_empty() {
            markdown.push_str("\n\n---\n\n");
            for doc in &imported_docs {
                markdown.push_str(doc.trim());
                markdown.push('\n');
            }
        }

        let _ = namespace;

        Ok(Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: markdown,
            }),
            range: None,
        }))
    }

    /// Run an IDE check of `module` against the warm registry and return its
    /// span→type map. `module_name` is the dotted name; `source` is the module
    /// text for per-decl hashing.
    async fn ide_span_types(
        &self,
        module: &cst::Module,
        source: &str,
    ) -> std::collections::HashMap<crate::span::Span, Type> {
        let module_name = interner::resolve_module_name(&module.name.value.parts);
        let input = ModuleInput::new(module_name, source.to_string(), module.clone());
        let mut reg = self.registry.write().await;
        let mut db = self.db.lock().await;
        check_module_ide(&mut db, &input, &mut reg).span_types
    }

    async fn hover_span_type(&self, module: &cst::Module, source: &str, offset: usize) -> Result<Option<Hover>> {
        let span_types = self.ide_span_types(module, source).await;
        // On ties, prefer the narrowest span containing the offset.
        let best = span_types
            .iter()
            .filter(|(span, _)| offset >= span.start && offset < span.end)
            .min_by_key(|(span, _)| span.end - span.start);
        if let Some((span, ty)) = best {
            let label = &source[span.start..span.end];
            let type_str = fmt_ty(ty);
            let sig = format_sig(label, &type_str);
            let markdown = format!("```purescript\n{sig}\n```");
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: markdown,
                }),
                range: None,
            }));
        }
        Ok(None)
    }

    async fn get_local_var_type(
        &self,
        module: &cst::Module,
        source: &str,
        span: crate::span::Span,
    ) -> Option<String> {
        let span_types = self.ide_span_types(module, source).await;
        span_types.get(&span).map(fmt_ty)
    }

    async fn get_local_type(&self, module: &cst::Module, symbol: interner::Symbol, source: &str) -> Option<String> {
        // The registry exports the GENERALIZED inferred type for signed decls
        // (e.g. `foo :: Int -> Int` → `a -> a`). Prefer the explicit CST
        // signature when present so hover matches what the user wrote.
        if let Some(sig) = find_cst_type_signature(&module.decls, symbol, source) {
            return Some(sig);
        }

        // No CST signature — read the inferred scheme from the registry (this
        // covers unsigned decls). Constructors live in `ctors`, not `values`,
        // so fall back to synthesizing their type from `CtorInfo`.
        let module_name = interner::resolve_module_name(&module.name.value.parts);
        let name_str = interner::resolve(symbol).unwrap_or_default();
        {
            let registry = self.registry.read().await;
            if let Some(exports) = registry.get(&module_name) {
                if let Some(scheme) = exports.values.get(&name_str) {
                    return Some(fmt_ty(&scheme.ty));
                }
                if let Some(info) = exports.ctors.get(&name_str) {
                    return Some(ctor_type_string(info));
                }
            }
        }

        None
    }

    async fn hover_import_item(
        &self,
        module: &cst::Module,
        offset: usize,
    ) -> Option<Hover> {
        use crate::cst::{Import, ImportList};

        for import_decl in &module.imports {
            if offset < import_decl.span.start || offset >= import_decl.span.end {
                continue;
            }

            // Check if cursor is on the module name
            if offset >= import_decl.module_span.start && offset < import_decl.module_span.end {
                let module_name = interner::resolve_module_name(&import_decl.module.parts);
                let docs = self.get_imported_module_doc(&module_name).await;
                let mut markdown = format!("```purescript\nmodule {module_name}\n```");
                if !docs.is_empty() {
                    markdown.push_str("\n\n---\n\n");
                    for doc in &docs {
                        markdown.push_str(doc.trim());
                        markdown.push('\n');
                    }
                }
                return Some(Hover {
                    contents: HoverContents::Markup(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: markdown,
                    }),
                    range: None,
                });
            }

            let items = match &import_decl.imports {
                Some(ImportList::Explicit(items)) | Some(ImportList::Hiding(items)) => items,
                None => continue,
            };
            for item in items {
                let item_span = item.span();
                let symbol = item.name();
                if offset >= item_span.start && offset < item_span.end {
                    let name_str = interner::resolve(symbol).unwrap_or_default();
                    let module_name = interner::resolve_module_name(&import_decl.module.parts);
                    let type_str = self.get_imported_type_by_name(&module_name, &name_str).await;
                    let type_str = match type_str {
                        Some(t) => t,
                        None => match item {
                            Import::Type(_, _) | Import::Class(_) => {
                                self.get_imported_kind_by_name(&module_name, &name_str).await
                                    .unwrap_or_else(|| "Type".to_string())
                            }
                            _ => "unknown".to_string(),
                        },
                    };
                    // Look up doc-comments from the source module
                    let doc_comments = self.get_imported_doc_comments(&module_name, symbol).await;
                    let sig = format_sig(&name_str, &type_str);
                    let mut markdown = format!("```purescript\n{sig}\n```");
                    if !doc_comments.is_empty() {
                        markdown.push_str("\n\n---\n\n");
                        for doc in &doc_comments {
                            markdown.push_str(doc.trim());
                            markdown.push('\n');
                        }
                    }
                    return Some(Hover {
                        contents: HoverContents::Markup(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: markdown,
                        }),
                        range: None,
                    });
                }
            }
        }
        None
    }

    async fn get_imported_type_by_name(&self, module_name: &str, name_str: &str) -> Option<String> {
        let registry = self.registry.read().await;
        let mod_exports = registry.get(module_name)?;
        mod_exports
            .values
            .get(name_str)
            .map(|scheme| fmt_ty(&scheme.ty))
    }

    async fn get_imported_doc_comments(&self, module_name: &str, symbol: interner::Symbol) -> Vec<String> {
        // Find the source file for this module and parse it to extract doc-comments
        let target_uri = {
            let mf = self.module_file_map.read().await;
            mf.get(module_name).cloned()
        };
        let target_uri = match target_uri {
            Some(u) => u,
            None => return Vec::new(),
        };
        let target_source = match self.get_source_for_uri(&target_uri).await {
            Some(s) => s,
            None => return Vec::new(),
        };
        let target_module = match crate::parser::parse(&target_source) {
            Ok(m) => m,
            Err(_) => return Vec::new(),
        };
        find_doc_comments(&target_module.decls, symbol)
            .into_iter()
            .filter_map(|c| {
                if let cst::Comment::Doc(text) = c {
                    Some(text)
                } else {
                    None
                }
            })
            .collect()
    }

    async fn get_imported_module_doc(&self, module_name: &str) -> Vec<String> {
        // typecheck_db exports don't carry module-level docs, so source them
        // from the target module's parsed CST.
        let target_uri = {
            let mf = self.module_file_map.read().await;
            mf.get(module_name).cloned()
        };
        let target_uri = match target_uri {
            Some(u) => u,
            None => return Vec::new(),
        };
        let target_source = match self.get_source_for_uri(&target_uri).await {
            Some(s) => s,
            None => return Vec::new(),
        };
        let target_module = match crate::parser::parse(&target_source) {
            Ok(m) => m,
            Err(_) => return Vec::new(),
        };
        target_module.doc_comments.iter().filter_map(|c| {
            if let cst::Comment::Doc(text) = c { Some(text.clone()) } else { None }
        }).collect()
    }

    async fn get_local_kind(&self, module: &cst::Module, symbol: interner::Symbol) -> Option<String> {
        let module_name = interner::resolve_module_name(&module.name.value.parts);
        let name_str = interner::resolve(symbol).unwrap_or_default();
        let registry = self.registry.read().await;
        let exports = registry.get(&module_name)?;
        // `type_kinds` is a single String-keyed map covering both types and
        // classes.
        exports.type_kinds.get(&name_str).map(|kind| kind.to_string())
    }

    async fn get_type_definition_text(
        &self,
        module: &cst::Module,
        source: &str,
        target: &HoverTarget,
    ) -> Option<String> {
        match target {
            HoverTarget::TypeDeclaration(sym) => {
                find_decl_source_text(&module.decls, *sym, source, DeclTextKind::Type)
            }
            HoverTarget::ValueDeclaration(sym) => {
                find_decl_source_text(&module.decls, *sym, source, DeclTextKind::Value)
            }
            HoverTarget::Reference(resolved) => {
                let kind = match resolved.namespace {
                    Namespace::Type | Namespace::Class => DeclTextKind::Type,
                    Namespace::Value => DeclTextKind::Value,
                    _ => return None,
                };
                let full_name = interner::resolve(resolved.src_symbol).unwrap_or_default();
                let name_str = full_name.rsplit('.').next().unwrap_or(&full_name);
                let name_sym = interner::intern(name_str);
                match &resolved.definition {
                    DefinitionSite::Local(_) => {
                        find_decl_source_text(&module.decls, name_sym, source, kind)
                    }
                    DefinitionSite::LocalVar(_) => None,
                    DefinitionSite::Imported(module_sym) => {
                        let module_name = interner::resolve(*module_sym).unwrap_or_default();
                        self.get_imported_decl_source(&module_name, name_sym, kind)
                            .await
                    }
                    DefinitionSite::Prim => None,
                }
            }
        }
    }

    async fn get_imported_decl_source(
        &self,
        module_name: &str,
        symbol: interner::Symbol,
        kind: DeclTextKind,
    ) -> Option<String> {
        let target_uri = {
            let mf = self.module_file_map.read().await;
            mf.get(module_name).cloned()
        }?;
        let target_source = self.get_source_for_uri(&target_uri).await?;
        let target_module = crate::parser::parse(&target_source).ok()?;
        find_decl_source_text(&target_module.decls, symbol, &target_source, kind)
    }

    async fn get_imported_type(&self, module_sym: interner::Symbol, name_str: &str) -> Option<String> {
        let module_name = interner::resolve(module_sym).unwrap_or_default();
        let registry = self.registry.read().await;
        let mod_exports = registry.get(&module_name)?;
        if let Some(scheme) = mod_exports.values.get(name_str) {
            return Some(fmt_ty(&scheme.ty));
        }
        // Constructors live in `ctors`, not `values`.
        mod_exports.ctors.get(name_str).map(ctor_type_string)
    }

    async fn get_imported_kind(&self, module_sym: interner::Symbol, name_str: &str) -> Option<String> {
        let module_name = interner::resolve(module_sym).unwrap_or_default();
        self.get_imported_kind_by_name(&module_name, name_str).await
    }

    async fn get_imported_kind_by_name(&self, module_name: &str, name_str: &str) -> Option<String> {
        // Try registry first (has inferred kinds from kind checker). `type_kinds`
        // is String-keyed and covers both types and classes.
        {
            let registry = self.registry.read().await;
            if let Some(mod_exports) = registry.get(module_name) {
                if let Some(kind) = mod_exports.type_kinds.get(name_str) {
                    return Some(kind.to_string());
                }
            }
        }

        // Fall back to CST kind annotation
        let target_uri = {
            let mf = self.module_file_map.read().await;
            mf.get(module_name).cloned()
        }?;
        let target_source = self.get_source_for_uri(&target_uri).await?;
        let target_module = crate::parser::parse(&target_source).ok()?;
        find_cst_kind(&target_module.decls, name_str, &target_source)
    }
}

#[derive(Clone, Copy)]
enum DeclTextKind {
    Type,
    Value,
}

/// Extract the source text of a matching declaration, truncated to 1000 characters
/// (with an ellipsis when truncated). `kind` controls which declaration flavors to
/// consider: `Type` covers data/newtype/type-alias/class/foreign-data; `Value` covers
/// value bindings and foreign imports (prefixed with their type signature if present).
fn find_decl_source_text(
    decls: &[Decl],
    symbol: interner::Symbol,
    source: &str,
    kind: DeclTextKind,
) -> Option<String> {
    let mut sig_text: Option<&str> = None;
    for decl in decls {
        let (match_kind, decl_sym, span) = match decl {
            // Skip standalone kind signatures (`data Foo :: Kind`, `type Foo :: Kind`, etc.) —
            // they share a name with the real declaration but don't contain its definition.
            Decl::Data { kind_sig, .. } if !matches!(kind_sig, cst::KindSigSource::None) => {
                continue;
            }
            Decl::Class { is_kind_sig: true, .. } => continue,
            Decl::Data { is_role_decl: true, .. } => continue,
            Decl::Data { name, span, .. } => (DeclTextKind::Type, name.value.symbol(), *span),
            Decl::TypeAlias { name, span, .. } => (DeclTextKind::Type, name.value.symbol(), *span),
            Decl::Newtype { name, span, .. } => (DeclTextKind::Type, name.value.symbol(), *span),
            Decl::Class { name, span, .. } => (DeclTextKind::Type, name.value.symbol(), *span),
            Decl::ForeignData { name, span, .. } => (DeclTextKind::Type, name.value.symbol(), *span),
            Decl::TypeSignature { name, span, .. } => {
                if matches!(kind, DeclTextKind::Value) && name.value.symbol() == symbol {
                    sig_text = source.get(span.start..span.end);
                }
                continue;
            }
            Decl::Value { name, span, .. } => (DeclTextKind::Value, name.value.symbol(), *span),
            Decl::Foreign { name, span, .. } => (DeclTextKind::Value, name.value.symbol(), *span),
            _ => continue,
        };
        if decl_sym != symbol {
            continue;
        }
        let matches_kind = matches!(
            (kind, match_kind),
            (DeclTextKind::Type, DeclTextKind::Type) | (DeclTextKind::Value, DeclTextKind::Value)
        );
        if !matches_kind {
            continue;
        }
        let body = source.get(span.start..span.end)?;
        let combined = match (kind, sig_text) {
            (DeclTextKind::Value, Some(sig)) => format!("{sig}\n{body}"),
            _ => body.to_string(),
        };
        return Some(truncate_to_chars(&combined, 1000));
    }
    // Value-namespace fallback: the symbol may be a data/newtype constructor. Return the
    // parent declaration so hover shows the type the constructor belongs to.
    if matches!(kind, DeclTextKind::Value) {
        for decl in decls {
            match decl {
                Decl::Data {
                    span,
                    constructors,
                    kind_sig,
                    is_role_decl,
                    ..
                } if matches!(kind_sig, cst::KindSigSource::None) && !is_role_decl => {
                    if constructors.iter().any(|c| c.name.value.symbol() == symbol) {
                        let text = source.get(span.start..span.end)?;
                        return Some(truncate_to_chars(text, 1000));
                    }
                }
                Decl::Newtype {
                    span, constructor, ..
                } if constructor.value.symbol() == symbol => {
                    let text = source.get(span.start..span.end)?;
                    return Some(truncate_to_chars(text, 1000));
                }
                _ => {}
            }
        }
    }
    None
}

fn truncate_to_chars(s: &str, max_chars: usize) -> String {
    let mut char_count = 0;
    for (i, _) in s.char_indices() {
        if char_count == max_chars {
            return format!("{}…", &s[..i]);
        }
        char_count += 1;
    }
    s.to_string()
}

/// Check if the offset falls on a declaration name (the definition site itself).
/// Returns (symbol, is_type_decl).
fn find_decl_name_at_offset(decls: &[Decl], offset: usize) -> Option<(interner::Symbol, bool)> {
    for decl in decls {
        let name_info: Option<(interner::Symbol, crate::span::Span, bool)> = match decl {
            Decl::Value { name, .. } => Some((name.value.symbol(), name.span, false)),
            Decl::TypeSignature { name, .. } => Some((name.value.symbol(), name.span, false)),
            Decl::Data { name, .. } => Some((name.value.symbol(), name.span, true)),
            Decl::TypeAlias { name, .. } => Some((name.value.symbol(), name.span, true)),
            Decl::Newtype { name, .. } => Some((name.value.symbol(), name.span, true)),
            Decl::Class { name, members, .. } => {
                // Check class name
                if offset >= name.span.start && offset < name.span.end {
                    return Some((name.value.symbol(), true));
                }
                // Check class member names
                for member in members {
                    if offset >= member.name.span.start && offset < member.name.span.end {
                        return Some((member.name.value.symbol(), false));
                    }
                }
                None
            }
            Decl::Foreign { name, .. } => Some((name.value.symbol(), name.span, false)),
            Decl::ForeignData { name, .. } => Some((name.value.symbol(), name.span, true)),
            _ => None,
        };
        if let Some((sym, span, is_type)) = name_info {
            if offset >= span.start && offset < span.end {
                return Some((sym, is_type));
            }
        }
    }
    None
}

/// Extract a type signature string from the CST for declarations not in CheckResult.types
/// (foreign imports, class methods, type signatures without corresponding values).
fn find_cst_type_signature(decls: &[Decl], symbol: interner::Symbol, source: &str) -> Option<String> {
    for decl in decls {
        match decl {
            Decl::Foreign { name, ty, .. } if name.value.symbol() == symbol => {
                let span = ty.span();
                return Some(source[span.start..span.end].to_string());
            }
            Decl::TypeSignature { name, ty, .. } if name.value.symbol() == symbol => {
                let span = ty.span();
                return Some(source[span.start..span.end].to_string());
            }
            Decl::Class { members, .. } => {
                for member in members {
                    if member.name.value.symbol() == symbol {
                        let span = member.ty.span();
                        return Some(source[span.start..span.end].to_string());
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// Find doc-comments attached to a declaration with the given name.
fn find_doc_comments(decls: &[Decl], symbol: interner::Symbol) -> Vec<Comment> {
    for decl in decls {
        // Check class members
        if let Decl::Class { members, .. } = decl {
            for member in members {
                if member.name.value.symbol() == symbol && !member.doc_comments.is_empty() {
                    return member.doc_comments.clone();
                }
            }
        }

        let decl_sym = match decl {
            Decl::Value { name, .. } => Some(name.value.symbol()),
            Decl::TypeSignature { name, .. } => Some(name.value.symbol()),
            Decl::Data { name, .. } => Some(name.value.symbol()),
            Decl::TypeAlias { name, .. } => Some(name.value.symbol()),
            Decl::Newtype { name, .. } => Some(name.value.symbol()),
            Decl::Class { name, .. } => Some(name.value.symbol()),
            Decl::Foreign { name, .. } => Some(name.value.symbol()),
            Decl::ForeignData { name, .. } => Some(name.value.symbol()),
            _ => None,
        };
        if decl_sym == Some(symbol) {
            let docs = decl.doc_comments();
            if !docs.is_empty() {
                return docs.to_vec();
            }
        }
    }
    Vec::new()
}

/// Extract a kind annotation string from a source module's CST for a type/class/foreign-data declaration.
fn find_cst_kind(decls: &[Decl], name_str: &str, source: &str) -> Option<String> {
    let target_sym = interner::intern(name_str);
    for decl in decls {
        match decl {
            Decl::ForeignData { name, kind, .. } if name.value.symbol() == target_sym => {
                let span = kind.span();
                return Some(source[span.start..span.end].to_string());
            }
            _ => {}
        }
    }
    // Default for classes and data types without explicit kind
    Some("Type".to_string())
}
