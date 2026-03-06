use std::sync::atomic::Ordering;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use crate::cst::{self, unqualified_ident, Comment, Decl};
use crate::interner;
use crate::lsp::utils::find_definition::position_to_offset;
use crate::lsp::utils::resolve::{self, DefinitionSite, Namespace};

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
        if !self.ready.load(Ordering::SeqCst) {
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
            return Ok(None);
        };

        let (symbol, name_str, type_str, namespace) = match &target {
            HoverTarget::Reference(resolved_name) => {
                let name_str = interner::resolve(resolved_name.src_symbol).unwrap_or_default();

                let type_str = match &resolved_name.definition {
                    DefinitionSite::Local(_) => {
                        self.get_local_type(&module, resolved_name.src_symbol, &source).await
                    }
                    DefinitionSite::LocalVar(local_span) => {
                        self.get_local_var_type(&module, *local_span).await
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

        // Look up doc-comments: local CST first, then imported module
        let doc_comments = find_doc_comments(&module.decls, symbol);
        let imported_docs = if doc_comments.is_empty() {
            if let HoverTarget::Reference(resolved_name) = &target {
                if let DefinitionSite::Imported(module_sym) = &resolved_name.definition {
                    let module_name = interner::resolve(*module_sym).unwrap_or_default();
                    self.get_imported_doc_comments(&module_name, symbol).await
                } else {
                    Vec::new()
                }
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Build markdown content
        let mut markdown = format!("```purescript\n{name_str} :: {type_str}\n```");

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

    async fn get_local_var_type(&self, module: &cst::Module, span: crate::span::Span) -> Option<String> {
        let registry = self.registry.read().await;
        let check_result = crate::typechecker::check_module_with_registry(module, &registry);
        check_result.span_types.get(&span).map(|ty| format!("{ty}"))
    }

    async fn get_local_type(&self, module: &cst::Module, symbol: interner::Symbol, source: &str) -> Option<String> {
        let registry = self.registry.read().await;
        let check_result = crate::typechecker::check_module_with_registry(module, &registry);
        if let Some(ty) = check_result.types.get(&symbol) {
            return Some(format!("{ty}"));
        }
        // Fall back to CST type signatures for declarations not in CheckResult.types
        // (foreign imports, class methods, etc.)
        find_cst_type_signature(&module.decls, symbol, source)
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
            let items = match &import_decl.imports {
                Some(ImportList::Explicit(items)) | Some(ImportList::Hiding(items)) => items,
                None => continue,
            };
            for item in items {
                let spanned = item.spanned_name();
                if offset >= spanned.span.start && offset < spanned.span.end {
                    let symbol = spanned.value;
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
                    let mut markdown = format!("```purescript\n{name_str} :: {type_str}\n```");
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
        let module_parts: Vec<interner::Symbol> = module_name
            .split('.')
            .map(|s| interner::intern(s))
            .collect();
        let registry = self.registry.read().await;
        let mod_exports = registry.lookup(&module_parts)?;
        let qi = unqualified_ident(name_str);
        mod_exports
            .values
            .get(&qi)
            .map(|scheme| format!("{}", scheme.ty))
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
        let target_source = {
            let sm = self.source_map.read().await;
            sm.get(&target_uri).cloned()
        };
        let target_source = match target_source {
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

    async fn get_local_kind(&self, module: &cst::Module, symbol: interner::Symbol) -> Option<String> {
        let registry = self.registry.read().await;
        let check_result = crate::typechecker::check_module_with_registry(module, &registry);
        if let Some(kind) = check_result.exports.class_type_kinds.get(&symbol) {
            return Some(format!("{kind}"));
        }
        if let Some(kind) = check_result.exports.type_kinds.get(&symbol) {
            return Some(format!("{kind}"));
        }
        None
    }

    async fn get_imported_type(&self, module_sym: interner::Symbol, name_str: &str) -> Option<String> {
        let module_name = interner::resolve(module_sym).unwrap_or_default();
        let module_parts: Vec<interner::Symbol> = module_name
            .split('.')
            .map(|s| interner::intern(s))
            .collect();

        let registry = self.registry.read().await;
        let mod_exports = registry.lookup(&module_parts)?;
        let qi = unqualified_ident(name_str);
        mod_exports
            .values
            .get(&qi)
            .map(|scheme| format!("{}", scheme.ty))
    }

    async fn get_imported_kind(&self, module_sym: interner::Symbol, name_str: &str) -> Option<String> {
        let module_name = interner::resolve(module_sym).unwrap_or_default();
        self.get_imported_kind_by_name(&module_name, name_str).await
    }

    async fn get_imported_kind_by_name(&self, module_name: &str, name_str: &str) -> Option<String> {
        let module_parts: Vec<interner::Symbol> = module_name
            .split('.')
            .map(|s| interner::intern(s))
            .collect();
        let name_sym = interner::intern(name_str);

        // Try registry first (has inferred kinds from kind checker)
        {
            let registry = self.registry.read().await;
            if let Some(mod_exports) = registry.lookup(&module_parts) {
                if let Some(kind) = mod_exports.class_type_kinds.get(&name_sym) {
                    return Some(format!("{kind}"));
                }
                if let Some(kind) = mod_exports.type_kinds.get(&name_sym) {
                    return Some(format!("{kind}"));
                }
            }
        }

        // Fall back to CST kind annotation
        let target_uri = {
            let mf = self.module_file_map.read().await;
            mf.get(module_name).cloned()
        }?;
        let target_source = {
            let sm = self.source_map.read().await;
            sm.get(&target_uri).cloned()
        }?;
        let target_module = crate::parser::parse(&target_source).ok()?;
        find_cst_kind(&target_module.decls, name_str, &target_source)
    }
}

/// Check if the offset falls on a declaration name (the definition site itself).
/// Returns (symbol, is_type_decl).
fn find_decl_name_at_offset(decls: &[Decl], offset: usize) -> Option<(interner::Symbol, bool)> {
    for decl in decls {
        let name_info = match decl {
            Decl::Value { name, .. } => Some((name.value, name.span, false)),
            Decl::TypeSignature { name, .. } => Some((name.value, name.span, false)),
            Decl::Data { name, .. } => Some((name.value, name.span, true)),
            Decl::TypeAlias { name, .. } => Some((name.value, name.span, true)),
            Decl::Newtype { name, .. } => Some((name.value, name.span, true)),
            Decl::Class { name, members, .. } => {
                // Check class name
                if offset >= name.span.start && offset < name.span.end {
                    return Some((name.value, true));
                }
                // Check class member names
                for member in members {
                    if offset >= member.name.span.start && offset < member.name.span.end {
                        return Some((member.name.value, false));
                    }
                }
                None
            }
            Decl::Foreign { name, .. } => Some((name.value, name.span, false)),
            Decl::ForeignData { name, .. } => Some((name.value, name.span, true)),
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
            Decl::Foreign { name, ty, .. } if name.value == symbol => {
                let span = ty.span();
                return Some(source[span.start..span.end].to_string());
            }
            Decl::TypeSignature { name, ty, .. } if name.value == symbol => {
                let span = ty.span();
                return Some(source[span.start..span.end].to_string());
            }
            Decl::Class { members, .. } => {
                for member in members {
                    if member.name.value == symbol {
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
                if member.name.value == symbol && !member.doc_comments.is_empty() {
                    return member.doc_comments.clone();
                }
            }
        }

        let decl_name = match decl {
            Decl::Value { name, .. }
            | Decl::TypeSignature { name, .. }
            | Decl::Data { name, .. }
            | Decl::TypeAlias { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::Class { name, .. }
            | Decl::Foreign { name, .. }
            | Decl::ForeignData { name, .. } => Some(name.value),
            _ => None,
        };
        if decl_name == Some(symbol) {
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
            Decl::ForeignData { name, kind, .. } if name.value == target_sym => {
                let span = kind.span();
                return Some(source[span.start..span.end].to_string());
            }
            _ => {}
        }
    }
    // Default for classes and data types without explicit kind
    Some("Type".to_string())
}
