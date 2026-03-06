use std::sync::atomic::Ordering;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use crate::cst::{self, unqualified_ident, Comment, Decl};
use crate::interner;
use crate::lsp::utils::find_definition::position_to_offset;
use crate::typechecker::resolve::{self, DefinitionSite, Namespace};

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
                    DefinitionSite::Local(_) | DefinitionSite::LocalVar(_) => {
                        self.get_local_type(&module, resolved_name.src_symbol).await
                    }
                    DefinitionSite::Imported(module_sym) => {
                        self.get_imported_type(*module_sym, &name_str).await
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
                let type_str = self.get_local_type(&module, *sym).await;
                match type_str {
                    Some(s) => (*sym, name_str, s, Namespace::Value),
                    None => return Ok(None),
                }
            }
            HoverTarget::TypeDeclaration(sym) => {
                let name_str = interner::resolve(*sym).unwrap_or_default();
                // For type declarations, show the kind
                (*sym, name_str, "Type".to_string(), Namespace::Type)
            }
        };

        // Look up doc-comments from the CST
        let doc_comments = find_doc_comments(&module.decls, symbol);

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
        }

        // For type references (Prim kind), adjust the display
        if matches!(target, HoverTarget::Reference(ref r) if matches!(r.namespace, Namespace::Type | Namespace::Class)) {
            let _ = namespace; // used above
        }

        Ok(Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: markdown,
            }),
            range: None,
        }))
    }

    async fn get_local_type(&self, module: &cst::Module, symbol: interner::Symbol) -> Option<String> {
        let registry = self.registry.read().await;
        let check_result = crate::typechecker::check_module_with_registry(module, &registry);
        check_result
            .types
            .get(&symbol)
            .map(|ty| format!("{ty}"))
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
            Decl::Class { name, .. } => Some((name.value, name.span, true)),
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

/// Find doc-comments attached to a declaration with the given name.
fn find_doc_comments(decls: &[Decl], symbol: interner::Symbol) -> Vec<Comment> {
    for decl in decls {
        let decl_name = match decl {
            Decl::Value { name, .. } => Some(name.value),
            Decl::TypeSignature { name, .. } => Some(name.value),
            Decl::Data { name, .. } => Some(name.value),
            Decl::TypeAlias { name, .. } => Some(name.value),
            Decl::Newtype { name, .. } => Some(name.value),
            Decl::Class { name, .. } => Some(name.value),
            Decl::Foreign { name, .. } => Some(name.value),
            Decl::ForeignData { name, .. } => Some(name.value),
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
