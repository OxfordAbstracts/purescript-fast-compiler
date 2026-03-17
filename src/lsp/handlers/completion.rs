use std::collections::HashSet;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use crate::cst::{self, ImportList};
use crate::interner;
use crate::lsp::utils::find_definition::position_to_offset;

use super::super::Backend;

impl Backend {
    pub(crate) async fn handle_completion(
        &self,
        params: CompletionParams,
    ) -> Result<Option<CompletionResponse>> {
        if !self.is_ready() {
            return Ok(None);
        }

        let uri = params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;

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

        // Extract the identifier prefix at the cursor position.
        // Try identifier prefix first, then operator prefix.
        let prefix = extract_prefix(&source, offset);
        let op_prefix = if prefix.is_empty() {
            extract_operator_prefix(&source, offset)
        } else {
            String::new()
        };
        if prefix.is_empty() && op_prefix.is_empty() {
            return Ok(None);
        }
        let is_operator = !op_prefix.is_empty();
        let effective_prefix = if is_operator { &op_prefix } else { &prefix };

        let module = match crate::parser::parse(&source) {
            Ok(m) => m,
            Err(_) => return Ok(None),
        };

        // Collect what's already imported in this module
        let current_module_name = interner::resolve_module_name(&module.name.value.parts);
        let already_imported = collect_imported_names(&module);

        // Find insert position for new imports (after last import, or after module header)
        let import_insert_line = find_import_insert_line(&source, &module);

        let comp_index = self.completion_index.read().await;
        let mut items = Vec::new();
        let mut seen = HashSet::new();

        // 1. Local declarations from the current module
        for decl in &module.decls {
            // Top-level declaration name
            if let Some(name_sym) = decl_name(decl) {
                let name = match interner::resolve(name_sym) {
                    Some(n) => n.to_string(),
                    None => continue,
                };
                if name.starts_with(effective_prefix) && !seen.contains(&name) {
                    seen.insert(name.clone());
                    let (kind, detail) = local_decl_info(decl);
                    items.push(CompletionItem {
                        label: name,
                        kind: Some(kind),
                        detail,
                        sort_text: Some(format!("0{}", items.len())),
                        ..Default::default()
                    });
                }
            }

            // Data constructors
            if let cst::Decl::Data { constructors, .. } = decl {
                for ctor in constructors {
                    let name = match interner::resolve(ctor.name.value) {
                        Some(n) => n.to_string(),
                        None => continue,
                    };
                    if name.starts_with(effective_prefix) && !seen.contains(&name) {
                        seen.insert(name.clone());
                        items.push(CompletionItem {
                            label: name,
                            kind: Some(CompletionItemKind::CONSTRUCTOR),
                            detail: Some("constructor".to_string()),
                            sort_text: Some(format!("0{}", items.len())),
                            ..Default::default()
                        });
                    }
                }
            }

            // Newtype constructor
            if let cst::Decl::Newtype { constructor, .. } = decl {
                let name = match interner::resolve(constructor.value) {
                    Some(n) => n.to_string(),
                    None => continue,
                };
                if name.starts_with(effective_prefix) && !seen.contains(&name) {
                    seen.insert(name.clone());
                    items.push(CompletionItem {
                        label: name,
                        kind: Some(CompletionItemKind::CONSTRUCTOR),
                        detail: Some("constructor".to_string()),
                        sort_text: Some(format!("0{}", items.len())),
                        ..Default::default()
                    });
                }
            }

            // Class members
            if let cst::Decl::Class { members, .. } = decl {
                for member in members {
                    let name = match interner::resolve(member.name.value) {
                        Some(n) => n.to_string(),
                        None => continue,
                    };
                    if name.starts_with(effective_prefix) && !seen.contains(&name) {
                        seen.insert(name.clone());
                        items.push(CompletionItem {
                            label: name,
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("class member".to_string()),
                            sort_text: Some(format!("0{}", items.len())),
                            ..Default::default()
                        });
                    }
                }
            }

            // Fixity operators
            if let cst::Decl::Fixity { operator, .. } = decl {
                let name = match interner::resolve(operator.value) {
                    Some(n) => n.to_string(),
                    None => continue,
                };
                if name.starts_with(effective_prefix) && !seen.contains(&name) {
                    seen.insert(name.clone());
                    items.push(CompletionItem {
                        label: name,
                        kind: Some(CompletionItemKind::OPERATOR),
                        detail: Some("operator".to_string()),
                        sort_text: Some(format!("0{}", items.len())),
                        ..Default::default()
                    });
                }
            }
        }

        // 2. Already-imported names (higher priority than unimported)
        // 3. All exported names from all modules via lightweight completion index
        for (mod_name, mod_entries) in &comp_index.entries {
            if mod_name == &current_module_name {
                continue;
            }

            for entry in mod_entries {
                if !entry.name.starts_with(effective_prefix) {
                    continue;
                }
                if seen.contains(&entry.name) {
                    continue;
                }
                seen.insert(entry.name.clone());

                let is_imported = already_imported.contains(&entry.name);
                let is_constructor = matches!(entry.kind, crate::lsp::CompletionEntryKind::Constructor);

                let kind = match entry.kind {
                    crate::lsp::CompletionEntryKind::Value => CompletionItemKind::FUNCTION,
                    crate::lsp::CompletionEntryKind::Constructor => CompletionItemKind::CONSTRUCTOR,
                    crate::lsp::CompletionEntryKind::Type => CompletionItemKind::CLASS,
                    crate::lsp::CompletionEntryKind::Class => CompletionItemKind::INTERFACE,
                };

                let detail = if entry.type_string.is_empty() {
                    Some(mod_name.clone())
                } else {
                    Some(format!("{mod_name} :: {}", entry.type_string))
                };

                // Imported items sort before unimported
                let sort_prefix = if is_imported { "1" } else { "2" };

                let mut item = CompletionItem {
                    label: entry.name.clone(),
                    kind: Some(kind),
                    detail,
                    sort_text: Some(format!("{sort_prefix}{}", items.len())),
                    ..Default::default()
                };

                // Auto-import: add additional_text_edits if not already imported
                if !is_imported {
                    if let Some(edit) = build_import_edit(
                        mod_name,
                        &entry.name,
                        is_constructor,
                        entry.parent_type.as_deref(),
                        &module,
                        &source,
                        import_insert_line,
                    ) {
                        item.additional_text_edits = Some(vec![edit]);
                    }
                }

                items.push(item);
            }
        }
        drop(comp_index);

        Ok(Some(CompletionResponse::List(CompletionList {
            is_incomplete: items.len() > 100,
            items,
        })))
    }
}

/// Extract the identifier prefix before the cursor position.
fn extract_prefix(source: &str, offset: usize) -> String {
    let before = &source[..offset];
    let start = before
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
        .map(|i| i + 1)
        .unwrap_or(0);
    before[start..].to_string()
}

/// Extract an operator prefix before the cursor position.
/// Operators consist of symbolic characters like +, -, *, /, <, >, =, etc.
fn extract_operator_prefix(source: &str, offset: usize) -> String {
    let before = &source[..offset];
    let start = before
        .rfind(|c: char| !is_operator_char(c))
        .map(|i| i + 1)
        .unwrap_or(0);
    before[start..].to_string()
}

fn is_operator_char(c: char) -> bool {
    matches!(c, ':' | '!' | '#' | '$' | '%' | '&' | '*' | '+' | '.' | '/' | '<' | '=' | '>' | '?' | '@' | '\\' | '^' | '|' | '-' | '~')
}

/// Collect all names that are already imported (or locally defined) in the module.
fn collect_imported_names(module: &cst::Module) -> HashSet<String> {
    let mut names = HashSet::new();

    // Local declarations
    for decl in &module.decls {
        if let Some(sym) = decl_name(decl) {
            if let Some(n) = interner::resolve(sym) {
                names.insert(n.to_string());
            }
        }
    }

    // Imported names
    for import_decl in &module.imports {
        match &import_decl.imports {
            Some(ImportList::Explicit(items)) => {
                for item in items {
                    if let Some(n) = interner::resolve(item.name()) {
                        names.insert(n.to_string());
                    }
                }
            }
            Some(ImportList::Hiding(_)) | None => {
                // `import M` or `import M hiding (...)` — we treat everything as potentially imported
                // For simplicity, we don't expand these here; the name might still need importing
                // explicitly if the user wants it. We'll be conservative and not auto-import
                // if there's a bare `import M` for that module.
            }
        }
    }

    names
}

/// Get the name symbol from a declaration.
fn decl_name(decl: &cst::Decl) -> Option<interner::Symbol> {
    match decl {
        cst::Decl::Value { name, .. }
        | cst::Decl::TypeSignature { name, .. }
        | cst::Decl::Data { name, .. }
        | cst::Decl::TypeAlias { name, .. }
        | cst::Decl::Newtype { name, .. }
        | cst::Decl::Class { name, .. }
        | cst::Decl::Foreign { name, .. }
        | cst::Decl::ForeignData { name, .. } => Some(name.value),
        _ => None,
    }
}

/// Get completion item kind and optional detail for a local declaration.
fn local_decl_info(decl: &cst::Decl) -> (CompletionItemKind, Option<String>) {
    match decl {
        cst::Decl::Value { .. } | cst::Decl::Foreign { .. } => {
            (CompletionItemKind::FUNCTION, None)
        }
        cst::Decl::TypeSignature { .. } => (CompletionItemKind::FUNCTION, None),
        cst::Decl::Data { .. } | cst::Decl::ForeignData { .. } => {
            (CompletionItemKind::CLASS, Some("data".to_string()))
        }
        cst::Decl::Newtype { .. } => (CompletionItemKind::CLASS, Some("newtype".to_string())),
        cst::Decl::TypeAlias { .. } => (CompletionItemKind::CLASS, Some("type alias".to_string())),
        cst::Decl::Class { .. } => (CompletionItemKind::INTERFACE, Some("class".to_string())),
        _ => (CompletionItemKind::TEXT, None),
    }
}

/// Find the line number (0-indexed) where new imports should be inserted.
/// This is after the last existing import, or after the module header if no imports exist.
fn find_import_insert_line(source: &str, module: &cst::Module) -> u32 {
    if let Some(last_import) = module.imports.last() {
        // Find the line number of the end of the last import
        let end = last_import.span.end;
        source[..end].chars().filter(|&c| c == '\n').count() as u32 + 1
    } else {
        // After module header line
        let header_end = module.name.span.end;
        source[..header_end].chars().filter(|&c| c == '\n').count() as u32 + 1
    }
}

/// Build a TextEdit that adds an import statement for the given name from the given module.
/// Returns None if the module already has a bare import for that module.
fn build_import_edit(
    mod_name: &str,
    name: &str,
    is_constructor: bool,
    parent_type: Option<&str>,
    module: &cst::Module,
    source: &str,
    import_insert_line: u32,
) -> Option<TextEdit> {
    // Format the import item: constructors use Type(Ctor) syntax
    let import_item = if is_constructor {
        if let Some(parent) = parent_type {
            format!("{parent}({name})")
        } else {
            name.to_string()
        }
    } else {
        name.to_string()
    };

    // Check if there's already an explicit import from this module that we can extend
    for import_decl in &module.imports {
        let import_mod_name = interner::resolve_module_name(&import_decl.module.parts);
        if import_mod_name == mod_name {
            match &import_decl.imports {
                Some(ImportList::Explicit(items)) => {
                    // Extend the existing explicit import list
                    // Find the closing paren position
                    let last_item = items.last()?;
                    let last_span = last_item.spanned_name().span;
                    // Insert after the last item, before the closing paren
                    // We need to find where in the source the `)` is after the last item
                    let after_last = &source[last_span.end..];
                    let close_paren_offset = after_last.find(')')? + last_span.end;
                    let insert_offset = close_paren_offset;
                    let (line, col) = offset_to_position(source, insert_offset);
                    return Some(TextEdit {
                        range: Range {
                            start: Position { line, character: col },
                            end: Position { line, character: col },
                        },
                        new_text: format!(", {import_item}"),
                    });
                }
                Some(ImportList::Hiding(_)) | None => {
                    // Already has a bare import or hiding import — name is likely available
                    return None;
                }
            }
        }
    }

    // No existing import for this module — add a new import line
    Some(TextEdit {
        range: Range {
            start: Position {
                line: import_insert_line,
                character: 0,
            },
            end: Position {
                line: import_insert_line,
                character: 0,
            },
        },
        new_text: format!("import {mod_name} ({import_item})\n"),
    })
}

/// Convert a byte offset to (line, character) in LSP 0-indexed coordinates.
fn offset_to_position(source: &str, offset: usize) -> (u32, u32) {
    let mut line = 0u32;
    let mut col = 0u32;
    for (i, c) in source.char_indices() {
        if i == offset {
            return (line, col);
        }
        if c == '\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }
    (line, col)
}
