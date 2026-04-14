use std::collections::HashMap;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use crate::cst::{Import, ImportDecl, ImportList, Module};
use crate::lsp::utils::find_definition::position_to_offset;
use crate::span::Span;

use super::super::Backend;

impl Backend {
    pub(crate) async fn handle_code_action(
        &self,
        params: CodeActionParams,
    ) -> Result<Option<CodeActionResponse>> {
        let uri = params.text_document.uri;
        let source = {
            let files = self.files.read().await;
            files.get(&uri.to_string()).map(|f| f.source.clone())
        };
        let source = match source {
            Some(s) => s,
            None => return Ok(None),
        };

        let module = crate::parser::parse(&source).ok();

        let mut actions: Vec<CodeActionOrCommand> = Vec::new();
        let mut unused_import_diags: Vec<&Diagnostic> = Vec::new();
        for diag in &params.context.diagnostics {
            let Some(code_str) = diag_code(diag) else { continue };
            match code_str.as_str() {
                "TypeWarning.UnusedName" => {
                    if let Some(action) =
                        prefix_underscore_action(&uri, &source, diag)
                    {
                        actions.push(CodeActionOrCommand::CodeAction(action));
                    }
                }
                "TypeWarning.UnusedImport" => {
                    unused_import_diags.push(diag);
                    if let Some(module) = &module {
                        if let Some(action) =
                            remove_import_action(&uri, &source, module, diag)
                        {
                            actions.push(CodeActionOrCommand::CodeAction(action));
                        }
                    }
                }
                _ => {}
            }
        }

        if unused_import_diags.len() >= 2 {
            if let Some(module) = &module {
                if let Some(action) =
                    remove_all_imports_action(&uri, &source, module, &unused_import_diags)
                {
                    actions.push(CodeActionOrCommand::CodeAction(action));
                }
            }
        }

        if actions.is_empty() {
            Ok(None)
        } else {
            Ok(Some(actions))
        }
    }
}

fn diag_code(diag: &Diagnostic) -> Option<String> {
    match &diag.code {
        Some(NumberOrString::String(s)) => Some(s.clone()),
        _ => None,
    }
}

fn prefix_underscore_action(
    uri: &Url,
    source: &str,
    diag: &Diagnostic,
) -> Option<CodeAction> {
    let (start, _) = range_to_offsets(source, diag.range)?;
    let insert_pos = Position {
        line: diag.range.start.line,
        character: diag.range.start.character,
    };
    let name_text = name_at_offset(source, start)?;
    let edit = TextEdit {
        range: Range {
            start: insert_pos,
            end: insert_pos,
        },
        new_text: "_".to_string(),
    };
    let workspace_edit = WorkspaceEdit {
        changes: Some(single_change(uri, vec![edit])),
        ..Default::default()
    };
    Some(CodeAction {
        title: format!("Prefix '{name_text}' with underscore"),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![diag.clone()]),
        edit: Some(workspace_edit),
        is_preferred: Some(true),
        ..Default::default()
    })
}

fn remove_import_action(
    uri: &Url,
    source: &str,
    module: &Module,
    diag: &Diagnostic,
) -> Option<CodeAction> {
    let (start, end) = range_to_offsets(source, diag.range)?;
    let target = Span { start, end };
    let (decl, item_idx, items_len) = find_import_item(module, target)?;
    let name_text = name_at_offset(source, start).unwrap_or_default();

    let edit = if items_len == 1 {
        delete_line_edit(source, decl.span)
    } else {
        delete_item_with_comma_edit(source, decl, item_idx)?
    };

    let workspace_edit = WorkspaceEdit {
        changes: Some(single_change(uri, vec![edit])),
        ..Default::default()
    };
    Some(CodeAction {
        title: format!("Remove unused import '{name_text}'"),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![diag.clone()]),
        edit: Some(workspace_edit),
        is_preferred: Some(true),
        ..Default::default()
    })
}

fn remove_all_imports_action(
    uri: &Url,
    source: &str,
    module: &Module,
    diagnostics: &[&Diagnostic],
) -> Option<CodeAction> {
    let targets: Vec<Span> = diagnostics
        .iter()
        .filter_map(|d| {
            range_to_offsets(source, d.range).map(|(start, end)| Span { start, end })
        })
        .collect();

    let mut edits: Vec<TextEdit> = Vec::new();

    for decl in &module.imports {
        let items = match &decl.imports {
            Some(ImportList::Explicit(items)) => items,
            _ => continue,
        };
        let unused: Vec<usize> = items
            .iter()
            .enumerate()
            .filter_map(|(i, item)| {
                let sp = import_item_span(item);
                if targets.iter().any(|t| t.start == sp.start && t.end == sp.end) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect();

        if unused.is_empty() {
            continue;
        }
        if unused.len() == items.len() {
            edits.push(delete_line_edit(source, decl.span));
            continue;
        }

        let mut i = 0;
        while i < items.len() {
            if !unused.contains(&i) {
                i += 1;
                continue;
            }
            let run_start = i;
            let mut run_end = i;
            while run_end + 1 < items.len() && unused.contains(&(run_end + 1)) {
                run_end += 1;
            }

            let (del_start, del_end) = if run_start == 0 {
                let next_start = import_item_span(&items[run_end + 1]).start;
                (import_item_span(&items[run_start]).start, next_start)
            } else {
                let prev_end = import_item_span(&items[run_start - 1]).end;
                let item_start = import_item_span(&items[run_start]).start;
                let comma_start = find_comma_start(source, prev_end, item_start)?;
                (comma_start, import_item_span(&items[run_end]).end)
            };
            let range = byte_span_to_range(source, del_start, del_end)?;
            edits.push(TextEdit {
                range,
                new_text: String::new(),
            });
            i = run_end + 1;
        }
    }

    if edits.is_empty() {
        return None;
    }

    let diag_clones: Vec<Diagnostic> = diagnostics.iter().map(|d| (*d).clone()).collect();
    let workspace_edit = WorkspaceEdit {
        changes: Some(single_change(uri, edits)),
        ..Default::default()
    };
    Some(CodeAction {
        title: format!("Remove all unused imports ({})", diagnostics.len()),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(diag_clones),
        edit: Some(workspace_edit),
        ..Default::default()
    })
}

fn find_import_item(module: &Module, target: Span) -> Option<(&ImportDecl, usize, usize)> {
    for decl in &module.imports {
        let items = match &decl.imports {
            Some(ImportList::Explicit(items)) | Some(ImportList::Hiding(items)) => items,
            None => continue,
        };
        for (idx, item) in items.iter().enumerate() {
            let sp = import_item_span(item);
            if sp.start == target.start && sp.end == target.end {
                return Some((decl, idx, items.len()));
            }
        }
    }
    None
}

fn import_item_span(item: &Import) -> Span {
    match item {
        Import::Value(s) => s.span,
        Import::Type(s, _) => s.span,
        Import::TypeOp(s) => s.span,
        Import::Class(s) => s.span,
    }
}

/// Delete an item + an adjacent comma (prefer the preceding comma for non-first items,
/// otherwise the trailing comma).
fn delete_item_with_comma_edit(
    source: &str,
    decl: &ImportDecl,
    item_idx: usize,
) -> Option<TextEdit> {
    let items = match &decl.imports {
        Some(ImportList::Explicit(items)) | Some(ImportList::Hiding(items)) => items,
        None => return None,
    };
    let item_span = import_item_span(&items[item_idx]);

    let (del_start, del_end) = if item_idx == 0 {
        // Remove item and the following comma + whitespace up to the next item's start.
        let next_start = import_item_span(&items[1]).start;
        (item_span.start, next_start)
    } else {
        // Remove preceding comma + whitespace up to this item and the item itself.
        let prev_end = import_item_span(&items[item_idx - 1]).end;
        let comma_start = find_comma_start(source, prev_end, item_span.start)?;
        (comma_start, item_span.end)
    };

    let range = byte_span_to_range(source, del_start, del_end)?;
    Some(TextEdit {
        range,
        new_text: String::new(),
    })
}

fn find_comma_start(source: &str, from: usize, to: usize) -> Option<usize> {
    source[from..to].find(',').map(|rel| from + rel)
}

fn delete_line_edit(source: &str, span: Span) -> TextEdit {
    let line_start = source[..span.start].rfind('\n').map_or(0, |i| i + 1);
    let line_end = source[span.end..]
        .find('\n')
        .map_or(source.len(), |i| span.end + i + 1);
    let range = byte_span_to_range(source, line_start, line_end).unwrap_or(Range {
        start: Position { line: 0, character: 0 },
        end: Position { line: 0, character: 0 },
    });
    TextEdit {
        range,
        new_text: String::new(),
    }
}

fn range_to_offsets(source: &str, range: Range) -> Option<(usize, usize)> {
    let start = position_to_offset(source, range.start.line, range.start.character)?;
    let end = position_to_offset(source, range.end.line, range.end.character)?;
    Some((start, end))
}

fn byte_span_to_range(source: &str, start: usize, end: usize) -> Option<Range> {
    let sp = Span { start, end };
    let (s, e) = sp.to_pos(source)?;
    Some(Range {
        start: Position {
            line: s.line.saturating_sub(1) as u32,
            character: s.column.saturating_sub(1) as u32,
        },
        end: Position {
            line: e.line.saturating_sub(1) as u32,
            character: e.column.saturating_sub(1) as u32,
        },
    })
}

fn name_at_offset(source: &str, start: usize) -> Option<&str> {
    let rest = source.get(start..)?;
    let end = rest
        .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
        .unwrap_or(rest.len());
    Some(&rest[..end])
}

fn single_change(uri: &Url, edits: Vec<TextEdit>) -> HashMap<Url, Vec<TextEdit>> {
    let mut changes = HashMap::new();
    changes.insert(uri.clone(), edits);
    changes
}
