use std::sync::atomic::Ordering;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use crate::lsp::utils::find_definition::position_to_offset;
use crate::typechecker::resolve::{self, DefinitionSite, Namespace};

use super::super::Backend;

impl Backend {
    pub(crate) async fn handle_goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        if !self.ready.load(Ordering::SeqCst) {
            return Ok(None);
        }

        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;

        // Get the source for this file
        let source = {
            let files = self.files.read().await;
            files.get(&uri.to_string()).map(|f| f.source.clone())
        };
        let source = match source {
            Some(s) => s,
            None => return Ok(None),
        };

        // Convert LSP position to byte offset
        let offset = match position_to_offset(&source, pos.line, pos.character) {
            Some(o) => o,
            None => return Ok(None),
        };

        // Parse the current file to get CST
        let module = match crate::parser::parse(&source) {
            Ok(m) => m,
            Err(_) => return Ok(None),
        };

        // Resolve names using the project-wide resolution exports
        let exports = self.resolution_exports.read().await;
        let resolved = resolve::resolve_names(&module, &exports);
        drop(exports);

        // Look up what's at the cursor
        let resolved_name = match resolved.lookup_at(offset) {
            Some(r) => r.clone(),
            None => return Ok(None),
        };

        match &resolved_name.definition {
            DefinitionSite::Local(span) | DefinitionSite::LocalVar(span) => {
                if let Some(loc) = span_to_location(&uri, &source, *span) {
                    return Ok(Some(GotoDefinitionResponse::Scalar(loc)));
                }
            }
            DefinitionSite::Imported(module_sym) => {
                // Look up the module's file URI
                let module_name = crate::interner::resolve(*module_sym)
                    .unwrap_or_default();

                let target_uri = {
                    let mf = self.module_file_map.read().await;
                    mf.get(&module_name).cloned()
                };

                if let Some(target_uri) = target_uri {
                    // Look up the definition span via the index
                    let def_index = self.def_index.read().await;
                    let key = (module_name.clone(), resolved_name.src_symbol);
                    let def_loc = match resolved_name.namespace {
                        Namespace::Value => def_index.values.get(&key)
                            .or_else(|| def_index.constructors.get(&key)),
                        Namespace::Type | Namespace::Class | Namespace::TypeOperator => {
                            def_index.types.get(&key)
                                .or_else(|| def_index.constructors.get(&key))
                        }
                    };

                    if let Some(def_loc) = def_loc {
                        let target_source = {
                            let sm = self.source_map.read().await;
                            sm.get(&target_uri).cloned()
                        };

                        if let Some(target_source) = target_source {
                            if let Ok(parsed_uri) = Url::parse(&target_uri) {
                                if let Some(loc) = span_to_location(&parsed_uri, &target_source, def_loc.span) {
                                    return Ok(Some(GotoDefinitionResponse::Scalar(loc)));
                                }
                            }
                        }
                    }
                }
            }
            DefinitionSite::Prim => {
                // Prim types have no source location
            }
        }

        Ok(None)
    }
}

fn span_to_location(uri: &Url, source: &str, span: crate::span::Span) -> Option<Location> {
    let (start, end) = span.to_pos(source)?;
    Some(Location {
        uri: uri.clone(),
        range: Range {
            start: Position {
                line: start.line.saturating_sub(1) as u32,
                character: start.column.saturating_sub(1) as u32,
            },
            end: Position {
                line: end.line.saturating_sub(1) as u32,
                character: end.column.saturating_sub(1) as u32,
            },
        },
    })
}
