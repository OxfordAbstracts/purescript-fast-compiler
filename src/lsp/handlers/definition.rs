use std::sync::atomic::Ordering;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use crate::lsp::utils::find_definition::{self, find_ident_at_offset, position_to_offset, ImportMap};

use super::super::Backend;

impl Backend {
    pub(crate) async fn handle_goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        self.info(format!("Go to definition:\n  {:?}", params)).await;
        if !self.ready.load(Ordering::SeqCst) {
            return Ok(None);
        }

        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;

        self.info(format!("{uri}: {:?}", pos)).await;

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

        self.info(offset).await;
        // Parse the current file to get CST
        let module = match crate::parser::parse(&source) {
            Ok(m) => m,
            Err(_) => return Ok(None),
        };

        // Find what identifier is at the cursor
        let ident = match find_ident_at_offset(&module, offset) {
            Some(i) => i,
            None => return Ok(None),
        };

        self.info(format!("ident: {:?}", ident)).await;

        let current_module = format!("{}", module.name.value);

        // First try local definitions in the current file
        if ident.name.module.is_none() {
            if let Some(span) = find_definition::find_local_definition(&module, ident.name.name) {
                self.info(format!("Local span found: {:?}", span)).await;
                if let Some(loc) = span_to_location(&uri, &source, span) {
                    self.info(format!("Local def found: {:?}", loc)).await;
                    return Ok(Some(GotoDefinitionResponse::Scalar(loc)));
                }
            }
        }

        // Try cross-module definitions via the index
        let def_index = self.def_index.read().await;
        let import_map = ImportMap::from_imports(&module.imports, &def_index);

        let def_loc_opt = def_index.find(&ident, &current_module, &import_map);

        self.info(format!("def_loc_opt: {:?}", def_loc_opt)).await;

        if let Some(def_loc) = def_index.find(&ident, &current_module, &import_map) {
            self.info(format!("def_loc: {:?}", def_loc)).await;
            // Need to convert the definition span to an LSP Location
            // Get the source of the target file
            let target_uri = if def_loc.file_path.starts_with("file://") {
                def_loc.file_path.clone()
            } else {
                std::path::Path::new(&def_loc.file_path)
                    .canonicalize()
                    .ok()
                    .and_then(|p| Url::from_file_path(p).ok())
                    .map(|u| u.to_string())
                    .unwrap_or_default()
            };

            self.info(&target_uri).await;

            let target_source = {
                let sm = self.source_map.read().await;
                sm.get(&target_uri).cloned()
            };

            self.info(format!("target_source found {}", target_source.is_some())).await;

            self.info(&target_uri).await;

            if let Some(target_source) = target_source {
                let parsed_target_uri = Url::parse(&target_uri);
                self.info(format!("parsed uri: {:?}", parsed_target_uri)).await;
                if let Some(uri) = Url::parse(&target_uri).ok() {
                    self.info("target uri found").await;
                    if let Some(loc) = span_to_location(&uri, &target_source, def_loc.span) {
                        self.info(format!("found location: {:?}", loc)).await;
                        // self.info
                        return Ok(Some(GotoDefinitionResponse::Scalar(loc)));
                    }
                }
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
