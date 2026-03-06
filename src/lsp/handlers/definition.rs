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

        // Check if the cursor is on an import item — these have spans now
        if let Some(result) = self.find_import_item_definition(&module, offset).await {
            return Ok(Some(result));
        }

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

                    // If direct lookup fails, try re-export fallback
                    // (e.g. `add` imported from Prelude but defined in Data.Semiring)
                    let def_loc_owned;
                    let def_loc = if def_loc.is_some() {
                        def_loc
                    } else {
                        match def_index.find_reexport(resolved_name.src_symbol, resolved_name.namespace) {
                            Some((reexport_module, loc)) => {
                                // Update target URI to the actual defining module
                                let reexport_uri = {
                                    let mf = self.module_file_map.read().await;
                                    mf.get(reexport_module).cloned()
                                };
                                if let Some(reexport_uri) = reexport_uri {
                                    let target_source = {
                                        let sm = self.source_map.read().await;
                                        sm.get(&reexport_uri).cloned()
                                    };
                                    if let Some(target_source) = target_source {
                                        if let Ok(parsed_uri) = Url::parse(&reexport_uri) {
                                            if let Some(loc) = span_to_location(&parsed_uri, &target_source, loc.span) {
                                                return Ok(Some(GotoDefinitionResponse::Scalar(loc)));
                                            }
                                        }
                                    }
                                }
                                def_loc_owned = loc.clone();
                                Some(&def_loc_owned)
                            }
                            None => None,
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

    /// Check if the cursor offset falls on an import item name.
    /// If so, look up the definition in the import's source module.
    async fn find_import_item_definition(
        &self,
        module: &crate::cst::Module,
        offset: usize,
    ) -> Option<GotoDefinitionResponse> {
        use crate::cst::{Import, ImportList, DataMembers};

        for import_decl in &module.imports {
            // Quick bounds check: is offset within this import's span?
            if offset < import_decl.span.start || offset >= import_decl.span.end {
                continue;
            }

            let items = match &import_decl.imports {
                Some(ImportList::Explicit(items)) | Some(ImportList::Hiding(items)) => items,
                None => continue,
            };

            // Check each import item's span
            for item in items {
                let spanned = item.spanned_name();
                if offset >= spanned.span.start && offset < spanned.span.end {
                    let symbol = spanned.value;
                    let namespace = match item {
                        Import::Value(_) => Namespace::Value,
                        Import::Type(_, _) => Namespace::Type,
                        Import::TypeOp(_) => Namespace::TypeOperator,
                        Import::Class(_) => Namespace::Class,
                    };
                    let module_name = crate::interner::resolve_module_name(&import_decl.module.parts);
                    return self.resolve_import_symbol(&module_name, symbol, namespace).await;
                }

                // Also check DataMembers::Explicit constructor names
                if let Import::Type(_, Some(DataMembers::Explicit(ctors))) = item {
                    for ctor in ctors {
                        if offset >= ctor.span.start && offset < ctor.span.end {
                            let module_name = crate::interner::resolve_module_name(&import_decl.module.parts);
                            return self.resolve_import_symbol(&module_name, ctor.value, Namespace::Value).await;
                        }
                    }
                }
            }
        }
        None
    }

    /// Resolve a symbol from an import to its definition location.
    async fn resolve_import_symbol(
        &self,
        module_name: &str,
        symbol: crate::interner::Symbol,
        namespace: Namespace,
    ) -> Option<GotoDefinitionResponse> {
        let def_index = self.def_index.read().await;
        let key = (module_name.to_string(), symbol);

        // Try direct lookup in the import source module
        let def_loc = match namespace {
            Namespace::Value => def_index.values.get(&key)
                .or_else(|| def_index.constructors.get(&key)),
            Namespace::Type | Namespace::Class | Namespace::TypeOperator => {
                def_index.types.get(&key)
                    .or_else(|| def_index.constructors.get(&key))
            }
        };

        // Fall back to re-export search (e.g. Prelude re-exports from Data.Semiring)
        let reexport;
        let (target_module, def_loc) = if let Some(loc) = def_loc {
            (module_name.to_string(), loc)
        } else {
            reexport = def_index.find_reexport(symbol, namespace)?;
            (reexport.0.clone(), reexport.1)
        };

        let target_uri = {
            let mf = self.module_file_map.read().await;
            mf.get(&target_module).cloned()
        }?;

        let target_source = {
            let sm = self.source_map.read().await;
            sm.get(&target_uri).cloned()
        }?;

        let parsed_uri = Url::parse(&target_uri).ok()?;
        let loc = span_to_location(&parsed_uri, &target_source, def_loc.span)?;
        Some(GotoDefinitionResponse::Scalar(loc))
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
