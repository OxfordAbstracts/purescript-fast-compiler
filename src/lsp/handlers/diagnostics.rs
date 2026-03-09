use std::fmt::Display;
use std::sync::atomic::Ordering;

use tower_lsp::lsp_types::*;

use crate::interner;
use crate::build::cache::ModuleCache;

use super::super::{Backend, FileState};

impl Backend {
    pub(crate) async fn info<M: Display>(&self, message: M) {
        self.client
            .log_message(MessageType::INFO, message)
            .await;
    }

    pub(crate) async fn on_change(&self, uri: Url, source: String) {
        {
            let mut files = self.files.write().await;
            files.insert(
                uri.to_string(),
                FileState {
                    source: source.clone(),
                    module_name: None,
                },
            );
        }

        // Don't publish diagnostics until sources are loaded
        if !self.ready.load(Ordering::SeqCst) {
            return;
        }

        let module = match crate::parser::parse(&source) {
            Ok(module) => {
                let module_name = format!("{}", module.name.value);
                {
                    let mut files = self.files.write().await;
                    if let Some(fs) = files.get_mut(&uri.to_string()) {
                        fs.module_name = Some(module_name);
                    }
                }
                module
            }
            Err(err) => {
                let range = error_to_range(&err, &source);
                let diagnostics = vec![Diagnostic {
                    range,
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String(err.code())),
                    source: Some("pfc".to_string()),
                    message: err.get_message(),
                    ..Default::default()
                }];
                self.client
                    .publish_diagnostics(uri, diagnostics, None)
                    .await;
                return;
            }
        };

        let module_name = interner::resolve_module_name(&module.name.value.parts);
        let module_parts: Vec<interner::Symbol> = module.name.value.parts.clone();

        // Type-check against the registry (use stacker to extend stack for deep recursion)
        let mut registry = self.registry.write().await;
        let check_result = crate::typechecker::check_module_with_registry(&module, &registry);

        // Update registry with new exports
        registry.register(&module_parts, check_result.exports.clone());

        // Update cache
        let source_hash = ModuleCache::content_hash(&source);
        let import_names: Vec<String> = module.imports.iter()
            .map(|imp| interner::resolve_module_name(&imp.module.parts))
            .collect();
        let mut cache = self.module_cache.write().await;
        cache.update(module_name.clone(), source_hash, check_result.exports, import_names);
        cache.build_reverse_deps();

        // Find transitive dependents that need re-checking
        let dependents = cache.transitive_dependents(&module_name);
        drop(cache);

        // Publish diagnostics for the changed module
        let diagnostics = type_errors_to_diagnostics(&check_result.errors, &source);
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;

        // Update source map
        {
            let mfmap = self.module_file_map.read().await;
            let mut smap = self.source_map.write().await;
            // Update the changed module's source in source_map
            if let Some(file_uri) = mfmap.get(&module_name) {
                smap.insert(file_uri.clone(), source);
            }
        }

        // Cascade: re-typecheck dependents
        if !dependents.is_empty() {
            log::debug!("Cascade rebuild: {} dependents of {}", dependents.len(), module_name);

            let mfmap = self.module_file_map.read().await;
            let smap = self.source_map.read().await;

            for dep_name in &dependents {
                let dep_uri_str = match mfmap.get(dep_name) {
                    Some(u) => u.clone(),
                    None => continue,
                };
                let dep_source = match smap.get(&dep_uri_str) {
                    Some(s) => s.clone(),
                    None => continue,
                };
                let dep_uri = match Url::parse(&dep_uri_str) {
                    Ok(u) => u,
                    Err(_) => continue,
                };

                let dep_module = match crate::parser::parse(&dep_source) {
                    Ok(m) => m,
                    Err(_) => continue,
                };

                let dep_result = crate::typechecker::check_module_with_registry(&dep_module, &registry);

                // Update registry with dependent's exports
                let dep_parts: Vec<interner::Symbol> = dep_module.name.value.parts.clone();
                registry.register(&dep_parts, dep_result.exports.clone());

                // Update cache for dependent
                let dep_hash = ModuleCache::content_hash(&dep_source);
                let dep_imports: Vec<String> = dep_module.imports.iter()
                    .map(|imp| interner::resolve_module_name(&imp.module.parts))
                    .collect();
                let mut cache = self.module_cache.write().await;
                cache.update(dep_name.clone(), dep_hash, dep_result.exports, dep_imports);
                drop(cache);

                let dep_diagnostics = type_errors_to_diagnostics(&dep_result.errors, &dep_source);
                self.client
                    .publish_diagnostics(dep_uri, dep_diagnostics, None)
                    .await;
            }
        }
    }
}

fn type_errors_to_diagnostics(errors: &[crate::typechecker::error::TypeError], source: &str) -> Vec<Diagnostic> {
    errors
        .iter()
        .map(|err| {
            let span = err.span();
            let range = match span.to_pos(source) {
                Some((start, end)) => Range {
                    start: Position {
                        line: start.line.saturating_sub(1) as u32,
                        character: start.column.saturating_sub(1) as u32,
                    },
                    end: Position {
                        line: end.line.saturating_sub(1) as u32,
                        character: end.column.saturating_sub(1) as u32,
                    },
                },
                None => Range::default(),
            };
            Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String(format!("TypeError.{}", err.code()))),
                source: Some("pfc".to_string()),
                message: format!("{err}"),
                ..Default::default()
            }
        })
        .collect()
}

fn error_to_range(err: &crate::diagnostics::CompilerError, source: &str) -> Range {
    match err.get_span() {
        Some(span) => match span.to_pos(source) {
            Some((start, end)) => Range {
                start: Position {
                    line: start.line.saturating_sub(1) as u32,
                    character: start.column.saturating_sub(1) as u32,
                },
                end: Position {
                    line: end.line.saturating_sub(1) as u32,
                    character: end.column.saturating_sub(1) as u32,
                },
            },
            None => Range::default(),
        },
        None => Range::default(),
    }
}
