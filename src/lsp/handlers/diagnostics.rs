use std::fmt::Display;

use tower_lsp::lsp_types::*;

use crate::cst::Module;
use crate::interner;
use crate::build::cache::{ModuleCache, extract_import_items};
use crate::typechecker::registry::ModuleRegistry;

use super::super::{Backend, FileState};

impl Backend {
    pub(crate) async fn info<M: Display>(&self, message: M) {
        self.client
            .log_message(MessageType::INFO, message)
            .await;
    }

    /// Ensure all modules imported by `module` have their exports loaded into the registry.
    /// Loads missing exports lazily from the ModuleCache (which reads from disk on demand).
    async fn ensure_imports_loaded(&self, module: &Module, registry: &mut ModuleRegistry) {
        for import_decl in &module.imports {
            let import_parts = &import_decl.module.parts;

            // Skip if already in registry
            if registry.lookup(import_parts).is_some() {
                continue;
            }

            let import_name = interner::resolve_module_name(import_parts);

            // Try to load from module cache (lazy disk load)
            let exports = {
                let mut cache = self.module_cache.write().await;
                cache.get_exports(&import_name).cloned()
            };

            if let Some(exports) = exports {
                registry.register(import_parts, exports);
                log::debug!("Lazy-loaded exports for {import_name}");
            }
        }
    }

    pub(crate) async fn on_change(&self, uri: Url, source: String) {
        let on_change_start = std::time::Instant::now();
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
        if !self.is_ready() {
            return;
        }

        let t = std::time::Instant::now();
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
        self.info(format!("[on_change] parse: {:.2?}", t.elapsed())).await;

        let module_name = interner::resolve_module_name(&module.name.value.parts);
        let module_parts: Vec<interner::Symbol> = module.name.value.parts.clone();

        // Ensure imported modules' exports are in the registry (lazy load from cache)
        let t = std::time::Instant::now();
        let mut registry = self.registry.write().await;
        self.ensure_imports_loaded(&module, &mut registry).await;
        self.info(format!("[on_change] ensure_imports_loaded: {:.2?}", t.elapsed())).await;

        // Type-check against the registry
        let t = std::time::Instant::now();
        let check_result = crate::typechecker::check_module_with_registry(&module, &registry);
        self.info(format!("[on_change] typecheck {module_name}: {:.2?}", t.elapsed())).await;

        // Update registry with new exports
        registry.register(&module_parts, check_result.exports.clone());

        // Update cache
        let source_hash = ModuleCache::content_hash(&source);
        let import_names: Vec<String> = module.imports.iter()
            .map(|imp| interner::resolve_module_name(&imp.module.parts))
            .collect();
        let import_items = extract_import_items(&module.imports);
        let mut cache = self.module_cache.write().await;
        cache.update(module_name.clone(), source_hash, check_result.exports, import_names, import_items);
        drop(cache);

        // Publish diagnostics for the changed module
        let diagnostics = type_errors_to_diagnostics(&check_result.errors, &source);
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;

        self.info(format!("[on_change] total: {:.2?}", on_change_start.elapsed())).await;
    }

    /// Re-typecheck all files that are currently open in the editor.
    /// Called after initialization completes to process files opened during loading.
    pub(crate) async fn typecheck_open_files(&self) {
        let open_files: Vec<(String, String)> = {
            let files = self.files.read().await;
            files.iter().map(|(uri, fs)| (uri.clone(), fs.source.clone())).collect()
        };
        if open_files.is_empty() {
            return;
        }
        self.info(format!("[lsp] typechecking {} open file(s) after init", open_files.len())).await;
        for (uri_str, source) in open_files {
            if let Ok(uri) = Url::parse(&uri_str) {
                self.on_change(uri, source).await;
            }
        }
    }
}

pub(crate) fn type_errors_to_diagnostics(errors: &[crate::typechecker::error::TypeError], source: &str) -> Vec<Diagnostic> {
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
                message: format!("{}\n", err.format_pretty()),
                ..Default::default()
            }
        })
        .collect()
}

pub(crate) fn error_to_range(err: &crate::diagnostics::CompilerError, source: &str) -> Range {
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
