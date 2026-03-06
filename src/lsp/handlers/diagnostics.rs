use std::fmt::Display;
use std::sync::atomic::Ordering;

use tower_lsp::lsp_types::*;

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

        // Type-check against the registry
        let registry = self.registry.read().await;
        let check_result = crate::typechecker::check_module_with_registry(&module, &registry);

        let diagnostics: Vec<Diagnostic> = check_result
            .errors
            .iter()
            .map(|err| {
                let span = err.span();
                let range = match span.to_pos(&source) {
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
            .collect();

        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }
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
