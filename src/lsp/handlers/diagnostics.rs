use std::fmt::Display;

use tower_lsp::lsp_types::*;

use crate::interner;
use crate::span::Span;
use crate::typecheck_db::driver_multi::{check_module_ide, ModuleCheckResult, ModuleInput};
use crate::typecheck_db::passes::warnings::WarningKind;

use super::super::{Backend, FileState};

impl Backend {
    pub(crate) async fn info<M: Display>(&self, message: M) {
        self.client
            .log_message(MessageType::INFO, message)
            .await;
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

        // Type-check the focused module against the warm registry. Its
        // dependencies are already present in the registry from the project
        // load (C3); `check_module_ide` forces full re-inference of this module
        // so span-types + warnings are complete, and refreshes the module's own
        // entry in the registry.
        let t = std::time::Instant::now();
        let input = ModuleInput::new(module_name.clone(), source.clone(), module);
        let check_result = {
            let mut reg = self.registry.write().await;
            let mut db = self.db.lock().await;
            check_module_ide(&mut db, &input, &mut reg)
        };
        self.info(format!("[on_change] typecheck {module_name}: {:.2?}", t.elapsed())).await;

        // Publish diagnostics for the changed module: errors and warnings together.
        let diagnostics = to_diagnostics(&check_result, &source);
        self.client
            .publish_diagnostics(uri.clone(), diagnostics, None)
            .await;

        // Code generation: `check_module_ide` produces `js_module_text` when
        // codegen is enabled (output_dir set), but does NOT write it — the LSP
        // does. Write `<output_dir>/<ModuleName>/index.js` and copy a companion
        // `foreign.js` when the source `.purs` has a sibling `.js`.
        if let (Some(js_text), Some(output_dir)) =
            (check_result.js_module_text.as_ref(), self.output_dir.as_ref())
        {
            let t = std::time::Instant::now();
            let module_dir = output_dir.join(&module_name);
            if let Err(e) = std::fs::create_dir_all(&module_dir) {
                self.info(format!("[codegen] failed to create dir {}: {e}", module_dir.display())).await;
            } else {
                let index_path = module_dir.join("index.js");
                if let Err(e) = std::fs::write(&index_path, js_text) {
                    self.info(format!("[codegen] failed to write {}: {e}", index_path.display())).await;
                }

                // Copy the FFI companion file (.js next to .purs) if present.
                if let Ok(purs_path) = uri.to_file_path() {
                    let js_src_path = purs_path.with_extension("js");
                    if js_src_path.exists() {
                        let foreign_path = module_dir.join("foreign.js");
                        if let Err(e) = std::fs::copy(&js_src_path, &foreign_path) {
                            self.info(format!("[codegen] failed to copy foreign.js: {e}")).await;
                        }
                    }
                }
            }
            self.info(format!("[on_change] codegen {module_name}: {:.2?}", t.elapsed())).await;
        }

        self.info(format!("[on_change] total: {:.2?}", on_change_start.elapsed())).await;
    }
}

/// Convert a `Span` into an LSP `Range` against `source`.
fn span_to_range(span: &Span, source: &str) -> Range {
    match span.to_pos(source) {
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
    }
}

fn error_diag(span: &Span, source: &str, code: &str, message: String) -> Diagnostic {
    Diagnostic {
        range: span_to_range(span, source),
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(NumberOrString::String(code.to_string())),
        source: Some("pfc".to_string()),
        message,
        ..Default::default()
    }
}

/// Map every diagnostic channel of a typecheck_db [`ModuleCheckResult`] — all
/// eight error channels plus the warning channel — to LSP `Diagnostic`s.
pub(crate) fn to_diagnostics(result: &ModuleCheckResult, source: &str) -> Vec<Diagnostic> {
    let mut diags: Vec<Diagnostic> = Vec::new();

    for e in &result.import_errors {
        diags.push(error_diag(
            &e.span,
            source,
            "TypeError.ImportError",
            format!("Import error: {:?}", e.kind),
        ));
    }
    for e in &result.validation_errors {
        diags.push(error_diag(
            &e.span,
            source,
            "TypeError.ValidationError",
            format!("{:?}", e.kind),
        ));
    }
    for e in &result.kind_errors {
        diags.push(error_diag(
            &e.span,
            source,
            "TypeError.KindError",
            format!("{:?}", e.kind),
        ));
    }
    for e in &result.coercible_errors {
        diags.push(error_diag(
            &e.span,
            source,
            "TypeError.CoercibleError",
            format!("{:?}", e.kind),
        ));
    }
    for e in &result.exhaustiveness_errors {
        diags.push(error_diag(
            &e.span,
            source,
            "TypeError.NonExhaustivePattern",
            format!(
                "Non-exhaustive patterns for {}: missing {:?}",
                e.type_name, e.missing
            ),
        ));
    }
    for e in &result.constraint_errors {
        diags.push(error_diag(
            &e.span,
            source,
            "TypeError.ConstraintError",
            format!(
                "{:?}: {} (args={:?})",
                e.kind, e.constraint.class.name, e.constraint.args
            ),
        ));
    }
    for h in &result.hole_diagnostics {
        diags.push(error_diag(
            &h.span,
            source,
            "TypeError.TypedHole",
            format!("{h:?}"),
        ));
    }
    // `inference_error` is a fatal early-bailout enum with no single reliable
    // span; use a best-effort range.
    if let Some(ie) = &result.inference_error {
        diags.push(Diagnostic {
            range: Range::default(),
            severity: Some(DiagnosticSeverity::ERROR),
            code: Some(NumberOrString::String("TypeError.InferenceError".to_string())),
            source: Some("pfc".to_string()),
            message: format!("Inference error: {ie:?}"),
            ..Default::default()
        });
    }

    for w in &result.warnings {
        let (code, message) = match &w.kind {
            WarningKind::UnusedImport { name } => (
                "TypeWarning.UnusedImport".to_string(),
                format!("Unused import: {name}"),
            ),
            WarningKind::UnusedName { name } => (
                "TypeWarning.UnusedName".to_string(),
                format!("Unused name: {name}"),
            ),
        };
        diags.push(Diagnostic {
            range: span_to_range(&w.span, source),
            severity: Some(DiagnosticSeverity::WARNING),
            code: Some(NumberOrString::String(code)),
            source: Some("pfc".to_string()),
            message,
            ..Default::default()
        });
    }

    diags
}

pub(crate) fn error_to_range(err: &crate::diagnostics::CompilerError, source: &str) -> Range {
    match err.get_span() {
        Some(span) => span_to_range(&span, source),
        None => Range::default(),
    }
}
