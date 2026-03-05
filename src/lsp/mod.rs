use std::collections::HashMap;
use std::sync::Arc;

use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::build::BuildOptions;
use crate::typechecker::registry::ModuleRegistry;

struct FileState {
    #[allow(dead_code)]
    source: String,
    module_name: Option<String>,
}

pub struct Backend {
    client: Client,
    files: Arc<RwLock<HashMap<String, FileState>>>,
    registry: Arc<RwLock<ModuleRegistry>>,
    sources_cmd: Option<String>,
}

impl Backend {
    async fn load_sources(&self) {
        let cmd = match &self.sources_cmd {
            Some(cmd) => cmd.clone(),
            None => return,
        };

        self.client
            .log_message(MessageType::INFO, format!("Running sources command: {cmd}"))
            .await;

        let client = self.client.clone();
        let registry = self.registry.clone();

        tokio::task::spawn_blocking(move || {
            // Run the shell command to get source globs
            let output = match std::process::Command::new("sh")
                .arg("-c")
                .arg(&cmd)
                .output()
            {
                Ok(output) => output,
                Err(e) => {
                    log::error!("Failed to run sources command: {e}");
                    return;
                }
            };

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                log::error!("Sources command failed: {stderr}");
                return;
            }

            let stdout = String::from_utf8_lossy(&output.stdout);
            let globs: Vec<String> = stdout.lines()
                .filter(|l| !l.is_empty())
                .map(|l| l.to_string())
                .collect();

            log::info!("Sources command returned {} globs", globs.len());

            // Resolve globs to file paths
            let mut sources: Vec<(String, String)> = Vec::new();
            for pattern in &globs {
                match glob::glob(pattern) {
                    Ok(entries) => {
                        for entry in entries.flatten() {
                            if entry.extension().map_or(false, |ext| ext == "purs") {
                                match std::fs::read_to_string(&entry) {
                                    Ok(source) => {
                                        sources.push((entry.to_string_lossy().into_owned(), source));
                                    }
                                    Err(e) => log::warn!("Failed to read {}: {e}", entry.display()),
                                }
                            }
                        }
                    }
                    Err(e) => log::warn!("Invalid glob pattern {pattern}: {e}"),
                }
            }

            log::info!("Read {} source files, building...", sources.len());

            // Build with no codegen to populate the registry
            let source_refs: Vec<(&str, &str)> = sources
                .iter()
                .map(|(p, s)| (p.as_str(), s.as_str()))
                .collect();

            let options = BuildOptions {
                output_dir: None,
                ..Default::default()
            };

            let (result, new_registry) = crate::build::build_from_sources_with_options(
                &source_refs,
                &None,
                None,
                &options,
            );

            let error_count: usize = result.modules.iter().map(|m| m.type_errors.len()).sum();
            log::info!(
                "Build complete: {} modules, {} errors",
                result.modules.len(),
                error_count
            );

            // Store the registry
            let rt = tokio::runtime::Handle::current();
            rt.block_on(async {
                let mut reg = registry.write().await;
                *reg = new_registry;
                client
                    .log_message(
                        MessageType::INFO,
                        format!(
                            "Loaded {} modules ({} with errors)",
                            result.modules.len(),
                            result.modules.iter().filter(|m| !m.type_errors.is_empty()).count()
                        ),
                    )
                    .await;
            });
        });
    }

    async fn on_change(&self, uri: Url, source: String) {
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
        let check_result =
            crate::typechecker::check_module_with_registry(&module, &registry);

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

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "pfc".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "pfc language server initialized")
            .await;
        self.load_sources().await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let source = params.text_document.text;
        self.on_change(uri, source).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(change) = params.content_changes.into_iter().next() {
            self.on_change(params.text_document.uri, change.text).await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            self.on_change(params.text_document.uri, text).await;
        }
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

pub fn run_server(sources_cmd: Option<String>) {
    let rt = tokio::runtime::Runtime::new().expect("failed to create tokio runtime");
    rt.block_on(async {
        let stdin = tokio::io::stdin();
        let stdout = tokio::io::stdout();

        let (service, socket) = LspService::new(|client| Backend {
            client,
            files: Arc::new(RwLock::new(HashMap::new())),
            registry: Arc::new(RwLock::new(ModuleRegistry::new())),
            sources_cmd,
        });

        Server::new(stdin, stdout, socket).serve(service).await;
    });
}
