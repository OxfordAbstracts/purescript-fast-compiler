use std::collections::HashMap;
use std::sync::Arc;

use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::typechecker::registry::ModuleRegistry;

struct FileState {
    #[allow(dead_code)]
    source: String,
    module_name: Option<String>,
}

pub struct Backend {
    client: Client,
    files: Arc<RwLock<HashMap<String, FileState>>>,
    #[allow(dead_code)]
    registry: Arc<RwLock<ModuleRegistry>>,
}

impl Backend {
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

        let diagnostics = match crate::parser::parse(&source) {
            Ok(module) => {
                let module_name = format!("{}", module.name.value);
                {
                    let mut files = self.files.write().await;
                    if let Some(fs) = files.get_mut(&uri.to_string()) {
                        fs.module_name = Some(module_name);
                    }
                }
                vec![]
            }
            Err(err) => {
                let range = error_to_range(&err, &source);
                vec![Diagnostic {
                    range,
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String(err.code())),
                    source: Some("pfc".to_string()),
                    message: err.get_message(),
                    ..Default::default()
                }]
            }
        };

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

pub fn run_server() {
    let rt = tokio::runtime::Runtime::new().expect("failed to create tokio runtime");
    rt.block_on(async {
        let stdin = tokio::io::stdin();
        let stdout = tokio::io::stdout();

        let (service, socket) = LspService::new(|client| Backend {
            client,
            files: Arc::new(RwLock::new(HashMap::new())),
            registry: Arc::new(RwLock::new(ModuleRegistry::new())),
        });

        Server::new(stdin, stdout, socket).serve(service).await;
    });
}
