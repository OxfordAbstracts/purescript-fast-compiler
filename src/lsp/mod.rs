mod handlers;
pub mod utils;

use std::collections::HashMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::typechecker::registry::ModuleRegistry;
use crate::lsp::utils::resolve::ResolutionExports;

use utils::find_definition::DefinitionIndex;

pub(crate) struct FileState {
    pub source: String,
    pub module_name: Option<String>,
}

pub struct Backend {
    pub(crate) client: Client,
    pub(crate) files: Arc<RwLock<HashMap<String, FileState>>>,
    pub(crate) registry: Arc<RwLock<ModuleRegistry>>,
    pub(crate) def_index: Arc<RwLock<DefinitionIndex>>,
    pub(crate) resolution_exports: Arc<RwLock<ResolutionExports>>,
    /// Maps module name symbol → file URI for cross-module go-to-def
    pub(crate) module_file_map: Arc<RwLock<HashMap<String, String>>>,
    /// Maps file URI → source content for loaded project files
    pub(crate) source_map: Arc<RwLock<HashMap<String, String>>>,
    pub(crate) sources_cmd: Option<String>,
    pub(crate) ready: Arc<AtomicBool>,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                definition_provider: Some(OneOf::Left(true)),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "pfc".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.info("pfc language server initialized").await;
        self.load_sources().await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.on_change(params.text_document.uri, params.text_document.text)
            .await;
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

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        self.handle_goto_definition(params).await
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        self.handle_hover(params).await
    }
}

impl Backend {
    pub fn new(client: Client, sources_cmd: Option<String>) -> Self {
        Backend {
            client,
            files: Arc::new(RwLock::new(HashMap::new())),
            registry: Arc::new(RwLock::new(ModuleRegistry::new())),
            def_index: Arc::new(RwLock::new(DefinitionIndex::new())),
            resolution_exports: Arc::new(RwLock::new(ResolutionExports::empty())),
            module_file_map: Arc::new(RwLock::new(HashMap::new())),
            source_map: Arc::new(RwLock::new(HashMap::new())),
            sources_cmd,
            ready: Arc::new(AtomicBool::new(false)),
        }
    }
}

pub fn run_server(sources_cmd: Option<String>) {
    let rt = tokio::runtime::Runtime::new().expect("failed to create tokio runtime");
    rt.block_on(async {
        let stdin = tokio::io::stdin();
        let stdout = tokio::io::stdout();

        let (service, socket) = LspService::new(|client| Backend::new(client, sources_cmd));

        Server::new(stdin, stdout, socket).serve(service).await;
    });
}
