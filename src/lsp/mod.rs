mod handlers;
pub mod utils;

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Arc;

use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::build::cache::ModuleCache;
use crate::typechecker::registry::ModuleRegistry;
use crate::lsp::utils::resolve::ResolutionExports;

use utils::find_definition::DefinitionIndex;

pub(crate) struct FileState {
    pub source: String,
    pub module_name: Option<String>,
}

/// Load state for progressive LSP initialization.
/// 0 = Initializing (no data), 1 = CacheLoaded (from disk, may be stale), 2 = Ready (authoritative)
pub(crate) const LOAD_STATE_INITIALIZING: u8 = 0;
pub(crate) const LOAD_STATE_CACHE_LOADED: u8 = 1;
pub(crate) const LOAD_STATE_READY: u8 = 2;

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
    pub(crate) module_cache: Arc<RwLock<ModuleCache>>,
    pub(crate) sources_cmd: Option<String>,
    pub(crate) cache_dir: Option<PathBuf>,
    pub(crate) load_state: Arc<AtomicU8>,
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
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string()]),
                    ..Default::default()
                }),
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

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        self.handle_completion(params).await
    }
}

impl Backend {
    async fn rebuild_module(&self, params: serde_json::Value) -> Result<serde_json::Value> {
        if let Some(uri_str) = params.get("uri").and_then(|v| v.as_str()) {
            if let Ok(uri) = Url::parse(uri_str) {
                // Try open files first, then source_map, then disk
                let source = {
                    let files = self.files.read().await;
                    files.get(uri_str).map(|f| f.source.clone())
                };
                let source = match source {
                    Some(s) => s,
                    None => {
                        let smap = self.source_map.read().await;
                        match smap.get(uri_str) {
                            Some(s) => s.clone(),
                            None => {
                                if let Ok(path) = uri.to_file_path() {
                                    std::fs::read_to_string(path).unwrap_or_default()
                                } else {
                                    String::new()
                                }
                            }
                        }
                    }
                };
                self.on_change(uri, source).await;
            }
        }
        Ok(serde_json::json!({ "success": true }))
    }

    async fn rebuild_project(&self) -> Result<serde_json::Value> {
        self.load_sources().await;
        Ok(serde_json::json!({ "success": true }))
    }

    pub fn new(client: Client, sources_cmd: Option<String>, cache_dir: Option<PathBuf>) -> Self {
        Backend {
            client,
            files: Arc::new(RwLock::new(HashMap::new())),
            registry: Arc::new(RwLock::new(ModuleRegistry::new())),
            def_index: Arc::new(RwLock::new(DefinitionIndex::new())),
            resolution_exports: Arc::new(RwLock::new(ResolutionExports::empty())),
            module_file_map: Arc::new(RwLock::new(HashMap::new())),
            source_map: Arc::new(RwLock::new(HashMap::new())),
            module_cache: Arc::new(RwLock::new(ModuleCache::default())),
            sources_cmd,
            cache_dir,
            load_state: Arc::new(AtomicU8::new(LOAD_STATE_INITIALIZING)),
        }
    }

    /// Check if the LSP has loaded enough state to serve requests.
    pub(crate) fn is_ready(&self) -> bool {
        self.load_state.load(Ordering::SeqCst) >= LOAD_STATE_CACHE_LOADED
    }

    /// Get source for a file URI, with lazy loading from disk.
    /// Tries source_map first, falls back to reading the file.
    pub(crate) async fn get_source_for_uri(&self, uri: &str) -> Option<String> {
        // Check source_map first
        {
            let sm = self.source_map.read().await;
            if let Some(source) = sm.get(uri) {
                return Some(source.clone());
            }
        }
        // Lazy load from disk
        let file_path = Url::parse(uri).ok()?.to_file_path().ok()?;
        let source = std::fs::read_to_string(&file_path).ok()?;
        // Cache it for next time
        {
            let mut sm = self.source_map.write().await;
            sm.insert(uri.to_string(), source.clone());
        }
        Some(source)
    }
}

pub fn run_server(sources_cmd: Option<String>, cache_dir: Option<PathBuf>) {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(16 * 1024 * 1024) // 16 MB — typechecker needs deep recursion
        .build()
        .expect("failed to create tokio runtime");
    rt.block_on(async {
        let stdin = tokio::io::stdin();
        let stdout = tokio::io::stdout();

        let (service, socket) = LspService::build(|client| Backend::new(client, sources_cmd, cache_dir))
            .custom_method("pfc/rebuildModule", Backend::rebuild_module)
            .custom_method("pfc/rebuildProject", Backend::rebuild_project)
            .finish();

        Server::new(stdin, stdout, socket).serve(service).await;
    });
}
