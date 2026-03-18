mod handlers;
pub mod utils;

use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::build::cache::ModuleCache;
use crate::lsp::utils::resolve::ResolutionExports;
use crate::typechecker::registry::ModuleRegistry;

use utils::find_definition::DefinitionIndex;

pub(crate) struct FileState {
    pub source: String,
    pub module_name: Option<String>,
}

/// Lightweight completion data extracted from CST type signatures.
/// Much smaller than full ModuleExports — just pre-formatted strings.
#[derive(Default, Serialize, Deserialize)]
pub(crate) struct CompletionIndex {
    /// module_name → list of completion entries
    pub entries: HashMap<String, Vec<CompletionEntry>>,
}

impl CompletionIndex {
    pub fn save_to_disk(&self, path: &Path) -> io::Result<()> {
        let encoded = bincode::serialize(self)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))?;
        let compressed = zstd::bulk::compress(&encoded, 1)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, compressed)
    }

    pub fn load_from_disk(path: &Path) -> io::Result<Self> {
        let compressed = std::fs::read(path)?;
        let data = zstd::bulk::decompress(&compressed, 64 * 1024 * 1024)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("zstd: {e}")))?;
        bincode::deserialize(&data)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("bincode: {e}")))
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct CompletionEntry {
    pub name: String,
    pub type_string: String,
    pub kind: CompletionEntryKind,
    /// For constructors, the parent data/newtype name (e.g. "LibType" for constructor "LibCon1").
    /// Used to generate correct import syntax: `import Mod (LibType(LibCon1))`.
    #[serde(default)]
    pub parent_type: Option<String>,
}

#[derive(Clone, Copy, PartialEq, Serialize, Deserialize)]
pub(crate) enum CompletionEntryKind {
    Value,
    Constructor,
    Type,
    Class,
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
    pub(crate) completion_index: Arc<RwLock<CompletionIndex>>,
    pub(crate) sources_cmd: Option<String>,
    pub(crate) cache_dir: Option<PathBuf>,
    pub(crate) output_dir: Option<PathBuf>,
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
        self.info("[lsp] pfc language server initializing").await;
        let t = std::time::Instant::now();
        self.load_sources().await;
        self.info(format!(
            "[lsp] pfc language server initialized in {:.2?}",
            t.elapsed()
        ))
        .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let name = params
            .text_document
            .uri
            .path()
            .rsplit('/')
            .next()
            .unwrap_or("")
            .to_string();
        self.info(format!("[lsp] >> textDocument/didOpen {name}"))
            .await;
        let t = std::time::Instant::now();
        self.on_change(params.text_document.uri, params.text_document.text)
            .await;
        self.info(format!(
            "[lsp] << textDocument/didOpen {name}: {:.2?}",
            t.elapsed()
        ))
        .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let name = params
            .text_document
            .uri
            .path()
            .rsplit('/')
            .next()
            .unwrap_or("")
            .to_string();
        self.info(format!("[lsp] >> textDocument/didChange {name}"))
            .await;
        let t = std::time::Instant::now();
        if let Some(change) = params.content_changes.into_iter().next() {
            self.on_change(params.text_document.uri, change.text).await;
        }
        self.info(format!(
            "[lsp] << textDocument/didChange {name}: {:.2?}",
            t.elapsed()
        ))
        .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let name = params
            .text_document
            .uri
            .path()
            .rsplit('/')
            .next()
            .unwrap_or("")
            .to_string();
        self.info(format!("[lsp] >> textDocument/didSave {name}"))
            .await;
        let t = std::time::Instant::now();
        if let Some(text) = params.text {
            self.on_change(params.text_document.uri, text).await;
        }
        self.info(format!(
            "[lsp] << textDocument/didSave {name}: {:.2?}",
            t.elapsed()
        ))
        .await;
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        self.info("[lsp] >> textDocument/definition").await;
        let t = std::time::Instant::now();
        let result = self.handle_goto_definition(params).await;
        self.info(format!(
            "[lsp] << textDocument/definition: {:.2?}",
            t.elapsed()
        ))
        .await;
        result
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        self.info("[lsp] >> textDocument/hover").await;
        let t = std::time::Instant::now();
        let result = self.handle_hover(params).await;
        self.info(format!("[lsp] << textDocument/hover: {:.2?}", t.elapsed()))
            .await;
        result
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        self.info("[lsp] >> textDocument/completion").await;
        let t = std::time::Instant::now();
        let result = self.handle_completion(params).await;
        self.info(format!(
            "[lsp] << textDocument/completion: {:.2?}",
            t.elapsed()
        ))
        .await;
        result
    }
}

impl Backend {
    async fn rebuild_module(&self, params: serde_json::Value) -> Result<serde_json::Value> {
        self.info("[lsp] >> pfc/rebuildModule").await;
        let t = std::time::Instant::now();
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
        self.info(format!("[lsp] << pfc/rebuildModule: {:.2?}", t.elapsed()))
            .await;
        Ok(serde_json::json!({ "success": true }))
    }

    async fn rebuild_project(&self) -> Result<serde_json::Value> {
        self.info("[lsp] >> pfc/rebuildProject").await;
        let t = std::time::Instant::now();
        self.load_sources().await;
        self.info(format!("[lsp] << pfc/rebuildProject: {:.2?}", t.elapsed()))
            .await;
        Ok(serde_json::json!({ "success": true }))
    }

    pub fn new(client: Client, sources_cmd: Option<String>, cache_dir: Option<PathBuf>, output_dir: Option<PathBuf>) -> Self {
        Backend {
            client,
            files: Arc::new(RwLock::new(HashMap::new())),
            registry: Arc::new(RwLock::new(ModuleRegistry::new())),
            def_index: Arc::new(RwLock::new(DefinitionIndex::new())),
            resolution_exports: Arc::new(RwLock::new(ResolutionExports::empty())),
            module_file_map: Arc::new(RwLock::new(HashMap::new())),
            source_map: Arc::new(RwLock::new(HashMap::new())),
            module_cache: Arc::new(RwLock::new(ModuleCache::default())),
            completion_index: Arc::new(RwLock::new(CompletionIndex::default())),
            sources_cmd,
            cache_dir,
            output_dir,
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

pub fn run_server(sources_cmd: Option<String>, cache_dir: Option<PathBuf>, output_dir: Option<PathBuf>) {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(16 * 1024 * 1024) // 16 MB — typechecker needs deep recursion
        .build()
        .expect("failed to create tokio runtime");
    rt.block_on(async {
        let stdin = tokio::io::stdin();
        let stdout = tokio::io::stdout();

        let (service, socket) =
            LspService::build(|client| Backend::new(client, sources_cmd, cache_dir, output_dir))
                .custom_method("pfc/rebuildModule", Backend::rebuild_module)
                .custom_method("pfc/rebuildProject", Backend::rebuild_project)
                .finish();

        Server::new(stdin, stdout, socket).serve(service).await;
    });
}
