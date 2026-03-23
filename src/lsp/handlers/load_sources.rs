use std::collections::HashMap;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use rayon::prelude::*;
use tokio::sync::RwLock;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;

use crate::build::cache;
use crate::build::cache::ModuleCache;
use crate::build::BuildOptions;
use crate::cst::{self, Decl};
use crate::interner;
use crate::lsp::utils::find_definition::DefinitionIndex;
use crate::lsp::{CompletionEntry, CompletionEntryKind, CompletionIndex, FileState};
use crate::typechecker::registry::ModuleRegistry;

use super::super::{Backend, LOAD_STATE_CACHE_LOADED, LOAD_STATE_READY};

impl Backend {
    pub(crate) async fn load_sources(&self) {
        let total_start = std::time::Instant::now();

        let cmd = match &self.sources_cmd {
            Some(cmd) => cmd.clone(),
            None => {
                self.load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
                return;
            }
        };

        // Phase A: Try to restore from disk cache (fast path)
        let mut all_snapshots_loaded = false;
        if let Some(ref cache_dir) = self.cache_dir {
            let lsp_dir = cache_dir.join("lsp");
            let phase_a_start = std::time::Instant::now();

            let t = std::time::Instant::now();
            let idx_result = DefinitionIndex::load_from_disk(&lsp_dir.join("def_index.bin"));
            self.info(format!("[timing] load def_index: {:.2?} ({})", t.elapsed(), if idx_result.is_ok() { "ok" } else { "miss" })).await;

            let t = std::time::Instant::now();
            let re_result = crate::lsp::utils::resolve::ResolutionExports::load_from_disk(
                &lsp_dir.join("resolution_exports.bin"),
            );
            self.info(format!("[timing] load resolution_exports: {:.2?} ({})", t.elapsed(), if re_result.is_ok() { "ok" } else { "miss" })).await;

            let t = std::time::Instant::now();
            let mfmap_result = cache::load_module_file_map(&lsp_dir.join("module_file_map.bin"));
            self.info(format!("[timing] load module_file_map: {:.2?} ({})", t.elapsed(), if mfmap_result.is_ok() { "ok" } else { "miss" })).await;

            let t = std::time::Instant::now();
            let comp_result = CompletionIndex::load_from_disk(&lsp_dir.join("completion_index.bin"));
            self.info(format!("[timing] load completion_index: {:.2?} ({})", t.elapsed(), if comp_result.is_ok() { "ok" } else { "miss" })).await;

            let t = std::time::Instant::now();
            let cache_result = cache::ModuleCache::load_from_disk(cache_dir);
            self.info(format!("[timing] load module_cache: {:.2?} ({})", t.elapsed(), if cache_result.is_ok() { "ok" } else { "miss" })).await;

            // Always load the module cache if available (shared with CLI builds)
            if let Ok(c) = cache_result {
                let mut mc = self.module_cache.write().await;
                *mc = c;
            }

            if let (Ok(idx), Ok(re), Ok(mfmap), Ok(comp)) = (idx_result, re_result, mfmap_result, comp_result) {
                {
                    let mut i = self.def_index.write().await;
                    *i = idx;
                }
                {
                    let mut e = self.resolution_exports.write().await;
                    *e = re;
                }
                {
                    let mut m = self.module_file_map.write().await;
                    *m = mfmap;
                }
                {
                    let mut ci = self.completion_index.write().await;
                    *ci = comp;
                }

                self.load_state
                    .store(LOAD_STATE_CACHE_LOADED, Ordering::SeqCst);
                all_snapshots_loaded = true;
                self.info(format!("[timing] Phase A complete (all snapshots loaded): {:.2?}", phase_a_start.elapsed())).await;
                self.info(format!(
                    "Cache loaded in {:.2?}",
                    phase_a_start.elapsed()
                ))
                .await;
            } else {
                self.info(format!("[timing] Phase A incomplete (missing snapshots): {:.2?}", phase_a_start.elapsed())).await;
            }
        }

        // If all snapshots loaded from disk, we're done — no need for Phase B
        if all_snapshots_loaded {
            self.load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
            self.info(format!("[timing] Ready from cache in {:.2?} total", total_start.elapsed())).await;
            self.typecheck_open_files().await;
            return;
        }

        // Phase B: Need to build indexes from source files
        let has_cache = {
            let mc = self.module_cache.read().await;
            mc.has_entries()
        };

        if has_cache {
            self.info("Module cache found but LSP snapshots missing — rebuilding indexes").await;
            self.spawn_index_build(cmd).await;
        } else {
            self.info("No module cache found — doing full build (cold start)").await;
            self.spawn_full_build(cmd).await;
        }
    }

    async fn spawn_index_build(&self, cmd: String) {
        let token = NumberOrString::String("pfc-loading".to_string());
        let _ = self
            .client
            .send_request::<request::WorkDoneProgressCreate>(WorkDoneProgressCreateParams {
                token: token.clone(),
            })
            .await;

        self.client
            .send_notification::<notification::Progress>(ProgressParams {
                token: token.clone(),
                value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(
                    WorkDoneProgressBegin {
                        title: "Indexing PureScript sources".to_string(),
                        message: Some(format!("Running: {cmd}")),
                        cancellable: Some(false),
                        percentage: None,
                    },
                )),
            })
            .await;

        let client = self.client.clone();
        let def_index = self.def_index.clone();
        let resolution_exports = self.resolution_exports.clone();
        let module_file_map = self.module_file_map.clone();
        let module_cache = self.module_cache.clone();
        let completion_index = self.completion_index.clone();
        let load_state = self.load_state.clone();
        let cache_dir = self.cache_dir.clone();
        let progress_token = token.clone();
        let files = self.files.clone();
        let registry = self.registry.clone();

        let rt_handle = tokio::runtime::Handle::current();
        std::thread::Builder::new()
            .name("pfc-load-sources".to_string())
            .stack_size(16 * 1024 * 1024)
            .spawn(move || {
                let _guard = rt_handle.enter();
                let build_start = std::time::Instant::now();

                let log_client = client.clone();
                let info = move |msg: String| {
                    let rt = tokio::runtime::Handle::current();
                    rt.block_on(log_client.log_message(MessageType::INFO, msg));
                };

                // Run the shell command to get source globs
                let t = std::time::Instant::now();
                let output = match std::process::Command::new("sh")
                    .arg("-c")
                    .arg(&cmd)
                    .output()
                {
                    Ok(output) => output,
                    Err(e) => {
                        info(format!("Failed to run sources command: {e}"));
                        load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
                        return;
                    }
                };
                info(format!("[timing] sources command: {:.2?}", t.elapsed()));

                if !output.status.success() {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    info(format!("Sources command failed: {stderr}"));
                    load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
                    return;
                }

                let stdout = String::from_utf8_lossy(&output.stdout);
                let globs: Vec<String> = stdout
                    .lines()
                    .filter(|l| !l.is_empty())
                    .map(|l| l.to_string())
                    .collect();

                let rt = tokio::runtime::Handle::current();

                // Resolve globs to file paths
                let t = std::time::Instant::now();
                let mut file_paths: Vec<std::path::PathBuf> = Vec::new();
                for pattern in &globs {
                    match glob::glob(pattern) {
                        Ok(entries) => {
                            for entry in entries.flatten() {
                                if entry.extension().map_or(false, |ext| ext == "purs") {
                                    file_paths.push(entry);
                                }
                            }
                        }
                        Err(e) => info(format!("Invalid glob pattern {pattern}: {e}")),
                    }
                }
                info(format!("[timing] glob resolution: {:.2?} ({} files)", t.elapsed(), file_paths.len()));

                // Read all files in parallel
                let t = std::time::Instant::now();
                let sources: Vec<(String, String)> = file_paths
                    .par_iter()
                    .filter_map(|entry| match std::fs::read_to_string(entry) {
                        Ok(source) => {
                            let abs_path = entry.canonicalize().unwrap_or_else(|_| entry.clone());
                            Some((abs_path.to_string_lossy().into_owned(), source))
                        }
                        Err(_) => None,
                    })
                    .collect();
                info(format!("[timing] read files: {:.2?} ({} files)", t.elapsed(), sources.len()));

                // Report progress
                rt.block_on(async {
                    client
                        .send_notification::<notification::Progress>(ProgressParams {
                            token: progress_token.clone(),
                            value: ProgressParamsValue::WorkDone(WorkDoneProgress::Report(
                                WorkDoneProgressReport {
                                    message: Some(format!(
                                        "Parsing {} source files...",
                                        sources.len()
                                    )),
                                    cancellable: Some(false),
                                    percentage: None,
                                },
                            )),
                        })
                        .await;
                });

                // Parse all files in parallel
                let t = std::time::Instant::now();
                let parse_pool = rayon::ThreadPoolBuilder::new()
                    .thread_name(|i| format!("pfc-lsp-parse-{i}"))
                    .stack_size(16 * 1024 * 1024)
                    .build()
                    .expect("failed to build parse thread pool");

                let parsed: Vec<_> = parse_pool.install(|| {
                    sources
                        .par_iter()
                        .filter_map(|(path, source)| {
                            crate::parser::parse(source)
                                .ok()
                                .map(|module| (path.clone(), source.clone(), module))
                        })
                        .collect()
                });
                info(format!("[timing] parse files: {:.2?} ({} modules)", t.elapsed(), parsed.len()));

                let module_count = parsed.len();

                // Build definition index, module_file_map, and completion index
                let t = std::time::Instant::now();
                let mut index = DefinitionIndex::new();
                let mut mfmap = HashMap::new();
                let mut comp_index = CompletionIndex::default();

                for (path, source, module) in &parsed {
                    let file_uri = Url::from_file_path(path)
                        .map(|u| u.to_string())
                        .unwrap_or_default();
                    let mod_name = format!("{}", module.name.value);
                    index.add_module(module, path);
                    mfmap.insert(mod_name.clone(), file_uri);

                    let entries = extract_completion_entries(module, source);
                    if !entries.is_empty() {
                        comp_index.entries.insert(mod_name, entries);
                    }
                }
                info(format!("[timing] build indexes: {:.2?}", t.elapsed()));

                // Build resolution exports
                let t = std::time::Instant::now();
                let just_modules: Vec<cst::Module> =
                    parsed.iter().map(|(_, _, m)| m.clone()).collect();
                let exports = crate::lsp::utils::resolve::ResolutionExports::new(&just_modules);
                info(format!("[timing] build resolution_exports: {:.2?}", t.elapsed()));

                // Register paths in module cache
                let t = std::time::Instant::now();
                {
                    let mut mcache = rt.block_on(async { module_cache.write().await });
                    for (path, _source, module) in &parsed {
                        let mod_name = format!("{}", module.name.value);
                        mcache.register_path(path.clone(), mod_name);
                    }
                    mcache.build_reverse_deps();

                    if let Some(ref dir) = cache_dir {
                        if let Err(e) = mcache.save_to_disk(dir) {
                            info(format!("Failed to save module cache: {e}"));
                        }
                    }
                }
                info(format!("[timing] update module cache: {:.2?}", t.elapsed()));

                // Save LSP snapshots to disk for next startup
                let t = std::time::Instant::now();
                if let Some(ref dir) = cache_dir {
                    let lsp_dir = dir.join("lsp");
                    if let Err(e) = index.save_to_disk(&lsp_dir.join("def_index.bin")) {
                        info(format!("Failed to save def_index snapshot: {e}"));
                    }
                    if let Err(e) = exports.save_to_disk(&lsp_dir.join("resolution_exports.bin")) {
                        info(format!("Failed to save resolution_exports snapshot: {e}"));
                    }
                    if let Err(e) =
                        cache::save_module_file_map(&mfmap, &lsp_dir.join("module_file_map.bin"))
                    {
                        info(format!("Failed to save module_file_map snapshot: {e}"));
                    }
                    if let Err(e) = comp_index.save_to_disk(&lsp_dir.join("completion_index.bin")) {
                        info(format!("Failed to save completion_index snapshot: {e}"));
                    }
                }
                info(format!("[timing] save snapshots: {:.2?}", t.elapsed()));

                // Store indexes and mark as ready
                rt.block_on(async {
                    let mut idx = def_index.write().await;
                    *idx = index;
                    let mut re = resolution_exports.write().await;
                    *re = exports;
                    let mut mf = module_file_map.write().await;
                    *mf = mfmap;
                    let mut ci = completion_index.write().await;
                    *ci = comp_index;
                    load_state.store(LOAD_STATE_READY, Ordering::SeqCst);

                    client
                        .send_notification::<notification::Progress>(ProgressParams {
                            token: progress_token,
                            value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(
                                WorkDoneProgressEnd {
                                    message: Some(format!("Indexed {module_count} modules")),
                                },
                            )),
                        })
                        .await;
                });
                info(format!("[timing] Phase B (index build) total: {:.2?}", build_start.elapsed()));

                // Typecheck any files that were opened during loading
                typecheck_open_files(&files, &registry, &module_cache, &client, &rt);
            })
            .expect("failed to spawn load-sources thread");
    }

    /// Cold-start path: full build with typechecking when no prior cache exists.
    async fn spawn_full_build(&self, cmd: String) {
        let token = NumberOrString::String("pfc-loading".to_string());
        let _ = self
            .client
            .send_request::<request::WorkDoneProgressCreate>(WorkDoneProgressCreateParams {
                token: token.clone(),
            })
            .await;

        self.client
            .send_notification::<notification::Progress>(ProgressParams {
                token: token.clone(),
                value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(
                    WorkDoneProgressBegin {
                        title: "Loading PureScript sources".to_string(),
                        message: Some(format!("Running: {cmd}")),
                        cancellable: Some(false),
                        percentage: None,
                    },
                )),
            })
            .await;

        let client = self.client.clone();
        let registry = self.registry.clone();
        let def_index = self.def_index.clone();
        let resolution_exports = self.resolution_exports.clone();
        let module_file_map = self.module_file_map.clone();
        let module_cache = self.module_cache.clone();
        let completion_index = self.completion_index.clone();
        let load_state = self.load_state.clone();
        let cache_dir = self.cache_dir.clone();
        let output_dir = self.output_dir.clone();
        let progress_token = token.clone();
        let files = self.files.clone();

        let rt_handle = tokio::runtime::Handle::current();
        std::thread::Builder::new()
            .name("pfc-load-sources".to_string())
            .stack_size(16 * 1024 * 1024)
            .spawn(move || {
            let _guard = rt_handle.enter();
            let build_start = std::time::Instant::now();

            let log_client = client.clone();
            let info = move |msg: String| {
                let rt = tokio::runtime::Handle::current();
                rt.block_on(log_client.log_message(MessageType::INFO, msg));
            };

            let t = std::time::Instant::now();
            let output = match std::process::Command::new("sh")
                .arg("-c")
                .arg(&cmd)
                .output()
            {
                Ok(output) => output,
                Err(e) => {
                    info(format!("Failed to run sources command: {e}"));
                    load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
                    return;
                }
            };
            info(format!("[timing] sources command: {:.2?}", t.elapsed()));

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                info(format!("Sources command failed: {stderr}"));
                load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
                return;
            }

            let stdout = String::from_utf8_lossy(&output.stdout);
            let globs: Vec<String> = stdout
                .lines()
                .filter(|l| !l.is_empty())
                .map(|l| l.to_string())
                .collect();

            let rt = tokio::runtime::Handle::current();

            // Resolve globs to file paths
            let t = std::time::Instant::now();
            let mut file_paths: Vec<std::path::PathBuf> = Vec::new();
            for pattern in &globs {
                match glob::glob(pattern) {
                    Ok(entries) => {
                        for entry in entries.flatten() {
                            if entry.extension().map_or(false, |ext| ext == "purs") {
                                file_paths.push(entry);
                            }
                        }
                    }
                    Err(e) => info(format!("Invalid glob pattern {pattern}: {e}")),
                }
            }
            info(format!("[timing] glob resolution: {:.2?} ({} files)", t.elapsed(), file_paths.len()));

            // Read all files in parallel
            let t = std::time::Instant::now();
            let sources: Vec<(String, String)> = file_paths
                .par_iter()
                .filter_map(|entry| {
                    match std::fs::read_to_string(entry) {
                        Ok(source) => {
                            let abs_path = entry
                                .canonicalize()
                                .unwrap_or_else(|_| entry.clone());
                            Some((abs_path.to_string_lossy().into_owned(), source))
                        }
                        Err(_) => None,
                    }
                })
                .collect();
            info(format!("[timing] read files: {:.2?} ({} files)", t.elapsed(), sources.len()));

            // Report progress
            rt.block_on(async {
                client
                    .send_notification::<notification::Progress>(ProgressParams {
                        token: progress_token.clone(),
                        value: ProgressParamsValue::WorkDone(WorkDoneProgress::Report(
                            WorkDoneProgressReport {
                                message: Some(format!(
                                    "Type-checking {} source files...",
                                    sources.len()
                                )),
                                cancellable: Some(false),
                                percentage: None,
                            },
                        )),
                    })
                    .await;
            });

            // Full build with typechecking
            let t = std::time::Instant::now();
            let source_refs: Vec<(&str, &str)> = sources
                .iter()
                .map(|(p, s)| (p.as_str(), s.as_str()))
                .collect();

            let options = BuildOptions {
                output_dir: output_dir.clone(),
                ..Default::default()
            };

            let mut mcache = rt.block_on(async { module_cache.write().await });
            let (result, new_registry, mut build_parsed_modules) = crate::build::build_from_sources_incremental(
                &source_refs,
                &None,
                None,
                &options,
                &mut mcache,
            );
            mcache.build_reverse_deps();
            info(format!("[timing] full build: {:.2?}", t.elapsed()));

            let t = std::time::Instant::now();
            if let Some(ref dir) = cache_dir {
                if let Err(e) = mcache.save_to_disk(dir) {
                    info(format!("Failed to save module cache: {e}"));
                }
            }
            drop(mcache);
            info(format!("[timing] save module cache: {:.2?}", t.elapsed()));

            let error_count: usize = result.modules.iter().map(|m| m.type_errors.len()).sum();
            let module_count = result.modules.len();
            let error_module_count = result
                .modules
                .iter()
                .filter(|m| !m.type_errors.is_empty())
                .count();

            // Parse only cache-hit sources that weren't parsed by the build
            let t = std::time::Instant::now();
            let already_parsed: std::collections::HashSet<String> = build_parsed_modules
                .iter()
                .map(|(p, _)| p.to_string_lossy().into_owned())
                .collect();

            let cache_hit_sources: Vec<_> = sources
                .iter()
                .filter(|(path, _)| !already_parsed.contains(path.as_str()))
                .collect();

            let parse_pool = rayon::ThreadPoolBuilder::new()
                .thread_name(|i| format!("pfc-lsp-parse-{i}"))
                .stack_size(16 * 1024 * 1024)
                .build()
                .expect("failed to build parse thread pool");
            let extra_parsed: Vec<_> = parse_pool.install(|| {
                cache_hit_sources
                    .par_iter()
                    .filter_map(|(path, source)| {
                        crate::parser::parse(source)
                            .ok()
                            .map(|m| (std::path::PathBuf::from(path.as_str()), m))
                    })
                    .collect()
            });
            info(format!("[timing] extra parse (cache hits): {:.2?} ({} modules)", t.elapsed(), extra_parsed.len()));

            build_parsed_modules.extend(extra_parsed);

            // Build indexes
            let t = std::time::Instant::now();
            let mut index = DefinitionIndex::new();
            let mut mfmap = HashMap::new();
            let mut comp_index = CompletionIndex::default();
            let sources_map: HashMap<&str, &str> = sources.iter().map(|(p, s)| (p.as_str(), s.as_str())).collect();

            for (path, module) in &build_parsed_modules {
                let path_str = path.to_string_lossy();
                let file_uri = Url::from_file_path(path_str.as_ref())
                    .map(|u| u.to_string())
                    .unwrap_or_default();
                let mod_name = format!("{}", module.name.value);
                index.add_module(module, &path_str);
                mfmap.insert(mod_name.clone(), file_uri);

                if let Some(source) = sources_map.get(path_str.as_ref()) {
                    let entries = extract_completion_entries(module, source);
                    if !entries.is_empty() {
                        comp_index.entries.insert(mod_name, entries);
                    }
                }
            }
            info(format!("[timing] build indexes: {:.2?}", t.elapsed()));

            let t = std::time::Instant::now();
            let just_modules: Vec<cst::Module> = build_parsed_modules.into_iter().map(|(_, m)| m).collect();
            let exports = crate::lsp::utils::resolve::ResolutionExports::new(&just_modules);
            info(format!("[timing] build resolution_exports: {:.2?}", t.elapsed()));

            // Save LSP snapshots
            let t = std::time::Instant::now();
            if let Some(ref dir) = cache_dir {
                let lsp_dir = dir.join("lsp");
                if let Err(e) = index.save_to_disk(&lsp_dir.join("def_index.bin")) {
                    info(format!("Failed to save def_index snapshot: {e}"));
                }
                if let Err(e) = exports.save_to_disk(&lsp_dir.join("resolution_exports.bin")) {
                    info(format!("Failed to save resolution_exports snapshot: {e}"));
                }
                if let Err(e) = cache::save_module_file_map(&mfmap, &lsp_dir.join("module_file_map.bin")) {
                    info(format!("Failed to save module_file_map snapshot: {e}"));
                }
                if let Err(e) = comp_index.save_to_disk(&lsp_dir.join("completion_index.bin")) {
                    info(format!("Failed to save completion_index snapshot: {e}"));
                }
            }
            info(format!("[timing] save snapshots: {:.2?}", t.elapsed()));

            rt.block_on(async {
                let mut reg = registry.write().await;
                *reg = new_registry;
                let mut idx = def_index.write().await;
                *idx = index;
                let mut re = resolution_exports.write().await;
                *re = exports;
                let mut mf = module_file_map.write().await;
                *mf = mfmap;
                let mut ci = completion_index.write().await;
                *ci = comp_index;
                load_state.store(LOAD_STATE_READY, Ordering::SeqCst);

                client
                    .send_notification::<notification::Progress>(ProgressParams {
                        token: progress_token,
                        value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(
                            WorkDoneProgressEnd {
                                message: Some(format!(
                                    "Loaded {module_count} modules ({error_count} errors in {error_module_count} modules)"
                                )),
                            },
                        )),
                    })
                    .await;
            });
            info(format!("[timing] Phase B (full build) total: {:.2?}", build_start.elapsed()));

            // Typecheck any files that were opened during loading
            typecheck_open_files(&files, &registry, &module_cache, &client, &rt);
        })
        .expect("failed to spawn load-sources thread");
    }
}

/// Typecheck any files that were opened in the editor during loading.
/// Called from spawned threads after setting READY.
fn typecheck_open_files(
    files: &Arc<RwLock<HashMap<String, FileState>>>,
    registry: &Arc<RwLock<ModuleRegistry>>,
    module_cache: &Arc<RwLock<ModuleCache>>,
    client: &Client,
    rt: &tokio::runtime::Handle,
) {
    let open_files: Vec<(String, String)> = rt.block_on(async {
        let f = files.read().await;
        f.iter().map(|(uri, fs)| (uri.clone(), fs.source.clone())).collect()
    });
    if open_files.is_empty() {
        return;
    }
    rt.block_on(client.log_message(
        MessageType::INFO,
        format!("[lsp] typechecking {} open file(s) after init", open_files.len()),
    ));
    for (uri_str, source) in open_files {
        let uri = match Url::parse(&uri_str) {
            Ok(u) => u,
            Err(_) => continue,
        };
        let module = match crate::parser::parse(&source) {
            Ok(m) => m,
            Err(err) => {
                let range = super::diagnostics::error_to_range(&err, &source);
                let diagnostics = vec![Diagnostic {
                    range,
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String(err.code())),
                    source: Some("pfc".to_string()),
                    message: err.get_message(),
                    ..Default::default()
                }];
                rt.block_on(client.publish_diagnostics(uri, diagnostics, None));
                continue;
            }
        };

        let module_name = interner::resolve_module_name(&module.name.value.parts);
        let module_parts: Vec<crate::interner::Symbol> = module.name.value.parts.clone();

        rt.block_on(async {
            // Update file state with module name
            {
                let mut f = files.write().await;
                if let Some(fs) = f.get_mut(&uri_str) {
                    fs.module_name = Some(module_name.clone());
                }
            }

            let mut reg = registry.write().await;

            // Lazy-load imports from cache
            for import_decl in &module.imports {
                let import_parts = &import_decl.module.parts;
                if reg.lookup(import_parts).is_some() {
                    continue;
                }
                let import_name = interner::resolve_module_name(import_parts);
                let exports = {
                    let mut mc = module_cache.write().await;
                    mc.get_exports(&import_name).cloned()
                };
                if let Some(exports) = exports {
                    reg.register(import_parts, exports);
                }
            }

            let check_result = crate::typechecker::check_module_with_registry(&module, &reg);
            reg.register(&module_parts, check_result.exports.clone());

            let source_hash = ModuleCache::content_hash(&source);
            let import_names: Vec<String> = module.imports.iter()
                .map(|imp| interner::resolve_module_name(&imp.module.parts))
                .collect();
            let import_items = cache::extract_import_items(&module.imports);
            let mut mc = module_cache.write().await;
            if check_result.errors.is_empty() {
                mc.update(module_name.clone(), source_hash, check_result.exports, import_names, import_items);
            }
            drop(mc);

            let diagnostics = super::diagnostics::type_errors_to_diagnostics(&check_result.errors, &source);
            client.publish_diagnostics(uri, diagnostics, None).await;
        });
    }
}

/// Extract completion entries from a module's CST declarations and source text.
fn extract_completion_entries(module: &cst::Module, source: &str) -> Vec<CompletionEntry> {
    let mut entries = Vec::new();
    let mut type_sigs: HashMap<String, String> = HashMap::new();

    // First pass: collect type signatures
    for decl in &module.decls {
        if let Decl::TypeSignature { name, ty, .. } = decl {
            let name_str = name.value.resolve()
                .unwrap_or_default()
                .to_string();
            let span = ty.span();
            if span.start < source.len() && span.end <= source.len() {
                type_sigs.insert(name_str, source[span.start..span.end].to_string());
            }
        }
    }

    // Check export list to filter what's actually exported
    let export_filter: Option<std::collections::HashSet<String>> =
        module.exports.as_ref().map(|spanned_list| {
            spanned_list
                .value
                .exports
                .iter()
                .filter_map(|exp| match exp {
                    cst::Export::Value(name) => name.resolve().map(|s| s.to_string()),
                    cst::Export::Type(name, _) => name.resolve().map(|s| s.to_string()),
                    cst::Export::Class(name) => name.resolve().map(|s| s.to_string()),
                    _ => None,
                })
                .collect()
        });

    // Second pass: build entries
    for decl in &module.decls {
        match decl {
            Decl::Value { name, .. } | Decl::Foreign { name, .. } => {
                let name_str = name.value.resolve()
                    .unwrap_or_default()
                    .to_string();
                if let Some(ref filter) = export_filter {
                    if !filter.contains(&name_str) {
                        continue;
                    }
                }
                let type_string = type_sigs.get(&name_str).cloned().unwrap_or_default();
                entries.push(CompletionEntry {
                    name: name_str,
                    type_string,
                    kind: CompletionEntryKind::Value,
                    parent_type: None,
                });
            }
            Decl::Data {
                name, constructors, ..
            } => {
                let type_name = name.value.resolve()
                    .unwrap_or_default()
                    .to_string();
                if let Some(ref filter) = export_filter {
                    if !filter.contains(&type_name) {
                        continue;
                    }
                }
                entries.push(CompletionEntry {
                    name: type_name.clone(),
                    type_string: String::new(),
                    kind: CompletionEntryKind::Type,
                    parent_type: None,
                });
                for ctor in constructors {
                    let ctor_name = ctor.name.value.resolve()
                        .unwrap_or_default()
                        .to_string();
                    entries.push(CompletionEntry {
                        name: ctor_name,
                        type_string: String::new(),
                        kind: CompletionEntryKind::Constructor,
                        parent_type: Some(type_name.clone()),
                    });
                }
            }
            Decl::Newtype {
                name, constructor, ..
            } => {
                let type_name = name.value.resolve()
                    .unwrap_or_default()
                    .to_string();
                if let Some(ref filter) = export_filter {
                    if !filter.contains(&type_name) {
                        continue;
                    }
                }
                entries.push(CompletionEntry {
                    name: type_name.clone(),
                    type_string: String::new(),
                    kind: CompletionEntryKind::Type,
                    parent_type: None,
                });
                let ctor_name = constructor.value.resolve()
                    .unwrap_or_default()
                    .to_string();
                entries.push(CompletionEntry {
                    name: ctor_name,
                    type_string: String::new(),
                    kind: CompletionEntryKind::Constructor,
                    parent_type: Some(type_name),
                });
            }
            Decl::Class { name, members, .. } => {
                let class_name = name.value.resolve()
                    .unwrap_or_default()
                    .to_string();
                if let Some(ref filter) = export_filter {
                    if !filter.contains(&class_name) {
                        continue;
                    }
                }
                entries.push(CompletionEntry {
                    name: class_name,
                    type_string: String::new(),
                    kind: CompletionEntryKind::Class,
                    parent_type: None,
                });
                for member in members {
                    let member_name = member.name.value.resolve()
                        .unwrap_or_default()
                        .to_string();
                    let type_string = {
                        let span = member.ty.span();
                        if span.start < source.len() && span.end <= source.len() {
                            source[span.start..span.end].to_string()
                        } else {
                            String::new()
                        }
                    };
                    entries.push(CompletionEntry {
                        name: member_name,
                        type_string,
                        kind: CompletionEntryKind::Value,
                        parent_type: None,
                    });
                }
            }
            Decl::TypeAlias { name, .. } => {
                let name_str = name.value.resolve()
                    .unwrap_or_default()
                    .to_string();
                if let Some(ref filter) = export_filter {
                    if !filter.contains(&name_str) {
                        continue;
                    }
                }
                entries.push(CompletionEntry {
                    name: name_str,
                    type_string: String::new(),
                    kind: CompletionEntryKind::Type,
                    parent_type: None,
                });
            }
            _ => {}
        }
    }

    entries
}
