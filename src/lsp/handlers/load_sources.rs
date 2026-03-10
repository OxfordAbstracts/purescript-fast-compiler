use std::collections::HashMap;
use std::sync::atomic::Ordering;

use rayon::prelude::*;
use tower_lsp::lsp_types::*;

use crate::build::cache;
use crate::build::BuildOptions;
use crate::lsp::utils::find_definition::DefinitionIndex;

use super::super::{Backend, LOAD_STATE_CACHE_LOADED, LOAD_STATE_READY};

impl Backend {
    pub(crate) async fn load_sources(&self) {
        let cmd = match &self.sources_cmd {
            Some(cmd) => cmd.clone(),
            None => {
                self.load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
                return;
            }
        };

        // Phase A: Try to restore from disk cache (fast path, ~50-100ms)
        if let Some(ref cache_dir) = self.cache_dir {
            let lsp_dir = cache_dir.join("lsp");
            let start = std::time::Instant::now();

            let registry_path = lsp_dir.join("registry.bin");
            let def_index_path = lsp_dir.join("def_index.bin");
            let resolution_exports_path = lsp_dir.join("resolution_exports.bin");
            let module_file_map_path = lsp_dir.join("module_file_map.bin");

            // Load all snapshots (attempt all, succeed if all present)
            let reg_result = cache::load_registry_snapshot(&registry_path);
            let idx_result = DefinitionIndex::load_from_disk(&def_index_path);
            let re_result = crate::lsp::utils::resolve::ResolutionExports::load_from_disk(&resolution_exports_path);
            let mfmap_result = cache::load_module_file_map(&module_file_map_path);
            let cache_result = cache::ModuleCache::load_from_disk(cache_dir);

            // Always load the module cache if available (shared with CLI builds)
            if let Ok(c) = cache_result {
                log::info!("Loaded module cache from disk in {:.2?}", start.elapsed());
                let mut mc = self.module_cache.write().await;
                *mc = c;
            }

            if let (Ok(reg), Ok(idx), Ok(re), Ok(mfmap)) = (reg_result, idx_result, re_result, mfmap_result) {
                log::info!("Restored LSP state from cache in {:.2?}", start.elapsed());

                // Store cached state
                {
                    let mut r = self.registry.write().await;
                    *r = reg;
                }
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

                // Mark as cache-loaded — handlers can now serve requests
                self.load_state.store(LOAD_STATE_CACHE_LOADED, Ordering::SeqCst);
                self.info(format!("Cache loaded in {:.2?}, starting background verification", start.elapsed())).await;
            } else {
                log::info!("No complete LSP snapshots found, doing full build (module cache may still help)");
            }
        }

        // Phase B: Full build in background (updates state when done)
        self.spawn_full_build(cmd).await;
    }

    async fn spawn_full_build(&self, cmd: String) {
        // Create a progress token for the loading spinner
        let token = NumberOrString::String("pfc-loading".to_string());
        let _ = self
            .client
            .send_request::<request::WorkDoneProgressCreate>(WorkDoneProgressCreateParams {
                token: token.clone(),
            })
            .await;

        let already_cached = self.load_state.load(Ordering::SeqCst) >= LOAD_STATE_CACHE_LOADED;

        self.client
            .send_notification::<notification::Progress>(ProgressParams {
                token: token.clone(),
                value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(
                    WorkDoneProgressBegin {
                        title: if already_cached {
                            "Verifying PureScript sources".to_string()
                        } else {
                            "Loading PureScript sources".to_string()
                        },
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
        let source_map = self.source_map.clone();
        let module_cache = self.module_cache.clone();
        let load_state = self.load_state.clone();
        let cache_dir = self.cache_dir.clone();
        let files = self.files.clone();
        let progress_token = token.clone();

        let rt_handle = tokio::runtime::Handle::current();
        std::thread::Builder::new()
            .name("pfc-load-sources".to_string())
            .stack_size(16 * 1024 * 1024) // 16 MB — typechecker needs deep recursion
            .spawn(move || {
            let _guard = rt_handle.enter();
            // Run the shell command to get source globs
            let output = match std::process::Command::new("sh")
                .arg("-c")
                .arg(&cmd)
                .output()
            {
                Ok(output) => output,
                Err(e) => {
                    log::error!("Failed to run sources command: {e}");
                    load_state.store(LOAD_STATE_READY, Ordering::SeqCst);
                    return;
                }
            };

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                log::error!("Sources command failed: {stderr}");
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

            // Report progress: resolving globs
            rt.block_on(async {
                client
                    .send_notification::<notification::Progress>(ProgressParams {
                        token: progress_token.clone(),
                        value: ProgressParamsValue::WorkDone(WorkDoneProgress::Report(
                            WorkDoneProgressReport {
                                message: Some(format!(
                                    "Resolving {} glob patterns...",
                                    globs.len()
                                )),
                                cancellable: Some(false),
                                percentage: None,
                            },
                        )),
                    })
                    .await;
            });

            // Resolve globs to file paths (collect paths first, then read in parallel)
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
                    Err(e) => log::warn!("Invalid glob pattern {pattern}: {e}"),
                }
            }

            // Read all files in parallel
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
                        Err(e) => {
                            log::warn!("Failed to read {}: {e}", entry.display());
                            None
                        }
                    }
                })
                .collect();

            // Report progress: building
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

            // Build with no codegen to populate the registry
            let source_refs: Vec<(&str, &str)> = sources
                .iter()
                .map(|(p, s)| (p.as_str(), s.as_str()))
                .collect();

            let options = BuildOptions {
                output_dir: None,
                ..Default::default()
            };

            // Use incremental build with cache
            let mut mcache = rt.block_on(async { module_cache.write().await });
            let (result, new_registry, mut build_parsed_modules) = crate::build::build_from_sources_incremental(
                &source_refs,
                &None,
                None,
                &options,
                &mut mcache,
            );
            mcache.build_reverse_deps();

            // Save module cache to disk
            if let Some(ref dir) = cache_dir {
                if let Err(e) = mcache.save_to_disk(dir) {
                    log::warn!("Failed to save module cache: {e}");
                }
            }
            drop(mcache);

            let error_count: usize = result.modules.iter().map(|m| m.type_errors.len()).sum();
            let module_count = result.modules.len();
            let error_module_count = result
                .modules
                .iter()
                .filter(|m| !m.type_errors.is_empty())
                .count();

            // Collect paths of modules already parsed by the build pipeline
            let already_parsed: std::collections::HashSet<String> = build_parsed_modules
                .iter()
                .map(|(p, _)| p.to_string_lossy().into_owned())
                .collect();

            // Parse only cache-hit sources that weren't parsed by the build (in parallel)
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

            build_parsed_modules.extend(extra_parsed);

            // Build definition index and source/module maps
            let mut index = DefinitionIndex::new();
            let mut smap = HashMap::with_capacity(sources.len());
            let mut mfmap = HashMap::new();

            for (path, module) in &build_parsed_modules {
                let path_str = path.to_string_lossy();
                let file_uri = Url::from_file_path(path_str.as_ref())
                    .map(|u| u.to_string())
                    .unwrap_or_default();
                let mod_name = format!("{}", module.name.value);
                index.add_module(module, &path_str);
                mfmap.insert(mod_name, file_uri);
            }

            // Build source map from all sources (doesn't need parsing)
            for (path, source) in &sources {
                let file_uri = Url::from_file_path(path)
                    .map(|u| u.to_string())
                    .unwrap_or_default();
                smap.insert(file_uri, source.clone());
            }

            let just_modules: Vec<crate::cst::Module> = build_parsed_modules.into_iter().map(|(_, m)| m).collect();
            let exports = crate::lsp::utils::resolve::ResolutionExports::new(&just_modules);

            // Save LSP snapshots to disk for next startup
            if let Some(ref dir) = cache_dir {
                let lsp_dir = dir.join("lsp");
                if let Err(e) = cache::save_registry_snapshot(&new_registry, &lsp_dir.join("registry.bin")) {
                    log::warn!("Failed to save registry snapshot: {e}");
                }
                if let Err(e) = index.save_to_disk(&lsp_dir.join("def_index.bin")) {
                    log::warn!("Failed to save def_index snapshot: {e}");
                }
                if let Err(e) = exports.save_to_disk(&lsp_dir.join("resolution_exports.bin")) {
                    log::warn!("Failed to save resolution_exports snapshot: {e}");
                }
                if let Err(e) = cache::save_module_file_map(&mfmap, &lsp_dir.join("module_file_map.bin")) {
                    log::warn!("Failed to save module_file_map snapshot: {e}");
                }
            }

            // Store the registry, index, source map and mark as ready
            rt.block_on(async {
                let mut reg = registry.write().await;
                *reg = new_registry;
                let mut idx = def_index.write().await;
                *idx = index;
                let mut re = resolution_exports.write().await;
                *re = exports;
                let mut mf = module_file_map.write().await;
                *mf = mfmap;
                let mut sm = source_map.write().await;
                *sm = smap;
                load_state.store(LOAD_STATE_READY, Ordering::SeqCst);

                // Re-typecheck any files the user edited during loading
                let edited_files: Vec<(String, String)> = {
                    let f = files.read().await;
                    f.iter()
                        .map(|(uri, fs)| (uri.clone(), fs.source.clone()))
                        .collect()
                };
                drop(reg);
                drop(idx);
                drop(re);
                drop(mf);
                drop(sm);

                if !edited_files.is_empty() {
                    log::info!("Re-checking {} files edited during loading", edited_files.len());
                }

                // End progress
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
        })
        .expect("failed to spawn load-sources thread");
    }
}
