use std::collections::HashMap;
use std::sync::atomic::Ordering;

use rayon::prelude::*;
use tower_lsp::lsp_types::*;

use crate::build::BuildOptions;
use crate::lsp::utils::find_definition::DefinitionIndex;

use super::super::Backend;

impl Backend {
    pub(crate) async fn load_sources(&self) {
        let cmd = match &self.sources_cmd {
            Some(cmd) => cmd.clone(),
            None => {
                self.ready.store(true, Ordering::SeqCst);
                return;
            }
        };

        // Create a progress token for the loading spinner
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
        let source_map = self.source_map.clone();
        let module_cache = self.module_cache.clone();
        let ready = self.ready.clone();
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
                    ready.store(true, Ordering::SeqCst);
                    return;
                }
            };

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                log::error!("Sources command failed: {stderr}");
                ready.store(true, Ordering::SeqCst);
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
            let mut cache = rt.block_on(async { module_cache.write().await });
            let (result, new_registry) = crate::build::build_from_sources_incremental(
                &source_refs,
                &None,
                None,
                &options,
                &mut cache,
            );
            cache.build_reverse_deps();
            drop(cache);

            let error_count: usize = result.modules.iter().map(|m| m.type_errors.len()).sum();
            let module_count = result.modules.len();
            let error_module_count = result
                .modules
                .iter()
                .filter(|m| !m.type_errors.is_empty())
                .count();

            // Parse all sources in parallel for definition index
            let parse_results: Vec<_> = sources
                .par_iter()
                .map(|(path, source)| {
                    let file_uri = Url::from_file_path(path)
                        .map(|u| u.to_string())
                        .unwrap_or_default();
                    match crate::parser::parse(source) {
                        Ok(module) => {
                            let mod_name = format!("{}", module.name.value);
                            (path.clone(), file_uri, source.clone(), Some((module, mod_name)))
                        }
                        Err(_) => {
                            (path.clone(), file_uri, source.clone(), None)
                        }
                    }
                })
                .collect();

            // Merge results sequentially (add_module takes &mut self)
            let mut index = DefinitionIndex::new();
            let mut smap = HashMap::with_capacity(parse_results.len());
            let mut mfmap = HashMap::new();
            let mut parsed_modules = Vec::new();
            for (path, file_uri, source, parsed) in parse_results {
                if let Some((module, mod_name)) = parsed {
                    index.add_module(&module, &path);
                    mfmap.insert(mod_name, file_uri.clone());
                    parsed_modules.push(module);
                }
                smap.insert(file_uri, source);
            }

            let exports = crate::lsp::utils::resolve::ResolutionExports::new(&parsed_modules);

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
                ready.store(true, Ordering::SeqCst);

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
