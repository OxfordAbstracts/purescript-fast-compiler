use std::collections::HashSet;
use std::path::PathBuf;
use std::time::Instant;

use clap::Parser;
use rayon::prelude::*;

use purescript_fast_compiler::build::{self, BuildOptions};
use purescript_fast_compiler::lsp::utils::find_definition::DefinitionIndex;
use purescript_fast_compiler::lsp::utils::resolve::ResolutionExports;

/// Profile the LSP load_sources phases with per-phase timing.
#[derive(Parser)]
#[command(name = "profile-load-sources")]
struct Args {
    /// Working directory to run the sources command in
    #[arg(long)]
    path: PathBuf,

    /// Shell command that outputs source globs/paths (e.g. "spago sources")
    #[arg(long)]
    sources_cmd: String,

    /// Directory for disk cache (enables warm-cache profiling across runs)
    #[arg(long)]
    cache_dir: Option<PathBuf>,
}

macro_rules! phase {
    ($name:expr, $body:expr) => {{
        let start = Instant::now();
        let result = $body;
        let elapsed = start.elapsed();
        eprintln!("  {:.<50} {:>8.2?}", $name, elapsed);
        result
    }};
}

fn main() {
    let args = Args::parse();
    let total_start = Instant::now();

    eprintln!("Profiling load_sources at: {}", args.path.display());
    eprintln!("Sources command: {}", args.sources_cmd);
    eprintln!();

    // Phase 1: Run shell command
    let globs: Vec<String> = phase!("Run sources command", {
        let output = std::process::Command::new("sh")
            .arg("-c")
            .arg(&args.sources_cmd)
            .current_dir(&args.path)
            .output()
            .expect("Failed to run sources command");

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprintln!("Command failed: {stderr}");
            std::process::exit(1);
        }

        String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter(|l| !l.is_empty())
            .map(|l| l.to_string())
            .collect()
    });
    eprintln!("    {} glob patterns", globs.len());

    // Phase 2: Resolve globs
    let file_paths: Vec<PathBuf> = phase!("Resolve globs", {
        let mut paths = Vec::new();
        for pattern in &globs {
            // Resolve relative globs against the working directory
            let full_pattern = if PathBuf::from(pattern).is_relative() {
                args.path.join(pattern).to_string_lossy().into_owned()
            } else {
                pattern.clone()
            };
            match glob::glob(&full_pattern) {
                Ok(entries) => {
                    for entry in entries.flatten() {
                        if entry.extension().map_or(false, |ext| ext == "purs") {
                            paths.push(entry);
                        }
                    }
                }
                Err(e) => eprintln!("    Invalid glob {pattern}: {e}"),
            }
        }
        paths
    });
    eprintln!("    {} .purs files", file_paths.len());

    // Phase 3: Read all sources in parallel
    let sources: Vec<(String, String)> = phase!("Read sources (parallel)", {
        file_paths
            .par_iter()
            .filter_map(|entry| {
                let source = std::fs::read_to_string(entry).ok()?;
                let abs = entry.canonicalize().unwrap_or_else(|_| entry.clone());
                Some((abs.to_string_lossy().into_owned(), source))
            })
            .collect()
    });
    eprintln!("    {} files read", sources.len());

    // Phase 4: Build with incremental cache
    let source_refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    let options = BuildOptions {
        output_dir: None,
        ..Default::default()
    };

    let cache_dir = args.cache_dir.as_ref().map(|d| {
        if d.is_relative() {
            args.path.join(d)
        } else {
            d.clone()
        }
    });

    let mut cache = if let Some(ref dir) = cache_dir {
        phase!("Load cache from disk", {
            match build::cache::ModuleCache::load_from_disk(dir) {
                Ok(c) => {
                    eprintln!("    loaded cache from {}", dir.display());
                    c
                }
                Err(_) => {
                    eprintln!("    no existing cache, starting fresh");
                    build::cache::ModuleCache::new()
                }
            }
        })
    } else {
        build::cache::ModuleCache::new()
    };

    let (result, _registry, build_parsed_modules) = phase!("Build (incremental)", {
        build::build_from_sources_incremental(&source_refs, &None, None, &options, &mut cache)
    });

    phase!("Build reverse deps", {
        cache.build_reverse_deps();
    });

    if let Some(ref dir) = cache_dir {
        phase!("Save cache to disk", {
            if let Err(e) = cache.save_to_disk(dir) {
                eprintln!("    failed to save cache: {e}");
            }
        });
    }

    let error_count: usize = result.modules.iter().map(|m| m.type_errors.len()).sum();
    let module_count = result.modules.len();
    let error_module_count = result.modules.iter().filter(|m| !m.type_errors.is_empty()).count();
    let cached_count = result.modules.iter().filter(|m| m.cached).count();
    eprintln!(
        "    {} modules ({} cached, {} errors in {} modules)",
        module_count, cached_count, error_count, error_module_count
    );

    // Phase 5: Parse cache-hit sources
    let already_parsed: HashSet<String> = build_parsed_modules
        .iter()
        .map(|(p, _)| p.to_string_lossy().into_owned())
        .collect();

    let cache_hit_sources: Vec<_> = sources
        .iter()
        .filter(|(path, _)| !already_parsed.contains(path.as_str()))
        .collect();

    let extra_count = cache_hit_sources.len();

    let mut all_modules: Vec<(PathBuf, purescript_fast_compiler::CstModule)> = build_parsed_modules;

    phase!(format!("Parse cache-hits ({extra_count} modules)"), {
        let extra: Vec<_> = cache_hit_sources
            .par_iter()
            .filter_map(|(path, source)| {
                purescript_fast_compiler::parse(source)
                    .ok()
                    .map(|m| (PathBuf::from(path.as_str()), m))
            })
            .collect();
        all_modules.extend(extra);
    });

    // Phase 6: Build definition index
    let index = phase!(format!("Build definition index ({} modules)", all_modules.len()), {
        let mut index = DefinitionIndex::new();
        for (path, module) in &all_modules {
            index.add_module(module, &path.to_string_lossy());
        }
        index
    });

    // Phase 7: Build ResolutionExports
    let exports = phase!("Build ResolutionExports", {
        let just_modules: Vec<purescript_fast_compiler::CstModule> =
            all_modules.into_iter().map(|(_, m)| m).collect();
        ResolutionExports::new(&just_modules)
    });

    // Phase 8: Save LSP snapshots
    if let Some(ref dir) = cache_dir {
        let lsp_dir = dir.join("lsp");
        phase!("Save registry snapshot", {
            if let Err(e) = build::cache::save_registry_snapshot(&_registry, &lsp_dir.join("registry.bin")) {
                eprintln!("    failed: {e}");
            }
        });
        phase!("Save def_index snapshot", {
            if let Err(e) = index.save_to_disk(&lsp_dir.join("def_index.bin")) {
                eprintln!("    failed: {e}");
            }
        });
        phase!("Save resolution_exports snapshot", {
            if let Err(e) = exports.save_to_disk(&lsp_dir.join("resolution_exports.bin")) {
                eprintln!("    failed: {e}");
            }
        });

        // Phase 9: Load LSP snapshots (benchmark restore time)
        eprintln!();
        eprintln!("  --- Restore from cache (simulated warm startup) ---");
        phase!("Load registry snapshot", {
            match build::cache::load_registry_snapshot(&lsp_dir.join("registry.bin")) {
                Ok(_) => {},
                Err(e) => eprintln!("    failed: {e}"),
            }
        });
        phase!("Load def_index snapshot", {
            match DefinitionIndex::load_from_disk(&lsp_dir.join("def_index.bin")) {
                Ok(_) => {},
                Err(e) => eprintln!("    failed: {e}"),
            }
        });
        phase!("Load resolution_exports snapshot", {
            match ResolutionExports::load_from_disk(&lsp_dir.join("resolution_exports.bin")) {
                Ok(_) => {},
                Err(e) => eprintln!("    failed: {e}"),
            }
        });
        phase!("Load cache index", {
            match build::cache::ModuleCache::load_from_disk(dir) {
                Ok(_) => {},
                Err(e) => eprintln!("    failed: {e}"),
            }
        });
    }

    eprintln!();
    eprintln!("  {:.<50} {:>8.2?}", "TOTAL", total_start.elapsed());
}
