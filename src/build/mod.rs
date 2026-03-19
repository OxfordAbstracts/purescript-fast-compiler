//! Multi-module build pipeline.
//!
//! Discovers PureScript source files via glob patterns, parses them,
//! builds a dependency graph from imports, topologically sorts, and
//! typechecks in dependency order.

pub mod cache;
pub mod error;
pub mod portable;

use std::collections::{HashMap, HashSet, VecDeque};
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use rayon::prelude::*;

use crate::cst::{Decl, Module};
use crate::interner::{self, Symbol};
use crate::span::Span;
use crate::js_ffi;
use crate::typechecker::check;
use crate::typechecker::registry::{ModuleExports, ModuleRegistry};
use crate::typechecker::error::TypeError;

pub use error::BuildError;

// ===== Build options =====

/// Configuration options for the build pipeline.
#[derive(Debug, Clone, Default)]
pub struct BuildOptions {
    /// Output directory for generated JavaScript files.
    /// `None` means skip codegen. `Some(path)` writes JS to `path/<Module.Name>/index.js`.
    pub output_dir: Option<PathBuf>,
}

// ===== Public types =====

pub struct ModuleResult {
    pub path: PathBuf,
    pub module_name: String,
    pub type_errors: Vec<TypeError>,
    pub cached: bool,
}

pub struct BuildResult {
    pub modules: Vec<ModuleResult>,
    pub build_errors: Vec<BuildError>,
}

// ===== Internal types =====

struct ParsedModule {
    path: PathBuf,
    /// The parsed CST. None for cache-skipped modules (lazy-parsed on demand).
    module: Option<Module>,
    /// Index into the sources array, for lazy parsing when needed.
    source_idx: usize,
    module_name: String,
    module_parts: Vec<Symbol>,
    import_parts: Vec<Vec<Symbol>>,
    js_source: Option<String>,
    source_hash: u64,
}

// ===== Helpers =====

fn module_name_string(parts: &[Symbol]) -> String {
    interner::resolve_module_name(parts)
}

fn module_name_to_parts(name: &str) -> Vec<Symbol> {
    name.split('.').map(|s| interner::intern(s)).collect()
}

fn is_prim_import(parts: &[Symbol]) -> bool {
    !parts.is_empty() && interner::symbol_eq(parts[0], "Prim")
}

/// Handle a typecheck panic by recording a build error.
fn handle_typecheck_panic(
    build_errors: &mut Vec<BuildError>,
    pm: &ParsedModule,
    elapsed: std::time::Duration,
    done: usize,
    total_modules: usize,
) {
    log::debug!(
        "  [{}/{}] panic: {} ({:.2?})",
        done, total_modules, pm.module_name, elapsed
    );
    build_errors.push(BuildError::TypecheckPanic {
        path: pm.path.clone(),
        module_name: pm.module_name.clone(),
    });
}

/// Extract the names of all `foreign import` declarations from a module.
fn extract_foreign_import_names(module: &Module) -> Vec<String> {
    module
        .decls
        .iter()
        .filter_map(|d| {
            if let Decl::Foreign { name, .. } = d {
                interner::resolve(name.value).map(|s| s.to_string())
            } else {
                None
            }
        })
        .collect()
}

// ===== Public API =====

/// Build all PureScript modules matching the given glob patterns, with incremental caching.
pub fn build_cached(globs: &[&str], output_dir: Option<PathBuf>, cache: &mut cache::ModuleCache) -> BuildResult {
    build_internal(globs, output_dir, Some(cache))
}

/// Build all PureScript modules matching the given glob patterns.
pub fn build(globs: &[&str], output_dir: Option<PathBuf>) -> BuildResult {
    build_internal(globs, output_dir, None)
}

fn build_internal(globs: &[&str], output_dir: Option<PathBuf>, cache: Option<&mut cache::ModuleCache>) -> BuildResult {
    let build_start = Instant::now();
    let mut build_errors = Vec::new();

    // Phase 1: Glob resolution
    log::debug!("Phase 1: Resolving glob patterns: {:?}", globs);
    let phase_start = Instant::now();
    let paths = resolve_globs(globs, &mut build_errors);
    log::debug!(
        "Phase 1 complete: found {} files in {:.2?}",
        paths.len(),
        phase_start.elapsed()
    );
    // Phase 2: Read and parse
    log::debug!("Phase 2a: Reading source files");
    let phase_start = Instant::now();
    let mut sources = Vec::new();
    for path in &paths {
        match std::fs::read_to_string(path) {
            Ok(source) => {
                log::debug!("  read {} ({} bytes)", path.display(), source.len());
                sources.push((path.to_string_lossy().into_owned(), source));
            }
            Err(e) => {
                log::debug!("  failed to read {}: {}", path.display(), e);
                build_errors.push(BuildError::FileReadError {
                    path: path.clone(),
                    error: e.to_string(),
                });
            }
        }
    }
    log::debug!(
        "Phase 2a complete: read {} source files in {:.2?}",
        sources.len(),
        phase_start.elapsed()
    );

    log::debug!("Phase 2b: Scanning for FFI companion .js files");
    let mut js_sources: HashMap<String, String> = HashMap::new();
    for (path_str, _) in &sources {
        let purs_path = PathBuf::from(path_str);
        let js_path = purs_path.with_extension("js");
        if js_path.exists() {
            if let Ok(js_source) = std::fs::read_to_string(&js_path) {
                log::debug!("  found FFI companion: {}", js_path.display());
                js_sources.insert(path_str.clone(), js_source);
            }
        }
    }
    log::debug!(
        "Phase 2b complete: found {} FFI companion files",
        js_sources.len()
    );

    let source_refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    let js_refs: HashMap<&str, &str> = js_sources
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();

    let options = BuildOptions {
        output_dir,
        ..Default::default()
    };
    let mut result =
        build_from_sources_impl(&source_refs, &Some(js_refs), None, &options, cache).0;
    // Prepend file-level errors before source-level errors
    build_errors.append(&mut result.build_errors);
    result.build_errors = build_errors;

    log::debug!("Build finished in {:.2?}", build_start.elapsed());
    result
}

pub fn build_from_sources_with_registry(
    sources: &[(&str, &str)],
    start_registry: Option<Arc<ModuleRegistry>>,
) -> (BuildResult, ModuleRegistry) {
    // No JS sources — skip FFI validation (used for support packages)
    build_from_sources_with_js(sources, &None, start_registry)
}

/// Build from pre-read source strings with optional JS companion sources for FFI validation.
/// Pass `None` to skip FFI validation entirely (e.g. for support packages).
/// Pass `Some(map)` to enable FFI validation using the provided JS sources.
pub fn build_from_sources_with_js(
    sources: &[(&str, &str)],
    js_sources: &Option<HashMap<&str, &str>>,
    start_registry: Option<Arc<ModuleRegistry>>,
) -> (BuildResult, ModuleRegistry) {
    build_from_sources_with_options(
        sources,
        js_sources,
        start_registry,
        &BuildOptions::default(),
    )
}

/// Build with full control over options (timeouts, etc.).
pub fn build_from_sources_with_options(
    sources: &[(&str, &str)],
    js_sources: &Option<HashMap<&str, &str>>,
    start_registry: Option<Arc<ModuleRegistry>>,
    options: &BuildOptions,
) -> (BuildResult, ModuleRegistry) {
    let (result, registry, _) = build_from_sources_impl(sources, js_sources, start_registry, options, None);
    (result, registry)
}

/// Build with incremental caching support.
/// Skips typechecking modules whose source hasn't changed and whose
/// dependencies haven't been rebuilt.
pub fn build_from_sources_incremental(
    sources: &[(&str, &str)],
    js_sources: &Option<HashMap<&str, &str>>,
    start_registry: Option<Arc<ModuleRegistry>>,
    options: &BuildOptions,
    cache: &mut cache::ModuleCache,
) -> (BuildResult, ModuleRegistry, Vec<(PathBuf, Module)>) {
    build_from_sources_impl(sources, js_sources, start_registry, options, Some(cache))
}

fn build_from_sources_impl(
    sources: &[(&str, &str)],
    js_sources: &Option<HashMap<&str, &str>>,
    start_registry: Option<Arc<ModuleRegistry>>,
    options: &BuildOptions,
    mut cache: Option<&mut cache::ModuleCache>,
) -> (BuildResult, ModuleRegistry, Vec<(PathBuf, Module)>) {
    let pipeline_start = Instant::now();
    let mut build_errors = Vec::new();
    // Phase 2c: Parse source files (with cache-aware skipping)
    log::debug!("Phase 2c: Processing {} source files", sources.len());
    let phase_start = Instant::now();

    // Step 1: Compute content hashes for all sources (fast, parallel)
    let source_hashes: Vec<u64> = sources
        .par_iter()
        .map(|&(_, source)| cache::ModuleCache::content_hash(source))
        .collect();

    // Step 2: Determine which sources can skip parsing (cache hit by path + hash)
    let mut skip_parse = vec![false; sources.len()];
    let mut skip_count = 0usize;
    if let Some(ref cache) = cache {
        for (i, &(path_str, _)) in sources.iter().enumerate() {
            if let Some(module_name) = cache.module_name_for_path(path_str) {
                if !cache.needs_rebuild(module_name, source_hashes[i], &HashSet::new()) {
                    skip_parse[i] = true;
                    skip_count += 1;
                }
            }
        }
    }
    log::debug!(
        "  {} modules cached (skip parse), {} need parsing",
        skip_count,
        sources.len() - skip_count
    );

    // Step 3: Parse only non-cached sources in parallel (use a pool with large stacks
    // since the parser can recurse deeply on complex files)
    let parse_pool = rayon::ThreadPoolBuilder::new()
        .thread_name(|i| format!("pfc-parse-{i}"))
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("failed to build parse thread pool");
    let parse_results: Vec<(usize, Result<(PathBuf, Module), BuildError>)> = parse_pool.install(|| {
        sources
            .par_iter()
            .enumerate()
            .filter(|(i, _)| !skip_parse[*i])
            .map(|(i, &(path_str, source))| {
                let path = PathBuf::from(path_str);
                let result = match crate::parser::parse(source) {
                    Ok(module) => Ok((path, module)),
                    Err(e) => Err(BuildError::CompileError { path, error: e }),
                };
                (i, result)
            })
            .collect()
    });

    // Step 4: Build parsed vec from both cached stubs and parsed results
    let mut parsed: Vec<ParsedModule> = Vec::new();
    let mut seen_modules: HashMap<Vec<Symbol>, PathBuf> = HashMap::new();

    // 4a: Create stubs for cache-hit modules
    if let Some(ref cache) = cache {
        for (i, &(path_str, _)) in sources.iter().enumerate() {
            if !skip_parse[i] {
                continue;
            }
            let module_name = match cache.module_name_for_path(path_str) {
                Some(name) => name.to_string(),
                None => continue,
            };
            let module_parts = module_name_to_parts(&module_name);

            // Duplicate check
            if let Some(existing_path) = seen_modules.get(&module_parts) {
                log::debug!(
                    "  rejected {}: duplicate (already at {})",
                    module_name,
                    existing_path.display()
                );
                build_errors.push(BuildError::DuplicateModule {
                    module_name,
                    path1: existing_path.clone(),
                    path2: PathBuf::from(path_str),
                });
                continue;
            }
            seen_modules.insert(module_parts.clone(), PathBuf::from(path_str));

            let import_parts: Vec<Vec<Symbol>> = cache
                .get_imports(&module_name)
                .map(|imports| imports.iter().map(|s| module_name_to_parts(s)).collect())
                .unwrap_or_default();

            let js_source = js_sources
                .as_ref()
                .and_then(|m| m.get(path_str))
                .map(|s| s.to_string());

            parsed.push(ParsedModule {
                path: PathBuf::from(path_str),
                module: None,
                source_idx: i,
                module_name,
                module_parts,
                import_parts,
                js_source,
                source_hash: source_hashes[i],
            });
        }
    }

    // 4b: Process parsed results (with full validation)
    for (i, result) in parse_results {
        let (path, module) = match result {
            Ok(pair) => pair,
            Err(e) => {
                log::debug!("Build error:\n{e}");
                build_errors.push(e);
                continue;
            }
        };

        let path_str = sources[i].0;
        let module_parts: Vec<Symbol> = module.name.value.parts.clone();
        let module_name = module_name_string(&module_parts);

        // Check for reserved Prim namespace
        if !module_parts.is_empty() {
            let is_prim =
                interner::with_resolved(module_parts[0], |s| s == "Prim").unwrap_or(false);
            if is_prim {
                log::debug!("  rejected {}: Prim namespace is reserved", module_name);
                build_errors.push(BuildError::CannotDefinePrimModules { module_name, path });
                continue;
            }
        }

        // Check for invalid characters in module name segments (no apostrophes or underscores)
        let mut invalid_module = false;
        for part in &module_parts {
            let invalid_char = interner::with_resolved(*part, |s| {
                s.chars().find(|&c| c == '\'' || c == '_')
            })
            .flatten();
            if let Some(c) = invalid_char {
                log::debug!(
                    "  rejected {}: invalid character '{}' in module name",
                    module_name,
                    c
                );
                build_errors.push(BuildError::InvalidModuleName {
                    module_name: module_name.clone(),
                    invalid_char: c,
                    path: path.clone(),
                });
                invalid_module = true;
                break;
            }
        }
        if invalid_module {
            continue;
        }

        // Check for duplicate module names
        if let Some(existing_path) = seen_modules.get(&module_parts) {
            log::debug!(
                "  rejected {}: duplicate (already at {})",
                module_name,
                existing_path.display()
            );
            build_errors.push(BuildError::DuplicateModule {
                module_name,
                path1: existing_path.clone(),
                path2: path,
            });
            continue;
        }
        seen_modules.insert(module_parts.clone(), path.clone());

        // Extract imports, filtering out Prim
        let import_parts: Vec<Vec<Symbol>> = module
            .imports
            .iter()
            .map(|imp| imp.module.parts.clone())
            .filter(|parts| !is_prim_import(parts))
            .collect();

        let js_source = js_sources
            .as_ref()
            .and_then(|m| m.get(path_str))
            .map(|s| s.to_string());

        // Register path → module_name mapping in cache
        if let Some(ref mut cache) = cache {
            cache.register_path(path_str.to_string(), module_name.clone());
        }

        parsed.push(ParsedModule {
            path,
            module: Some(module),
            source_idx: i,
            module_name,
            module_parts,
            import_parts,
            js_source,
            source_hash: source_hashes[i],
        });
    }
    log::debug!(
        "Phase 2c complete: {} modules ({} cached, {} parsed, {} rejected) in {:.2?}",
        parsed.len(),
        skip_count,
        parsed.len().saturating_sub(skip_count),
        sources.len() - parsed.len(),
        phase_start.elapsed()
    );

    if !build_errors.is_empty() {
        let registry = match start_registry {
            Some(base) => ModuleRegistry::with_base(base),
            None => ModuleRegistry::default(),
        };
        return (BuildResult { modules: Vec::new(), build_errors }, registry, Vec::new());
    }

    // Phase 3: Build dependency graph and check for unknown imports
    log::debug!("Phase 3: Building dependency graph");
    let phase_start = Instant::now();
    let known_modules: HashSet<Vec<Symbol>> =
        parsed.iter().map(|p| p.module_parts.clone()).collect();

    let mut registry = match start_registry {
        Some(base) => {
            log::debug!("  using base registry from support packages");
            ModuleRegistry::with_base(base)
        }
        None => ModuleRegistry::default(),
    };

    for pm in &parsed {
        for imp_parts in &pm.import_parts {
            let imp_name = module_name_string(imp_parts);
            if !known_modules.contains(imp_parts) && !registry.contains(imp_parts) {
                log::debug!(
                    "  missing import: {} imports {} (not found)",
                    pm.module_name,
                    imp_name
                );
                build_errors.push(BuildError::ModuleNotFound {
                    module_name: imp_name,
                    importing_module: pm.module_name.clone(),
                    path: pm.path.clone(),
                    span: pm.module.as_ref().map(|m| m.span).unwrap_or(Span::new(0, 0)),
                });
            }
        }
    }

    // Build index: module_parts → index in parsed vec
    let module_index: HashMap<Vec<Symbol>, usize> = parsed
        .iter()
        .enumerate()
        .map(|(i, pm)| (pm.module_parts.clone(), i))
        .collect();

    // Topological sort (Kahn's algorithm)
    log::debug!("Phase 3b: Topological sort of {} modules", parsed.len());

    let mut levels: Vec<Vec<usize>> = match topological_sort_levels(&parsed, &module_index) {
        Ok(levels) => {
            log::debug!("  {} dependency levels for parallel build", levels.len());
            levels
        }
        Err(cycle_indices) => {
            let cycle_names: Vec<(String, PathBuf)> = cycle_indices
                .iter()
                .map(|&i| (parsed[i].module_name.clone(), parsed[i].path.clone()))
                .collect();
            log::debug!(
                "  cycle detected among: {:?}",
                cycle_names
                    .iter()
                    .map(|(n, _)| n.as_str())
                    .collect::<Vec<_>>()
            );
            build_errors.push(BuildError::CycleInModules { cycle: cycle_names });
            // Typecheck only non-cyclic modules
            let cyclic: HashSet<usize> = cycle_indices.into_iter().collect();
            match topological_sort_excluding(&parsed, &module_index, &cyclic) {
                Ok(order) => order.into_iter().map(|i| vec![i]).collect(),
                Err(_) => Vec::new(),
            }
        }
    };
    log::debug!(
        "Phase 3 complete: dependency graph built in {:.2?}",
        phase_start.elapsed()
    );

    if !build_errors.is_empty() {
        log::debug!("Phase 3 failed");
        return (BuildResult { modules: Vec::new(), build_errors }, registry, Vec::new());
    }

    // Phase 3c: Prune unchanged upstream modules
    // If a module's source is unchanged AND none of its transitive dependencies
    // changed source, its cached exports are guaranteed valid. Pre-load them into
    // the registry and remove from levels to skip all Phase 4 overhead.
    let mut module_results: Vec<ModuleResult> = Vec::new();
    if let Some(ref mut cache) = cache {
        let phase_start = Instant::now();
        let empty_rebuilt = HashSet::new();

        // 1. Find dirty roots: source-changed or uncached modules
        let mut source_dirty: HashSet<usize> = HashSet::new();
        for (idx, pm) in parsed.iter().enumerate() {
            if cache.needs_rebuild(&pm.module_name, pm.source_hash, &empty_rebuilt) {
                source_dirty.insert(idx);
            }
        }
        log::debug!(
            "Phase 3c.1 complete in {:.2?}",
            phase_start.elapsed()
        );
        // 2. Build forward adjacency: dependents[i] = modules that depend on i
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); parsed.len()];
        for (i, pm) in parsed.iter().enumerate() {
            for imp in &pm.import_parts {
                if let Some(&dep_idx) = module_index.get(imp) {
                    dependents[dep_idx].push(i);
                }
            }
        }
        log::debug!(
            "Phase 3c.2 complete in {:.2?}",
            phase_start.elapsed()
        );
        // 3. BFS from dirty roots to find all potentially affected modules
        let mut potentially_dirty: HashSet<usize> = source_dirty.clone();
        let mut queue: VecDeque<usize> = source_dirty.into_iter().collect();
        while let Some(idx) = queue.pop_front() {
            for &dependent in &dependents[idx] {
                if potentially_dirty.insert(dependent) {
                    queue.push_back(dependent);
                }
            }
        }
        log::debug!(
            "Phase 3c.3 complete in {:.2?}",
            phase_start.elapsed()
        );
        // 4. Pre-load exports for clean modules and collect pruned set
        // Load from disk in parallel (zstd decompress + bincode deserialize is expensive)
        let clean_indices: Vec<usize> = (0..parsed.len())
            .filter(|idx| !potentially_dirty.contains(idx))
            .collect();

        let loaded: Vec<(usize, Option<ModuleExports>)> = if let Some(cache_dir) = cache.cache_dir() {
            let cache_dir = cache_dir.to_path_buf();
            clean_indices.par_iter().map(|&idx| {
                let pm = &parsed[idx];
                let path = cache::module_file_path(&cache_dir, &pm.module_name);
                let exports = cache::load_module_file(&path).ok();
                (idx, exports)
            }).collect()
        } else {
            clean_indices.iter().map(|&idx| {
                let exports = cache.get_exports(&parsed[idx].module_name).cloned();
                (idx, exports)
            }).collect()
        };

        let mut pruned_set: HashSet<usize> = HashSet::new();
        for (idx, exports) in loaded {
            if let Some(exports) = exports {
                let pm = &parsed[idx];
                registry.register(&pm.module_parts, exports);
                pruned_set.insert(idx);
                module_results.push(ModuleResult {
                    path: pm.path.clone(),
                    module_name: pm.module_name.clone(),
                    type_errors: vec![],
                    cached: true,
                });
            }
        }
        log::debug!(
            "Phase 3c.4 complete in {:.2?}",
            phase_start.elapsed()
        );
        // 5. Remove pruned modules from levels
        let pruned_count = pruned_set.len();
        if pruned_count > 0 {
            for level in levels.iter_mut() {
                level.retain(|idx| !pruned_set.contains(idx));
            }
            levels.retain(|level| !level.is_empty());
        }

        log::debug!(
            "Phase 3c complete: pruned {} unchanged upstream modules in {:.2?}",
            pruned_count,
            phase_start.elapsed()
        );
    }

    // Phase 4: Typecheck in dependency order
    let total_modules: usize = levels.iter().map(|l| l.len()).sum();
    log::debug!(
        "Phase 4: Typechecking {} modules ({} levels, parallel within levels)",
        total_modules,
        levels.len(),
    );
    let phase_start = Instant::now();
    // Build a rayon thread pool with large stacks for deep recursion in the typechecker.
    // Codegen also runs on this pool (fused with typecheck).
    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    let pool = rayon::ThreadPoolBuilder::new()
        .thread_name(|i| format!("pfc-typecheck-{i}"))
        .num_threads(num_threads)
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("failed to build rayon thread pool");
    log::debug!("  using {} worker threads", num_threads);

    let mut done = 0usize;
    let mut export_diffs: HashMap<String, cache::ExportDiff> = HashMap::new();
    let mut cached_count = 0usize;

    for level in &levels {
        {
            let mut to_typecheck = Vec::new();
            for &idx in level.iter() {
                let pm = &parsed[idx];
                if let Some(ref mut cache) = cache {
                    if !cache.needs_rebuild_smart(&pm.module_name, pm.source_hash, &export_diffs) {
                        if let Some(exports) = cache.get_exports(&pm.module_name) {
                            done += 1;
                            cached_count += 1;
                            eprintln!(
                                "[{}/{}] [skipping] {}",
                                done, total_modules, pm.module_name
                            );
                            registry.register(&pm.module_parts, exports.clone());
                            module_results.push(ModuleResult {
                                path: pm.path.clone(),
                                module_name: pm.module_name.clone(),
                                type_errors: vec![],
                                cached: true,
                            });
                            continue;
                        }
                    }
                }
                to_typecheck.push(idx);
            }

            // Lazy parse any cache-skipped modules that now need typechecking
            for &idx in &to_typecheck {
                if parsed[idx].module.is_none() {
                    let source = sources[parsed[idx].source_idx].1;
                    match crate::parser::parse(source) {
                        Ok(module) => {
                            parsed[idx].module = Some(module);
                        }
                        Err(e) => {
                            build_errors.push(BuildError::CompileError {
                                path: parsed[idx].path.clone(),
                                error: e,
                            });
                        }
                    }
                }
            }
            // Remove entries that failed to parse
            to_typecheck.retain(|&idx| parsed[idx].module.is_some());

            // Print [compiling] for all modules in this level before starting
            for &idx in &to_typecheck {
                let pm = &parsed[idx];
                eprintln!(
                    "[{}/{}] [compiling] {}",
                    done, total_modules, pm.module_name
                );
            }

            // Build GlobalCodegenData before parallel block (modules in same level are independent)
            let global_codegen = if options.output_dir.is_some() {
                Some(crate::codegen::js::GlobalCodegenData::from_registry(&registry))
            } else {
                None
            };
            let do_ffi = js_sources.is_some();

            // Typecheck + codegen in parallel
            let level_results: Vec<_> = pool.install(|| {
                to_typecheck.par_iter().map(|&idx| {
                    let pm = &parsed[idx];
                    let module_ref = pm.module.as_ref().unwrap();
                    let tc_start = Instant::now();
                    let check_result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                        let (ast_module, convert_errors) = crate::ast::convert(module_ref, &registry);
                        let mut result = check::check_module(&ast_module, &registry);
                        if !convert_errors.is_empty() {
                            let mut all_errors = convert_errors;
                            all_errors.extend(result.errors);
                            result.errors = all_errors;
                        }

                        // FFI validation
                        let mut ffi_errors_out = Vec::new();
                        if do_ffi {
                            let foreign_names = extract_foreign_import_names(module_ref);
                            let has_foreign = !foreign_names.is_empty();
                            match (&pm.js_source, has_foreign) {
                                (Some(js_src), _) => {
                                    match js_ffi::parse_foreign_module(js_src) {
                                        Ok(info) => {
                                            for err in js_ffi::validate_foreign_module(&foreign_names, &info) {
                                                ffi_errors_out.push(match err {
                                                    js_ffi::FfiError::DeprecatedFFICommonJSModule =>
                                                        BuildError::DeprecatedFFICommonJSModule { module_name: pm.module_name.clone(), path: pm.path.clone() },
                                                    js_ffi::FfiError::MissingFFIImplementations { missing } =>
                                                        BuildError::MissingFFIImplementations { module_name: pm.module_name.clone(), path: pm.path.clone(), missing },
                                                    js_ffi::FfiError::UnsupportedFFICommonJSExports { exports } =>
                                                        BuildError::UnsupportedFFICommonJSExports { module_name: pm.module_name.clone(), path: pm.path.clone(), exports },
                                                    js_ffi::FfiError::UnsupportedFFICommonJSImports { imports } =>
                                                        BuildError::UnsupportedFFICommonJSImports { module_name: pm.module_name.clone(), path: pm.path.clone(), imports },
                                                    js_ffi::FfiError::ParseError { message } =>
                                                        BuildError::FFIParseError { module_name: pm.module_name.clone(), path: pm.path.clone(), message },
                                                });
                                            }
                                        }
                                        Err(msg) => {
                                            ffi_errors_out.push(BuildError::FFIParseError { module_name: pm.module_name.clone(), path: pm.path.clone(), message: msg });
                                        }
                                    }
                                }
                                (None, true) => {
                                    ffi_errors_out.push(BuildError::MissingFFIModule { module_name: pm.module_name.clone(), path: pm.path.with_extension("js") });
                                }
                                (None, false) => {}
                            }
                        }

                        // Codegen (only if no type errors)
                        let js_text = if result.errors.is_empty() {
                            if let Some(ref global_codegen) = global_codegen {
                                let module_exports_ref = &result.exports;
                                let has_ffi = pm.js_source.is_some();
                                let js_module = crate::codegen::js::module_to_js(
                                    module_ref, &pm.module_name, &pm.module_parts,
                                    module_exports_ref, &registry, has_ffi, global_codegen,
                                );
                                Some(crate::codegen::printer::print_module(&js_module))
                            } else {
                                None
                            }
                        } else {
                            None
                        };

                        (result, ffi_errors_out, js_text)
                    }));
                    (idx, check_result, tc_start.elapsed())
                }).collect()
            });

            // Register results sequentially (registry needs &mut)
            for (idx, check_result, elapsed) in level_results {
                let pm = &parsed[idx];
                done += 1;
                match check_result {
                    Ok((result, ffi_errors, js_text)) => {
                        log::debug!(
                            "  [{}/{}] ok: {} ({:.2?})",
                            done, total_modules, pm.module_name, elapsed
                        );
                        build_errors.extend(ffi_errors);

                        let has_errors = !result.errors.is_empty();
                        if has_errors {
                            // Don't cache modules with type errors
                            let old_exports = cache.as_mut().and_then(|c| c.get_exports(&pm.module_name).cloned());
                            if let Some(ref mut c) = cache {
                                c.remove(&pm.module_name);
                            }
                            let diff = if let Some(old) = old_exports {
                                cache::ExportDiff::compute(&old, &result.exports)
                            } else {
                                let mut d = cache::ExportDiff::default();
                                d.instances_changed = true;
                                d
                            };
                            if !diff.is_empty() {
                                log::debug!(
                                    "[build-plan] {} exports changed: values={:?}, types={:?}, classes={:?}, instances={}, operators={}",
                                    pm.module_name, diff.changed_values, diff.changed_types, diff.changed_classes,
                                    diff.instances_changed, diff.operators_changed
                                );
                                export_diffs.insert(pm.module_name.clone(), diff);
                            }
                        } else {
                            let import_names: Vec<String> = pm.import_parts.iter()
                                .map(|parts| interner::resolve_module_name(parts))
                                .collect();
                            let module_ref = pm.module.as_ref().unwrap();
                            let import_items = cache::extract_import_items(&module_ref.imports);
                            let old_exports = cache.as_mut().and_then(|c| c.get_exports(&pm.module_name).cloned());
                            let exports_changed = if let Some(ref mut c) = cache {
                                c.update(pm.module_name.clone(), pm.source_hash, result.exports.clone(), import_names, import_items)
                            } else {
                                true
                            };
                            if exports_changed {
                                let diff = if let Some(old) = old_exports {
                                    cache::ExportDiff::compute(&old, &result.exports)
                                } else {
                                    let mut d = cache::ExportDiff::default();
                                    d.instances_changed = true;
                                    d
                                };
                                if !diff.is_empty() {
                                    log::debug!(
                                    "[build-plan] {} exports changed: values={:?}, types={:?}, classes={:?}, instances={}, operators={}",
                                    pm.module_name, diff.changed_values, diff.changed_types, diff.changed_classes,
                                    diff.instances_changed, diff.operators_changed
                                );
                                export_diffs.insert(pm.module_name.clone(), diff);
                                }
                            }
                        }
                        registry.register(&pm.module_parts, result.exports);

                        // Write codegen output
                        if let Some(js_text) = js_text {
                            if let Some(ref output_dir) = options.output_dir {
                                let module_dir = output_dir.join(&pm.module_name);
                                if let Err(e) = std::fs::create_dir_all(&module_dir) {
                                    build_errors.push(BuildError::FileReadError {
                                        path: module_dir,
                                        error: format!("Failed to create output directory: {e}"),
                                    });
                                } else {
                                    let index_path = module_dir.join("index.js");
                                    if let Err(e) = std::fs::write(&index_path, &js_text) {
                                        build_errors.push(BuildError::FileReadError {
                                            path: index_path,
                                            error: format!("Failed to write JS output: {e}"),
                                        });
                                    }
                                    if let Some(ref js_src) = pm.js_source {
                                        let foreign_path = module_dir.join("foreign.js");
                                        if let Err(e) = std::fs::write(&foreign_path, js_src) {
                                            build_errors.push(BuildError::FileReadError {
                                                path: foreign_path,
                                                error: format!("Failed to write foreign JS: {e}"),
                                            });
                                        }
                                    }
                                }
                            }
                        }

                        module_results.push(ModuleResult {
                            path: pm.path.clone(),
                            module_name: pm.module_name.clone(),
                            type_errors: result.errors,
                            cached: false,
                        });
                    }
                    Err(_payload) => {
                        handle_typecheck_panic(
                            &mut build_errors, pm, elapsed,
                            done, total_modules,
                        );
                    }
                }
            }

            // Drop CSTs to free memory (when codegen is enabled, CSTs are no longer needed)
            if options.output_dir.is_some() {
                for &idx in &to_typecheck {
                    parsed[idx].module = None;
                }
            }
        }
        let err_count = module_results.iter().filter(|r| !r.type_errors.is_empty()).count();
        if !build_errors.is_empty() || err_count > 0 {
            log::debug!("Phase 4: error after level ({} done, {} with errors), stopping", done, err_count);
            break;
        }
    }
    log::debug!(
        "Phase 4 complete: {} modules ({} cached, {} typechecked) in {:.2?}",
        module_results.len(),
        cached_count,
        module_results.len() - cached_count,
        phase_start.elapsed()
    );

    log::debug!(
        "Build pipeline finished in {:.2?} ({} modules, {} errors)",
        pipeline_start.elapsed(),
        module_results.len(),
        build_errors.len()
    );

    let returned_modules: Vec<(PathBuf, Module)> = parsed
        .into_iter()
        .filter_map(|pm| pm.module.map(|m| (pm.path, m)))
        .collect();

    (
        BuildResult {
            modules: module_results,
            build_errors,
        },
        registry,
        returned_modules,
    )
}

/// Build from pre-read source strings. Each entry is (file_path, source_code).
pub fn build_from_sources(sources: &[(&str, &str)]) -> BuildResult {
    let (result, _registry) = build_from_sources_with_registry(sources, None);
    result
}

// ===== Internal functions =====

fn resolve_globs(patterns: &[&str], errors: &mut Vec<BuildError>) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = Vec::new();
    for &pattern in patterns {
        match glob::glob(pattern) {
            Ok(entries) => {
                for entry in entries {
                    match entry {
                        Ok(path) => {
                            if path.extension().map_or(false, |ext| ext == "purs") {
                                paths.push(path);
                            }
                        }
                        Err(e) => errors.push(BuildError::FileReadError {
                            path: e.path().to_path_buf(),
                            error: e.to_string(),
                        }),
                    }
                }
            }
            Err(e) => errors.push(BuildError::InvalidGlob {
                pattern: pattern.to_string(),
                error: e.to_string(),
            }),
        }
    }
    paths.sort();
    paths.dedup();
    paths
}

/// Like topological_sort_levels but excludes certain indices (cyclic modules).
fn topological_sort_excluding(
    parsed: &[ParsedModule],
    module_index: &HashMap<Vec<Symbol>, usize>,
    exclude: &HashSet<usize>,
) -> Result<Vec<usize>, Vec<usize>> {
    let n = parsed.len();
    let active: HashSet<usize> = (0..n).filter(|i| !exclude.contains(i)).collect();
    let mut in_degree: HashMap<usize, usize> = active.iter().map(|&i| (i, 0)).collect();
    let mut dependents: HashMap<usize, Vec<usize>> =
        active.iter().map(|&i| (i, Vec::new())).collect();

    for &i in &active {
        let pm = &parsed[i];
        for imp in &pm.import_parts {
            if let Some(&dep_idx) = module_index.get(imp) {
                if active.contains(&dep_idx) {
                    *in_degree.entry(i).or_default() += 1;
                    dependents.entry(dep_idx).or_default().push(i);
                }
            }
        }
    }

    let mut queue: VecDeque<usize> = in_degree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(&i, _)| i)
        .collect();

    let mut sorted = Vec::new();
    while let Some(idx) = queue.pop_front() {
        sorted.push(idx);
        if let Some(deps) = dependents.get(&idx) {
            for &dep in deps {
                if let Some(deg) = in_degree.get_mut(&dep) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(dep);
                    }
                }
            }
        }
    }

    if sorted.len() == active.len() {
        Ok(sorted)
    } else {
        Err(sorted)
    }
}

/// Topological sort that returns levels (wavefronts) for parallel execution.
/// Modules within the same level have no dependencies on each other and can
/// be typechecked concurrently. Level N+1 depends only on levels 0..=N.
fn topological_sort_levels(
    parsed: &[ParsedModule],
    module_index: &HashMap<Vec<Symbol>, usize>,
) -> Result<Vec<Vec<usize>>, Vec<usize>> {
    let n = parsed.len();
    let mut in_degree = vec![0usize; n];
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); n];

    for (i, pm) in parsed.iter().enumerate() {
        for imp in &pm.import_parts {
            if let Some(&dep_idx) = module_index.get(imp) {
                in_degree[i] += 1;
                dependents[dep_idx].push(i);
            }
        }
    }

    let mut levels = Vec::new();
    let mut current: Vec<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
    let mut total_sorted = 0;

    while !current.is_empty() {
        total_sorted += current.len();
        let mut next = Vec::new();
        for &idx in &current {
            for &dep in &dependents[idx] {
                in_degree[dep] -= 1;
                if in_degree[dep] == 0 {
                    next.push(dep);
                }
            }
        }
        levels.push(current);
        current = next;
    }

    if total_sorted == n {
        Ok(levels)
    } else {
        let sorted_set: HashSet<usize> = levels.iter().flatten().copied().collect();
        let cyclic: Vec<usize> = (0..n).filter(|i| !sorted_set.contains(i)).collect();
        Err(cyclic)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_module() {
        let result = build_from_sources(&[("src/A.purs", "module A where\nx :: Int\nx = 42")]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect::<Vec<_>>()
        );
        assert_eq!(result.modules.len(), 1);
        assert_eq!(result.modules[0].module_name, "A");
        assert!(result.modules[0].type_errors.is_empty());
    }

    #[test]
    fn two_modules_with_dependency() {
        let result = build_from_sources(&[
            ("src/A.purs", "module A where\nx :: Int\nx = 42"),
            ("src/B.purs", "module B where\nimport A\ny = x"),
        ]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect::<Vec<_>>()
        );
        assert_eq!(result.modules.len(), 2);
        // A must come before B
        assert_eq!(result.modules[0].module_name, "A");
        assert_eq!(result.modules[1].module_name, "B");
        assert!(result.modules[0].type_errors.is_empty());
        assert!(result.modules[1].type_errors.is_empty());
    }

    #[test]
    fn diamond_dependency() {
        let result = build_from_sources(&[
            ("src/A.purs", "module A where\nx :: Int\nx = 1"),
            ("src/B.purs", "module B where\nimport A\ny = x"),
            ("src/C.purs", "module C where\nimport A\nz = x"),
            ("src/D.purs", "module D where\nimport B\nimport C\nw = y"),
        ]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect::<Vec<_>>()
        );
        assert_eq!(result.modules.len(), 4);
        // A must come first, D must come last
        assert_eq!(result.modules[0].module_name, "A");
        assert_eq!(result.modules[3].module_name, "D");
        for m in &result.modules {
            assert!(
                m.type_errors.is_empty(),
                "errors in {}: {:?}",
                m.module_name,
                m.type_errors
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn cycle_detection() {
        let result = build_from_sources(&[
            ("src/A.purs", "module A where\nimport B"),
            ("src/B.purs", "module B where\nimport A"),
        ]);
        assert!(
            result
                .build_errors
                .iter()
                .any(|e| matches!(e, BuildError::CycleInModules { .. })),
            "expected CycleInModules error, got: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn missing_module() {
        let result = build_from_sources(&[("src/A.purs", "module A where\nimport NonExistent")]);
        assert!(
            result
                .build_errors
                .iter()
                .any(|e| matches!(e, BuildError::ModuleNotFound { .. })),
            "expected ModuleNotFound error, got: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn duplicate_module_names() {
        let result = build_from_sources(&[
            ("src/A.purs", "module A where\nx = 1"),
            ("lib/A.purs", "module A where\ny = 2"),
        ]);
        assert!(
            result
                .build_errors
                .iter()
                .any(|e| matches!(e, BuildError::DuplicateModule { .. })),
            "expected DuplicateModule error, got: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn prim_import_not_missing() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "module A where\nimport Prim\nx :: Int\nx = 42",
        )]);
        assert!(
            !result
                .build_errors
                .iter()
                .any(|e| matches!(e, BuildError::ModuleNotFound { .. })),
            "Prim import should not cause ModuleNotFound, got: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn type_alias_unification() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "\
module A where

data Identity a = Identity a

data ExceptT e m a = ExceptT (m a)

type Except e a = ExceptT e Identity a

mkExcept :: forall e a. a -> Except e a
mkExcept x = ExceptT (Identity x)

useExceptT :: forall e a. ExceptT e Identity a -> a
useExceptT (ExceptT (Identity x)) = x

roundtrip :: forall a. a -> a
roundtrip x = useExceptT (mkExcept x)
",
        )]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        let m = &result.modules[0];
        assert!(
            m.type_errors.is_empty(),
            "type errors in A: {:?}",
            m.type_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn type_alias_cross_module() {
        let result = build_from_sources(&[
            (
                "src/A.purs",
                "\
module A where

data Identity a = Identity a
data ExceptT e m a = ExceptT (m a)
type Except e a = ExceptT e Identity a

mkExcept :: forall e a. a -> Except e a
mkExcept x = ExceptT (Identity x)
",
            ),
            (
                "src/B.purs",
                "\
module B where
import A

useExceptT :: forall e a. ExceptT e Identity a -> a
useExceptT (ExceptT (Identity x)) = x

roundtrip :: forall a. a -> a
roundtrip x = useExceptT (mkExcept x)
",
            ),
        ]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        for m in &result.modules {
            assert!(
                m.type_errors.is_empty(),
                "type errors in {}: {:?}",
                m.module_name,
                m.type_errors
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn tab_characters_accepted() {
        let result = build_from_sources(&[("src/A.purs", "module A where\nx :: Int\nx =\t42")]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        assert_eq!(result.modules.len(), 1);
        assert!(result.modules[0].type_errors.is_empty());
    }

    #[test]
    fn tab_in_multiline() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "module A where\nf :: Int -> Int\nf x =\n\tlet y = x\n\tin y",
        )]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        assert_eq!(result.modules.len(), 1);
        assert!(result.modules[0].type_errors.is_empty());
    }

    #[test]
    fn instance_head_record_in_type_app() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "\
module A where

data Maybe a = Nothing | Just a

class MyClass a where
  myMethod :: a -> Int

instance myClassMaybe :: MyClass (Maybe { x :: Int }) where
  myMethod _ = 0
",
        )]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        let m = &result.modules[0];
        let head_errors: Vec<_> = m
            .type_errors
            .iter()
            .filter(|e| e.to_string().contains("Invalid"))
            .collect();
        assert!(
            head_errors.is_empty(),
            "should not reject record inside type constructor in instance head, got: {:?}",
            head_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn let_function_binding_recursive() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "module A where\n\nf :: Int -> Int\nf n = let go acc = go acc in go n",
        )]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        let m = &result.modules[0];
        assert!(
            m.type_errors.is_empty(),
            "type errors: {:?}",
            m.type_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn cons_operator_in_pattern() {
        let result = build_from_sources(&[
            (
                "src/A.purs",
                "\
module A where

data List a = Nil | Cons a (List a)

infixr 6 Cons as :
",
            ),
            (
                "src/B.purs",
                "\
module B where
import A

head :: forall a. List a -> a
head (x : _) = x
head Nil = head Nil
",
            ),
        ]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        let b = result
            .modules
            .iter()
            .find(|m| m.module_name == "B")
            .unwrap();
        let pattern_errors: Vec<_> = b
            .type_errors
            .iter()
            .filter(|e| {
                let s = e.to_string();
                s.contains("not a constructor") || s.contains("ctor") || s.contains("operator")
            })
            .collect();
        assert!(
            pattern_errors.is_empty(),
            ": operator should work in patterns, got: {:?}",
            b.type_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn record_instance_resolution() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "\
module A where

data Box a = MkBox a

class MyShow a where
  myShow :: a -> String

instance myShowInt :: MyShow Int where
  myShow _ = \"int\"

instance myShowBox :: MyShow a => MyShow (Box a) where
  myShow (MkBox x) = myShow x

test :: String
test = myShow (MkBox 42)
",
        )]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        let m = &result.modules[0];
        let instance_errors: Vec<_> = m
            .type_errors
            .iter()
            .filter(|e| e.to_string().contains("No instance") || e.to_string().contains("instance"))
            .collect();
        assert!(
            instance_errors.is_empty(),
            "should resolve parameterized instance, got: {:?}",
            m.type_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn nested_type_alias_expansion_across_modules() {
        let result = build_from_sources(&[
            (
                "src/Types.purs",
                "\
module Types where

type Optic p s t a b = p a b -> p s t
type Optic' p s a = Optic p s s a a
",
            ),
            (
                "src/Main.purs",
                "\
module Main where
import Types

myId :: Optic' Function String String
myId f = f
",
            ),
        ]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        for m in &result.modules {
            assert!(
                m.type_errors.is_empty(),
                "type errors in {}: {:?}",
                m.module_name,
                m.type_errors
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn type_alias_with_kind_sig_import() {
        let result = build_from_sources(&[
            (
                "src/Types.purs",
                "\
module Types (module Types) where

type Optic :: (Type -> Type -> Type) -> Type -> Type -> Type -> Type -> Type
type Optic p s t a b = p a b -> p s t
",
            ),
            (
                "src/User.purs",
                "\
module User where
import Types (Optic)

myId :: Optic Function String String String String
myId f = f
",
            ),
        ]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        for m in &result.modules {
            assert!(
                m.type_errors.is_empty(),
                "type errors in {}: {:?}",
                m.module_name,
                m.type_errors
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn type_alias_self_reexport() {
        let result = build_from_sources(&[
            (
                "src/Types.purs",
                "\
module Types (module Types) where

type Optic p s t a b = p a b -> p s t
type Optic' p s a = Optic p s s a a
",
            ),
            (
                "src/User.purs",
                "\
module User where
import Types (Optic, Optic')

myId :: Optic' Function String String
myId f = f
",
            ),
        ]);
        assert!(
            result.build_errors.is_empty(),
            "build errors: {:?}",
            result
                .build_errors
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
        );
        for m in &result.modules {
            assert!(
                m.type_errors.is_empty(),
                "type errors in {}: {:?}",
                m.module_name,
                m.type_errors
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn let_value_cycle_still_detected() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "module A where\n\nf :: Int\nf = let x = x in x",
        )]);
        let m = &result.modules[0];
        assert!(!m.type_errors.is_empty(), "should detect cycle in x = x");
    }
}
