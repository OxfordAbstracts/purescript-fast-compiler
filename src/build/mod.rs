//! Multi-module build pipeline.
//!
//! Discovers PureScript source files via glob patterns, parses them,
//! builds a dependency graph from imports, topologically sorts, and
//! typechecks in dependency order.

pub mod error;

use std::collections::{HashMap, HashSet, VecDeque};
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, RwLock};
use std::time::Instant;

use crate::cst::{Decl, Module};
use crate::interner::{self, Symbol};
use crate::js_ffi;
use crate::typechecker::check::{self, ModuleRegistry};
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;

pub use error::BuildError;

// ===== Build options =====

/// Configuration options for the build pipeline.
#[derive(Debug, Clone, Default)]
pub struct BuildOptions {
    /// Per-module typecheck timeout. If a module takes longer than this to
    /// typecheck, it is skipped and a `TypecheckTimeout` error is recorded.
    /// `None` means no timeout (the default).
    pub module_timeout: Option<std::time::Duration>,
}

// ===== Public types =====

pub struct ModuleResult {
    pub path: PathBuf,
    pub module_name: String,
    pub types: HashMap<Symbol, Type>,
    pub type_errors: Vec<TypeError>,
}

pub struct BuildResult {
    pub modules: Vec<ModuleResult>,
    pub build_errors: Vec<BuildError>,
}

// ===== Internal types =====

struct ParsedModule {
    path: PathBuf,
    module: Module,
    module_name: String,
    module_parts: Vec<Symbol>,
    import_parts: Vec<Vec<Symbol>>,
    js_source: Option<String>,
}

// ===== Helpers =====

fn module_name_string(parts: &[Symbol]) -> String {
    parts
        .iter()
        .map(|s| interner::resolve(*s).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
}

fn is_prim_import(parts: &[Symbol]) -> bool {
    !parts.is_empty() && interner::resolve(parts[0]).unwrap_or_default() == "Prim"
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

/// Build all PureScript modules matching the given glob patterns.
pub fn build(globs: &[&str]) -> BuildResult {
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
    for path in &paths {
        log::debug!("  discovered: {}", path.display());
    }

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

    let mut result = build_from_sources_with_js(&source_refs, &Some(js_refs), None).0;
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
    build_from_sources_with_options(sources, js_sources, start_registry, &BuildOptions::default())
}

/// Build with full control over options (timeouts, etc.).
pub fn build_from_sources_with_options(
    sources: &[(&str, &str)],
    js_sources: &Option<HashMap<&str, &str>>,
    start_registry: Option<Arc<ModuleRegistry>>,
    options: &BuildOptions,
) -> (BuildResult, ModuleRegistry) {
    let pipeline_start = Instant::now();
    let mut build_errors = Vec::new();

    // Phase 2: Parse all sources
    log::debug!(
        "Phase 2c: Parsing {} source files",
        sources.len()
    );
    let phase_start = Instant::now();
    let mut parsed: Vec<ParsedModule> = Vec::new();
    let mut seen_modules: HashMap<Vec<Symbol>, PathBuf> = HashMap::new();

    for &(path_str, source) in sources {
        let path = PathBuf::from(path_str);
        let parse_start = Instant::now();
        let module = match crate::parser::parse(source) {
            Ok(m) => {
                log::debug!(
                    "  parsed {} ({} decls, {} imports) in {:.2?}",
                    path_str,
                    m.decls.len(),
                    m.imports.len(),
                    parse_start.elapsed()
                );
                m
            }
            Err(e) => {
                log::debug!("  parse error in {}: {}", path_str, e);
                build_errors.push(BuildError::CompileError { path, error: e });
                continue;
            }
        };

        let module_parts: Vec<Symbol> = module.name.value.parts.clone();
        let module_name = module_name_string(&module_parts);

        // Check for reserved Prim namespace
        if !module_parts.is_empty() {
            let first = interner::resolve(module_parts[0]).unwrap_or_default();
            if first == "Prim" {
                log::debug!("  rejected {}: Prim namespace is reserved", module_name);
                build_errors.push(BuildError::CannotDefinePrimModules {
                    module_name,
                    path,
                });
                continue;
            }
        }

        // Check for invalid characters in module name segments (no apostrophes or underscores)
        let mut invalid_module = false;
        for part in &module_parts {
            let part_str = interner::resolve(*part).unwrap_or_default();
            if let Some(c) = part_str.chars().find(|&c| c == '\'' || c == '_') {
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

        parsed.push(ParsedModule {
            path,
            module,
            module_name,
            module_parts,
            import_parts,
            js_source,
        });
    }
    log::debug!(
        "Phase 2c complete: parsed {} modules (rejected {}) in {:.2?}",
        parsed.len(),
        sources.len() - parsed.len(),
        phase_start.elapsed()
    );

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
                    span: pm.module.span,
                });
            } else {
                log::debug!(
                    "  resolved import: {} -> {}",
                    pm.module_name,
                    imp_name
                );
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

    let levels: Vec<Vec<usize>> = match topological_sort_levels(&parsed, &module_index) {
        Ok(levels) => {
            log::debug!(
                "  {} dependency levels for parallel build",
                levels.len()
            );
            levels
        }
        Err(cycle_indices) => {
            let cycle_names: Vec<(String, PathBuf)> = cycle_indices
                .iter()
                .map(|&i| (parsed[i].module_name.clone(), parsed[i].path.clone()))
                .collect();
            log::debug!(
                "  cycle detected among: {:?}",
                cycle_names.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>()
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

    // Phase 4: Typecheck in dependency order (parallel by level)
    let total_modules: usize = levels.iter().map(|l| l.len()).sum();
    let num_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    log::debug!(
        "Phase 4: Typechecking {} modules (parallel, {} workers)",
        total_modules,
        num_workers
    );
    let phase_start = Instant::now();
    let timeout = options.module_timeout;

    // Process each level concurrently, synchronize between levels.
    // Registry is behind RwLock: check_module reads, register writes.
    // Use a bounded number of worker threads that pull work from a shared queue.
    let rw_registry = RwLock::new(registry);
    let results = Mutex::new(Vec::new());
    let errors = Mutex::new(Vec::new());
    let modules_done = std::sync::atomic::AtomicUsize::new(0);

    for (level_idx, level) in levels.iter().enumerate() {
        log::debug!(
            "  level {}: {} modules",
            level_idx,
            level.len()
        );
        let work_queue = Mutex::new(level.iter().copied());
        std::thread::scope(|s| {
            let thread_count = num_workers.min(level.len());
            let handles: Vec<_> = (0..thread_count)
                .map(|_| {
                    let work_queue = &work_queue;
                    let rw_registry = &rw_registry;
                    let results = &results;
                    let errors = &errors;
                    let parsed = &parsed;
                    let modules_done = &modules_done;
                    std::thread::Builder::new()
                        .stack_size(64 * 1024 * 1024)
                        .spawn_scoped(s, move || {
                            loop {
                                let idx = {
                                    let mut q = work_queue.lock().unwrap();
                                    q.next()
                                };
                                let Some(idx) = idx else { break };
                                let pm = &parsed[idx];
                                let tc_start = Instant::now();
                                let deadline = timeout.map(|t| tc_start + t);
                                let check_result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                                    crate::typechecker::set_deadline(deadline);
                                    let reg = rw_registry.read().unwrap_or_else(|e| e.into_inner());
                                    let result = check::check_module(&pm.module, &reg);
                                    crate::typechecker::set_deadline(None);
                                    result
                                }));
                                let elapsed = tc_start.elapsed();
                                let done = modules_done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                                match check_result {
                                    Ok(result) => {
                                        log::debug!(
                                            "  [{}/{}] ok: {} ({:.2?})",
                                            done, total_modules, pm.module_name, elapsed
                                        );
                                        rw_registry.write().unwrap_or_else(|e| e.into_inner()).register(&pm.module_parts, result.exports);
                                        results.lock().unwrap().push(ModuleResult {
                                            path: pm.path.clone(),
                                            module_name: pm.module_name.clone(),
                                            types: result.types,
                                            type_errors: result.errors,
                                        });
                                    }
                                    Err(payload) => {
                                        // Distinguish deadline panics from other panics
                                        let is_deadline = payload
                                            .downcast_ref::<&str>()
                                            .map_or(false, |s| *s == "typechecking deadline exceeded")
                                            || payload
                                                .downcast_ref::<String>()
                                                .map_or(false, |s| s == "typechecking deadline exceeded");
                                        if is_deadline {
                                            log::debug!(
                                                "  [{}/{}] timeout: {} ({:.2?})",
                                                done, total_modules, pm.module_name, elapsed
                                            );
                                            errors.lock().unwrap().push(BuildError::TypecheckTimeout {
                                                path: pm.path.clone(),
                                                module_name: pm.module_name.clone(),
                                                timeout_secs: timeout.unwrap().as_secs(),
                                            });
                                        } else {
                                            log::debug!(
                                                "  [{}/{}] panic: {} ({:.2?})",
                                                done, total_modules, pm.module_name, elapsed
                                            );
                                            errors.lock().unwrap().push(BuildError::TypecheckPanic {
                                                path: pm.path.clone(),
                                                module_name: pm.module_name.clone(),
                                            });
                                        }
                                    }
                                }
                            }
                        })
                        .expect("failed to spawn typecheck thread")
                })
                .collect();
            for handle in handles {
                let _ = handle.join();
            }
        });
    }

    build_errors.extend(errors.into_inner().unwrap());
    let module_results = results.into_inner().unwrap();
    registry = rw_registry.into_inner().unwrap_or_else(|e| e.into_inner());
    log::debug!(
        "Phase 4 complete: typechecked {} modules in {:.2?}",
        module_results.len(),
        phase_start.elapsed()
    );

    // Phase 5: FFI validation (only when JS sources were provided)
    if js_sources.is_some() {
    log::debug!("Phase 5: FFI validation");
    let phase_start = Instant::now();
    let mut ffi_checked = 0;
    for pm in &parsed {
        let foreign_names = extract_foreign_import_names(&pm.module);
        let has_foreign = !foreign_names.is_empty();

        match (&pm.js_source, has_foreign) {
            (Some(js_src), _) => {
                log::debug!(
                    "  validating FFI for {} ({} foreign imports)",
                    pm.module_name,
                    foreign_names.len()
                );
                ffi_checked += 1;
                match js_ffi::parse_foreign_module(js_src) {
                    Ok(info) => {
                        let ffi_errors = js_ffi::validate_foreign_module(&foreign_names, &info);
                        if ffi_errors.is_empty() {
                            log::debug!("    FFI OK for {}", pm.module_name);
                        }
                        for err in ffi_errors {
                            match err {
                                js_ffi::FfiError::DeprecatedFFICommonJSModule => {
                                    log::debug!("    FFI error in {}: deprecated CommonJS module", pm.module_name);
                                    build_errors.push(BuildError::DeprecatedFFICommonJSModule {
                                        module_name: pm.module_name.clone(),
                                        path: pm.path.clone(),
                                    });
                                }
                                js_ffi::FfiError::MissingFFIImplementations { missing } => {
                                    log::debug!("    FFI error in {}: missing implementations: {:?}", pm.module_name, missing);
                                    build_errors.push(BuildError::MissingFFIImplementations {
                                        module_name: pm.module_name.clone(),
                                        path: pm.path.clone(),
                                        missing,
                                    });
                                }
                                js_ffi::FfiError::UnusedFFIImplementations { unused } => {
                                    log::debug!("    FFI error in {}: unused implementations: {:?}", pm.module_name, unused);
                                    build_errors.push(BuildError::UnusedFFIImplementations {
                                        module_name: pm.module_name.clone(),
                                        path: pm.path.clone(),
                                        unused,
                                    });
                                }
                                js_ffi::FfiError::UnsupportedFFICommonJSExports { exports } => {
                                    build_errors.push(BuildError::UnsupportedFFICommonJSExports {
                                        module_name: pm.module_name.clone(),
                                        path: pm.path.clone(),
                                        exports,
                                    });
                                }
                                js_ffi::FfiError::UnsupportedFFICommonJSImports { imports } => {
                                    build_errors.push(BuildError::UnsupportedFFICommonJSImports {
                                        module_name: pm.module_name.clone(),
                                        path: pm.path.clone(),
                                        imports,
                                    });
                                }
                                js_ffi::FfiError::ParseError { message } => {
                                    log::debug!("    FFI parse error in {}: {}", pm.module_name, message);
                                    build_errors.push(BuildError::FFIParseError {
                                        module_name: pm.module_name.clone(),
                                        path: pm.path.clone(),
                                        message,
                                    });
                                }
                            }
                        }
                    }
                    Err(msg) => {
                        log::debug!("    FFI parse error in {}: {}", pm.module_name, msg);
                        build_errors.push(BuildError::FFIParseError {
                            module_name: pm.module_name.clone(),
                            path: pm.path.clone(),
                            message: msg,
                        });
                    }
                }
            }
            (None, true) => {
                log::debug!(
                    "  missing FFI companion for {} ({} foreign imports)",
                    pm.module_name,
                    foreign_names.len()
                );
                build_errors.push(BuildError::MissingFFIModule {
                    module_name: pm.module_name.clone(),
                    path: pm.path.with_extension("js"),
                });
            }
            (None, false) => {}
        }
    }
    log::debug!(
        "Phase 5 complete: validated {} FFI modules in {:.2?}",
        ffi_checked,
        phase_start.elapsed()
    );
    } // end if js_sources.is_some()

    log::debug!(
        "Build pipeline finished in {:.2?} ({} modules, {} errors)",
        pipeline_start.elapsed(),
        module_results.len(),
        build_errors.len()
    );

    (
        BuildResult {
            modules: module_results,
            build_errors,
        },
        registry,
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
        // B should have y :: Int
        let y_sym = interner::intern("y");
        let y_ty = result.modules[1].types.get(&y_sym).expect("y not found");
        assert_eq!(*y_ty, Type::int());
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
    fn parse_error_resilience() {
        let result = build_from_sources(&[
            ("src/A.purs", "module A where\nx :: Int\nx = 42"),
            ("src/Bad.purs", "this is not valid purescript"),
            ("src/B.purs", "module B where\nimport A\ny = x"),
        ]);
        // Should have a parse error for Bad.purs
        assert!(
            result
                .build_errors
                .iter()
                .any(|e| matches!(e, BuildError::CompileError { .. })),
            "expected CompileError"
        );
        // A and B should still compile successfully
        assert_eq!(result.modules.len(), 2);
        assert!(result.modules.iter().all(|m| m.type_errors.is_empty()));
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
        let result = build_from_sources(&[
            ("src/A.purs", "\
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
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        let m = &result.modules[0];
        assert!(m.type_errors.is_empty(), "type errors in A: {:?}",
            m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn type_alias_cross_module() {
        let result = build_from_sources(&[
            ("src/A.purs", "\
module A where

data Identity a = Identity a
data ExceptT e m a = ExceptT (m a)
type Except e a = ExceptT e Identity a

mkExcept :: forall e a. a -> Except e a
mkExcept x = ExceptT (Identity x)
"),
            ("src/B.purs", "\
module B where
import A

useExceptT :: forall e a. ExceptT e Identity a -> a
useExceptT (ExceptT (Identity x)) = x

roundtrip :: forall a. a -> a
roundtrip x = useExceptT (mkExcept x)
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        for m in &result.modules {
            assert!(m.type_errors.is_empty(), "type errors in {}: {:?}",
                m.module_name,
                m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        }
    }

    #[test]
    fn tab_characters_accepted() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "module A where\nx :: Int\nx =\t42",
        )]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        assert_eq!(result.modules.len(), 1);
        assert!(result.modules[0].type_errors.is_empty());
    }

    #[test]
    fn tab_in_multiline() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "module A where\nf :: Int -> Int\nf x =\n\tlet y = x\n\tin y",
        )]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        assert_eq!(result.modules.len(), 1);
        assert!(result.modules[0].type_errors.is_empty());
    }

    #[test]
    fn export_despite_type_error() {
        let result = build_from_sources(&[
            ("src/A.purs", "\
module A where

f :: Int -> Int
f x = x

g :: String
g = 42
"),
            ("src/B.purs", "\
module B where
import A

y :: Int
y = f 1
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        let a = result.modules.iter().find(|m| m.module_name == "A").unwrap();
        assert!(!a.type_errors.is_empty(), "A should have type errors from g");
        let b = result.modules.iter().find(|m| m.module_name == "B").unwrap();
        assert!(b.type_errors.is_empty(), "B should compile cleanly, got: {:?}",
            b.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn signature_exported_on_body_error() {
        let result = build_from_sources(&[
            ("src/A.purs", "\
module A where

h :: Int -> Int
h x = \"not an int\"
"),
            ("src/B.purs", "\
module B where
import A

y :: Int -> Int
y = h
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        let a = result.modules.iter().find(|m| m.module_name == "A").unwrap();
        assert!(!a.type_errors.is_empty(), "A should have type errors from h");
        let b = result.modules.iter().find(|m| m.module_name == "B").unwrap();
        assert!(b.type_errors.is_empty(), "B should compile cleanly using h's declared signature, got: {:?}",
            b.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
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
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        let m = &result.modules[0];
        let head_errors: Vec<_> = m.type_errors.iter()
            .filter(|e| e.to_string().contains("Invalid"))
            .collect();
        assert!(head_errors.is_empty(),
            "should not reject record inside type constructor in instance head, got: {:?}",
            head_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn let_function_binding_recursive() {
        let result = build_from_sources(&[(
            "src/A.purs",
            "module A where\n\nf :: Int -> Int\nf n = let go acc = go acc in go n",
        )]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        let m = &result.modules[0];
        assert!(m.type_errors.is_empty(), "type errors: {:?}",
            m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn cons_operator_in_pattern() {
        let result = build_from_sources(&[
            ("src/A.purs", "\
module A where

data List a = Nil | Cons a (List a)

infixr 6 Cons as :
"),
            ("src/B.purs", "\
module B where
import A

head :: forall a. List a -> a
head (x : _) = x
head Nil = head Nil
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        let b = result.modules.iter().find(|m| m.module_name == "B").unwrap();
        let pattern_errors: Vec<_> = b.type_errors.iter()
            .filter(|e| {
                let s = e.to_string();
                s.contains("not a constructor") || s.contains("ctor") || s.contains("operator")
            })
            .collect();
        assert!(pattern_errors.is_empty(),
            ": operator should work in patterns, got: {:?}",
            b.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
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
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        let m = &result.modules[0];
        let instance_errors: Vec<_> = m.type_errors.iter()
            .filter(|e| e.to_string().contains("No instance") || e.to_string().contains("instance"))
            .collect();
        assert!(instance_errors.is_empty(),
            "should resolve parameterized instance, got: {:?}",
            m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn nested_type_alias_expansion_across_modules() {
        let result = build_from_sources(&[
            ("src/Types.purs", "\
module Types where

type Optic p s t a b = p a b -> p s t
type Optic' p s a = Optic p s s a a
"),
            ("src/Main.purs", "\
module Main where
import Types

myId :: Optic' Function String String
myId f = f
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        for m in &result.modules {
            assert!(m.type_errors.is_empty(), "type errors in {}: {:?}",
                m.module_name,
                m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        }
    }

    #[test]
    fn type_alias_with_kind_sig_import() {
        let result = build_from_sources(&[
            ("src/Types.purs", "\
module Types (module Types) where

type Optic :: (Type -> Type -> Type) -> Type -> Type -> Type -> Type -> Type
type Optic p s t a b = p a b -> p s t
"),
            ("src/User.purs", "\
module User where
import Types (Optic)

myId :: Optic Function String String String String
myId f = f
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        for m in &result.modules {
            assert!(m.type_errors.is_empty(), "type errors in {}: {:?}",
                m.module_name,
                m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
        }
    }

    #[test]
    fn type_alias_self_reexport() {
        let result = build_from_sources(&[
            ("src/Types.purs", "\
module Types (module Types) where

type Optic p s t a b = p a b -> p s t
type Optic' p s a = Optic p s s a a
"),
            ("src/User.purs", "\
module User where
import Types (Optic, Optic')

myId :: Optic' Function String String
myId f = f
"),
        ]);
        assert!(result.build_errors.is_empty(), "build errors: {:?}",
            result.build_errors.iter().map(|e| format!("{}", e)).collect::<Vec<_>>());
        for m in &result.modules {
            assert!(m.type_errors.is_empty(), "type errors in {}: {:?}",
                m.module_name,
                m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
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
