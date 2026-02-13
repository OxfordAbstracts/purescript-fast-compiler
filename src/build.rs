//! Multi-module build pipeline.
//!
//! Discovers PureScript source files via glob patterns, parses them,
//! builds a dependency graph from imports, topologically sorts, and
//! typechecks in dependency order.

use std::collections::{HashMap, HashSet, VecDeque};
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::sync::Arc;

use crate::ast::span::Span;
use crate::cst::Module;
use crate::diagnostics::CompilerError;
use crate::interner::{self, Symbol};
use crate::typechecker::check::{self, ModuleRegistry};
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;
use thiserror::Error;

// ===== Public types =====

#[derive(Error, Debug)]
pub enum BuildError {
    #[error("Invalid glob pattern '{pattern}': {error}")]
    InvalidGlob { pattern: String, error: String },
    #[error("Failed to read file '{path}': {error}")]
    FileReadError { path: PathBuf, error: String },
    #[error("Compile error in '{path}': {error}")]
    CompileError { path: PathBuf, error: CompilerError },
    #[error("Module not found: '{module_name}' imported by '{importing_module}' found in '{path}' at '{span}'")]
    ModuleNotFound {
        module_name: String,
        importing_module: String,
        path: PathBuf,
        span: Span,
    },
    #[error("Cycle detected in module imports: {cycle:?}")]
    CycleInModules { cycle: Vec<(String, PathBuf)> },
    #[error("Duplicate module name '{module_name}' found in '{path1}' and '{path2}'")]
    DuplicateModule {
        module_name: String,
        path1: PathBuf,
        path2: PathBuf,
    },
    #[error("Typechecking panicked in module '{module_name}' at '{path}'")]
    TypecheckPanic { path: PathBuf, module_name: String },
}

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

// ===== Public API =====

/// Build all PureScript modules matching the given glob patterns.
pub fn build(globs: &[&str]) -> BuildResult {
    let mut build_errors = Vec::new();

    // Phase 1: Glob resolution
    let paths = resolve_globs(globs, &mut build_errors);

    // Phase 2: Read and parse
    let mut sources = Vec::new();
    for path in &paths {
        match std::fs::read_to_string(path) {
            Ok(source) => sources.push((path.to_string_lossy().into_owned(), source)),
            Err(e) => build_errors.push(BuildError::FileReadError {
                path: path.clone(),
                error: e.to_string(),
            }),
        }
    }

    let source_refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    let mut result = build_from_sources(&source_refs);
    // Prepend file-level errors before source-level errors
    build_errors.append(&mut result.build_errors);
    result.build_errors = build_errors;
    result
}

pub fn build_from_sources_with_registry(
    sources: &[(&str, &str)],
    start_registry: Option<Arc<ModuleRegistry>>,
) -> (BuildResult, ModuleRegistry) {
    let mut build_errors = Vec::new();

    // Phase 2: Parse all sources
    let mut parsed: Vec<ParsedModule> = Vec::new();
    let mut seen_modules: HashMap<Vec<Symbol>, PathBuf> = HashMap::new();

    for &(path_str, source) in sources {
        let path = PathBuf::from(path_str);
        let module = match crate::parser::parse(source) {
            Ok(m) => m,
            Err(e) => {
                build_errors.push(BuildError::CompileError { path, error: e });
                continue;
            }
        };

        let module_parts: Vec<Symbol> = module.name.value.parts.clone();
        let module_name = module_name_string(&module_parts);

        // Check for duplicate module names
        if let Some(existing_path) = seen_modules.get(&module_parts) {
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

        parsed.push(ParsedModule {
            path,
            module,
            module_name,
            module_parts,
            import_parts,
        });
    }

    // Phase 3: Build dependency graph and check for unknown imports
    let known_modules: HashSet<Vec<Symbol>> =
        parsed.iter().map(|p| p.module_parts.clone()).collect();

    let mut registry = match start_registry {
        Some(base) => ModuleRegistry::with_base(base),
        None => ModuleRegistry::default(),
    };

    for pm in &parsed {
        for imp_parts in &pm.import_parts {
            if !known_modules.contains(imp_parts) && !registry.contains(imp_parts) {
                build_errors.push(BuildError::ModuleNotFound {
                    module_name: module_name_string(imp_parts),
                    importing_module: pm.module_name.clone(),
                    path: pm.path.clone(),
                    span: pm.module.span,
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
    let sorted = match topological_sort(&parsed, &module_index) {
        Ok(order) => order,
        Err(cycle_indices) => {
            let cycle_names: Vec<(String, PathBuf)> = cycle_indices
                .iter()
                .map(|&i| (parsed[i].module_name.clone(), parsed[i].path.clone()))
                .collect();
            build_errors.push(BuildError::CycleInModules { cycle: cycle_names });
            // Typecheck only non-cyclic modules
            let cyclic: HashSet<usize> = cycle_indices.into_iter().collect();
            match topological_sort_excluding(&parsed, &module_index, &cyclic) {
                Ok(order) => order,
                Err(_) => Vec::new(),
            }
        }
    };

    // Phase 4: Typecheck in dependency order
    // Each module is typechecked in a catch_unwind so a panic in one module
    // (e.g. from an unimplemented feature) doesn't abort the entire build.
    let mut module_results = Vec::new();

    for idx in sorted {
        let pm = &parsed[idx];
        let check_result = std::panic::catch_unwind(AssertUnwindSafe(|| {
            check::check_module(&pm.module, &registry)
        }));
        match check_result {
            Ok(result) => {
                registry.register(&pm.module_parts, result.exports);
                module_results.push(ModuleResult {
                    path: pm.path.clone(),
                    module_name: pm.module_name.clone(),
                    types: result.types,
                    type_errors: result.errors,
                });
            }
            Err(_) => {
                // Module typechecking panicked — record as a build error and skip
                build_errors.push(BuildError::TypecheckPanic {
                    path: pm.path.clone(),
                    module_name: pm.module_name.clone(),
                });
            }
        }
    }

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

/// Kahn's algorithm topological sort. Returns ordered indices into `parsed`.
fn topological_sort(
    parsed: &[ParsedModule],
    module_index: &HashMap<Vec<Symbol>, usize>,
) -> Result<Vec<usize>, Vec<usize>> {
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

    let mut queue: VecDeque<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();

    let mut sorted = Vec::with_capacity(n);
    while let Some(idx) = queue.pop_front() {
        sorted.push(idx);
        for &dep in &dependents[idx] {
            in_degree[dep] -= 1;
            if in_degree[dep] == 0 {
                queue.push_back(dep);
            }
        }
    }

    if sorted.len() == n {
        Ok(sorted)
    } else {
        // Return indices of modules stuck in cycles
        let sorted_set: HashSet<usize> = sorted.iter().copied().collect();
        let cyclic: Vec<usize> = (0..n).filter(|i| !sorted_set.contains(i)).collect();
        Err(cyclic)
    }
}

/// Like topological_sort but excludes certain indices (cyclic modules).
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
}
