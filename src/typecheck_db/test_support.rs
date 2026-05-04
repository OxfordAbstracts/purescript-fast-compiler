//! Shared discovery / parsing helpers used by both
//! `typecheck_db::tests::all_packages` (the in-tree acceptance test)
//! and the `typecheck_db_packages` criterion bench under `benches/`.
//!
//! Lives here rather than under `tests/` so the helpers are visible
//! to both rustdoc-test and the bench crate (benches build as
//! separate binaries that only see `pub` items in the lib).

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::cst;
use crate::parser::parse;
use crate::typecheck_db::driver_multi::ModuleInput;

const FIXTURES_ROOT: &str = "tests/fixtures";

pub fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

pub fn packages_root() -> PathBuf {
    manifest_dir().join(FIXTURES_ROOT).join("packages")
}

/// Recursively gather `.purs` files under `root`, skipping spago /
/// build caches.
pub fn collect_purs_files(root: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    if !root.exists() {
        return out;
    }
    let entries = match fs::read_dir(root) {
        Ok(e) => e,
        Err(_) => return out,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name == ".spago" || name == "output" || name == ".psc-package" {
            continue;
        }
        if path.is_dir() {
            out.extend(collect_purs_files(&path));
        } else if path.extension().and_then(|s| s.to_str()) == Some("purs") {
            out.push(path);
        }
    }
    out
}

/// Discover every `.purs` source under `tests/fixtures/packages/<pkg>/src/`.
/// Mirrors the discovery rule of `tests/build.rs::build_all_packages`:
/// only packages that have a `src/` subdirectory, only files inside
/// `src/`.
pub fn gather_package_src_sources() -> Vec<PathBuf> {
    let packages = packages_root();
    let mut files: Vec<PathBuf> = Vec::new();
    let entries = match fs::read_dir(&packages) {
        Ok(e) => e,
        Err(_) => return files,
    };
    let mut sorted: Vec<_> = entries.flatten().collect();
    sorted.sort_by_key(|e| e.file_name());
    for entry in sorted {
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        let src_dir = path.join("src");
        if !src_dir.exists() {
            continue;
        }
        files.extend(collect_purs_files(&src_dir));
    }
    files
}

pub fn module_name_of(m: &cst::Module) -> String {
    m.name
        .value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
}

pub fn extract_panic_msg(
    payload: Box<dyn std::any::Any + Send + 'static>,
) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "panicked (non-string payload)".to_string()
    }
}

/// Pull out each top-level import target from a CST.
pub fn imports_of(module: &cst::Module) -> Vec<String> {
    module
        .imports
        .iter()
        .map(|imp| {
            imp.module
                .parts
                .iter()
                .map(|p| crate::interner::resolve(*p).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect()
}

/// Parse every `.purs` source under packages/<pkg>/src and index by
/// module name.
pub fn package_modules_by_name() -> HashMap<String, ModuleInput> {
    let files = gather_package_src_sources();
    let mut out = HashMap::with_capacity(files.len());
    for file in files {
        let src = match fs::read_to_string(&file) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let module = match parse(&src) {
            Ok(m) => m,
            Err(_) => continue,
        };
        let name = module_name_of(&module);
        out.entry(name.clone())
            .or_insert(ModuleInput::new(name, src, module));
    }
    out
}

/// Compute the transitive import closure of a single target module
/// against a parsed-package map. Returns fresh `ModuleInput`s
/// (cloned), suitable for feeding to `check_many_modules`.
pub fn transitive_closure_of(
    target: &str,
    pkgs: &HashMap<String, ModuleInput>,
) -> Vec<ModuleInput> {
    let mut visited: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut stack: Vec<String> = vec![target.to_string()];
    let mut out: Vec<ModuleInput> = Vec::new();
    while let Some(name) = stack.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        if let Some(m) = pkgs.get(&name) {
            stack.extend(imports_of(&m.module));
            out.push(ModuleInput::new(
                m.name.clone(),
                m.source.clone(),
                m.module.clone(),
            ));
        }
    }
    out
}
