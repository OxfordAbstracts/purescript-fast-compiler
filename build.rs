use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

fn main() {
    lalrpop::process_root().unwrap();

    // Embed git commit hash at compile time
    let output = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output();
    if let Ok(output) = output {
        let hash = String::from_utf8_lossy(&output.stdout).trim().to_string();
        println!("cargo:rustc-env=PFC_GIT_COMMIT={hash}");
    }

    // Cache epoch: a digest of every compiler source file. Folded into every
    // persistent cache key (per-decl `input_hash` + module memo), so ANY change
    // to the compiler invalidates stale cached results. Without this, a cache
    // written by one compiler build is silently reused by a later build whose
    // inference logic changed — the exact incoherence that produced spurious
    // `Mismatch(Record([], None), …)` errors on the oa app after the compiler
    // was iterated on (PASS_VERSION bumps are easy to forget; this makes cache
    // coherence automatic). A committed, unchanged compiler yields a stable
    // epoch, so warm rebuilds of the SAME binary still hit the cache.
    let mut hasher = DefaultHasher::new();
    let mut files: Vec<PathBuf> = Vec::new();
    collect_rs_files(Path::new("src"), &mut files);
    files.sort();
    for path in &files {
        // Watch each file so cargo reruns this script (and recomputes the
        // epoch) whenever any source file's contents change.
        println!("cargo:rerun-if-changed={}", path.display());
        if let Ok(bytes) = std::fs::read(path) {
            path.to_string_lossy().hash(&mut hasher);
            bytes.hash(&mut hasher);
        }
    }
    // Cargo manifest + lockfile also affect compiled behavior (a dependency
    // version bump can change inference/codegen without touching any .rs file).
    for extra in ["Cargo.toml", "Cargo.lock", "build.rs"] {
        println!("cargo:rerun-if-changed={extra}");
        if let Ok(bytes) = std::fs::read(extra) {
            extra.hash(&mut hasher);
            bytes.hash(&mut hasher);
        }
    }
    let epoch = hasher.finish();
    println!("cargo:rustc-env=PFC_CACHE_EPOCH={epoch:016x}");
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else {
            // `.rs` source plus `.lalrpop` grammars: a grammar edit changes how
            // identical source text parses, so it must bump the epoch too (the
            // per-decl cache keys on source TEXT, not the parsed CST).
            let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
            if ext == "rs" || ext == "lalrpop" {
                out.push(path);
            }
        }
    }
}
