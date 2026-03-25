mod test_utils;

use ntest_timeout::timeout;
use purescript_fast_compiler::build::{build_from_sources_with_options, BuildOptions};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;
use wait_timeout::ChildExt;

fn collect_purs_files(dir: &Path, files: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_purs_files(&path, files);
            } else if path.extension().is_some_and(|e| e == "purs") {
                files.push(path);
            }
        }
    }
}

/// Collect JS companion files for a set of .purs sources.
fn collect_js_companions(sources: &[(String, String)]) -> HashMap<String, String> {
    let mut js_sources = HashMap::new();
    for (purs_path, _) in sources {
        let p = PathBuf::from(purs_path);
        let js_path = p.with_extension("js");
        if js_path.exists() {
            if let Ok(js_source) = std::fs::read_to_string(&js_path) {
                js_sources.insert(purs_path.clone(), js_source);
            }
        }
    }
    js_sources
}

/// Read sources.txt and resolve globs relative to the package directory.
/// Returns (purs_path, purs_source) pairs.
fn collect_sources_from_globs(package_dir: &Path) -> Vec<(String, String)> {
    let sources_txt = package_dir.join("sources.txt");
    let content = std::fs::read_to_string(&sources_txt)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", sources_txt.display(), e));

    let mut sources = Vec::new();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let pattern = package_dir.join(line);
        let pattern_str = pattern.to_string_lossy();
        for entry in glob::glob(&pattern_str).expect("Invalid glob pattern") {
            if let Ok(path) = entry {
                if path.extension().is_some_and(|e| e == "purs") {
                    if let Ok(source) = std::fs::read_to_string(&path) {
                        sources.push((path.to_string_lossy().into_owned(), source));
                    }
                }
            }
        }
    }
    sources
}

fn run_package_test(package_name: &str, timeout_secs: u64) {
    let package_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/fixtures/packages/{}", package_name));
    let output_dir = package_dir.join("output-new");

    let _ = std::fs::remove_dir_all(&output_dir);
    std::fs::create_dir_all(&output_dir).unwrap();

    let sources = collect_sources_from_globs(&package_dir);
    assert!(!sources.is_empty(), "No PureScript sources found");

    eprintln!("Building {} package ({} modules)...", package_name, sources.len());

    let js_companions = collect_js_companions(&sources);
    let js_refs: HashMap<&str, &str> = js_companions
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();

    let source_refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    let options = BuildOptions {
        output_dir: Some(output_dir.clone()),
        ..Default::default()
    };

    let (result, _registry) =
        build_from_sources_with_options(&source_refs, &Some(js_refs), None, &options);

    if !result.build_errors.is_empty() {
        for e in &result.build_errors {
            eprintln!("Build error: {}", e);
        }
        panic!("{} build error(s)", result.build_errors.len());
    }

    let mut type_error_count = 0;
    for m in &result.modules {
        if !m.type_errors.is_empty() {
            type_error_count += m.type_errors.len();
            eprintln!("Type errors in {}:", m.module_name);
            for e in &m.type_errors {
                eprintln!("  {}", e);
            }
        }
    }
    assert!(type_error_count == 0, "{} type error(s) across modules", type_error_count);

    let main_index = output_dir.join("Test.Main").join("index.js");
    assert!(
        main_index.exists(),
        "Test.Main/index.js was not generated at {}",
        main_index.display()
    );

    let script = format!(
        "import('file://{}').then(m => m.main())",
        main_index.display()
    );
    let node_bin = ["/opt/homebrew/bin/node", "/usr/local/bin/node", "/usr/bin/node"]
        .iter()
        .find(|p| Path::new(p).exists())
        .copied()
        .unwrap_or("node");
    let node_result = Command::new(node_bin)
        .arg("--no-warnings")
        .arg("-e")
        .arg(&script)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn();

    match node_result {
        Ok(mut child) => {
            match child.wait_timeout(Duration::from_secs(timeout_secs)) {
                Ok(Some(status)) => {
                    let mut stdout = String::new();
                    let mut stderr = String::new();
                    if let Some(ref mut out) = child.stdout {
                        std::io::Read::read_to_string(out, &mut stdout).ok();
                    }
                    if let Some(ref mut err) = child.stderr {
                        std::io::Read::read_to_string(err, &mut stderr).ok();
                    }

                    eprintln!("Node stdout:\n{}", stdout);
                    if !stderr.is_empty() {
                        eprintln!("Node stderr:\n{}", stderr);
                    }

                    assert!(
                        status.success(),
                        "Node exited with non-zero status: {}",
                        status
                    );
                }
                Ok(None) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("Node timed out ({}s)", timeout_secs);
                }
                Err(e) => {
                    panic!("Node wait failed: {}", e);
                }
            }
        }
        Err(e) => {
            panic!("Failed to spawn node: {}", e);
        }
    }
}

#[test]
#[timeout(20000)]
fn aff_test_main() {
    run_package_test("aff", 30);
}
#[test]
#[timeout(20000)]
fn spec_test_main() {
    run_package_test("spec", 30);
}

#[test]
#[timeout(20000)]
fn datetime_parsing_test_main() {
    run_package_test("datetime-parsing", 30);
}

#[test]
#[timeout(20000)]
fn argonaut_codecs_test_main() {
    run_package_test("argonaut-codecs", 30);
}

#[test]
#[timeout(20000)]
fn hyrlue_test_main() {
    run_package_test("hyrule", 30);
}

#[test]
#[timeout(20000)]
fn tidy_codegen_test_main() {
    run_package_test("tidy-codegen", 30);
}
#[test]
#[timeout(20000)]
fn routing_duplex_test_main() {
    run_package_test("routing-duplex", 30);
}
