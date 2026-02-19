//! Node.js integration tests for the full compiler pipeline.
//!
//! These tests compile PureScript modules using the test-compiler-fun project
//! (with real Prelude, Effect, etc.) and run the output with Node.js to verify
//! correctness of the generated JavaScript.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Get the project root directory (where Cargo.toml lives).
fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Get the test-compiler-fun project directory.
fn test_project_dir() -> PathBuf {
    project_root().join("..").join("test-compiler-fun")
}

/// Mutex to serialize integration tests that share the filesystem.
use std::sync::Mutex;
static TEST_MUTEX: Mutex<()> = Mutex::new(());

/// Write a Main.purs to the test project, compile all modules, and return
/// the output directory path. Panics on compilation failure.
fn compile_with_main(main_source: &str) -> PathBuf {
    let test_dir = test_project_dir();
    let main_path = test_dir.join("src").join("Main.purs");
    let output_dir = project_root().join("output");

    // Write the Main.purs source
    std::fs::write(&main_path, main_source).expect("Failed to write Main.purs");

    // Clean output
    let _ = std::fs::remove_dir_all(&output_dir);

    // Compile using cargo run
    let status = Command::new("cargo")
        .args([
            "run",
            "--",
            "compile",
            "../test-compiler-fun/src/**/*.purs",
            "../test-compiler-fun/.spago/*/src/**/*.purs",
        ])
        .current_dir(&project_root())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .status()
        .expect("Failed to run cargo");

    assert!(status.success(), "Compilation failed");
    output_dir
}

/// Run a Node.js expression that imports and executes Main, returning stdout.
fn run_main(output_dir: &Path) -> String {
    let main_js = output_dir.join("Main").join("index.js");
    assert!(
        main_js.exists(),
        "Main/index.js not found at {}",
        main_js.display()
    );

    let script = format!(
        "import('{}').then(m => {{ if (typeof m.main === 'function') m.main(); }})",
        main_js.display()
    );

    let output = Command::new("node")
        .args(["--input-type=module", "-e", &script])
        .output()
        .expect("Failed to run node");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    if !output.status.success() {
        panic!(
            "Node.js execution failed:\n--- stdout ---\n{}\n--- stderr ---\n{}",
            stdout, stderr
        );
    }

    stdout
}

/// Compile and run a Main.purs, returning stdout.
fn compile_and_run(main_source: &str) -> String {
    let output_dir = compile_with_main(main_source);
    run_main(&output_dir)
}

// ===== Integration tests =====

#[test]
fn node_simple_map_show_log() {
    let _lock = TEST_MUTEX.lock().unwrap();
    let output = compile_and_run(
        r#"module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main =
  [ 1, 2, 3 ] <#> (\x -> x + 1)
    # show >>> log
"#,
    );
    assert_eq!(output.trim(), "[2,3,4]");
}

#[test]
fn node_do_notation_bind_pure() {
    let _lock = TEST_MUTEX.lock().unwrap();
    let output = compile_and_run(
        r#"module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  twoThreeFour <- pure $ [ 1, 2, 3 ] <#> (\x -> x + 1)
  log $ show twoThreeFour
  log $ "HI!"
  pure unit
"#,
    );
    assert_eq!(output.trim(), "[2,3,4]\nHI!");
}
