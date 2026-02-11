//! Fixture-based integration tests.
//!
//! Parses all PureScript files from tests/fixtures/packages/ to verify
//! the parser handles real-world code without panicking or erroring.

use std::path::Path;

use purescript_fast_compiler::parse;

fn collect_purs_files(dir: &Path, files: &mut Vec<std::path::PathBuf>) {
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

#[test]
fn parse_fixture_package_prelude() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages/prelude");
    if !fixtures_dir.exists() {
        eprintln!("Skipping: prelude fixtures not found");
        return;
    }

    let mut files = Vec::new();
    collect_purs_files(&fixtures_dir, &mut files);

    assert!(!files.is_empty(), "Expected prelude fixture files");

    for path in &files {
        let source = std::fs::read_to_string(path).unwrap();
        parse(&source).unwrap_or_else(|e| {
            panic!("Failed to parse {}: {}", path.display(), e);
        });
    }
}

#[test]
fn parse_fixture_orignal_compiler_passing() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/original-compiler/passing");
    if !fixtures_dir.exists() {
        eprintln!("Skipping: original-compiler/passing fixtures not found");
        return;
    }

    let mut files = Vec::new();
    collect_purs_files(&fixtures_dir, &mut files);
    files.sort();

    let mut total = 0;
    let mut failed = Vec::new();
    let mut total_bytes = 0u64;

    let start = std::time::Instant::now();

    for path in &files {
        let source = std::fs::read_to_string(path).unwrap();
        total_bytes += source.len() as u64;
        total += 1;
        if let Err(e) = parse(&source) {
            let span = e.get_span();
            let pos = match span.and_then(|s| s.to_pos(&source)) {
                Some((start, end)) => format!("{}:{}..{}:{}", start.line, start.column, end.line, end.column),
                None => "unknown position".to_string(),
            };
            
            failed.push((path.clone(), pos, e.to_string()));
        }
    }

    if !failed.is_empty() {
        let rel = |p: &Path| {
            p.strip_prefix(&fixtures_dir)
                .unwrap_or(p)
                .display()
                .to_string()
        };
        let summary: Vec<String> = failed
            .iter()
            .map(|(p, pos, e)| format!("  {}:{}: {}", rel(p), pos, e))
            .collect();
        panic!(
            "{}/{} files failed to parse:\n{}",
            failed.len(),
            total,
            summary.join("\n")
        );
    }
}


#[test]
fn parse_all_package_files() {
    let fixtures_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    if !fixtures_dir.exists() {
        eprintln!(
            "Skipping fixture test: {} not found",
            fixtures_dir.display()
        );
        return;
    }

    let mut files = Vec::new();
    collect_purs_files(&fixtures_dir, &mut files);
    files.sort();

    let mut total = 0;
    let mut failed = Vec::new();
    let mut total_bytes = 0u64;

    let start = std::time::Instant::now();

    for path in &files {
        let source = std::fs::read_to_string(path).unwrap();
        total_bytes += source.len() as u64;
        total += 1;
        if let Err(e) = parse(&source) {
            let span = e.get_span();
            let pos = match span.and_then(|s| s.to_pos(&source)) {
                Some((start, end)) => format!("{}:{}..{}:{}", start.line, start.column, end.line, end.column),
                None => "unknown position".to_string(),
            };
            
            failed.push((path.clone(), pos, e.to_string()));
        }
    }

    let elapsed = start.elapsed();

    println!("\n=== Fixture Parse Results ===");
    println!("Files:      {total}");
    println!(
        "Bytes:      {total_bytes} ({:.1} MB)",
        total_bytes as f64 / 1_048_576.0
    );
    println!("Time:       {:.3}s", elapsed.as_secs_f64());
    println!("Files/sec:  {:.0}", total as f64 / elapsed.as_secs_f64());
    println!(
        "MB/sec:     {:.1}",
        (total_bytes as f64 / 1_048_576.0) / elapsed.as_secs_f64()
    );
    println!("Succeeded:  {}", total - failed.len());
    println!("Failed:     {}", failed.len());

    if !failed.is_empty() {
        let rel = |p: &Path| {
            p.strip_prefix(&fixtures_dir)
                .unwrap_or(p)
                .display()
                .to_string()
        };
        let summary: Vec<String> = failed
            .iter()
            .map(|(p, pos, e)| format!("  {}:{}: {}", rel(p), pos, e))
            .collect();
        panic!(
            "{}/{} files failed to parse:\n{}",
            failed.len(),
            total,
            summary.join("\n")
        );
    }
}
