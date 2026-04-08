use std::path::PathBuf;
use std::process::Command;

use clap::{Parser, Subcommand};
use purescript_fast_compiler::build;

/// PureScript Fast Compiler
#[derive(Parser)]
#[command(name = "pfc", version, about)]
struct Cli {
    /// Enable verbose debug logging
    #[arg(short, long, global = true)]
    verbose: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Compile PureScript source files matching the given glob patterns
    Compile {
        /// Glob patterns for PureScript source files (e.g. "src/**/*.purs")
        #[arg(required = true)]
        globs: Vec<String>,

        /// Output directory for generated JavaScript (default: "output")
        #[arg(short, long, default_value = "output")]
        output: String,
    },
    /// Compile and run tests
    Test {
        /// Glob patterns for PureScript source files (e.g. "src/**/*.purs")
        #[arg(required = true)]
        globs: Vec<String>,

        /// Output directory for generated JavaScript (default: "output")
        #[arg(short, long, default_value = "output")]
        output: String,

        /// Test module containing the main entry point (default: "Test.Main")
        #[arg(short, long, default_value = "Test.Main")]
        test_module: String,
    },
    /// Start the PureScript language server (LSP over stdio)
    Lsp {
        /// Shell command that outputs source file paths (one per line)
        #[arg(long)]
        sources_cmd: Option<String>,

        /// Directory for disk cache (enables fast warm startup)
        #[arg(long)]
        cache_dir: Option<PathBuf>,

        /// Output directory for generated JavaScript (enables codegen on save)
        #[arg(long)]
        output_dir: Option<PathBuf>,

        /// External command for document formatting (receives filepath as argument)
        #[arg(long)]
        formatter: Option<String>,
    },
}

/// Run compilation and report errors. Returns true on success.
fn run_compile(globs: &[String], output: &str) -> bool {
    log::debug!("Starting compile with globs: {:?}", globs);

    let output_path = PathBuf::from(output);
    let cache_dir = output_path.join(".pfc-cache");

    let cache_load_start = std::time::Instant::now();
    let mut cache = build::cache::ModuleCache::load_from_disk(&cache_dir)
        .unwrap_or_default();
    log::debug!("Cache load: {:.2?}", cache_load_start.elapsed());

    let glob_refs: Vec<&str> = globs.iter().map(|s| s.as_str()).collect();
    let result = build::build_cached(&glob_refs, Some(output_path.clone()), &mut cache);

    let cache_save_start = std::time::Instant::now();
    if let Err(e) = cache.save_to_disk(&cache_dir) {
        log::debug!("Failed to save build cache: {e}");
    }
    log::debug!("Cache save: {:.2?}", cache_save_start.elapsed());

    let mut error_messages: Vec<String> = Vec::new();

    for err in &result.build_errors {
        error_messages.push(format!("{err}"));
    }

    for module in &result.modules {
        if module.type_errors.is_empty() {
            continue;
        }
        let source = std::fs::read_to_string(&module.path).unwrap_or_default();
        for err in &module.type_errors {
            let span = err.span();
            let location = match span.to_pos(&source) {
                Some((start, end)) => format!(
                    "{}:{}:{} - {}:{}",
                    module.path.display(),
                    start.line, start.column,
                    end.line, end.column
                ),
                None => format!("{}", module.path.display()),
            };
            error_messages.push(format!("{location}:\n\n  {}", err.format_pretty()));
        }
    }

    if !error_messages.is_empty() {
        let error_count = error_messages.len();
        eprintln!(
            "\nCompilation failed with {error_count} error{}:\n",
            if error_count == 1 { "" } else { "s" }
        );
        for msg in &error_messages {
            eprintln!("  {msg}");
        }
        false
    } else {
        println!(
            "\nCompiled {} module{} successfully.",
            result.modules.len(),
            if result.modules.len() == 1 { "" } else { "s" }
        );
        true
    }
}

fn main() {
    let cli = Cli::parse();

    env_logger::Builder::new()
        .filter_level(if cli.verbose {
            log::LevelFilter::Debug
        } else {
            log::LevelFilter::Warn
        })
        .format_timestamp(None)
        .format_target(false)
        .init();

    match cli.command {
        Commands::Lsp { sources_cmd, cache_dir, output_dir, formatter } => {
            // Default to the same cache dir as CLI compile (output/.pfc-cache)
            let cache_dir = cache_dir.or_else(|| {
                let default = PathBuf::from("output/.pfc-cache");
                if default.exists() { Some(default) } else { None }
            });
            purescript_fast_compiler::lsp::run_server(sources_cmd, cache_dir, output_dir, formatter);
        }
        Commands::Compile { globs, output } => {
            if !run_compile(&globs, &output) {
                std::process::exit(1);
            }
        }
        Commands::Test { globs, output, test_module } => {
            if !run_compile(&globs, &output) {
                std::process::exit(1);
            }

            let entry_path = format!("./{}/{}/index.js", output, test_module);
            let script = format!(
                "import {{ main }} from '{}'; main();",
                entry_path
            );

            let status = Command::new("node")
                .arg("--input-type=module")
                .arg("-e")
                .arg(&script)
                .status();

            match status {
                Ok(s) => std::process::exit(s.code().unwrap_or(1)),
                Err(e) => {
                    eprintln!("Failed to run node: {e}");
                    std::process::exit(1);
                }
            }
        }
    }
}
