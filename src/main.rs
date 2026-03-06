use std::path::PathBuf;

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
    /// Start the PureScript language server (LSP over stdio)
    Lsp {
        /// Shell command that outputs source file paths (one per line)
        #[arg(long)]
        sources_cmd: Option<String>,
    },
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
        Commands::Lsp { sources_cmd } => {
            purescript_fast_compiler::lsp::run_server(sources_cmd);
        }
        Commands::Compile { globs, output } => {
            log::debug!("Starting compile with globs: {:?}", globs);

            let output_path = PathBuf::from(&output);
            let cache_path = output_path.join(".pfc-cache").join("cache.bin");

            let mut cache = cache_path
                .parent()
                .and_then(|_| build::cache::ModuleCache::load_from_disk(&cache_path).ok())
                .unwrap_or_default();

            let glob_refs: Vec<&str> = globs.iter().map(|s| s.as_str()).collect();
            let result = build::build_cached(&glob_refs, Some(output_path.clone()), &mut cache);

            // Save cache for next build
            if let Some(parent) = cache_path.parent() {
                std::fs::create_dir_all(parent).ok();
            }
            if let Err(e) = cache.save_to_disk(&cache_path) {
                log::debug!("Failed to save build cache: {e}");
            }

            let mut error_messages: Vec<String> = Vec::new();

            for err in &result.build_errors {
                error_messages.push(format!("{err}"));
            }

            let total = result.modules.len();
            for (i, module) in result.modules.iter().enumerate() {
                if module.type_errors.is_empty() {
                    println!("[{}/{}] {}", i + 1, total, module.module_name);
                } else {
                    for err in &module.type_errors {
                        error_messages.push(format!("{}: {err}", module.module_name));
                    }
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
                std::process::exit(1);
            } else {
                println!(
                    "\nCompiled {} module{} successfully.",
                    result.modules.len(),
                    if result.modules.len() == 1 { "" } else { "s" }
                );
            }
        }
    }
}
