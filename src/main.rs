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
                for err in &module.type_errors {
                    error_messages.push(format!("{}: {err}", module.module_name));
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
