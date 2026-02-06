use purescript_fast_compiler::lexer::lex;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <purescript-file>", args[0]);
        eprintln!("\nOr pipe PureScript code to stdin:");
        eprintln!("  echo 'module Main where' | {}", args[0]);
        std::process::exit(1);
    }

    // Read from file or stdin
    let source = if args[1] == "-" {
        use std::io::Read;
        let mut buffer = String::new();
        std::io::stdin()
            .read_to_string(&mut buffer)
            .expect("Failed to read from stdin");
        buffer
    } else {
        std::fs::read_to_string(&args[1])
            .unwrap_or_else(|e| {
                eprintln!("Error reading file '{}': {}", args[1], e);
                std::process::exit(1);
            })
    };

    // Lex the source
    match lex(&source) {
        Ok(tokens) => {
            println!("Lexed {} tokens:", tokens.len());
            for (i, spanned) in tokens.iter().enumerate() {
                println!(
                    "{:4}: {:?} @ {}..{}",
                    i,
                    spanned.node,
                    spanned.span.start,
                    spanned.span.end
                );
            }
        }
        Err(e) => {
            eprintln!("Lexer error: {}", e);
            std::process::exit(1);
        }
    }
}
