pub mod token;
pub mod logos_lexer;
pub mod layout;

pub use token::{Token, Ident};
pub use logos_lexer::{lex as lex_raw, SpannedToken};
pub use layout::process_layout;

use crate::ast::span::Spanned;

/// Main lexer entry point: lex and process layout
pub fn lex(source: &str) -> Result<Vec<Spanned<Token>>, String> {
    // Step 1: Raw lexing with Logos
    let raw_tokens = lex_raw(source)?;

    // Step 2: Layout processing
    let tokens = process_layout(raw_tokens)?;

    // Step 3: Convert to spanned tokens
    Ok(tokens
        .into_iter()
        .map(|(tok, span)| Spanned::new(tok, span))
        .collect())
}
