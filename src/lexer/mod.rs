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
    let tokens = process_layout(raw_tokens, source)?;

    // Step 3: Convert to spanned tokens
    Ok(tokens
        .into_iter()
        .map(|(tok, span)| Spanned::new(tok, span))
        .collect())
}

/// Print tokens as source text (for debugging)
pub fn print(tokens: Vec<Token>) -> String {
    // tokens.iter().map(|spanned| spanned.node.print()).collect::<Vec<_>>().join(" ")
    let mut result = String::new();

    let mut indentation = 0;

    for token in tokens {
        let token_str = token.print();
        result.push_str(&token_str);
        match token {
            Token::LayoutStart => { 
                indentation += 1;
                result.push('\n');
                result.push_str(&"  ".repeat(indentation));
            }
            Token::LayoutEnd => { 
                indentation -= 1;
                result.push('\n');
                result.push_str(&"  ".repeat(indentation));
            }
            Token::LayoutSep => {
                result.push('\n');
                result.push_str(&"  ".repeat(indentation));
            }
            _ => {
                result.push(' ');
            }
        }
    }
    result
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     // write a property-based test to check that lexing and printing are inverses, ignoring spans
//     use proptest::prelude::*;
//     use string_interner::symbol::SymbolU32;
//             // Generator for tokens
//         fn arb_token() -> impl Strategy<Value = Token> {
//             prop_oneof![
//                 Just(Token::Where),
//                 Just(Token::Let),
//                 Just(Token::Do),
//                 Just(Token::Of),
//                 Just(Token::Ado),
//                 Just(Token::Data),
//                 Just(Token::Type),
//                 Just(Token::Newtype),
//                 Just(Token::Class),
//                 Just(Token::Instance),
//                 Just(Token::LowerIdent(SymbolU32::from("foo"))),
//                 Just(Token::Operator(SymbolU32::from("+"))),
                
//             ]
//         }


// }