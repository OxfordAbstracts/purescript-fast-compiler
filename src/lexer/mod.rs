pub mod token;
pub mod logos_lexer;
pub mod layout;

pub use token::{Token, Ident};
pub use logos_lexer::{lex as lex_raw, SpannedToken};
pub use layout::process_layout;

use crate::span::{Span, Spanned};
use crate::interner;
use crate::lexer::logos_lexer::LexError;

/// Result of lexing: tokens and comments
pub struct LexResult {
    pub tokens: Vec<Spanned<Token>>,
    pub comments: Vec<Spanned<crate::cst::Comment>>,
}

/// Main lexer entry point: lex and process layout
pub fn lex(source: &str) -> Result<LexResult, LexError> {
    // Step 1: Raw lexing with Logos
    let raw_tokens = lex_raw(source)?;

    // Step 2: Layout processing (also collects comments)
    let (tokens, comments) = process_layout(raw_tokens, source);

    // Step 3: Merge adjacent Tilde + Operator tokens (e.g., ~ > → ~>)
    // Logos lexes ~ with higher priority than operators, so ~> becomes two tokens.
    let tokens = merge_tilde_operators(tokens);

    // Step 4: Resolve qualified names (merge adjacent UpperIdent.Ident sequences)
    let tokens = resolve_qualified_names(tokens);

    // Step 5: Convert to spanned tokens
    let tokens = tokens
        .into_iter()
        .map(|(tok, span)| Spanned::new(tok, span))
        .collect();

    let comments = comments
        .into_iter()
        .map(|(comment, span)| Spanned::new(comment, span))
        .collect();

    Ok(LexResult { tokens, comments })
}

/// Merge adjacent Tilde tokens with following Operator/Tilde tokens into a single Operator.
/// Logos lexes `~` with priority 2 (above operators at priority 1), so `~>` becomes
/// `Tilde` + `Operator(">")`. This step merges them back into `Operator("~>")`.
fn merge_tilde_operators(tokens: Vec<SpannedToken>) -> Vec<SpannedToken> {
    let mut result: Vec<SpannedToken> = Vec::with_capacity(tokens.len());
    let mut i = 0;

    while i < tokens.len() {
        if matches!(&tokens[i].0, Token::Tilde) {
            let start_span = tokens[i].1;
            let mut merged = String::from("~");
            let mut end_span = start_span;
            let mut j = i + 1;

            // Consume adjacent Tilde and Operator tokens
            while j < tokens.len() && end_span.end == tokens[j].1.start {
                match &tokens[j].0 {
                    Token::Tilde => {
                        merged.push('~');
                        end_span = tokens[j].1;
                        j += 1;
                    }
                    Token::Operator(op) => {
                        let op_str = interner::resolve(*op).unwrap_or_default();
                        merged.push_str(&op_str);
                        end_span = tokens[j].1;
                        j += 1;
                        break; // Operator already consumed remaining chars
                    }
                    _ => break,
                }
            }

            if j > i + 1 {
                // Merged: produce a single Operator token
                eprintln!("[TILDE_MERGE] Merged {} tokens into Operator(\"{}\")", j - i, merged);
                let sym = interner::intern(&merged);
                let span = Span::new(start_span.start, end_span.end);
                result.push((Token::Operator(sym), span));
            } else {
                // Standalone Tilde, keep as-is
                result.push(tokens[i].clone());
            }
            i = j;
        } else {
            result.push(tokens[i].clone());
            i += 1;
        }
    }

    result
}

/// Resolve qualified names by merging adjacent token sequences:
/// - UpperIdent.LowerIdent → QualifiedLower
/// - UpperIdent.UpperIdent → QualifiedUpper (chained for multi-segment)
/// - UpperIdent.Operator → QualifiedOperator
/// Tokens must be adjacent (no whitespace) to be merged.
fn resolve_qualified_names(tokens: Vec<SpannedToken>) -> Vec<SpannedToken> {
    let mut result: Vec<SpannedToken> = Vec::with_capacity(tokens.len());
    let mut i = 0;

    while i < tokens.len() {
        // Check if this is an UpperIdent that could start a qualified name
        if let Token::UpperIdent(first_ident) = &tokens[i].0 {
            // Try to build a qualified name chain: A.B.C.name
            let mut module_parts: Vec<Ident> = vec![*first_ident];
            let start_span = tokens[i].1;
            let mut j = i + 1;
            let mut resolved = false;

            // Consume as many UpperIdent.UpperIdent. chains as possible
            loop {
                if j + 1 >= tokens.len() {
                    break;
                }
                // Check for adjacent Dot
                if !matches!(&tokens[j].0, Token::Dot) {
                    break;
                }
                if tokens[j - 1].1.end != tokens[j].1.start
                    || tokens[j].1.end != tokens[j + 1].1.start
                {
                    break;
                }
                match &tokens[j + 1].0 {
                    Token::UpperIdent(next_ident) => {
                        // Could be more chaining or terminal
                        module_parts.push(*next_ident);
                        j += 2;
                        continue;
                    }
                    Token::LowerIdent(name) => {
                        // Terminal: Module.name
                        let module_str = module_parts_to_string(&module_parts);
                        let module_sym = interner::intern(&module_str);
                        let end_span = tokens[j + 1].1;
                        let span = Span::new(start_span.start, end_span.end);
                        result.push((Token::QualifiedLower(module_sym, *name), span));
                        i = j + 2;
                        resolved = true;
                        break;
                    }
                    Token::Operator(op) => {
                        // Terminal: Module.(op)
                        let module_str = module_parts_to_string(&module_parts);
                        let module_sym = interner::intern(&module_str);
                        let end_span = tokens[j + 1].1;
                        let span = Span::new(start_span.start, end_span.end);
                        result.push((Token::QualifiedOperator(module_sym, *op), span));
                        i = j + 2;
                        resolved = true;
                        break;
                    }
                    // Contextual keywords used as identifiers after module qualifier
                    Token::As | Token::Hiding | Token::Export => {
                        let kw_str = match &tokens[j + 1].0 {
                            Token::As => "as",
                            Token::Hiding => "hiding",
                            Token::Export => "export",
                            _ => unreachable!(),
                        };
                        let name = interner::intern(kw_str);
                        let module_str = module_parts_to_string(&module_parts);
                        let module_sym = interner::intern(&module_str);
                        let end_span = tokens[j + 1].1;
                        let span = Span::new(start_span.start, end_span.end);
                        result.push((Token::QualifiedLower(module_sym, name), span));
                        i = j + 2;
                        resolved = true;
                        break;
                    }
                    _ => break,
                }
            }

            // Check for adjacent Operator starting with '.' (logos merges .>>> into one token)
            if !resolved && j < tokens.len() {
                if let Token::Operator(op) = &tokens[j].0 {
                    let op_str = interner::resolve(*op).unwrap_or_default();
                    if op_str.starts_with('.')
                        && op_str.len() > 1
                        && tokens[j - 1].1.end == tokens[j].1.start
                    {
                        let real_op = interner::intern(&op_str[1..]);
                        let module_str = module_parts_to_string(&module_parts);
                        let module_sym = interner::intern(&module_str);
                        let end_span = tokens[j].1;
                        let span = Span::new(start_span.start, end_span.end);
                        result.push((Token::QualifiedOperator(module_sym, real_op), span));
                        i = j + 1;
                        resolved = true;
                    }
                }
            }

            if !resolved {
                if module_parts.len() > 1 {
                    // Multiple UpperIdents chained: A.B.C → QualifiedUpper("A.B", C)
                    let name = module_parts.pop().unwrap();
                    let module_str = module_parts_to_string(&module_parts);
                    let module_sym = interner::intern(&module_str);
                    let end_span = tokens[j - 1].1;
                    let span = Span::new(start_span.start, end_span.end);
                    result.push((Token::QualifiedUpper(module_sym, name), span));
                    i = j;
                } else {
                    // Just a plain UpperIdent, no qualification
                    result.push(tokens[i].clone());
                    i += 1;
                }
            }
        } else {
            result.push(tokens[i].clone());
            i += 1;
        }
    }

    result
}

fn module_parts_to_string(parts: &[Ident]) -> String {
    parts
        .iter()
        .map(|s| interner::resolve(*s).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
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