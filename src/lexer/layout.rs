use crate::ast::span::Span;
use crate::lexer::SpannedToken;
use crate::lexer::token::Token;
use crate::lexer::logos_lexer::RawToken;

/// Layout delimiter types
#[derive(Debug, Clone, Copy, PartialEq)]
enum LayoutDelim {
    LytWhere,
    LytLet,
    LytDo,
    LytOf,
}

/// Stack entry: either an implicit layout block or an explicit delimiter
#[derive(Debug, Clone, Copy, PartialEq)]
enum StackEntry {
    Layout(LayoutDelim, usize), // (kind, reference_column)
    Explicit,                   // For ( [ {
}

/// Compute 0-indexed column of a byte offset in the source
fn column_of(source: &str, offset: usize) -> usize {
    let before = &source[..offset];
    match before.rfind('\n') {
        Some(newline_pos) => offset - newline_pos - 1,
        None => offset,
    }
}

/// Map layout keywords to their layout delimiter type
fn layout_delim_for(token: &Token) -> LayoutDelim {
    match token {
        Token::Where => LayoutDelim::LytWhere,
        Token::Let => LayoutDelim::LytLet,
        Token::Do => LayoutDelim::LytDo,
        Token::Of => LayoutDelim::LytOf,
        Token::Ado => LayoutDelim::LytDo,
        _ => unreachable!("not a layout keyword"),
    }
}

/// Process layout: convert indentation-sensitive syntax to explicit { } and ; tokens.
///
/// Algorithm:
/// - After a layout keyword (where/let/do/of/ado), the next token establishes
///   the reference column for that block and a virtual { is emitted.
/// - Subsequent tokens at the same column get ; before them.
/// - Tokens at a lesser column close the block with virtual }.
/// - Tokens at a greater column are continuations (no action).
/// - 'in' keyword explicitly closes 'let' layout blocks.
/// - Closing delimiters ) ] } close all implicit layout blocks until matching opener.
pub fn process_layout(raw_tokens: Vec<(RawToken, Span)>, source: &str) -> Result<Vec<SpannedToken>, String> {
    let mut result = Vec::new();
    let mut stack: Vec<StackEntry> = vec![];
    let mut pending_layout: Option<LayoutDelim> = None;

    for (raw_token, span) in raw_tokens {
        // Skip newlines — handled implicitly via column tracking
        if matches!(raw_token, RawToken::Newline) {
            continue;
        }

        let Some(token) = raw_token.to_token() else {
            continue;
        };

        // Skip comments — the grammar doesn't handle them
        if matches!(
            token,
            Token::LineComment(_) | Token::BlockComment(_) | Token::DocComment(_)
        ) {
            continue;
        }

        let col = column_of(source, span.start);
        let dummy_span = Span::new(span.start, span.start);

        let mut just_opened = false;

        // Step 1: Handle pending layout start
        if let Some(layout_delim) = pending_layout.take() {
            if matches!(token, Token::LBrace | Token::LParen | Token::LBracket) {
                // Explicit delimiter cancels pending layout — don't emit virtual {
            } else {
                result.push((Token::LBrace, dummy_span));
                stack.push(StackEntry::Layout(layout_delim, col));
                just_opened = true;
            }
        }

        // Step 2: Handle 'in' keyword — closes let layout blocks
        if matches!(token, Token::In) {
            while let Some(entry) = stack.last() {
                match entry {
                    StackEntry::Layout(LayoutDelim::LytLet, _) => {
                        result.push((Token::RBrace, dummy_span));
                        stack.pop();
                        break;
                    }
                    StackEntry::Layout(_, _) => {
                        result.push((Token::RBrace, dummy_span));
                        stack.pop();
                    }
                    StackEntry::Explicit => break,
                }
            }
        }
        // Step 3: Handle closing delimiters — close layout blocks until matching explicit
        else if matches!(token, Token::RParen | Token::RBracket | Token::RBrace) {
            while let Some(entry) = stack.last() {
                match entry {
                    StackEntry::Explicit => {
                        stack.pop();
                        break;
                    }
                    StackEntry::Layout(_, _) => {
                        result.push((Token::RBrace, dummy_span));
                        stack.pop();
                    }
                }
            }
        }
        // Step 4: Column-based layout checks (skip if just opened a new block)
        else if !just_opened {
            loop {
                match stack.last() {
                    None => break,
                    Some(StackEntry::Explicit) => break,
                    Some(StackEntry::Layout(_, ref_col)) => {
                        let ref_col = *ref_col;
                        if col == ref_col {
                            result.push((Token::Semicolon, dummy_span));
                            break;
                        } else if col < ref_col {
                            result.push((Token::RBrace, dummy_span));
                            stack.pop();
                            // Continue loop — may need to close more blocks or emit ;
                        } else {
                            break; // col > ref_col: continuation line
                        }
                    }
                }
            }
        }

        // Pre-compute before moving token
        let is_layout_kw = token.is_layout_keyword();
        let is_open_delim = matches!(token, Token::LParen | Token::LBracket | Token::LBrace);
        let delim = if is_layout_kw {
            Some(layout_delim_for(&token))
        } else {
            None
        };

        // Step 5: Push token to result
        result.push((token, span));

        // Step 6: Track opening delimiters
        if is_open_delim {
            stack.push(StackEntry::Explicit);
        }

        // Step 7: Set pending layout for layout keywords
        if let Some(d) = delim {
            pending_layout = Some(d);
        }
    }

    // EOF: handle pending layout (e.g., "module Test where" with no decls)
    if let Some(layout_delim) = pending_layout.take() {
        let eof_span = Span::new(0, 0);
        result.push((Token::LBrace, eof_span));
        stack.push(StackEntry::Layout(layout_delim, 0));
    }

    // Close all remaining layout blocks
    let eof_span = Span::new(0, 0);
    while let Some(entry) = stack.pop() {
        if matches!(entry, StackEntry::Layout(_, _)) {
            result.push((Token::RBrace, eof_span));
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_layout() {
        let raw_tokens = vec![];
        let result = process_layout(raw_tokens, "").unwrap();
        assert_eq!(result.len(), 0);
    }

    #[test]
    fn test_column_of_first_line() {
        assert_eq!(column_of("hello", 0), 0);
        assert_eq!(column_of("hello", 3), 3);
    }

    #[test]
    fn test_column_of_second_line() {
        assert_eq!(column_of("hi\nworld", 3), 0);
        assert_eq!(column_of("hi\n  world", 5), 2);
    }
}
