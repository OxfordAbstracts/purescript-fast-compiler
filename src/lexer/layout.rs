use crate::ast::span::Span;
use crate::lexer::SpannedToken;
use crate::lexer::token::Token;
use crate::lexer::logos_lexer::{RawToken};

/// Layout delimiter types
#[derive(Debug, Clone, Copy, PartialEq)]
enum LayoutDelim {
    LytWhere,
    LytLet,
    LytDo,
    LytOf,
    LytAdo,
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
        Token::Do | Token::QualifiedDo(_) => LayoutDelim::LytDo,
        Token::Of => LayoutDelim::LytOf,
        Token::Ado | Token::QualifiedAdo(_) => LayoutDelim::LytAdo,
        _ => unreachable!("not a layout keyword"),
    }
}

/// Preprocess raw tokens: convert to Token, skip newlines/comments,
/// and combine `UpperIdent "." Do/Ado` into `QualifiedDo`/`QualifiedAdo`.
fn preprocess_tokens(raw_tokens: Vec<(RawToken, Span)>) -> Vec<(Token, Span)> {
    // Phase 1: convert raw tokens, skip newlines and comments
    let mut tokens: Vec<(Token, Span)> = Vec::new();
    for (raw_token, span) in raw_tokens {
        if matches!(raw_token, RawToken::Newline) {
            continue;
        }
        let Some(token) = raw_token.to_token() else {
            continue;
        };
        if matches!(
            token,
            Token::LineComment(_) | Token::BlockComment(_) | Token::DocComment(_)
        ) {
            continue;
        }
        tokens.push((token, span));
    }

    // Phase 2: combine UpperIdent "." Do/Ado into QualifiedDo/QualifiedAdo
    let mut result = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        if i + 2 < tokens.len() {
            if let Token::UpperIdent(module) = &tokens[i].0 {
                if matches!(tokens[i + 1].0, Token::Dot) {
                    let module = *module;
                    if matches!(tokens[i + 2].0, Token::Do) {
                        let span = Span::new(tokens[i].1.start, tokens[i + 2].1.end);
                        result.push((Token::QualifiedDo(module), span));
                        i += 3;
                        continue;
                    }
                    if matches!(tokens[i + 2].0, Token::Ado) {
                        let span = Span::new(tokens[i].1.start, tokens[i + 2].1.end);
                        result.push((Token::QualifiedAdo(module), span));
                        i += 3;
                        continue;
                    }
                }
            }
        }
        result.push(tokens[i].clone());
        i += 1;
    }

    result
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
pub fn process_layout(raw_tokens: Vec<(RawToken, Span)>, source: &str) -> Vec<SpannedToken> {
    let tokens = preprocess_tokens(raw_tokens);
    let mut result = Vec::new();
    let mut stack: Vec<StackEntry> = vec![];
    let mut pending_layout: Option<LayoutDelim> = None;
    let mut last_was_else = false;
    let mut last_was_comma = false;
    let mut last_was_operator = false;
    // Track accessor dots (record field access like `obj.where`) vs qualifier dots (`Module.do`).
    // Accessor dot = dot preceded by non-UpperIdent; qualifier dot = dot preceded by UpperIdent.
    // Only accessor dots should suppress keyword/layout handling.
    let mut last_was_accessor_dot = false;
    let mut prev_was_upper = false;
    // Track if-then-else nesting with stack depths for precise block closing.
    // When `if` is seen, record the current stack depth.
    // When `then` is seen, transfer the depth from if_depths to then_depths.
    // When `else` is seen, pop from then_depths and close layout blocks back to that depth.
    let mut if_depths: Vec<usize> = vec![];
    let mut then_depths: Vec<usize> = vec![];
    // Track `case ... of` nesting so commas between scrutinees (case a, b of ...)
    // don't incorrectly close layout blocks.
    let mut case_depth: usize = 0;

    for (token, span) in tokens {
        let col = column_of(source, span.start);
        let dummy_span = Span::new(span.start, span.start);

        let mut just_opened = false;

        // Step 1: Handle pending layout start
        // Always emit virtual { — PureScript does not use explicit brace syntax
        // for layout blocks. A real { after a layout keyword is a record literal/pattern.
        // Cancel pending layout if the next token is : or :: or = — these indicate
        // the layout keyword is being used as a record label (e.g., { let: 1 } or { do :: Int }).
        if let Some(layout_delim) = pending_layout.take() {
            if matches!(token, Token::Colon | Token::DoubleColon | Token::Equals) {
                // Not a layout block — keyword is a record label
            } else {
                // Check if the new block's first token is at or before the enclosing
                // layout block's column. If so, the block is empty (offside rule).
                // E.g. `instance Eq Foo where\neq _ _` — `eq` at col 1 ≤ module's col 1.
                let enclosing_col = stack.iter().rev().find_map(|e| match e {
                    StackEntry::Layout(_, c) => Some(*c),
                    _ => None,
                });
                if let Some(enc_col) = enclosing_col {
                    if col <= enc_col {
                        // Empty block: emit {} immediately, don't push onto stack
                        result.push((Token::LBrace, dummy_span));
                        result.push((Token::RBrace, dummy_span));
                        // Don't set just_opened — the token still needs column-based processing
                    } else {
                        result.push((Token::LBrace, dummy_span));
                        stack.push(StackEntry::Layout(layout_delim, col));
                        just_opened = true;
                    }
                } else {
                    result.push((Token::LBrace, dummy_span));
                    stack.push(StackEntry::Layout(layout_delim, col));
                    just_opened = true;
                }
            }
        }

        // Step 1b: Handle comma — close do/let/ado layout blocks when inside an explicit
        // delimiter (record, array, parens). Commas are field/element separators in explicit
        // structures, so any implicit do/let/ado blocks must end. We don't close LytOf or
        // LytWhere because commas are valid syntax within case-of binders (multi-value case)
        // and within where clauses (fundeps, etc.). After this pre-step, Step 4's column-based
        // logic handles closing LytOf/LytWhere when the comma is on a new outdented line.
        // Skip when inside a `case ... of` expression (case_depth > 0) — commas there
        // separate scrutinees, not record fields.
        if matches!(token, Token::Comma) && case_depth == 0 {
            let has_explicit = stack.iter().any(|e| matches!(e, StackEntry::Explicit));
            if has_explicit {
                while let Some(StackEntry::Layout(delim, _)) = stack.last() {
                    match delim {
                        LayoutDelim::LytDo | LayoutDelim::LytLet | LayoutDelim::LytAdo => {
                            result.push((Token::RBrace, dummy_span));
                            stack.pop();
                        }
                        _ => break,
                    }
                }
            }
        }

        // Step 2: Handle 'in' keyword — closes let and ado layout blocks
        // Skip if after accessor dot (e.g., `letIn.in.value` — record field access, not layout keyword)
        if matches!(token, Token::In) && !last_was_accessor_dot {
            while let Some(entry) = stack.last() {
                match entry {
                    StackEntry::Layout(LayoutDelim::LytLet, _) => {
                        result.push((Token::RBrace, dummy_span));
                        stack.pop();
                        // After closing LytLet, also close LytAdo if `in` is at/before its ref column.
                        // This handles `ado ... let ... in ...` where `in` ends both the let and the ado.
                        // But NOT `ado ... x <- let y = 1 in y + 2 ...` where `in` is indented (expression-level let).
                        if let Some(StackEntry::Layout(LayoutDelim::LytAdo, ado_ref)) = stack.last() {
                            if col <= *ado_ref {
                                result.push((Token::RBrace, dummy_span));
                                stack.pop();
                            }
                        }
                        break;
                    }
                    StackEntry::Layout(LayoutDelim::LytAdo, _) => {
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
        // Step 2b: Handle 'else' keyword — closes layout blocks back to where `if` was seen.
        // Uses depth tracking: only close blocks that were opened between `then` and `else`.
        else if matches!(token, Token::Else) && !last_was_accessor_dot && !then_depths.is_empty() {
            let target_depth = then_depths.last().copied().unwrap_or(0);
            while stack.len() > target_depth {
                match stack.last() {
                    Some(StackEntry::Layout(_, _)) => {
                        result.push((Token::RBrace, dummy_span));
                        stack.pop();
                    }
                    _ => break,
                }
            }
        }
        // Step 2c: Handle 'where' keyword — closes layout blocks based on column.
        // Follows the reference PureScript layout algorithm:
        // - 'where' always closes do blocks
        // - For let: close if col < ref_col (strict, since where inside let bindings is common)
        // - For where/of/ado: close if col <= ref_col (offside end rule)
        // - Skip if inside Explicit block (where is a record field label).
        else if matches!(token, Token::Where) && !last_was_accessor_dot && !matches!(stack.last(), Some(StackEntry::Explicit)) {
            while let Some(entry) = stack.last() {
                match entry {
                    StackEntry::Layout(delim, ref_col) => {
                        let ref_col = *ref_col;
                        let delim = *delim;
                        match delim {
                            LayoutDelim::LytDo => {
                                // where always closes do blocks
                                result.push((Token::RBrace, dummy_span));
                                stack.pop();
                            }
                            LayoutDelim::LytLet => {
                                if col < ref_col {
                                    // where is outdented past the let — close it
                                    result.push((Token::RBrace, dummy_span));
                                    stack.pop();
                                } else {
                                    // where belongs to a binding inside the let — stop
                                    break;
                                }
                            }
                            _ => {
                                // For LytWhere, LytOf, LytAdo: offside end rule
                                // Close if where is at or before the reference column
                                if col <= ref_col {
                                    result.push((Token::RBrace, dummy_span));
                                    stack.pop();
                                } else {
                                    // where is indented inside this block — stop
                                    break;
                                }
                            }
                        }
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
                    Some(StackEntry::Layout(delim, ref_col)) => {
                        let ref_col = *ref_col;
                        let delim = *delim;
                        if col == ref_col {
                            // Suppress semicolons in specific contexts:
                            // - `then` when there's a pending `if` (if-then-else continuation)
                            // - `else` when there's a pending `then` (if-then-else continuation)
                            // - any token after else (for "else instance" chains)
                            // - operators at reference column are continuation lines
                            // - -> in case-of blocks (arrow on next line after binder)
                            // - | in case-of blocks (guards at same column as binder)
                            let suppress = (matches!(token, Token::Else) && !then_depths.is_empty())
                                || (matches!(token, Token::Then) && !if_depths.is_empty())
                                || last_was_else
                                || last_was_comma
                                || (last_was_operator && !matches!(delim, LayoutDelim::LytWhere | LayoutDelim::LytLet))
                                || matches!(token, Token::Operator(_) | Token::QualifiedOperator(_, _) | Token::Backtick)
                                || (matches!(token, Token::Arrow) && matches!(delim, LayoutDelim::LytOf))
                                || (matches!(token, Token::Pipe) && matches!(delim, LayoutDelim::LytOf));
                            if !suppress {
                                result.push((Token::Semicolon, dummy_span));
                            }
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
        // Don't treat `where` as a layout keyword inside explicit blocks (record field label)
        // Other layout keywords (do, let, of, ado) still work inside parens/brackets
        let inside_explicit = matches!(stack.last(), Some(StackEntry::Explicit));
        let suppress_layout = (inside_explicit && matches!(token, Token::Where)) || last_was_accessor_dot;
        let delim = if is_layout_kw && !suppress_layout {
            let d = layout_delim_for(&token);
            Some(d)
        } else {
            None
        };

        // Track case-of nesting: `case` increments, `of` decrements.
        // This prevents commas between case scrutinees from closing layout blocks.
        if matches!(token, Token::Case) {
            case_depth += 1;
        } else if matches!(token, Token::Of) && case_depth > 0 {
            case_depth -= 1;
        }

        // Track if-then-else nesting with stack depths
        if matches!(token, Token::If) {
            if_depths.push(stack.len());
        } else if matches!(token, Token::Then) && !if_depths.is_empty() {
            let depth = if_depths.pop().unwrap();
            then_depths.push(depth);
        } else if matches!(token, Token::Else) && !then_depths.is_empty() {
            then_depths.pop();
        }

        // Track else for "else instance" chain support
        last_was_else = matches!(token, Token::Else);
        // Track comma for multi-line continuation (e.g., case binder lists)
        last_was_comma = matches!(token, Token::Comma);
        // Track operators for continuation: token after an operator is part of same expression
        last_was_operator = matches!(token, Token::Operator(_) | Token::QualifiedOperator(_, _) | Token::Backtick);
        // Track accessor dots: `.` preceded by non-UpperIdent is record field access
        if matches!(token, Token::Dot) {
            last_was_accessor_dot = !prev_was_upper;
        } else {
            last_was_accessor_dot = false;
        }
        prev_was_upper = matches!(token, Token::UpperIdent(_));

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

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_layout() {
        let raw_tokens = vec![];
        let result = process_layout(raw_tokens, "");
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
