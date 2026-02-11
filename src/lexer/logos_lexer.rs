use std::fmt::Display;

use crate::ast::span::Span;
use crate::interner;
use crate::lexer::token::{Ident, Token};
use logos::Logos;

/// Raw tokens from Logos lexer (before layout processing)
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\r]+")] // Skip whitespace except newlines
pub enum RawToken {
    // Keywords
    #[token("module")]
    Module,
    #[token("import")]
    Import,
    #[token("export")]
    Export,
    #[token("foreign")]
    Foreign,
    #[token("data")]
    Data,
    #[token("type")]
    Type,
    #[token("newtype")]
    Newtype,
    #[token("class")]
    Class,
    #[token("instance")]
    Instance,
    #[token("derive")]
    Derive,
    #[token("where")]
    Where,
    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("do")]
    Do,
    #[token("ado")]
    Ado,
    #[token("case")]
    Case,
    #[token("of")]
    Of,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("forall")]
    #[token("∀")]
    Forall,
    #[token("infix")]
    Infix,
    #[token("infixl")]
    Infixl,
    #[token("infixr")]
    Infixr,
    #[token("as")]
    As,
    #[token("hiding")]
    Hiding,
    #[token("true")]
    True,
    #[token("false")]
    False,

    // Identifiers - lowercase starting (excluding lone underscore)
    // Includes Unicode lowercase letters (\p{Ll}) and other letters (\p{Lo})
    #[regex(r"[a-z\p{Ll}\p{Lo}][a-zA-Z0-9_'\p{L}]*", |lex| interner::intern(lex.slice()))]
    #[regex(r"_[a-zA-Z0-9_'\p{L}]+", |lex| interner::intern(lex.slice()))]
    LowerIdent(Ident),

    // Identifiers - uppercase starting (types, constructors, modules)
    #[regex(r"[A-Z\p{Lu}][a-zA-Z0-9_'\p{L}]*", |lex| interner::intern(lex.slice()))]
    UpperIdent(Ident),

    // Typed holes: ?identifier
    #[regex(r"\?[a-zA-Z][a-zA-Z0-9_']*", priority = 2, callback = |lex| interner::intern(&lex.slice()[1..]))]
    Hole(Ident),

    // Operators - sequences of operator characters (lower priority than specific tokens)
    // Includes Unicode math symbols (\p{Sm}) and other symbols (\p{So}) per PureScript spec
    #[regex(r"[!#$%&*+./<=>?@\\^|~:\p{Sm}\p{So}-]+", priority = 1, callback = |lex| interner::intern(lex.slice()))]
    Operator(Ident),

    // Integer literals (clamp to i64 bounds on overflow, support _ separators)
    // Note: negative literals are NOT handled here — `-42` lexes as Operator(-) + Integer(42).
    // The parser handles negation at expression/pattern/type level.
    #[regex(r"[0-9][0-9_]*", |lex| {
        let s: String = lex.slice().chars().filter(|&c| c != '_').collect();
        Some(s.parse::<i64>().unwrap_or(i64::MAX))
    })]
    #[regex(r"0x[0-9a-fA-F][0-9a-fA-F_]*", |lex| {
        let s: String = lex.slice().chars().filter(|&c| c != '_').collect();
        let hex = &s[2..];
        Some(i64::from_str_radix(hex, 16).unwrap_or(i64::MAX))
    })]
    #[regex(r"0o[0-7][0-7_]*", |lex| {
        let s: String = lex.slice().chars().filter(|&c| c != '_').collect();
        let oct = &s[2..];
        Some(i64::from_str_radix(oct, 8).unwrap_or(i64::MAX))
    })]
    Integer(i64),

    // Float literals (support _ separators)
    #[regex(r"[0-9][0-9_]*\.[0-9][0-9_]*([eE][+-]?[0-9][0-9_]*)?", |lex| {
        let s: String = lex.slice().chars().filter(|&c| c != '_').collect();
        s.parse::<f64>().ok()
    })]
    #[regex(r"[0-9][0-9_]*[eE][+-]?[0-9][0-9_]*", |lex| {
        let s: String = lex.slice().chars().filter(|&c| c != '_').collect();
        s.parse::<f64>().ok()
    })]
    Float(f64),

    // String literals — supports escapes and multi-line gap syntax (\ newline spaces \)
    #[regex(r#""([^"\\]|\\(.|\n[^"\\]*\\))*""#, |lex| {
        let s = lex.slice();
        // Remove quotes and handle escapes
        parse_string(&s[1..s.len()-1])
    })]
    String(String),

    // Triple-quoted raw strings: """content""" (content may contain " and "")
    #[regex(r#""""([^"]|"[^"]|""[^"])*(""|")?""""#, |lex| {
        let s = lex.slice();
        Some(s[3..s.len()-3].to_string())
    })]
    RawString(String),

    // Character literals (supports \xHH, \uHHHH, and simple escapes)
    #[regex(r"'([^'\\]|\\(x[0-9a-fA-F]+|u[0-9a-fA-F]+|.))'", |lex| {
        let s = lex.slice();
        parse_char(&s[1..s.len()-1])
    })]
    Char(char),

    // Delimiters
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,

    // Special multi-character symbols (must come before single-char operators)
    #[token("->")]
    #[token("→")]
    Arrow,
    #[token("=>")]
    #[token("⇒")]
    FatArrow,
    #[token("::")]
    #[token("∷")]
    DoubleColon,
    #[token("<-")]
    #[token("←")]
    LeftArrow,
    #[token("<=>")]
    DoubleArrow,

    // Single-character special symbols (higher priority than Operator regex)
    #[token(":", priority = 2)]
    Colon,
    #[token("|", priority = 2)]
    Pipe,
    #[token("\\", priority = 2)]
    Backslash,
    #[token(".", priority = 2)]
    Dot,
    #[token(",", priority = 2)]
    Comma,
    #[token(";", priority = 2)]
    Semicolon,
    #[token("=", priority = 2)]
    Equals,
    #[token("`", priority = 2)]
    Backtick,
    #[token("@", priority = 2)]
    At,
    #[token("_", priority = 2)]
    Underscore,
    #[token("~", priority = 2)]
    Tilde,

    // Newlines (important for layout processing)
    #[regex(r"\n")]
    Newline,

    // Line comments
    #[regex(r"--[^\n]*", |lex| Some(lex.slice()[2..].to_string()))]
    LineComment(String),

    // Documentation comments (special line comments starting with |)
    #[regex(r"-- \|[^\n]*", |lex| Some(lex.slice()[4..].to_string()))]
    DocComment(String),

    // Block comments (handled by callback for nesting)
    #[regex(r"\{-", lex_block_comment)]
    BlockComment(String),
}

/// Parse string escape sequences
fn parse_string(s: &str) -> Option<String> {
    let mut result = String::new();
    let mut i = 0;
    let bytes = s.as_bytes();

    while i < bytes.len() {
        if bytes[i] == b'\\' {
            i += 1;
            if i >= bytes.len() {
                break;
            }
            match bytes[i] {
                b'n' => {
                    result.push('\n');
                    i += 1;
                }
                b't' => {
                    result.push('\t');
                    i += 1;
                }
                b'r' => {
                    result.push('\r');
                    i += 1;
                }
                b'\\' => {
                    result.push('\\');
                    i += 1;
                }
                b'"' => {
                    result.push('"');
                    i += 1;
                }
                b'\'' => {
                    result.push('\'');
                    i += 1;
                }
                b'0' => {
                    result.push('\0');
                    i += 1;
                }
                b'x' | b'u' => {
                    let prefix = bytes[i] as char;
                    i += 1;
                    let start = i;
                    while i < bytes.len() && (bytes[i] as char).is_ascii_hexdigit() {
                        i += 1;
                    }
                    let hex = &s[start..i];
                    if hex.is_empty() {
                        result.push('\\');
                        result.push(prefix);
                    } else {
                        let code = u32::from_str_radix(hex, 16).unwrap_or(0xFFFD);
                        result.push(char::from_u32(code).unwrap_or('\u{FFFD}'));
                    }
                }
                b'\n' => {
                    // String gap: \ newline whitespace \ — skip the gap
                    i += 1;
                    while i < bytes.len() && matches!(bytes[i], b' ' | b'\t' | b'\r' | b'\n') {
                        i += 1;
                    }
                    if i < bytes.len() && bytes[i] == b'\\' {
                        i += 1; // skip the closing backslash of the gap
                    }
                }
                other => {
                    // Unknown escape, keep literal
                    result.push(other as char);
                    i += 1;
                }
            }
        } else {
            // Regular character (may be multi-byte UTF-8)
            let c = s[i..].chars().next()?;
            result.push(c);
            i += c.len_utf8();
        }
    }

    Some(result)
}

/// Parse character with escape sequences
fn parse_char(s: &str) -> Option<char> {
    // Single character (including multi-byte Unicode)
    let mut chars = s.chars();
    let first = chars.next()?;
    if first != '\\' {
        // Non-escape: should be exactly one character
        return if chars.next().is_none() {
            Some(first)
        } else {
            None
        };
    }

    // Escape sequence
    let esc = chars.as_str();
    if let Some(hex) = esc.strip_prefix('x') {
        let code = u32::from_str_radix(hex, 16).ok()?;
        return char::from_u32(code);
    }
    if let Some(hex) = esc.strip_prefix('u') {
        let code = u32::from_str_radix(hex, 16).ok()?;
        return char::from_u32(code);
    }

    match esc {
        "n" => Some('\n'),
        "t" => Some('\t'),
        "r" => Some('\r'),
        "\\" => Some('\\'),
        "'" => Some('\''),
        "\"" => Some('"'),
        "0" => Some('\0'),
        _ => esc.chars().next(),
    }
}

/// Lex nested block comments
/// PureScript allows nested block comments: {- outer {- inner -} outer -}
fn lex_block_comment(lex: &mut logos::Lexer<RawToken>) -> Option<String> {
    let remainder = lex.remainder();
    let mut depth = 1;
    let bytes = remainder.as_bytes();
    let mut pos = 0;

    while pos < bytes.len() && depth > 0 {
        if pos + 1 < bytes.len() {
            match (bytes[pos], bytes[pos + 1]) {
                (b'{', b'-') => {
                    depth += 1;
                    pos += 2;
                    continue;
                }
                (b'-', b'}') => {
                    depth -= 1;
                    pos += 2;
                    if depth == 0 {
                        let content = &remainder[..pos - 2];
                        lex.bump(pos);
                        return Some(content.to_string());
                    }
                    continue;
                }
                _ => {}
            }
        }
        pos += 1;
    }

    // Unclosed block comment
    None
}

/// Convert RawToken to Token
impl RawToken {
    pub fn to_token(&self) -> Option<Token> {
        match self {
            RawToken::Module => Some(Token::Module),
            RawToken::Import => Some(Token::Import),
            RawToken::Export => Some(Token::Export),
            RawToken::Foreign => Some(Token::Foreign),
            RawToken::Data => Some(Token::Data),
            RawToken::Type => Some(Token::Type),
            RawToken::Newtype => Some(Token::Newtype),
            RawToken::Class => Some(Token::Class),
            RawToken::Instance => Some(Token::Instance),
            RawToken::Derive => Some(Token::Derive),
            RawToken::Where => Some(Token::Where),
            RawToken::Let => Some(Token::Let),
            RawToken::In => Some(Token::In),
            RawToken::Do => Some(Token::Do),
            RawToken::Ado => Some(Token::Ado),
            RawToken::Case => Some(Token::Case),
            RawToken::Of => Some(Token::Of),
            RawToken::If => Some(Token::If),
            RawToken::Then => Some(Token::Then),
            RawToken::Else => Some(Token::Else),
            RawToken::Forall => Some(Token::Forall),
            RawToken::Infix => Some(Token::Infix),
            RawToken::Infixl => Some(Token::Infixl),
            RawToken::Infixr => Some(Token::Infixr),
            RawToken::As => Some(Token::As),
            RawToken::Hiding => Some(Token::Hiding),
            RawToken::True => Some(Token::True),
            RawToken::False => Some(Token::False),
            RawToken::LowerIdent(id) => Some(Token::LowerIdent(*id)),
            RawToken::UpperIdent(id) => Some(Token::UpperIdent(*id)),
            RawToken::Hole(id) => Some(Token::Hole(*id)),
            RawToken::Operator(op) => Some(Token::Operator(*op)),
            RawToken::Integer(n) => Some(Token::Integer(*n)),
            RawToken::Float(f) => Some(Token::Float(*f)),
            RawToken::String(s) => Some(Token::String(s.clone())),
            RawToken::RawString(s) => Some(Token::String(s.clone())),
            RawToken::Char(c) => Some(Token::Char(*c)),
            RawToken::LParen => Some(Token::LParen),
            RawToken::RParen => Some(Token::RParen),
            RawToken::LBrace => Some(Token::LBrace),
            RawToken::RBrace => Some(Token::RBrace),
            RawToken::LBracket => Some(Token::LBracket),
            RawToken::RBracket => Some(Token::RBracket),
            RawToken::Arrow => Some(Token::Arrow),
            RawToken::FatArrow => Some(Token::FatArrow),
            RawToken::DoubleColon => Some(Token::DoubleColon),
            RawToken::Colon => Some(Token::Colon),
            RawToken::LeftArrow => Some(Token::LeftArrow),
            RawToken::DoubleArrow => Some(Token::DoubleArrow),
            RawToken::Pipe => Some(Token::Pipe),
            RawToken::Backslash => Some(Token::Backslash),
            RawToken::Dot => Some(Token::Dot),
            RawToken::Comma => Some(Token::Comma),
            RawToken::Semicolon => Some(Token::Semicolon),
            RawToken::Equals => Some(Token::Equals),
            RawToken::Backtick => Some(Token::Backtick),
            RawToken::At => Some(Token::At),
            RawToken::Underscore => Some(Token::Underscore),
            RawToken::Tilde => Some(Token::Tilde),
            RawToken::LineComment(s) => Some(Token::LineComment(s.clone())),
            RawToken::DocComment(s) => Some(Token::DocComment(s.clone())),
            RawToken::BlockComment(s) => Some(Token::BlockComment(s.clone())),
            RawToken::Newline => None, // Handled by layout processor
        }
    }
}

/// Lexer output: token with span
pub type SpannedToken = (Token, Span);

#[derive(Debug, Clone)]
pub struct LexError(pub String, pub Span);

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.1, self.0)
    }
}



/// Lex source code into raw tokens with spans
pub fn lex(source: &str) -> Result<Vec<(RawToken, Span)>, LexError> {
    let mut lexer = RawToken::lexer(source);
    let mut tokens = Vec::new();

    while let Some(result) = lexer.next() {
        let span = Span::new(lexer.span().start, lexer.span().end);

        match result {
            Ok(token) => tokens.push((token, span)),
            Err(_) => {
                return Err(LexError(
                    format!("Unexpected token {}", &source[span.start..span.end]),
                    span,
                ));
            }
        }
    }

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keywords() {
        let source = "module import where let in do case of";
        let tokens = lex(source).unwrap();

        assert_eq!(tokens[0].0, RawToken::Module);
        assert_eq!(tokens[1].0, RawToken::Import);
        assert_eq!(tokens[2].0, RawToken::Where);
        assert_eq!(tokens[3].0, RawToken::Let);
        assert_eq!(tokens[4].0, RawToken::In);
        assert_eq!(tokens[5].0, RawToken::Do);
        assert_eq!(tokens[6].0, RawToken::Case);
        assert_eq!(tokens[7].0, RawToken::Of);
    }

    #[test]
    fn test_identifiers() {
        let source = "foo Bar myVar MyType _underscore var'";
        let tokens = lex(source).unwrap();

        // Check token types (not values since they're interned)
        assert!(matches!(tokens[0].0, RawToken::LowerIdent(_)));
        assert!(matches!(tokens[1].0, RawToken::UpperIdent(_)));
        assert!(matches!(tokens[2].0, RawToken::LowerIdent(_)));
        assert!(matches!(tokens[3].0, RawToken::UpperIdent(_)));
        assert!(matches!(tokens[4].0, RawToken::LowerIdent(_)));
        assert!(matches!(tokens[5].0, RawToken::LowerIdent(_)));
    }

    #[test]
    fn test_operators() {
        let source = "+ - * / == :: -> => <-";
        let tokens = lex(source).unwrap();

        assert!(matches!(tokens[0].0, RawToken::Operator(_)));
        assert!(matches!(tokens[1].0, RawToken::Operator(_)));
        assert!(matches!(tokens[2].0, RawToken::Operator(_)));
        assert!(matches!(tokens[3].0, RawToken::Operator(_)));
        assert!(matches!(tokens[4].0, RawToken::Operator(_)));
        assert_eq!(tokens[5].0, RawToken::DoubleColon);
        assert_eq!(tokens[6].0, RawToken::Arrow);
        assert_eq!(tokens[7].0, RawToken::FatArrow);
        assert_eq!(tokens[8].0, RawToken::LeftArrow);
    }

    #[test]
    fn test_literals() {
        let source = r#"42 3.14 "hello" 'c' true false"#;
        let tokens = lex(source).unwrap();

        assert_eq!(tokens[0].0, RawToken::Integer(42));
        assert_eq!(tokens[1].0, RawToken::Float(3.14));
        assert!(matches!(tokens[2].0, RawToken::String(_)));
        assert!(matches!(tokens[3].0, RawToken::Char('c')));
        assert_eq!(tokens[4].0, RawToken::True);
        assert_eq!(tokens[5].0, RawToken::False);
    }

    #[test]
    fn test_comments() {
        let source = "-- line comment\n{- block comment -} foo";
        let tokens = lex(source).unwrap();

        assert!(matches!(tokens[0].0, RawToken::LineComment(_)));
        assert_eq!(tokens[1].0, RawToken::Newline);
        assert!(matches!(tokens[2].0, RawToken::BlockComment(_)));
        assert!(matches!(tokens[3].0, RawToken::LowerIdent(_)));
    }

    #[test]
    fn test_nested_block_comments() {
        let source = "{- outer {- inner -} still outer -} foo";
        let tokens = lex(source).unwrap();

        assert!(matches!(tokens[0].0, RawToken::BlockComment(_)));
        if let RawToken::BlockComment(content) = &tokens[0].0 {
            assert!(content.contains("inner"));
        }
        assert!(matches!(tokens[1].0, RawToken::LowerIdent(_)));
    }

    /// Property test: tokens should reconstruct to original source
    /// This ensures we don't lose any characters during lexing
    #[test]
    fn test_token_roundtrip_simple() {
        let test_cases = vec![
            "module Main where",
            "factorial n = n * factorial (n - 1)",
            "let x = 42 in x + 1",
            "data Maybe a = Just a | Nothing",
            "class Show a where\n  show :: a -> String",
            "import Data.Array (head, tail)",
            "-- comment\nfoo = bar",
            "{- block -} test",
            r#""hello world""#,
            "'c'",
            "42 + 3.14",
            "(>>= ) <$> <*>",
            "_ `mod` @",
        ];

        for source in test_cases {
            let result = lex(source);
            assert!(result.is_ok(), "Failed to lex: {}", source);

            let tokens = result.unwrap();

            // Check that spans are sequential and non-overlapping
            for i in 0..tokens.len().saturating_sub(1) {
                let current_end = tokens[i].1.end;
                let next_start = tokens[i + 1].1.start;
                assert!(
                    current_end <= next_start,
                    "Overlapping spans at token {}: {}..{} and {}..{}",
                    i,
                    tokens[i].1.start,
                    current_end,
                    next_start,
                    tokens[i + 1].1.end
                );
            }

            // Check that we can reconstruct meaningful parts of the source
            let reconstructed = reconstruct_from_tokens(source, &tokens);

            // The reconstructed text should equal the original minus skipped whitespace
            let source_normalized = source.replace([' ', '\t', '\r'], "");
            let reconstructed_normalized = reconstructed.replace([' ', '\t', '\r'], "");

            assert_eq!(
                reconstructed_normalized, source_normalized,
                "Roundtrip failed for: {}\nReconstructed: {}",
                source, reconstructed
            );
        }
    }

    /// Helper to reconstruct source from tokens
    fn reconstruct_from_tokens(source: &str, tokens: &[(RawToken, Span)]) -> String {
        let mut result = String::new();
        let mut last_end = 0;

        for (_, span) in tokens {
            // Add any skipped content (whitespace/newlines) between tokens
            if span.start > last_end {
                let between = &source[last_end..span.start];
                // Only add newlines, skip other whitespace since we skip it in lexer
                for ch in between.chars() {
                    if ch == '\n' {
                        result.push(ch);
                    }
                }
            }

            // Add the token's source text
            result.push_str(&source[span.start..span.end]);
            last_end = span.end;
        }

        result
    }

    #[test]
    fn test_no_dropped_characters() {
        // Comprehensive test that no non-whitespace characters are dropped
        let source = r#"
module Test.Example where

import Prelude
import Data.Maybe (Maybe(..))

-- | Documentation comment
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)

{- Multi-line
   comment -}
main = do
  let x = 42
  log $ show $ factorial x
"#;

        let tokens = lex(source).unwrap();

        // Collect all characters covered by token spans
        let mut covered = vec![false; source.len()];
        for (_, span) in &tokens {
            for i in span.start..span.end {
                covered[i] = true;
            }
        }

        // Check that all non-skipped characters are covered
        for (i, ch) in source.char_indices() {
            if !covered[i] && !matches!(ch, ' ' | '\t' | '\r' | '\n') {
                panic!(
                    "Character '{}' at position {} was not covered by any token",
                    ch, i
                );
            }
        }
    }

    // Property-based fuzz testing
    #[cfg(test)]
    mod proptests {
        use super::*;
        use proptest::prelude::*;

        // Generator for valid PureScript identifiers
        fn arb_lower_ident() -> impl Strategy<Value = String> {
            prop::string::string_regex("[a-z][a-zA-Z0-9_']*").unwrap()
        }

        fn arb_upper_ident() -> impl Strategy<Value = String> {
            prop::string::string_regex("[A-Z][a-zA-Z0-9_']*").unwrap()
        }

        // Generator for simple PureScript expressions
        fn arb_simple_expr() -> impl Strategy<Value = String> {
            prop_oneof![
                arb_lower_ident(),
                arb_upper_ident(),
                prop::num::i64::ANY.prop_map(|n| n.to_string()),
                Just("true".to_string()),
                Just("false".to_string()),
            ]
        }

        proptest! {
            #[test]
            fn prop_lex_identifiers_roundtrip(ident in arb_lower_ident()) {
                let tokens = lex(&ident).unwrap();
                assert!(!tokens.is_empty(), "Should lex at least one token");

                // Reconstruct from spans
                let reconstructed: String = tokens.iter()
                    .map(|(_, span)| &ident[span.start..span.end])
                    .collect();

                assert_eq!(reconstructed, ident);
            }

            #[test]
            fn prop_lex_never_panics(expr in arb_simple_expr()) {
                // Lexer should never panic, even on invalid input
                let _ = lex(&expr);
            }

            #[test]
            fn prop_spans_are_valid(expr in arb_simple_expr()) {
                if let Ok(tokens) = lex(&expr) {
                    for (_, span) in &tokens {
                        // Spans should be within source bounds
                        assert!(span.start <= expr.len());
                        assert!(span.end <= expr.len());
                        assert!(span.start <= span.end);
                    }
                }
            }

            #[test]
            fn prop_spans_cover_source(
                parts in prop::collection::vec(arb_simple_expr(), 1..10)
            ) {
                let source = parts.join(" ");
                if let Ok(tokens) = lex(&source) {
                    // All non-whitespace characters should be covered
                    let mut covered = vec![false; source.len()];
                    for (_, span) in &tokens {
                        for i in span.start..span.end {
                            covered[i] = true;
                        }
                    }

                    for (i, ch) in source.char_indices() {
                        if !matches!(ch, ' ' | '\t' | '\r' | '\n') {
                            prop_assert!(
                                covered[i],
                                "Character '{}' at {} not covered in: {}",
                                ch, i, source
                            );
                        }
                    }
                }
            }
        }
    }

}
