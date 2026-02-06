use crate::ast::span::Spanned;
use crate::lexer::Token;

/// Adapter to convert our token stream to LALRPOP's expected format
pub struct LexerAdapter {
    tokens: Vec<Spanned<Token>>,
    position: usize,
}

impl LexerAdapter {
    pub fn new(tokens: Vec<Spanned<Token>>) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }
}

impl Iterator for LexerAdapter {
    type Item = Result<(usize, Token, usize), String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.tokens.len() {
            return None;
        }

        let spanned = &self.tokens[self.position];
        self.position += 1;

        Some(Ok((
            spanned.span.start,
            spanned.node.clone(),
            spanned.span.end,
        )))
    }
}
