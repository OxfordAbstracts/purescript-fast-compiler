use std::fmt::Display;

/// Represents a source code position with line and column
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourcePos {
    /// Line number (0-indexed)
    pub line: usize,
    /// Column number (0-indexed, in bytes)
    pub column: usize,
}

/// Represents a span in the source code
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// Start byte offset
    pub start: usize,
    /// End byte offset (exclusive)
    pub end: usize,
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Span({}-{})", self.start, self.end)
    }
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
    pub fn to_pos(&self, source: &str) -> (SourcePos, SourcePos) {
        let mut line = 1;
        let mut column = 1;
        let mut current_pos = 1;    
        for (i, c) in source.char_indices() {
            if i >= self.start {
                break;
            }
            if c == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
            current_pos = i + c.len_utf8();
        }
        let start_pos = SourcePos { line, column };
        for (i, c) in source[current_pos..].char_indices() {
            if current_pos + i >= self.end {
                break;
            }
            if c == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
        let end_pos = SourcePos { line, column };
        (start_pos, end_pos)
    }
}

/// A value with associated span information
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        Spanned {
            node: f(self.node),
            span: self.span,
        }
    }
}
