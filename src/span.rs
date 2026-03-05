use std::fmt::Display;

/// Represents a source code position with line and column
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourcePos {
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed, in bytes)
    pub column: usize,
}

/// Represents a span in the source code
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// Start byte offset
    pub start: usize,
    /// End byte offset (exclusive)
    pub end: usize,
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.start, self.end)
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
    pub fn to_pos(&self, source: &str) -> Option<(SourcePos, SourcePos)> {
        if self.start > source.len() || self.end > source.len() || self.start > self.end {
            return None;
        }

        let mut line = 1;
        let mut col = 1;
        let mut start_pos = None;

        for (i, c) in source.char_indices() {
            if i == self.start {
                start_pos = Some(SourcePos { line, column: col });
            }
            if i == self.end {
                return start_pos.map(|s| (s, SourcePos { line, column: col }));
            }
            if c == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }

        // Handle start/end at source.len() (past last char)
        let end_pos = SourcePos { line, column: col };
        if self.start == source.len() && start_pos.is_none() {
            start_pos = Some(end_pos);
        }
        if self.end == source.len() {
            return start_pos.map(|s| (s, end_pos));
        }

        None
    }
}

/// A value with associated span information
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_pos_single_line() {
        let src = "hello world";
        // Span covering "world" (bytes 6..11)
        let span = Span::new(6, 11);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 7 });
        assert_eq!(end, SourcePos { line: 1, column: 12 });
    }

    #[test]
    fn test_to_pos_start_of_source() {
        let src = "abc";
        let span = Span::new(0, 3);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 1 });
        assert_eq!(end, SourcePos { line: 1, column: 4 });
    }

    #[test]
    fn test_to_pos_single_char_at_start() {
        let src = "abc";
        let span = Span::new(0, 1);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 1 });
        assert_eq!(end, SourcePos { line: 1, column: 2 });
    }

    #[test]
    fn test_to_pos_multiline() {
        let src = "abc\ndef\nghi";
        // Span covering "def" (bytes 4..7)
        let span = Span::new(4, 7);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 2, column: 1 });
        assert_eq!(end, SourcePos { line: 2, column: 4 });
    }

    #[test]
    fn test_to_pos_spanning_newline() {
        let src = "abc\ndef";
        // Span covering "c\nd" (bytes 2..5)
        let span = Span::new(2, 5);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 3 });
        assert_eq!(end, SourcePos { line: 2, column: 2 });
    }

    #[test]
    fn test_to_pos_end_of_source() {
        let src = "abc";
        // Span covering last char "c" (bytes 2..3)
        let span = Span::new(2, 3);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 3 });
        assert_eq!(end, SourcePos { line: 1, column: 4 });
    }

    #[test]
    fn test_to_pos_entire_source() {
        let src = "ab\ncd";
        let span = Span::new(0, 5);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 1 });
        assert_eq!(end, SourcePos { line: 2, column: 3 });
    }

    #[test]
    fn test_to_pos_empty_span() {
        let src = "abc";
        let span = Span::new(1, 1);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 2 });
        assert_eq!(end, SourcePos { line: 1, column: 2 });
    }

    #[test]
    fn test_to_pos_empty_span_at_start() {
        let src = "abc";
        let span = Span::new(0, 0);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 1 });
        assert_eq!(end, SourcePos { line: 1, column: 1 });
    }

    #[test]
    fn test_to_pos_out_of_bounds() {
        let src = "abc";
        assert!(Span::new(0, 4).to_pos(src).is_none());
        assert!(Span::new(4, 5).to_pos(src).is_none());
        assert!(Span::new(3, 2).to_pos(src).is_none());
    }

    #[test]
    fn test_to_pos_multibyte_utf8() {
        let src = "a§b"; // § is 2 bytes (0xC2 0xA7)
        // "b" starts at byte 3
        let span = Span::new(3, 4);
        let (start, end) = span.to_pos(src).unwrap();
        // § occupies 1 column despite being 2 bytes
        assert_eq!(start, SourcePos { line: 1, column: 3 });
        assert_eq!(end, SourcePos { line: 1, column: 4 });
    }

    #[test]
    fn test_to_pos_on_newline_char() {
        let src = "ab\ncd";
        // Span covering just the newline (byte 2..3)
        let span = Span::new(2, 3);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 1, column: 3 });
        assert_eq!(end, SourcePos { line: 2, column: 1 });
    }

    #[test]
    fn test_to_pos_third_line() {
        let src = "a\nb\ncdef";
        // Span covering "cd" (bytes 4..6)
        let span = Span::new(4, 6);
        let (start, end) = span.to_pos(src).unwrap();
        assert_eq!(start, SourcePos { line: 3, column: 1 });
        assert_eq!(end, SourcePos { line: 3, column: 3 });
    }
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
