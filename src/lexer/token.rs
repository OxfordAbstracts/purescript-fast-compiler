use crate::interner::Symbol;

/// Interned string symbol for identifiers
pub type Ident = Symbol;

/// Tokens in the PureScript language
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Keywords
    Module,
    Import,
    Export,
    Foreign,
    Data,
    Type,
    Newtype,
    Class,
    Instance,
    Derive,
    Where,
    Let,
    In,
    Do,
    Ado,
    Case,
    Of,
    If,
    Then,
    Else,
    Forall,
    Infix,
    Infixl,
    Infixr,
    As,
    Hiding,

    // Identifiers
    LowerIdent(Ident),        // foo, myVariable
    UpperIdent(Ident),        // Foo, MyType
    QualifiedLower(Ident, Ident), // Module.foo
    QualifiedUpper(Ident, Ident), // Module.Type
    Operator(Ident),          // +, <>, >>>
    QualifiedOperator(Ident, Ident), // Module.+

    // Literals
    Integer(i64),
    Float(f64),
    String(String),
    Char(char),
    True,
    False,

    // Layout tokens (inserted by layout processor)
    LayoutStart,    // Virtual { after where, let, do, of
    LayoutSep,      // Virtual ; on same-indentation newlines
    LayoutEnd,      // Virtual } on dedent

    // Delimiters
    LParen,         // (
    RParen,         // )
    LBrace,         // {
    RBrace,         // }
    LBracket,       // [
    RBracket,       // ]

    // Special symbols
    Arrow,          // ->
    FatArrow,       // =>
    DoubleColon,    // ::
    Pipe,           // |
    Backslash,      // \
    LeftArrow,      // <-
    Dot,            // .
    Comma,          // ,
    Semicolon,      // ;
    Equals,         // =
    Backtick,       // `
    At,             // @
    Underscore,     // _
    DoubleArrow,    // <=>
    Tilde,          // ~

    // Comments (preserved for documentation tools)
    LineComment(String),
    BlockComment(String),
    DocComment(String),

    // End of file
    Eof,
}

impl Token {
    /// Returns true if this token is a layout keyword
    pub fn is_layout_keyword(&self) -> bool {
        matches!(self, Token::Where | Token::Let | Token::Do | Token::Of | Token::Ado)
    }

    /// Returns true if this token starts a declaration
    pub fn starts_decl(&self) -> bool {
        matches!(
            self,
            Token::Data
                | Token::Type
                | Token::Newtype
                | Token::Class
                | Token::Instance
                | Token::Foreign
                | Token::Derive
                | Token::Infix
                | Token::Infixl
                | Token::Infixr
                | Token::LowerIdent(_)
        )
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Module => write!(f, "module"),
            Token::Import => write!(f, "import"),
            Token::Where => write!(f, "where"),
            Token::Let => write!(f, "let"),
            Token::In => write!(f, "in"),
            Token::Do => write!(f, "do"),
            Token::Case => write!(f, "case"),
            Token::Of => write!(f, "of"),
            Token::If => write!(f, "if"),
            Token::Then => write!(f, "then"),
            Token::Else => write!(f, "else"),
            Token::LowerIdent(_) => write!(f, "identifier"),
            Token::UpperIdent(_) => write!(f, "type identifier"),
            Token::Operator(_) => write!(f, "operator"),
            Token::Integer(_) => write!(f, "integer"),
            Token::Float(_) => write!(f, "float"),
            Token::String(_) => write!(f, "string"),
            Token::Char(_) => write!(f, "char"),
            Token::Arrow => write!(f, "->"),
            Token::FatArrow => write!(f, "=>"),
            Token::DoubleColon => write!(f, "::"),
            Token::LayoutStart => write!(f, "{{layout}}"),
            Token::LayoutSep => write!(f, ";{{layout}}"),
            Token::LayoutEnd => write!(f, "}}{{layout}}"),
            Token::Eof => write!(f, "end of file"),
            _ => write!(f, "{:?}", self),
        }
    }
}
