use crate::interner::{Symbol, resolve};

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
    Hole(Ident),              // ?hole, ?myHole
    QualifiedOperator(Ident, Ident), // Module.+
    QualifiedDo(Ident),              // Module.do (combined by layout processor)
    QualifiedAdo(Ident),             // Module.ado (combined by layout processor)

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
    Colon,          // :
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
        matches!(self, Token::Where | Token::Let | Token::Do | Token::Of | Token::Ado | Token::QualifiedDo(_) | Token::QualifiedAdo(_))
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


    /// display the token as its original source text (for debugging)
    pub fn print(&self) -> String {
        match self {
            Token::Module => "module".to_string(),
            Token::Import => "import".to_string(),
            Token::Export => "export".to_string(),
            Token::Foreign => "foreign".to_string(),      
            Token::Data => "data".to_string(),
            Token::Type => "type".to_string(),
            Token::Newtype => "newtype".to_string(),
            Token::Class => "class".to_string(),
            Token::Instance => "instance".to_string(),
            Token::Derive => "derive".to_string(),
            Token::Where => "where".to_string(),
            Token::Let => "let".to_string(),
            Token::In => "in".to_string(),
            Token::Do => "do".to_string(),
            Token::Ado => "ado".to_string(),
            Token::Case => "case".to_string(),
            Token::Of => "of".to_string(),
            Token::If => "if".to_string(),
            Token::Then => "then".to_string(),
            Token::Else => "else".to_string(),
            Token::Forall => "forall".to_string(),
            Token::Infix => "infix".to_string(),
            Token::Infixl => "infixl".to_string(),  
            Token::Infixr => "infixr".to_string(),
            Token::As => "as".to_string(),
            Token::Hiding => "hiding".to_string(),
            Token::LowerIdent(ident) => format!("{:?}", ident),
            Token::UpperIdent(ident) => format!("{:?}", ident),
            Token::QualifiedLower(module, ident) => format!("{:?}.{:?}", module, ident),
            Token::QualifiedUpper(module, ident) => format!("{:?}.{:?}", module, ident),
            Token::Operator(op) => format!("{:?}", op),
            Token::Hole(id) => format!("?{:?}", id),
            Token::QualifiedOperator(module, op) => format!("{:?}.{:?}", module, op),
            Token::QualifiedDo(module) => format!("{:?}.do", module),
            Token::QualifiedAdo(module) => format!("{:?}.ado", module),
            Token::Integer(i) => i.to_string(),
            Token::Float(f) => f.to_string(),
            Token::String(s) => format!("{:?}", s), // add quotes
            Token::Char(c) => format!("{:?}", c),   // add quotes
            Token::True => "true".to_string(),
            Token::False => "false".to_string(),
            Token::LayoutStart => "".to_string(),
            Token::LayoutSep => "".to_string(),
            Token::LayoutEnd => "".to_string(),
            Token::LParen => "(".to_string(),
            Token::RParen => ")".to_string(),
            Token::LBrace => "{".to_string(),
            Token::RBrace => "}".to_string(),
            Token::LBracket => "[".to_string(),
            Token::RBracket => "]".to_string(),
            Token::Arrow => "->".to_string(),
            Token::FatArrow => "=>".to_string(),
            Token::DoubleColon => "::".to_string(),
            Token::Colon => ":".to_string(),
            Token::Pipe => "|".to_string(),
            Token::Backslash => "\\".to_string(),
            Token::LeftArrow => "<-".to_string(),
            Token::Dot => ".".to_string(),
            Token::Comma => ",".to_string(),
            Token::Semicolon => ";".to_string(),    
            Token::Equals => "=".to_string(),
            Token::Backtick => "`".to_string(),
            Token::At => "@".to_string(),
            Token::Underscore => "_".to_string(),
            Token::DoubleArrow => "<=>".to_string(),
            Token::Tilde => "~".to_string(),
            Token::LineComment(s) => format!("--{}", s),
            Token::BlockComment(s) => format!("/*{}*/", s),
            Token::DocComment(s) => format!("///{}", s),
            Token::Eof => "".to_string(),  
        }
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
            Token::LowerIdent(ident) => write!(f, "{}", resolve(*ident).unwrap_or_default()),
            Token::UpperIdent(ident) => write!(f, "{}", resolve(*ident).unwrap_or_default()),
            Token::Operator(ident) => write!(f, "{}", resolve(*ident).unwrap_or_default()),
            Token::Hole(ident) => write!(f, "?{}", resolve(*ident).unwrap_or_default()),
            Token::Integer(n) => write!(f, "{}", n),
            Token::Float(n) => write!(f, "{}", n),
            Token::String(s) => write!(f, "{:?}", s),
            Token::Char(c) => write!(f, "{:?}", c),
            Token::Arrow => write!(f, "->"),
            Token::FatArrow => write!(f, "=>"),
            Token::DoubleColon => write!(f, "::"),
            Token::LayoutStart => write!(f, "{{layout}}"),
            Token::LayoutSep => write!(f, "{{layout}}"),
            Token::LayoutEnd => write!(f, "}}{{layout}}"),
            Token::Eof => write!(f, "end of file"),
            Token::Data => write!(f, "data"),
            Token::Type => write!(f, "type"),
            Token::Newtype => write!(f, "newtype"),
            Token::Class => write!(f, "class"),
            Token::Instance => write!(f, "instance"),
            Token::Derive => write!(f, "derive"),
            Token::Ado => write!(f, "ado"),
            Token::Forall => write!(f, "forall"),
            Token::Infix => write!(f, "infix"),
            Token::Infixl => write!(f, "infixl"),
            Token::Infixr => write!(f, "infixr"),
            Token::As => write!(f, "as"),
            Token::Hiding => write!(f, "hiding"),
            Token::QualifiedLower(module, ident) => write!(f, "{}.{}", resolve(*module).unwrap_or_default(), resolve(*ident).unwrap_or_default()),
            Token::QualifiedUpper(module, ident) => write!(f, "{}.{}", resolve(*module).unwrap_or_default(), resolve(*ident).unwrap_or_default()),
            Token::QualifiedOperator(module, op) => write!(f, "{}.{}", resolve(*module).unwrap_or_default(), resolve(*op).unwrap_or_default()),
            Token::QualifiedDo(module) => write!(f, "{}.do", resolve(*module).unwrap_or_default()),
            Token::QualifiedAdo(module) => write!(f, "{}.ado", resolve(*module).unwrap_or_default()),
            Token::LineComment(s) => write!(f, "--{}", s),
            Token::BlockComment(s) => write!(f, "/*{}*/", s),
            Token::DocComment(s) => write!(f, "///{}", s), 
            Token::Comma => write!(f, ","),
            Token::Semicolon => write!(f, ";"),
            Token::Equals => write!(f, "="),
            Token::Backslash => write!(f, "\\"),
            Token::LeftArrow => write!(f, "<-"),
            Token::Dot => write!(f, "."),
            Token::Backtick => write!(f, "`"),
            Token::At => write!(f, "@"),
            Token::Underscore => write!(f, "_"),
            Token::DoubleArrow => write!(f, "<=>"),
            Token::Tilde => write!(f, "~"),
            Token::Export => write!(f, "export"),
            Token::Foreign => write!(f, "foreign"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::Colon => write!(f, ":"),
            Token::Pipe => write!(f, "|"),
        }
    }
}