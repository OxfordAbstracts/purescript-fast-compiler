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
    Hole(Ident),              // ?hole, ?myHole
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
            Token::LowerIdent(_) => write!(f, "identifier"),
            Token::UpperIdent(_) => write!(f, "type identifier"),
            Token::Operator(_) => write!(f, "operator"),
            Token::Hole(_) => write!(f, "hole"),
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