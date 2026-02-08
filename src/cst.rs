//! Concrete Syntax Tree (CST) for PureScript
//!
//! Unlike an AST, the CST preserves all syntactic information including:
//! - Exact source spans for every node
//! - Parentheses and delimiters
//! - Comments (potentially)
//! - Original formatting
//!
//! This is essential for:
//! - Precise error messages
//! - IDE features (go-to-definition, hover, etc.)
//! - Code formatting tools
//! - Refactoring tools

use crate::ast::span::Span;
use crate::lexer::token::Ident;

/// Module with full span information
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub span: Span,
    pub name: Spanned<ModuleName>,
    pub exports: Option<Spanned<ExportList>>,
    pub imports: Vec<ImportDecl>,
    pub decls: Vec<Decl>,
}

/// Module name (potentially qualified: Data.Array)
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleName {
    pub parts: Vec<Ident>,
}

/// Export list
#[derive(Debug, Clone, PartialEq)]
pub struct ExportList {
    pub exports: Vec<Export>,
}

/// Single export
#[derive(Debug, Clone, PartialEq)]
pub enum Export {
    Value(Ident),
    Type(Ident, Option<DataMembers>),
    TypeOp(Ident),
    Class(Ident),
    Module(ModuleName),
}

/// Data constructor exports
#[derive(Debug, Clone, PartialEq)]
pub enum DataMembers {
    All,                    // (..)
    Explicit(Vec<Ident>),   // (Foo, Bar)
}

/// Import declaration
#[derive(Debug, Clone, PartialEq)]
pub struct ImportDecl {
    pub span: Span,
    pub module: ModuleName,
    pub imports: Option<ImportList>,
    pub qualified: Option<ModuleName>,
}

/// Import list (either imports or hiding)
#[derive(Debug, Clone, PartialEq)]
pub enum ImportList {
    Explicit(Vec<Import>),
    Hiding(Vec<Import>),
}

/// Single import
#[derive(Debug, Clone, PartialEq)]
pub enum Import {
    Value(Ident),
    Type(Ident, Option<DataMembers>),
    TypeOp(Ident),
    Class(Ident),
}

/// Top-level declaration
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// Value declaration: foo = bar
    Value {
        span: Span,
        name: Spanned<Ident>,
        binders: Vec<Binder>,
        guarded: GuardedExpr,
    },

    /// Type signature: foo :: Int -> Int
    TypeSignature {
        span: Span,
        name: Spanned<Ident>,
        ty: TypeExpr,
    },

    /// Data declaration: data Foo a = Bar a | Baz
    Data {
        span: Span,
        name: Spanned<Ident>,
        type_vars: Vec<Spanned<Ident>>,
        constructors: Vec<DataConstructor>,
    },

    /// Type synonym: type Foo = Bar
    TypeAlias {
        span: Span,
        name: Spanned<Ident>,
        type_vars: Vec<Spanned<Ident>>,
        ty: TypeExpr,
    },

    /// Newtype: newtype Foo = Foo Bar
    Newtype {
        span: Span,
        name: Spanned<Ident>,
        type_vars: Vec<Spanned<Ident>>,
        constructor: Spanned<Ident>,
        ty: TypeExpr,
    },

    /// Type class declaration
    Class {
        span: Span,
        name: Spanned<Ident>,
        type_var: Spanned<Ident>,
        members: Vec<ClassMember>,
    },

    /// Instance declaration
    Instance {
        span: Span,
        name: Spanned<Ident>,
        types: Vec<TypeExpr>,
        members: Vec<Decl>,
    },

    /// Fixity declaration: infixl 6 +
    Fixity {
        span: Span,
        associativity: Associativity,
        precedence: u8,
        operator: Spanned<Ident>,
    },
}

/// Data constructor in data declaration
#[derive(Debug, Clone, PartialEq)]
pub struct DataConstructor {
    pub span: Span,
    pub name: Spanned<Ident>,
    pub fields: Vec<TypeExpr>,
}

/// Class member (method signature)
#[derive(Debug, Clone, PartialEq)]
pub struct ClassMember {
    pub span: Span,
    pub name: Spanned<Ident>,
    pub ty: TypeExpr,
}

/// Operator associativity
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
    None,
}

/// Guarded expression (for pattern matching)
#[derive(Debug, Clone, PartialEq)]
pub enum GuardedExpr {
    Unconditional(Box<Expr>),
    Guarded(Vec<Guard>),
}

/// Guard in pattern matching
#[derive(Debug, Clone, PartialEq)]
pub struct Guard {
    pub span: Span,
    pub patterns: Vec<GuardPattern>,
    pub expr: Box<Expr>,
}

/// Pattern in guard
#[derive(Debug, Clone, PartialEq)]
pub enum GuardPattern {
    Boolean(Box<Expr>),
    Pattern(Binder, Box<Expr>),
}

/// Expression with full span tracking
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Variable: x, Data.Array.head
    Var {
        span: Span,
        name: QualifiedIdent,
    },

    /// Constructor: Just, Nothing
    Constructor {
        span: Span,
        name: QualifiedIdent,
    },

    /// Literal value
    Literal {
        span: Span,
        lit: Literal,
    },

    /// Function application: f x
    App {
        span: Span,
        func: Box<Expr>,
        arg: Box<Expr>,
    },

    /// Lambda: \x -> x + 1
    Lambda {
        span: Span,
        binders: Vec<Binder>,
        body: Box<Expr>,
    },

    /// Operator application: x + y
    Op {
        span: Span,
        left: Box<Expr>,
        op: Spanned<Ident>,
        right: Box<Expr>,
    },

    /// Operator section: (+ 1), (1 +)
    OpSection {
        span: Span,
        op: Spanned<Ident>,
        arg: Option<Box<Expr>>,
    },

    /// If-then-else
    If {
        span: Span,
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },

    /// Case expression
    Case {
        span: Span,
        exprs: Vec<Expr>,
        alts: Vec<CaseAlternative>,
    },

    /// Let binding
    Let {
        span: Span,
        bindings: Vec<LetBinding>,
        body: Box<Expr>,
    },

    /// Do notation
    Do {
        span: Span,
        statements: Vec<DoStatement>,
    },

    /// Record literal: { x: 1, y: 2 }
    Record {
        span: Span,
        fields: Vec<RecordField>,
    },

    /// Record accessor: rec.field
    RecordAccess {
        span: Span,
        expr: Box<Expr>,
        field: Spanned<Ident>,
    },

    /// Record update: rec { x = 1 }
    RecordUpdate {
        span: Span,
        expr: Box<Expr>,
        updates: Vec<RecordUpdate>,
    },

    /// Parenthesized expression (preserved in CST)
    Parens {
        span: Span,
        expr: Box<Expr>,
    },

    /// Type annotation: expr :: Type
    TypeAnnotation {
        span: Span,
        expr: Box<Expr>,
        ty: TypeExpr,
    },

    /// Typed hole: ?hole
    Hole {
        span: Span,
        name: Ident,
    },
}

/// Qualified identifier (potentially with module prefix)
#[derive(Debug, Clone, PartialEq)]
pub struct QualifiedIdent {
    pub module: Option<ModuleName>,
    pub name: Ident,
}

/// Literal values
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
    Char(char),
    Boolean(bool),
    Array(Vec<Expr>),
}

/// Pattern binder
#[derive(Debug, Clone, PartialEq)]
pub enum Binder {
    /// Wildcard: _
    Wildcard {
        span: Span,
    },

    /// Variable: x
    Var {
        span: Span,
        name: Spanned<Ident>,
    },

    /// Literal pattern: 42, "foo"
    Literal {
        span: Span,
        lit: Literal,
    },

    /// Constructor pattern: Just x
    Constructor {
        span: Span,
        name: QualifiedIdent,
        args: Vec<Binder>,
    },

    /// Record pattern: { x, y }
    Record {
        span: Span,
        fields: Vec<RecordBinderField>,
    },

    /// As-pattern: x@(Just y)
    As {
        span: Span,
        name: Spanned<Ident>,
        binder: Box<Binder>,
    },

    /// Parenthesized pattern
    Parens {
        span: Span,
        binder: Box<Binder>,
    },
}

/// Case alternative
#[derive(Debug, Clone, PartialEq)]
pub struct CaseAlternative {
    pub span: Span,
    pub binders: Vec<Binder>,
    pub result: GuardedExpr,
}

/// Let binding
#[derive(Debug, Clone, PartialEq)]
pub enum LetBinding {
    /// Value binding: x = expr
    Value {
        span: Span,
        binder: Binder,
        expr: Expr,
    },

    /// Type signature: x :: Type
    Signature {
        span: Span,
        name: Spanned<Ident>,
        ty: TypeExpr,
    },
}

/// Do statement
#[derive(Debug, Clone, PartialEq)]
pub enum DoStatement {
    /// Bind: x <- action
    Bind {
        span: Span,
        binder: Binder,
        expr: Expr,
    },

    /// Let: let x = expr
    Let {
        span: Span,
        bindings: Vec<LetBinding>,
    },

    /// Expression statement: action
    Discard {
        span: Span,
        expr: Expr,
    },
}

/// Record field in literal
#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub span: Span,
    pub label: Spanned<Ident>,
    pub value: Expr,
}

/// Record update
#[derive(Debug, Clone, PartialEq)]
pub struct RecordUpdate {
    pub span: Span,
    pub label: Spanned<Ident>,
    pub value: Expr,
}

/// Record binder field
#[derive(Debug, Clone, PartialEq)]
pub struct RecordBinderField {
    pub span: Span,
    pub label: Spanned<Ident>,
    pub binder: Option<Binder>,
}

/// Type expression
#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    /// Type variable: a
    Var {
        span: Span,
        name: Spanned<Ident>,
    },

    /// Type constructor: Int, Array
    Constructor {
        span: Span,
        name: QualifiedIdent,
    },

    /// Type application: Array Int
    App {
        span: Span,
        constructor: Box<TypeExpr>,
        arg: Box<TypeExpr>,
    },

    /// Function type: Int -> String
    Function {
        span: Span,
        from: Box<TypeExpr>,
        to: Box<TypeExpr>,
    },

    /// Forall quantification: forall a. a -> a
    Forall {
        span: Span,
        vars: Vec<Spanned<Ident>>,
        ty: Box<TypeExpr>,
    },

    /// Constrained type: Show a => a -> String
    Constrained {
        span: Span,
        constraints: Vec<Constraint>,
        ty: Box<TypeExpr>,
    },

    /// Record type: { x :: Int, y :: String }
    Record {
        span: Span,
        fields: Vec<TypeField>,
    },

    /// Row type (for extensible records): ( x :: Int | r )
    Row {
        span: Span,
        fields: Vec<TypeField>,
        tail: Option<Box<TypeExpr>>,
    },

    /// Parenthesized type
    Parens {
        span: Span,
        ty: Box<TypeExpr>,
    },

    /// Type hole: ?hole 
    TypeHole {
        span: Span,
        name: Ident,
    },
}

/// Type constraint (for type classes)
#[derive(Debug, Clone, PartialEq)]
pub struct Constraint {
    pub span: Span,
    pub class: QualifiedIdent,
    pub args: Vec<TypeExpr>,
}

/// Type field in record/row
#[derive(Debug, Clone, PartialEq)]
pub struct TypeField {
    pub span: Span,
    pub label: Spanned<Ident>,
    pub ty: TypeExpr,
}

/// Helper type for values with spans
#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub value: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }
}

// Convenience constructors for common patterns
impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var { span, .. }
            | Expr::Constructor { span, .. }
            | Expr::Literal { span, .. }
            | Expr::App { span, .. }
            | Expr::Lambda { span, .. }
            | Expr::Op { span, .. }
            | Expr::OpSection { span, .. }
            | Expr::If { span, .. }
            | Expr::Case { span, .. }
            | Expr::Let { span, .. }
            | Expr::Do { span, .. }
            | Expr::Record { span, .. }
            | Expr::RecordAccess { span, .. }
            | Expr::RecordUpdate { span, .. }
            | Expr::Parens { span, .. }
            | Expr::TypeAnnotation { span, .. }
            | Expr::Hole { span, .. } => *span,
        }
    }
}

impl Binder {
    pub fn span(&self) -> Span {
        match self {
            Binder::Wildcard { span }
            | Binder::Var { span, .. }
            | Binder::Literal { span, .. }
            | Binder::Constructor { span, .. }
            | Binder::Record { span, .. }
            | Binder::As { span, .. }
            | Binder::Parens { span, .. } => *span,
        }
    }
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Var { span, .. }
            | TypeExpr::Constructor { span, .. }
            | TypeExpr::App { span, .. }
            | TypeExpr::Function { span, .. }
            | TypeExpr::Forall { span, .. }
            | TypeExpr::Constrained { span, .. }
            | TypeExpr::Record { span, .. }
            | TypeExpr::Row { span, .. }
            | TypeExpr::TypeHole { span, .. }
            | TypeExpr::Parens { span, .. } => *span,
        }
    }
}
