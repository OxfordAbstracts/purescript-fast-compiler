//! Abstract Syntax Tree (AST) for PureScript
//!
//! Similar to the CST but with:
//! - Parentheses removed (replaced by inner value)
//! - Operators desugared to function application
//! - Definition sites on key nodes

use crate::cst::{
    self, Associativity, ExportList, FunDep, ImportDecl, KindSigSource, ModuleName, QualifiedIdent, Spanned
};
use crate::lexer::token::Ident;
use crate::span::Span;
use crate::typechecker::ModuleRegistry;
use crate::typechecker::error::TypeError;

/// Where a name was defined
#[derive(Debug, Clone, PartialEq)]
pub enum DefinitionSite {
    Local(Span),
    Imported { module: Ident },
}

/// Module
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub span: Span,
    pub name: Spanned<ModuleName>,
    pub exports: Option<Spanned<ExportList>>,
    pub imports: Vec<ImportDecl>,
    pub decls: Vec<Decl>,
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
        where_clause: Vec<LetBinding>,
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
        kind_sig: KindSigSource,
        is_role_decl: bool,
        kind_type: Option<Box<TypeExpr>>,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
    },

    /// Type synonym: type Foo = Bar
    TypeAlias {
        span: Span,
        name: Spanned<Ident>,
        type_vars: Vec<Spanned<Ident>>,
        ty: TypeExpr,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
    },

    /// Newtype: newtype Foo = Foo Bar
    Newtype {
        span: Span,
        name: Spanned<Ident>,
        type_vars: Vec<Spanned<Ident>>,
        constructor: Spanned<Ident>,
        ty: TypeExpr,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
    },

    /// Type class declaration: class Eq a where ...
    Class {
        span: Span,
        constraints: Vec<Constraint>,
        name: Spanned<Ident>,
        type_vars: Vec<Spanned<Ident>>,
        fundeps: Vec<FunDep>,
        members: Vec<ClassMember>,
        is_kind_sig: bool,
        kind_type: Option<Box<TypeExpr>>,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
    },

    /// Instance declaration: instance Eq Int where ...
    Instance {
        span: Span,
        name: Option<Spanned<Ident>>,
        constraints: Vec<Constraint>,
        class_name: QualifiedIdent,
        types: Vec<TypeExpr>,
        members: Vec<Decl>,
        chain: bool,
        definition_site: DefinitionSite,
    },

    /// Fixity declaration: infixl 6 add as +
    Fixity {
        span: Span,
        associativity: Associativity,
        precedence: u8,
        target: QualifiedIdent,
        operator: Spanned<Ident>,
        is_type: bool,
    },

    /// Foreign value import: foreign import foo :: Type
    Foreign {
        span: Span,
        name: Spanned<Ident>,
        ty: TypeExpr,
    },

    /// Foreign data import: foreign import data Foo :: Kind
    ForeignData {
        span: Span,
        name: Spanned<Ident>,
        kind: TypeExpr,
    },

    /// Derive instance declaration: derive instance Eq MyType
    Derive {
        span: Span,
        newtype: bool,
        name: Option<Spanned<Ident>>,
        constraints: Vec<Constraint>,
        class_name: QualifiedIdent,
        types: Vec<TypeExpr>,
        definition_site: DefinitionSite,
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

/// Expression
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Variable: x, Data.Array.head
    Var {
        span: Span,
        name: QualifiedIdent,
        definition_site: DefinitionSite,
    },

    /// Constructor: Just, Nothing
    Constructor {
        span: Span,
        name: QualifiedIdent,
        definition_site: DefinitionSite,
    },

    /// Literal value
    Literal { span: Span, lit: Literal },

    /// Function application: f x
    App {
        span: Span,
        func: Box<Expr>,
        arg: Box<Expr>,
    },

    /// Visible type application: f @Type
    VisibleTypeApp {
        span: Span,
        func: Box<Expr>,
        ty: TypeExpr,
    },

    /// Lambda: \x -> x + 1
    Lambda {
        span: Span,
        binders: Vec<Binder>,
        body: Box<Expr>,
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
        module: Option<Ident>,
        statements: Vec<DoStatement>,
    },

    Ado {
        span: Span,
        module: Option<Ident>,
        statements: Vec<DoStatement>,
        result: Box<Expr>,
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

    /// Type annotation: expr :: Type
    TypeAnnotation {
        span: Span,
        expr: Box<Expr>,
        ty: TypeExpr,
    },

    /// Typed hole: ?hole
    Hole { span: Span, name: Ident },

    /// Array literal: [1, 2, 3]
    Array { span: Span, elements: Vec<Expr> },

    /// Negation: -x
    Negate { span: Span, expr: Box<Expr> },

    /// As-pattern expression: name@pattern
    AsPattern {
        span: Span,
        name: Box<Expr>,
        pattern: Box<Expr>,
    },
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
    Wildcard { span: Span },

    /// Variable: x
    Var { span: Span, name: Spanned<Ident> },

    /// Literal pattern: 42, "foo"
    Literal { span: Span, lit: Literal },

    /// Constructor pattern: Just x (also used for desugared operator patterns)
    Constructor {
        span: Span,
        name: QualifiedIdent,
        args: Vec<Binder>,
        definition_site: DefinitionSite,
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

    /// Array pattern: [a, b, c]
    Array { span: Span, elements: Vec<Binder> },

    /// Type-annotated pattern: (x :: Type)
    Typed {
        span: Span,
        binder: Box<Binder>,
        ty: TypeExpr,
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
    Discard { span: Span, expr: Expr },
}

/// Record field in literal
#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub span: Span,
    pub label: Spanned<Ident>,
    pub value: Option<Expr>,
    pub type_ann: Option<TypeExpr>,
    pub is_update: bool,
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
    Var { span: Span, name: Spanned<Ident> },

    /// Type constructor: Int, Array
    Constructor {
        span: Span,
        name: QualifiedIdent,
        definition_site: DefinitionSite,
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
        vars: Vec<(Spanned<Ident>, bool, Option<Box<TypeExpr>>)>,
        ty: Box<TypeExpr>,
    },

    /// Constrained type: Show a => a -> String
    Constrained {
        span: Span,
        constraints: Vec<Constraint>,
        ty: Box<TypeExpr>,
    },

    /// Record type: { x :: Int, y :: String }
    Record { span: Span, fields: Vec<TypeField> },

    /// Row type: (), (a :: String), ( x :: Int | r )
    Row {
        span: Span,
        fields: Vec<TypeField>,
        tail: Option<Box<TypeExpr>>,
        is_record: bool,
    },

    /// Type hole: ?hole
    Hole { span: Span, name: Ident },

    /// Wildcard type: _
    Wildcard { span: Span },

    /// Kind annotation: Const Void :: Type -> Type
    Kinded {
        span: Span,
        ty: Box<TypeExpr>,
        kind: Box<TypeExpr>,
    },

    /// Type-level string literal: "hello"
    StringLiteral { span: Span, value: String },

    /// Type-level integer literal: 42
    IntLiteral { span: Span, value: i64 },
}

/// Type constraint (for type classes)
#[derive(Debug, Clone, PartialEq)]
pub struct Constraint {
    pub span: Span,
    pub class: QualifiedIdent,
    pub args: Vec<TypeExpr>,
    pub definition_site: DefinitionSite,
}

/// Type field in record/row
#[derive(Debug, Clone, PartialEq)]
pub struct TypeField {
    pub span: Span,
    pub label: Spanned<Ident>,
    pub ty: TypeExpr,
}

// --- span() impls ---

impl Decl {
    pub fn span(&self) -> Span {
        match self {
            Decl::Value { span, .. }
            | Decl::TypeSignature { span, .. }
            | Decl::Data { span, .. }
            | Decl::TypeAlias { span, .. }
            | Decl::Newtype { span, .. }
            | Decl::Class { span, .. }
            | Decl::Instance { span, .. }
            | Decl::Fixity { span, .. }
            | Decl::Foreign { span, .. }
            | Decl::ForeignData { span, .. }
            | Decl::Derive { span, .. } => *span,
        }
    }
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var { span, .. }
            | Expr::Constructor { span, .. }
            | Expr::Literal { span, .. }
            | Expr::App { span, .. }
            | Expr::Lambda { span, .. }
            | Expr::If { span, .. }
            | Expr::Case { span, .. }
            | Expr::Let { span, .. }
            | Expr::Do { span, .. }
            | Expr::Ado { span, .. }
            | Expr::Record { span, .. }
            | Expr::RecordAccess { span, .. }
            | Expr::RecordUpdate { span, .. }
            | Expr::TypeAnnotation { span, .. }
            | Expr::Hole { span, .. }
            | Expr::Array { span, .. }
            | Expr::Negate { span, .. }
            | Expr::AsPattern { span, .. }
            | Expr::VisibleTypeApp { span, .. } => *span,
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
            | Binder::Array { span, .. }
            | Binder::Typed { span, .. } => *span,
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
            | TypeExpr::Hole { span, .. }
            | TypeExpr::Wildcard { span, .. }
            | TypeExpr::Kinded { span, .. }
            | TypeExpr::StringLiteral { span, .. }
            | TypeExpr::IntLiteral { span, .. } => *span,
        }
    }
}


pub fn convert(cst: cst::Module, registry: ModuleRegistry) -> (Module, Vec<TypeError>){ 
  todo!("convert CST to AST with proper module resolution and error handling")
}