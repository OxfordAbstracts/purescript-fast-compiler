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

/// What kind of kind signature this Decl::Data represents (if any)
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum KindSigSource {
    /// Not a kind signature — a real data/type declaration or role declaration
    None,
    /// `data Foo :: Kind`
    Data,
    /// `type Foo :: Kind`
    Type,
    /// `newtype Foo :: Kind`
    Newtype,
    /// `class Foo :: Kind`
    Class,
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
        /// What kind of kind signature this is, or None for real declarations/role decls
        kind_sig: KindSigSource,
        /// True when this is a role declaration (e.g., `type role Foo phantom`)
        is_role_decl: bool,
        /// Kind type expression for kind signatures (e.g., `data Foo :: Type -> Type`)
        kind_type: Option<Box<TypeExpr>>,
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

    /// Type class declaration: class Eq a where ...
    Class {
        span: Span,
        constraints: Vec<Constraint>,
        name: Spanned<Ident>,
        type_vars: Vec<Spanned<Ident>>,
        fundeps: Vec<FunDep>,
        members: Vec<ClassMember>,
        /// True when this is a kind signature: `class Foo :: Kind`
        is_kind_sig: bool,
    },

    /// Instance declaration: instance Eq Int where ...
    Instance {
        span: Span,
        name: Option<Spanned<Ident>>,
        constraints: Vec<Constraint>,
        class_name: QualifiedIdent,
        types: Vec<TypeExpr>,
        members: Vec<Decl>,
        /// True if this instance is a continuation of an instance chain (preceded by `else`)
        chain: bool,
    },

    /// Fixity declaration: infixl 6 add as +
    /// When `is_type` is true, this is a type-level fixity: infixr 6 type Tuple as /\
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
    },
}

/// Functional dependency: a b -> c
#[derive(Debug, Clone, PartialEq)]
pub struct FunDep {
    pub lhs: Vec<Ident>,
    pub rhs: Vec<Ident>,
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

    /// Visibile type application: f @Type, f @(T a) f @(T () a)
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

    /// Operator application: x + y
    Op {
        span: Span,
        left: Box<Expr>,
        op: Spanned<QualifiedIdent>,
        right: Box<Expr>,
    },

    /// Operator in parens: (+)
    OpParens {
        span: Span,
        op: Spanned<QualifiedIdent>,
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

    /// Array literal: [1, 2, 3]
    Array {
        span: Span,
        elements: Vec<Expr>,
    },

    /// Negation: -x
    Negate {
        span: Span,
        expr: Box<Expr>,
    },

    /// As-pattern expression: name@pattern (for do-bind conversion to binder)
    AsPattern {
        span: Span,
        name: Box<Expr>,
        pattern: Box<Expr>,
    },


}

/// Qualified identifier (potentially with module prefix)
#[derive(Debug, Clone, PartialEq)]
pub struct QualifiedIdent {
    pub module: Option<Ident>,
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

    /// Array pattern: [a, b, c]
    Array {
        span: Span,
        elements: Vec<Binder>,
    },

    /// Operator pattern: a /\ b, x :| xs
    Op {
        span: Span,
        left: Box<Binder>,
        op: Spanned<Ident>,
        right: Box<Binder>,
    },

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
    pub value: Option<Expr>,
    /// Type annotation for record type fields: `{ label :: Type }`
    pub type_ann: Option<TypeExpr>,
    /// True when `=` was used (record update syntax), false when `:` was used (record literal)
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
    /// Each var is (name, visible) where visible means `@a` syntax for VTA
    Forall {
        span: Span,
        vars: Vec<(Spanned<Ident>, bool)>,
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

    /// Row type: (), (a :: String), ( x :: Int | r )
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
    Hole {
        span: Span,
        name: Ident,
    },

    /// Wildcard type: _
    Wildcard {
        span: Span,
    },

    /// Type-level operator application: a ~> b
    TypeOp {
        span: Span,
        left: Box<TypeExpr>,
        op: Spanned<QualifiedIdent>,
        right: Box<TypeExpr>,
    },

    /// Kind annotation: Const Void :: Type -> Type
    Kinded {
        span: Span,
        ty: Box<TypeExpr>,
        kind: Box<TypeExpr>,
    },

    /// Type-level string literal: "hello"
    StringLiteral {
        span: Span,
        value: String,
    },

    /// Type-level integer literal: 42
    IntLiteral {
        span: Span,
        value: i64,
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

/// Helper enum for mixed import/declaration parsing
#[derive(Debug, Clone, PartialEq)]
pub enum ImportOrDecl {
    Import(ImportDecl),
    Decl(Decl),
}

/// Convert a TypeExpr (parsed as type application) into a Constraint.
/// For example, `Show a` parsed as `TypeExpr::App(Constructor("Show"), Var("a"))`
/// becomes `Constraint { class: "Show", args: [Var("a")] }`.
pub fn type_to_constraint(ty: TypeExpr, span: Span) -> Constraint {
    let mut args = Vec::new();
    let mut current = ty;
    loop {
        match current {
            TypeExpr::App { constructor, arg, .. } => {
                args.push(*arg);
                current = *constructor;
            }
            TypeExpr::Constructor { name, .. } => {
                args.reverse();
                return Constraint {
                    span,
                    class: name,
                    args,
                };
            }
            TypeExpr::Parens { ty, .. } => {
                current = *ty;
            }
            other => {
                args.reverse();
                return Constraint {
                    span,
                    class: QualifiedIdent { module: None, name: crate::interner::intern("Unknown") },
                    args: {
                        let mut all = vec![other];
                        all.extend(args);
                        all
                    },
                };
            }
        }
    }
}

/// Convert an Expr (parsed as expression) into a Binder for do-bind patterns.
/// For example, `{ x, y }` parsed as a record expression becomes a record binder,
/// and `Tuple a b` parsed as constructor application becomes a constructor binder.
/// Returns an error if the expression cannot be represented as a valid binder.
pub fn expr_to_binder(expr: Expr) -> Result<Binder, String> {
    match expr {
        Expr::Var { span, name } => {
            Ok(Binder::Var {
                span,
                name: Spanned::new(name.name, span),
            })
        }
        Expr::Constructor { span, name } => {
            Ok(Binder::Constructor { span, name, args: vec![] })
        }
        Expr::Hole { span, name } => {
            let resolved = crate::interner::resolve(name).unwrap_or_default();
            if resolved == "_" {
                Ok(Binder::Wildcard { span })
            } else {
                Ok(Binder::Var { span, name: Spanned::new(name, span) })
            }
        }
        Expr::Literal { span, lit } => {
            Ok(Binder::Literal { span, lit })
        }
        Expr::App { span, func, arg } => {
            let arg_binder = expr_to_binder(*arg)?;
            match expr_to_binder(*func)? {
                Binder::Constructor { name, mut args, .. } => {
                    args.push(arg_binder);
                    Ok(Binder::Constructor { span, name, args })
                }
                _ => {
                    Err(format!("expected constructor application in binder"))
                }
            }
        }
        Expr::Parens { span, expr } => {
            Ok(Binder::Parens { span, binder: Box::new(expr_to_binder(*expr)?) })
        }
        Expr::Op { span, left, op, right } => {
            Ok(Binder::Op {
                span,
                left: Box::new(expr_to_binder(*left)?),
                op: Spanned::new(op.value.name, op.span),
                right: Box::new(expr_to_binder(*right)?),
            })
        }
        Expr::Record { span, fields } => {
            let binder_fields: Result<Vec<RecordBinderField>, String> = fields.into_iter().map(|f| {
                let binder = f.value.map(expr_to_binder).transpose()?;
                Ok(RecordBinderField {
                    span: f.span,
                    label: f.label,
                    binder,
                })
            }).collect();
            Ok(Binder::Record { span, fields: binder_fields? })
        }
        Expr::Array { span, elements } => {
            let binders: Result<Vec<Binder>, String> = elements.into_iter().map(expr_to_binder).collect();
            Ok(Binder::Array { span, elements: binders? })
        }
        Expr::TypeAnnotation { span, expr, ty } => {
            let inner = expr_to_binder(*expr)?;
            Ok(Binder::Typed { span, binder: Box::new(inner), ty })
        }
        Expr::Negate { expr, .. } => {
            match expr_to_binder(*expr)? {
                Binder::Literal { span, lit } => Ok(Binder::Literal { span, lit }),
                _ => Err(format!("negation in binder must be applied to a literal")),
            }
        }
        Expr::AsPattern { span, name, pattern } => {
            let name_ident = match *name {
                Expr::Var { name: qi, span: ns, .. } => Spanned::new(qi.name, ns),
                _ => return Err(format!("expected variable name in as-pattern")),
            };
            Ok(Binder::As {
                span,
                name: name_ident,
                binder: Box::new(expr_to_binder(*pattern)?),
            })
        }
        Expr::VisibleTypeApp { span, func, ty } => {
            let name_ident = match *func {
                Expr::Var { name: qi, span: ns, .. } => Spanned::new(qi.name, ns),
                _ => return Err(format!("expected variable name in as-pattern")),
            };
            Ok(Binder::As {
                span,
                name: name_ident,
                binder: Box::new(type_to_binder(ty)?),
            })
        }
        _other => {
            Err(format!("expression cannot be used as a binder"))
        }
    }
}

/// Convert a type expression to a binder (for as-pattern conversion via visible type app).
/// This handles the case where `name@pattern` is parsed as `VisibleTypeApp` because
/// `@` takes a type argument. Common patterns like `x@y`, `x@(Constructor args)` need
/// the type to be converted back to a binder.
pub fn type_to_binder(ty: TypeExpr) -> Result<Binder, String> {
    match ty {
        TypeExpr::Var { span, name } => {
            Ok(Binder::Var { span, name })
        }
        TypeExpr::Constructor { span, name } => {
            Ok(Binder::Constructor { span, name, args: vec![] })
        }
        TypeExpr::App { constructor, arg, .. } => {
            let mut args = vec![type_to_binder(*arg)?];
            let mut current = *constructor;
            loop {
                match current {
                    TypeExpr::App { constructor, arg, .. } => {
                        args.push(type_to_binder(*arg)?);
                        current = *constructor;
                    }
                    TypeExpr::Constructor { span, name } => {
                        args.reverse();
                        return Ok(Binder::Constructor { span, name, args });
                    }
                    _ => return Err(format!("expected constructor application in binder")),
                }
            }
        }
        TypeExpr::Parens { ty, .. } => {
            type_to_binder(*ty)
        }
        TypeExpr::Record { span, fields } => {
            let binder_fields: Result<Vec<RecordBinderField>, String> = fields.into_iter().map(|f| {
                let binder = if matches!(f.ty, TypeExpr::Wildcard { .. }) {
                    None
                } else {
                    Some(type_to_binder(f.ty)?)
                };
                Ok(RecordBinderField {
                    span: f.span,
                    label: f.label,
                    binder,
                })
            }).collect();
            Ok(Binder::Record { span, fields: binder_fields? })
        }
        TypeExpr::Wildcard { span } => {
            Ok(Binder::Wildcard { span })
        }
        TypeExpr::TypeOp { span, left, op, right } => {
            Ok(Binder::Op {
                span,
                left: Box::new(type_to_binder(*left)?),
                op: Spanned::new(op.value.name, op.span),
                right: Box::new(type_to_binder(*right)?),
            })
        }
        _ => {
            Err(format!("type expression cannot be used as a binder"))
        }
    }
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
            | Expr::OpParens { span, .. }
            | Expr::If { span, .. }
            | Expr::Case { span, .. }
            | Expr::Let { span, .. }
            | Expr::Do { span, .. }
            | Expr::Ado { span, .. }
            | Expr::Record { span, .. }
            | Expr::RecordAccess { span, .. }
            | Expr::RecordUpdate { span, .. }
            | Expr::Parens { span, .. }
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
            | Binder::Parens { span, .. }
            | Binder::Array { span, .. }
            | Binder::Op { span, .. }
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
            | TypeExpr::Parens { span, .. }
            | TypeExpr::Wildcard { span, .. }
            | TypeExpr::TypeOp { span, .. }
            | TypeExpr::Kinded { span, .. }
            | TypeExpr::StringLiteral { span, .. }
            | TypeExpr::IntLiteral { span, .. } => *span,
        }
    }
}
