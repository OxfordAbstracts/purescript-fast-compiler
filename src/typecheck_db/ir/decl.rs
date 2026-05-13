//! Top-level IR structures: `Module`, `Decl`, and the sub-types
//! that value decls recursively embed (`GuardedExpr`, `Guard`,
//! `CaseAlternative`, `LetBinding`, `DoStatement`).
//!
//! Decl variants that only carry type syntax (`Data`, `Newtype`,
//! `TypeAlias`, `Class`, `Fixity`, `Foreign`, `ForeignData`,
//! `Derive`) re-use `cst::TypeExpr` and related CST sub-types; we
//! don't lower types in this pass.
//!
//! `Instance.members` contains `Decl::Value` entries, which *do*
//! carry expressions, so the `Decl::Instance` variant recurses on
//! [`Decl`] rather than `cst::Decl`.

use crate::cst::{self, Associativity, Comment, Constraint as CstConstraint, DataConstructor,
    ClassMember, ExportList, FunDep, ImportDecl, KindSigSource, ModuleName, QualifiedIdent,
    Spanned, TypeExpr};
use crate::names::{ClassName, ConstructorName, InstanceName, OpName, Qualified, Resolved,
    TypeName, TypeVarName, ValueName};
use crate::span::Span;

use super::binder::Binder;
use super::expr::Expr;

#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub span: Span,
    pub name: Spanned<ModuleName>,
    pub exports: Option<Spanned<ExportList>>,
    pub imports: Vec<ImportDecl>,
    pub decls: Vec<Decl>,
    pub comments: Vec<(Comment, Span)>,
    pub doc_comments: Vec<Comment>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Value {
        span: Span,
        name: Spanned<ValueName>,
        binders: Vec<Binder>,
        guarded: GuardedExpr,
        where_clause: Vec<LetBinding>,
        doc_comments: Vec<Comment>,
    },
    TypeSignature {
        span: Span,
        name: Spanned<ValueName>,
        ty: TypeExpr,
        doc_comments: Vec<Comment>,
    },
    Data {
        span: Span,
        name: Spanned<TypeName>,
        type_vars: Vec<Spanned<TypeVarName>>,
        constructors: Vec<DataConstructor>,
        kind_sig: KindSigSource,
        is_role_decl: bool,
        kind_type: Option<Box<TypeExpr>>,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
        doc_comments: Vec<Comment>,
    },
    TypeAlias {
        span: Span,
        name: Spanned<TypeName>,
        type_vars: Vec<Spanned<TypeVarName>>,
        ty: TypeExpr,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
        doc_comments: Vec<Comment>,
    },
    Newtype {
        span: Span,
        name: Spanned<TypeName>,
        type_vars: Vec<Spanned<TypeVarName>>,
        constructor: Spanned<ConstructorName>,
        ty: TypeExpr,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
        doc_comments: Vec<Comment>,
    },
    Class {
        span: Span,
        constraints: Vec<CstConstraint>,
        name: Spanned<ClassName>,
        type_vars: Vec<Spanned<TypeVarName>>,
        fundeps: Vec<FunDep>,
        members: Vec<ClassMember>,
        is_kind_sig: bool,
        kind_type: Option<Box<TypeExpr>>,
        type_var_kind_anns: Vec<Option<Box<TypeExpr>>>,
        doc_comments: Vec<Comment>,
    },
    Instance {
        span: Span,
        name: Option<Spanned<InstanceName>>,
        constraints: Vec<CstConstraint>,
        class_name: Resolved<ClassName>,
        types: Vec<TypeExpr>,
        members: Vec<Decl>,
        chain: bool,
        doc_comments: Vec<Comment>,
    },
    Fixity {
        span: Span,
        associativity: Associativity,
        precedence: u8,
        target: QualifiedIdent,
        operator: Spanned<OpName>,
        is_type: bool,
        doc_comments: Vec<Comment>,
    },
    Foreign {
        span: Span,
        name: Spanned<ValueName>,
        ty: TypeExpr,
        doc_comments: Vec<Comment>,
    },
    ForeignData {
        span: Span,
        name: Spanned<TypeName>,
        kind: TypeExpr,
        doc_comments: Vec<Comment>,
    },
    Derive {
        span: Span,
        newtype: bool,
        name: Option<Spanned<InstanceName>>,
        constraints: Vec<CstConstraint>,
        class_name: Resolved<ClassName>,
        types: Vec<TypeExpr>,
        doc_comments: Vec<Comment>,
    },
}

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

#[derive(Debug, Clone, PartialEq)]
pub enum GuardedExpr {
    Unconditional(Box<Expr>),
    Guarded(Vec<Guard>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Guard {
    pub span: Span,
    pub patterns: Vec<GuardPattern>,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum GuardPattern {
    Boolean(Box<Expr>),
    Pattern(Binder, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseAlternative {
    pub span: Span,
    pub binders: Vec<Binder>,
    pub result: GuardedExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LetBinding {
    Value {
        span: Span,
        binder: Binder,
        expr: Expr,
    },
    Signature {
        span: Span,
        name: Spanned<ValueName>,
        ty: TypeExpr,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoStatement {
    Bind {
        span: Span,
        binder: Binder,
        expr: Expr,
    },
    Let {
        span: Span,
        bindings: Vec<LetBinding>,
    },
    Discard {
        span: Span,
        expr: Expr,
    },
}

// Keep this anchored to cst so doc-generating tools link the two.
#[allow(dead_code)]
fn _touch_cst_anchor(_: &cst::Decl) {}
