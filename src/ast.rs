//! Abstract Syntax Tree (AST) for PureScript
//!
//! Similar to the CST but with:
//! - Parentheses removed (replaced by inner value)
//! - Operators desugared to function application
//! - Definition sites on key nodes

use std::collections::{HashMap, HashSet};

use crate::cst::{
    self, Associativity, ExportList, FunDep, ImportDecl, ImportList, KindSigSource, ModuleName,
    QualifiedIdent, Spanned,
};
use crate::interner::{self, intern, Symbol};
use crate::lexer::token::Ident;
use crate::span::Span;
use crate::typechecker::registry::{ModuleExports, ModuleRegistry};
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
        class_definition_site: DefinitionSite,
        types: Vec<TypeExpr>,
        members: Vec<Decl>,
        chain: bool,
    },

    /// Fixity declaration: infixl 6 add as +
    Fixity {
        span: Span,
        associativity: Associativity,
        precedence: u8,
        target: QualifiedIdent,
        target_definition_site: DefinitionSite,
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
        class_definition_site: DefinitionSite,
        types: Vec<TypeExpr>,
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

    pub fn name(&self) -> Option<Symbol> {
        match self {
            Decl::Value { name, .. }
            | Decl::TypeSignature { name, .. }
            | Decl::Data { name, .. }
            | Decl::TypeAlias { name, .. }
            | Decl::Newtype { name, .. }
            | Decl::Class { name, .. } => Some(name.value),
            Decl::Instance { name: Some(name), .. } => Some(name.value),
            _ => None,
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


// ===== CST → AST Conversion =====

pub fn convert(module: cst::Module, registry: &ModuleRegistry) -> (Module, Vec<TypeError>) {
    let mut conv = Converter::from_module(&module, registry);
    let decls = module.decls.iter().map(|d| conv.convert_decl(d)).collect();
    let ast = Module {
        span: module.span,
        name: module.name.clone(),
        exports: module.exports.clone(),
        imports: module.imports.clone(),
        decls,
    };
    (ast, conv.errors)
}

/// Convert a standalone CST expression to an AST expression.
/// Uses a minimal converter with no operator fixity info or definition sites.
/// Suitable for standalone expression inference (e.g. in tests).
pub fn convert_expr(expr: cst::Expr) -> Expr {
    let mut conv = Converter::default();
    conv.convert_expr(&expr)
}

struct Converter {
    /// Module-level values (vars, constructors, methods) → definition site
    values: HashMap<Symbol, DefinitionSite>,
    /// Module-level type constructors → definition site
    types: HashMap<Symbol, DefinitionSite>,
    /// Module-level type class names → definition site
    classes: HashMap<Symbol, DefinitionSite>,

    /// Type-level operators: op symbol → target type name
    type_operators: HashMap<Symbol, Symbol>,
    /// Type-level operator fixities
    type_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// Value-level operator fixities
    value_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// Value-level operator targets: op symbol → target name (e.g. + → add)
    value_operator_targets: HashMap<Symbol, QualifiedIdent>,
    /// Operators that alias functions (not constructors)
    function_op_aliases: HashSet<Symbol>,
    /// Definition sites for operator targets (not user-visible, only for operator desugaring).
    /// Maps target names (e.g. `add`) to their definition sites.
    operator_target_sites: HashMap<Symbol, DefinitionSite>,

    /// Local variable scopes (pushed/popped during walk)
    local_scopes: Vec<HashMap<Symbol, Span>>,

    /// Whether we're inside a Parens expression (enables post-rebalance section detection)
    in_parens: bool,

    errors: Vec<TypeError>,
}

impl Default for Converter {
    fn default() -> Self {
        Converter {
            values: HashMap::new(),
            types: HashMap::new(),
            classes: HashMap::new(),
            type_operators: HashMap::new(),
            type_fixities: HashMap::new(),
            value_fixities: HashMap::new(),
            value_operator_targets: HashMap::new(),
            function_op_aliases: HashSet::new(),
            operator_target_sites: HashMap::new(),
            local_scopes: Vec::new(),
            in_parens: false,
            errors: Vec::new(),
        }
    }
}

fn module_name_to_symbol(name: &ModuleName) -> Symbol {
    let parts: Vec<String> = name
        .parts
        .iter()
        .map(|p| interner::resolve(*p).unwrap_or_default())
        .collect();
    intern(&parts.join("."))
}

fn is_prim_module(name: &ModuleName) -> bool {
    name.parts.len() == 1 && interner::resolve(name.parts[0]).unwrap_or_default() == "Prim"
}

fn is_prim_submodule(name: &ModuleName) -> bool {
    name.parts.len() >= 2 && interner::resolve(name.parts[0]).unwrap_or_default() == "Prim"
}

fn qualified_symbol(module: Symbol, name: Symbol) -> Symbol {
    let m = interner::resolve(module).unwrap_or_default();
    let n = interner::resolve(name).unwrap_or_default();
    intern(&format!("{}.{}", m, n))
}

impl Converter {
    fn from_module(module: &cst::Module, registry: &ModuleRegistry) -> Self {
        let mut conv = Converter {
            values: HashMap::new(),
            types: HashMap::new(),
            classes: HashMap::new(),
            type_operators: HashMap::new(),
            type_fixities: HashMap::new(),
            value_fixities: HashMap::new(),
            value_operator_targets: HashMap::new(),
            function_op_aliases: HashSet::new(),
            operator_target_sites: HashMap::new(),
            local_scopes: Vec::new(),
            in_parens: false,
            errors: Vec::new(),
        };

        // 1. Register Prim types (unless module has explicit `import Prim (...)`)
        let has_explicit_prim_import = module.imports.iter().any(|imp|
            is_prim_module(&imp.module) && imp.imports.is_some() && imp.qualified.is_none()
        );
        if !has_explicit_prim_import {
            conv.register_prim();
        }

        // 2. Process imports
        conv.process_imports(module, registry);

        // 3. Register local declarations
        conv.register_local_decls(&module.decls);

        conv
    }

    fn register_prim(&mut self) {
        let prim = intern("Prim");
        let site = DefinitionSite::Imported { module: prim };
        for name in &[
            "Int", "Number", "String", "Char", "Boolean", "Array", "Record", "Function",
            "Type", "Constraint", "Symbol", "Row",
        ] {
            self.types.insert(intern(name), site.clone());
            // Also register with "Prim." qualifier for explicit Prim.Array etc. references
            self.types.insert(qualified_symbol(prim, intern(name)), site.clone());
        }
        // `(->)` is the function type constructor. When fully applied via `(->) a b`,
        // convert_type_expr normalizes to Type::fun(a, b).
        self.types.insert(intern("->"), site.clone());
        // Partial class
        self.classes.insert(intern("Partial"), site.clone());
    }

    /// Register types and classes from a Prim submodule import.
    fn register_prim_submodule(&mut self, import_decl: &cst::ImportDecl) {
        let qualifier = import_decl.qualified.as_ref().map(module_name_to_symbol);
        let mod_sym = module_name_to_symbol(&import_decl.module);
        let site = DefinitionSite::Imported { module: mod_sym };

        let sub = if import_decl.module.parts.len() >= 2 {
            interner::resolve(import_decl.module.parts[1]).unwrap_or_default()
        } else {
            return;
        };

        let (type_names, class_names): (&[&str], &[&str]) = match sub.as_str() {
            "Boolean" => (&["True", "False"], &[]),
            "Coerce" => (&[], &["Coercible"]),
            "Int" => (&[], &["Add", "Compare", "Mul", "ToString"]),
            "Ordering" => (&["Ordering", "LT", "EQ", "GT"], &[]),
            "Row" => (&[], &["Lacks", "Cons", "Nub", "Union"]),
            "RowList" => (&["RowList", "Cons", "Nil"], &["RowToList"]),
            "Symbol" => (&[], &["Append", "Compare", "Cons"]),
            "TypeError" => (&["Doc", "Beside", "Above", "Text", "Quote", "QuoteLabel"], &["Fail", "Warn"]),
            _ => (&[], &[]),
        };

        // Filter based on import list
        let allowed: Option<HashSet<Symbol>> = match &import_decl.imports {
            None => None, // import all
            Some(ImportList::Explicit(items)) => {
                Some(items.iter().map(|i| match i {
                    cst::Import::Value(n) | cst::Import::Type(n, _)
                    | cst::Import::TypeOp(n) | cst::Import::Class(n) => *n,
                }).collect())
            }
            Some(ImportList::Hiding(items)) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| match i {
                    cst::Import::Value(n) | cst::Import::Type(n, _)
                    | cst::Import::TypeOp(n) | cst::Import::Class(n) => *n,
                }).collect();
                // Build allowed = all names minus hidden
                let all_names: HashSet<Symbol> = type_names.iter().chain(class_names.iter())
                    .map(|n| intern(n))
                    .collect();
                Some(all_names.difference(&hidden).cloned().collect())
            }
        };

        for name in type_names {
            let sym = intern(name);
            if allowed.as_ref().map_or(true, |s| s.contains(&sym)) {
                let key = Self::maybe_qualify(sym, qualifier);
                self.types.insert(key, site.clone());
            }
        }
        for name in class_names {
            let sym = intern(name);
            if allowed.as_ref().map_or(true, |s| s.contains(&sym)) {
                let key = Self::maybe_qualify(sym, qualifier);
                self.classes.insert(key, site.clone());
            }
        }
    }

    fn process_imports(&mut self, module: &cst::Module, registry: &ModuleRegistry) {
        for import_decl in &module.imports {
            let module_exports = if is_prim_module(&import_decl.module) {
                let prim_site = DefinitionSite::Imported { module: intern("Prim") };
                let prim_sym = intern("Prim");
                // Register qualifier if present (e.g. import Prim as P).
                if let Some(ref qual) = import_decl.qualified {
                    let q = module_name_to_symbol(qual);
                    for name in &[
                        "Int", "Number", "String", "Char", "Boolean", "Array", "Record",
                        "Function", "Type", "Constraint", "Symbol", "Row",
                    ] {
                        self.types.insert(qualified_symbol(q, intern(name)), prim_site.clone());
                    }
                    self.classes.insert(qualified_symbol(q, intern("Partial")), prim_site.clone());
                }
                // If explicit `import Prim (X, Y)`, register only the listed items.
                // register_prim() was skipped for this case, so we must add them here.
                if let Some(ImportList::Explicit(items)) = &import_decl.imports {
                    for item in items {
                        match item {
                            cst::Import::Type(name, _) => {
                                let sym = *name;
                                self.types.insert(sym, prim_site.clone());
                                self.types.insert(qualified_symbol(prim_sym, sym), prim_site.clone());
                            }
                            cst::Import::Class(name) => {
                                let sym = *name;
                                self.classes.insert(sym, prim_site.clone());
                                self.classes.insert(qualified_symbol(prim_sym, sym), prim_site.clone());
                            }
                            cst::Import::Value(name) => {
                                self.values.insert(*name, prim_site.clone());
                            }
                            cst::Import::TypeOp(name) => {
                                self.types.insert(*name, prim_site.clone());
                            }
                        }
                    }
                    // Always register (->) even for explicit imports
                    self.types.insert(intern("->"), prim_site.clone());
                } else if let Some(ImportList::Hiding(items)) = &import_decl.imports {
                    // `import Prim hiding (X, Y)` — register all Prim types/classes
                    // except the hidden ones.
                    let hidden: HashSet<Symbol> = items.iter().map(|i| match i {
                        cst::Import::Value(n) | cst::Import::Type(n, _)
                        | cst::Import::TypeOp(n) | cst::Import::Class(n) => *n,
                    }).collect();
                    for name in &[
                        "Int", "Number", "String", "Char", "Boolean", "Array", "Record",
                        "Function", "Type", "Constraint", "Symbol", "Row",
                    ] {
                        let sym = intern(name);
                        if !hidden.contains(&sym) {
                            self.types.insert(sym, prim_site.clone());
                            self.types.insert(qualified_symbol(prim_sym, sym), prim_site.clone());
                        }
                    }
                    if !hidden.contains(&intern("Partial")) {
                        self.classes.insert(intern("Partial"), prim_site.clone());
                    }
                    self.types.insert(intern("->"), prim_site.clone());
                }
                continue;
            } else if is_prim_submodule(&import_decl.module) {
                // Register Prim submodule types/classes so the AST converter knows about them.
                self.register_prim_submodule(import_decl);
                continue;
            } else {
                match registry.lookup(&import_decl.module.parts) {
                    Some(exports) => exports,
                    None => {
                        self.errors.push(TypeError::ModuleNotFound {
                            span: import_decl.span,
                            name: module_name_to_symbol(&import_decl.module),
                        });
                        continue;
                    }
                }
            };

            let mod_sym = module_name_to_symbol(&import_decl.module);
            let qualifier = import_decl.qualified.as_ref().map(module_name_to_symbol);
            let site = DefinitionSite::Imported { module: mod_sym };

            match &import_decl.imports {
                None => {
                    self.import_all(module_exports, qualifier, &site);
                }
                Some(ImportList::Explicit(items)) => {
                    for item in items {
                        self.import_item(item, module_exports, qualifier, &site);
                    }
                }
                Some(ImportList::Hiding(items)) => {
                    let hidden: HashSet<Symbol> = items
                        .iter()
                        .map(|i| match i {
                            cst::Import::Value(n)
                            | cst::Import::Type(n, _)
                            | cst::Import::TypeOp(n)
                            | cst::Import::Class(n) => *n,
                        })
                        .collect();
                    self.import_all_except(module_exports, &hidden, qualifier, &site);
                }
            }

            // Import fixities, type operators, and operator targets, respecting import filter.
            // Collect which value operators and type operators are allowed by this import.
            let (allowed_value_ops, allowed_type_ops): (Option<HashSet<Symbol>>, Option<HashSet<Symbol>>) = match &import_decl.imports {
                None => (None, None), // open import: all allowed
                Some(ImportList::Explicit(items)) => {
                    let mut vops = HashSet::new();
                    let mut tops = HashSet::new();
                    for item in items {
                        match item {
                            cst::Import::Value(n) => { vops.insert(*n); }
                            cst::Import::TypeOp(n) => { tops.insert(*n); }
                            _ => {}
                        }
                    }
                    (Some(vops), Some(tops))
                }
                Some(ImportList::Hiding(items)) => {
                    // Start with all, remove hidden
                    let hidden_vops: HashSet<Symbol> = items.iter().filter_map(|i| match i {
                        cst::Import::Value(n) => Some(*n),
                        _ => None,
                    }).collect();
                    let hidden_tops: HashSet<Symbol> = items.iter().filter_map(|i| match i {
                        cst::Import::TypeOp(n) => Some(*n),
                        _ => None,
                    }).collect();
                    let vops: HashSet<Symbol> = module_exports.value_fixities.keys()
                        .filter(|k| !hidden_vops.contains(&k.name))
                        .map(|k| k.name)
                        .collect();
                    let tops: HashSet<Symbol> = module_exports.type_operators.keys()
                        .filter(|k| !hidden_tops.contains(&k.name))
                        .map(|k| k.name)
                        .collect();
                    (Some(vops), Some(tops))
                }
            };

            for (op, fixity) in &module_exports.value_fixities {
                if allowed_value_ops.as_ref().map_or(true, |s| s.contains(&op.name)) {
                    let key = Self::maybe_qualify(op.name, qualifier);
                    self.value_fixities.insert(key, *fixity);
                }
            }
            for (op, target) in &module_exports.type_operators {
                if allowed_type_ops.as_ref().map_or(true, |s| s.contains(&op.name)) {
                    let key = Self::maybe_qualify(op.name, qualifier);
                    self.type_operators.insert(key, target.name);
                    // Also register the target type so that type operator desugaring
                    // (e.g. `a + r` → `App(App(RowApply, a), r)`) can resolve the
                    // target type constructor.
                    if !self.types.contains_key(&target.name) {
                        let target_origin = Self::type_origin_site(module_exports, target.name, &site);
                        self.types.insert(target.name, target_origin);
                    }
                }
            }
            // Only import function_op_aliases when operators are available unqualified.
            // `import M as Q` (qualifier, no explicit list) only provides qualified access,
            // so operators like `:` from Data.Array shouldn't pollute the unqualified scope.
            let has_unqualified_access = qualifier.is_none() || import_decl.imports.is_some();
            if has_unqualified_access {
                for op in &module_exports.function_op_aliases {
                    if allowed_value_ops.as_ref().map_or(true, |s| s.contains(&op.name)) {
                        self.function_op_aliases.insert(op.name);
                    }
                }
            }
            for (op, target) in &module_exports.value_operator_targets {
                if allowed_value_ops.as_ref().map_or(true, |s| s.contains(&op.name)) {
                    self.value_operator_targets.insert(op.name, *target);
                    // Record the definition site for the operator's target so that
                    // operator desugaring (e.g. `1 + 2` → `add 1 2`) can produce
                    // a valid definition_site without requiring `add` to be in `values`.
                    let target_origin = Self::value_origin_site(module_exports, target.name, &site);
                    self.operator_target_sites.insert(target.name, target_origin);
                }
            }
        }
    }

    /// Look up the original defining module for a value name, falling back to the
    /// importing module's site if no origin is recorded.
    fn value_origin_site(exports: &ModuleExports, name: Symbol, fallback: &DefinitionSite) -> DefinitionSite {
        exports.value_origins.get(&name)
            .map(|&origin_mod| DefinitionSite::Imported { module: origin_mod })
            .unwrap_or_else(|| fallback.clone())
    }

    fn type_origin_site(exports: &ModuleExports, name: Symbol, fallback: &DefinitionSite) -> DefinitionSite {
        exports.type_origins.get(&name)
            .map(|&origin_mod| DefinitionSite::Imported { module: origin_mod })
            .unwrap_or_else(|| fallback.clone())
    }

    fn class_origin_site(exports: &ModuleExports, name: Symbol, fallback: &DefinitionSite) -> DefinitionSite {
        exports.class_origins.get(&name)
            .map(|&origin_mod| DefinitionSite::Imported { module: origin_mod })
            .unwrap_or_else(|| fallback.clone())
    }

    fn import_all(
        &mut self,
        exports: &ModuleExports,
        qualifier: Option<Symbol>,
        site: &DefinitionSite,
    ) {
        for name in exports.values.keys() {
            let key = Self::maybe_qualify(name.name, qualifier);
            let origin = Self::value_origin_site(exports, name.name, site);
            self.values.insert(key, origin);
        }
        for name in exports.data_constructors.keys() {
            let key = Self::maybe_qualify(name.name, qualifier);
            let origin = Self::type_origin_site(exports, name.name, site);
            self.types.insert(key, origin);
        }
        // Also import type aliases as known types
        for name in exports.type_aliases.keys() {
            let key = Self::maybe_qualify(name.name, qualifier);
            let origin = Self::type_origin_site(exports, name.name, site);
            self.types.insert(key, origin);
        }
        for name in exports.class_param_counts.keys() {
            let key = Self::maybe_qualify(name.name, qualifier);
            let origin = Self::class_origin_site(exports, name.name, site);
            self.classes.insert(key, origin);
        }
    }

    fn import_all_except(
        &mut self,
        exports: &ModuleExports,
        hidden: &HashSet<Symbol>,
        qualifier: Option<Symbol>,
        site: &DefinitionSite,
    ) {
        for name in exports.values.keys() {
            if !hidden.contains(&name.name) {
                let key = Self::maybe_qualify(name.name, qualifier);
                let origin = Self::value_origin_site(exports, name.name, site);
                self.values.insert(key, origin);
            }
        }
        for name in exports.data_constructors.keys() {
            if !hidden.contains(&name.name) {
                let key = Self::maybe_qualify(name.name, qualifier);
                let origin = Self::type_origin_site(exports, name.name, site);
                self.types.insert(key, origin);
            }
        }
        // Also import type aliases as known types
        for name in exports.type_aliases.keys() {
            if !hidden.contains(&name.name) {
                let key = Self::maybe_qualify(name.name, qualifier);
                let origin = Self::type_origin_site(exports, name.name, site);
                self.types.insert(key, origin);
            }
        }
        for name in exports.class_param_counts.keys() {
            if !hidden.contains(&name.name) {
                let key = Self::maybe_qualify(name.name, qualifier);
                let origin = Self::class_origin_site(exports, name.name, site);
                self.classes.insert(key, origin);
            }
        }
    }

    fn import_item(
        &mut self,
        item: &cst::Import,
        exports: &ModuleExports,
        qualifier: Option<Symbol>,
        site: &DefinitionSite,
    ) {
        match item {
            cst::Import::Value(name) => {
                let key = Self::maybe_qualify(*name, qualifier);
                let origin = Self::value_origin_site(exports, *name, site);
                self.values.insert(key, origin);
            }
            cst::Import::Type(name, members) => {
                let key = Self::maybe_qualify(*name, qualifier);
                let origin = Self::type_origin_site(exports, *name, site);
                self.types.insert(key, origin);
                // Import constructors if (..) or explicit list
                if let Some(members) = members {
                    let qi = QualifiedIdent { module: None, name: *name };
                    if let Some(ctors) = exports.data_constructors.get(&qi) {
                        match members {
                            cst::DataMembers::All => {
                                for ctor in ctors {
                                    let k = Self::maybe_qualify(ctor.name, qualifier);
                                    let ctor_origin = Self::value_origin_site(exports, ctor.name, site);
                                    self.values.insert(k, ctor_origin);
                                }
                            }
                            cst::DataMembers::Explicit(names) => {
                                for n in names {
                                    let k = Self::maybe_qualify(*n, qualifier);
                                    let ctor_origin = Self::value_origin_site(exports, *n, site);
                                    self.values.insert(k, ctor_origin);
                                }
                            }
                        }
                    }
                }
            }
            cst::Import::TypeOp(name) => {
                let key = Self::maybe_qualify(*name, qualifier);
                let origin = Self::value_origin_site(exports, *name, site);
                self.values.insert(key, origin);
            }
            cst::Import::Class(name) => {
                let key = Self::maybe_qualify(*name, qualifier);
                let origin = Self::class_origin_site(exports, *name, site);
                self.classes.insert(key, origin);
                // Import class methods
                for (method_name, _) in &exports.class_methods {
                    // Check if this method belongs to the imported class
                    let qi = QualifiedIdent { module: None, name: *name };
                    if exports.class_methods.get(method_name).map(|(cn, _)| cn) == Some(&qi) {
                        let k = Self::maybe_qualify(method_name.name, qualifier);
                        let method_origin = Self::value_origin_site(exports, method_name.name, site);
                        self.values.insert(k, method_origin);
                    }
                }
            }
        }
    }

    fn register_local_decls(&mut self, decls: &[cst::Decl]) {
        // Pass 1: Register all values, types, and classes (so targets exist before fixities)
        for decl in decls {
            match decl {
                cst::Decl::Value { span, name, .. } => {
                    self.values
                        .insert(name.value, DefinitionSite::Local(*span));
                }
                cst::Decl::Data {
                    span,
                    name,
                    constructors,
                    ..
                } => {
                    self.types
                        .insert(name.value, DefinitionSite::Local(*span));
                    for ctor in constructors {
                        self.values
                            .insert(ctor.name.value, DefinitionSite::Local(ctor.span));
                    }
                }
                cst::Decl::Newtype {
                    span,
                    name,
                    constructor,
                    ..
                } => {
                    self.types
                        .insert(name.value, DefinitionSite::Local(*span));
                    self.values
                        .insert(constructor.value, DefinitionSite::Local(*span));
                }
                cst::Decl::Class {
                    span,
                    name,
                    members,
                    ..
                } => {
                    self.classes
                        .insert(name.value, DefinitionSite::Local(*span));
                    for member in members {
                        self.values
                            .insert(member.name.value, DefinitionSite::Local(member.span));
                    }
                }
                cst::Decl::TypeAlias { span, name, .. } => {
                    self.types
                        .insert(name.value, DefinitionSite::Local(*span));
                }
                cst::Decl::Foreign { span, name, .. } => {
                    self.values
                        .insert(name.value, DefinitionSite::Local(*span));
                }
                cst::Decl::ForeignData { span, name, .. } => {
                    self.types
                        .insert(name.value, DefinitionSite::Local(*span));
                }
                _ => {}
            }
        }

        // Pass 2: Process fixity declarations (targets are now registered from pass 1)
        for decl in decls {
            if let cst::Decl::Fixity {
                target,
                operator,
                is_type,
                associativity,
                precedence,
                ..
            } = decl
            {
                if *is_type {
                    self.type_operators.insert(operator.value, target.name);
                    self.type_fixities.insert(operator.value, (*associativity, *precedence));
                } else {
                    self.value_fixities
                        .insert(operator.value, (*associativity, *precedence));
                    // Register operator → target mapping
                    self.value_operator_targets.insert(operator.value, *target);
                    // Operator inherits the target's definition site
                    if let Some(target_site) = self.values.get(&target.name).cloned() {
                        self.values.insert(operator.value, target_site);
                    }
                    // Check if target is a function (not a constructor)
                    let target_str =
                        interner::resolve(target.name).unwrap_or_default();
                    if target_str
                        .chars()
                        .next()
                        .map_or(false, |c| c.is_lowercase() || c == '_')
                    {
                        self.function_op_aliases.insert(QualifiedIdent {
                            module: None,
                            name: operator.value,
                        }.name);
                    }
                }
            }
        }
    }

    fn maybe_qualify(name: Symbol, qualifier: Option<Symbol>) -> Symbol {
        match qualifier {
            Some(q) => qualified_symbol(q, name),
            None => name,
        }
    }

    // --- Underscore section detection and desugaring ---

    /// Check if a CST expression is an `_` (wildcard used for anonymous functions).
    fn is_wildcard(expr: &cst::Expr) -> bool {
        matches!(expr, cst::Expr::Wildcard { .. })
    }

    /// Check if a CST expression is a valid underscore section (single-operator with `_` hole).
    /// Only valid when `_` is a direct operand of a single Op (no nested Op chain)
    /// or a direct argument of App. Multi-operator chains are handled post-rebalancing
    /// in convert_op_chain when in_parens is set.
    fn has_wildcard(expr: &cst::Expr) -> bool {
        match expr {
            cst::Expr::Op { left, right, .. } => {
                let has_hole = Self::is_wildcard(left) || Self::is_wildcard(right);
                // Reject if the non-hole operand is a nested Op (multi-operator chain)
                let has_nested_op = matches!(left.as_ref(), cst::Expr::Op { .. })
                    || matches!(right.as_ref(), cst::Expr::Op { .. });
                has_hole && !has_nested_op
            }
            cst::Expr::App { func, arg, .. } => {
                Self::is_wildcard(func) || Self::is_wildcard(arg)
            }
            _ => false,
        }
    }

    /// Desugar an underscore section: `(_ * 1000.0)` → `\$_arg -> mul $_arg 1000.0`.
    /// Replaces `_` holes with a fresh variable and wraps in a Lambda.
    fn desugar_wildcard_section(&mut self, span: Span, expr: &cst::Expr) -> Expr {
        let param_name = intern("$_arg");

        // Replace all `_` holes in the CST with a variable reference
        let replaced = self.replace_underscore_holes(expr, param_name);

        // Push a local scope with the param so resolve_value finds it during body conversion
        let mut scope = HashMap::new();
        scope.insert(param_name, span);
        self.local_scopes.push(scope);
        let body = self.convert_expr(&replaced);
        self.local_scopes.pop();

        Expr::Lambda {
            span,
            binders: vec![Binder::Var {
                span,
                name: cst::Spanned { span, value: param_name },
            }],
            body: Box::new(body),
        }
    }

    /// Replace `_` holes in a CST expression with a variable reference.
    fn replace_underscore_holes(&self, expr: &cst::Expr, replacement: Symbol) -> cst::Expr {
        if Self::is_wildcard(expr) {
            return cst::Expr::Var {
                span: expr.span(),
                name: QualifiedIdent { module: None, name: replacement },
            };
        }
        match expr {
            cst::Expr::Op { span, left, op, right } => cst::Expr::Op {
                span: *span,
                left: Box::new(self.replace_underscore_holes(left, replacement)),
                op: op.clone(),
                right: Box::new(self.replace_underscore_holes(right, replacement)),
            },
            cst::Expr::App { span, func, arg } => cst::Expr::App {
                span: *span,
                func: Box::new(self.replace_underscore_holes(func, replacement)),
                arg: Box::new(self.replace_underscore_holes(arg, replacement)),
            },
            other => other.clone(),
        }
    }

    // --- Definition site resolution ---

    fn resolve_value(&mut self, name: &QualifiedIdent, span: Span) -> DefinitionSite {
        // Check local scopes first (innermost first)
        if name.module.is_none() {
            for scope in self.local_scopes.iter().rev() {
                if let Some(&local_span) = scope.get(&name.name) {
                    return DefinitionSite::Local(local_span);
                }
            }
        }
        // Check module scope
        let key = match name.module {
            Some(m) => qualified_symbol(m, name.name),
            None => name.name,
        };
        match self.values.get(&key).cloned() {
            Some(site) => site,
            None => {
                self.errors.push(TypeError::UndefinedVariable {
                    span,
                    name: key,
                });
                DefinitionSite::Local(span)
            }
        }
    }

    /// Resolve the definition site of an operator's target (e.g. `add` for operator `+`).
    /// Checks `operator_target_sites` first, then falls back to `values` (for locally
    /// defined operators whose targets are already in scope).
    fn resolve_operator_target(&self, target_name: Symbol, span: Span) -> DefinitionSite {
        if let Some(site) = self.operator_target_sites.get(&target_name) {
            return site.clone();
        }
        // Fall back to values (e.g. for locally defined operators)
        if let Some(site) = self.values.get(&target_name) {
            return site.clone();
        }
        DefinitionSite::Local(span)
    }

    fn resolve_type(&mut self, name: &QualifiedIdent, span: Span) -> DefinitionSite {
        let key = match name.module {
            Some(m) => qualified_symbol(m, name.name),
            None => name.name,
        };
        match self.types.get(&key).cloned() {
            Some(site) => site,
            None => {
                // Also check type operators — `(~>)` used as a type constructor is valid
                // if `~>` is a known type operator.
                if self.type_operators.contains_key(&key) {
                    return DefinitionSite::Local(span);
                }
                self.errors.push(TypeError::UnknownName {
                    span,
                    name: key,
                });
                DefinitionSite::Local(span)
            }
        }
    }

    fn resolve_class(&mut self, name: &QualifiedIdent, span: Span) -> DefinitionSite {
        let key = match name.module {
            Some(m) => qualified_symbol(m, name.name),
            None => name.name,
        };
        match self.classes.get(&key).cloned() {
            Some(site) => site,
            None => {
                // PureScript reports unknown class names as UnknownName during name
                // resolution (the name isn't in scope). UnknownClass is reserved for
                // constraint-solver failures where a class can't be found.
                self.errors.push(TypeError::UnknownName {
                    span,
                    name: key,
                });
                DefinitionSite::Local(span)
            }
        }
    }

    /// Like resolve_class, but doesn't emit an error if the class isn't found.
    /// Used for derive declarations where the class may be handled specially by the typechecker.
    fn resolve_class_lenient(&self, name: &QualifiedIdent, span: Span) -> DefinitionSite {
        let key = match name.module {
            Some(m) => qualified_symbol(m, name.name),
            None => name.name,
        };
        self.classes.get(&key).cloned().unwrap_or(DefinitionSite::Local(span))
    }

    fn push_scope(&mut self) {
        self.local_scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn add_local(&mut self, name: Symbol, span: Span) {
        if let Some(scope) = self.local_scopes.last_mut() {
            scope.insert(name, span);
        }
    }

    /// Collect all variable names bound by a CST binder (for scope registration)
    fn collect_binder_names(binder: &cst::Binder, names: &mut Vec<(Symbol, Span)>) {
        match binder {
            cst::Binder::Var { name, .. } => {
                names.push((name.value, name.span));
            }
            cst::Binder::Constructor { args, .. } => {
                for arg in args {
                    Self::collect_binder_names(arg, names);
                }
            }
            cst::Binder::As { name, binder, .. } => {
                names.push((name.value, name.span));
                Self::collect_binder_names(binder, names);
            }
            cst::Binder::Parens { binder, .. } => {
                Self::collect_binder_names(binder, names);
            }
            cst::Binder::Record { fields, .. } => {
                for field in fields {
                    if let Some(b) = &field.binder {
                        Self::collect_binder_names(b, names);
                    } else {
                        // Pun: { x } binds x
                        names.push((field.label.value, field.label.span));
                    }
                }
            }
            cst::Binder::Array { elements, .. } => {
                for elem in elements {
                    Self::collect_binder_names(elem, names);
                }
            }
            cst::Binder::Op { left, right, .. } => {
                Self::collect_binder_names(left, names);
                Self::collect_binder_names(right, names);
            }
            cst::Binder::Typed { binder, .. } => {
                Self::collect_binder_names(binder, names);
            }
            cst::Binder::Wildcard { .. } | cst::Binder::Literal { .. } => {}
        }
    }

    // --- Expression conversion ---

    fn convert_expr(&mut self, expr: &cst::Expr) -> Expr {
        match expr {
            cst::Expr::Var { span, name } => Expr::Var {
                span: *span,
                name: *name,
                definition_site: self.resolve_value(name, *span),
            },
            cst::Expr::Constructor { span, name } => Expr::Constructor {
                span: *span,
                name: *name,
                definition_site: self.resolve_value(name, *span),
            },
            cst::Expr::Literal { span, lit } => Expr::Literal {
                span: *span,
                lit: self.convert_literal(lit),
            },
            cst::Expr::App { span, func, arg } => Expr::App {
                span: *span,
                func: Box::new(self.convert_expr(func)),
                arg: Box::new(self.convert_expr(arg)),
            },
            cst::Expr::VisibleTypeApp { span, func, ty } => Expr::VisibleTypeApp {
                span: *span,
                func: Box::new(self.convert_expr(func)),
                ty: self.convert_type_expr(ty),
            },
            cst::Expr::Lambda {
                span,
                binders,
                body,
            } => {
                self.push_scope();
                for b in binders {
                    let mut names = Vec::new();
                    Self::collect_binder_names(b, &mut names);
                    for (n, s) in names {
                        self.add_local(n, s);
                    }
                }
                let ast_binders: Vec<Binder> =
                    binders.iter().map(|b| self.convert_binder(b)).collect();
                let ast_body = self.convert_expr(body);
                self.pop_scope();
                Expr::Lambda {
                    span: *span,
                    binders: ast_binders,
                    body: Box::new(ast_body),
                }
            }
            cst::Expr::Op {
                span,
                left,
                op,
                right,
            } => self.convert_op_chain(*span, left, op, right),
            cst::Expr::OpParens { span, op } => {
                // Use the operator name (not target), same as build_op_app
                if !self.value_operator_targets.contains_key(&op.value.name) {
                    self.errors.push(TypeError::UndefinedVariable {
                        span: *span,
                        name: op.value.name,
                    });
                }
                let def_site = self.resolve_operator_target(op.value.name, *span);
                if self.function_op_aliases.contains(&op.value.name) {
                    Expr::Var {
                        span: *span,
                        name: op.value,
                        definition_site: def_site,
                    }
                } else {
                    Expr::Constructor {
                        span: *span,
                        name: op.value,
                        definition_site: def_site,
                    }
                }
            }
            cst::Expr::If {
                span,
                cond,
                then_expr,
                else_expr,
            } => Expr::If {
                span: *span,
                cond: Box::new(self.convert_expr(cond)),
                then_expr: Box::new(self.convert_expr(then_expr)),
                else_expr: Box::new(self.convert_expr(else_expr)),
            },
            cst::Expr::Case { span, exprs, alts } => {
                let ast_exprs: Vec<Expr> = exprs.iter().map(|e| self.convert_expr(e)).collect();
                let ast_alts: Vec<CaseAlternative> = alts
                    .iter()
                    .map(|alt| {
                        self.push_scope();
                        for b in &alt.binders {
                            let mut names = Vec::new();
                            Self::collect_binder_names(b, &mut names);
                            for (n, s) in names {
                                self.add_local(n, s);
                            }
                        }
                        let binders =
                            alt.binders.iter().map(|b| self.convert_binder(b)).collect();
                        let result = self.convert_guarded(&alt.result);
                        self.pop_scope();
                        CaseAlternative {
                            span: alt.span,
                            binders,
                            result,
                        }
                    })
                    .collect();
                Expr::Case {
                    span: *span,
                    exprs: ast_exprs,
                    alts: ast_alts,
                }
            }
            cst::Expr::Let {
                span,
                bindings,
                body,
            } => {
                self.push_scope();
                // Register let binding names first (for mutual recursion)
                for lb in bindings {
                    if let cst::LetBinding::Value { binder, .. } = lb {
                        let mut names = Vec::new();
                        Self::collect_binder_names(binder, &mut names);
                        for (n, s) in names {
                            self.add_local(n, s);
                        }
                    }
                }
                let ast_bindings: Vec<LetBinding> =
                    bindings.iter().map(|lb| self.convert_let_binding(lb)).collect();
                let ast_body = self.convert_expr(body);
                self.pop_scope();
                Expr::Let {
                    span: *span,
                    bindings: ast_bindings,
                    body: Box::new(ast_body),
                }
            }
            cst::Expr::Do {
                span,
                module,
                statements,
            } => {
                self.push_scope();
                let ast_stmts: Vec<DoStatement> = statements
                    .iter()
                    .map(|s| self.convert_do_statement(s))
                    .collect();
                self.pop_scope();
                Expr::Do {
                    span: *span,
                    module: *module,
                    statements: ast_stmts,
                }
            }
            cst::Expr::Ado {
                span,
                module,
                statements,
                result,
            } => {
                self.push_scope();
                let ast_stmts: Vec<DoStatement> = statements
                    .iter()
                    .map(|s| self.convert_do_statement(s))
                    .collect();
                let ast_result = self.convert_expr(result);
                self.pop_scope();
                Expr::Ado {
                    span: *span,
                    module: *module,
                    statements: ast_stmts,
                    result: Box::new(ast_result),
                }
            }
            cst::Expr::Record { span, fields } => Expr::Record {
                span: *span,
                fields: fields.iter().map(|f| self.convert_record_field(f)).collect(),
            },
            cst::Expr::RecordAccess { span, expr, field } => Expr::RecordAccess {
                span: *span,
                expr: Box::new(self.convert_expr(expr)),
                field: field.clone(),
            },
            cst::Expr::RecordUpdate {
                span,
                expr,
                updates,
            } => Expr::RecordUpdate {
                span: *span,
                expr: Box::new(self.convert_expr(expr)),
                updates: updates
                    .iter()
                    .map(|u| RecordUpdate {
                        span: u.span,
                        label: u.label.clone(),
                        value: self.convert_expr(&u.value),
                    })
                    .collect(),
            },
            cst::Expr::Parens { span, expr } => {
                // Detect underscore sections: (_ * 1000.0) → \$_arg -> mul $_arg 1000.0
                if Self::has_wildcard(expr) {
                    self.desugar_wildcard_section(*span, expr)
                } else {
                    // Set in_parens so convert_op_chain can handle post-rebalance sections
                    // for multi-operator chains like (_ /\ x /\ y)
                    let prev = self.in_parens;
                    self.in_parens = true;
                    let result = self.convert_expr(expr);
                    self.in_parens = prev;
                    result
                }
            }
            cst::Expr::TypeAnnotation { span, expr, ty } => Expr::TypeAnnotation {
                span: *span,
                expr: Box::new(self.convert_expr(expr)),
                ty: self.convert_type_expr(ty),
            },
            cst::Expr::Hole { span, name } => Expr::Hole {
                span: *span,
                name: *name,
            },
            cst::Expr::Wildcard { span } => Expr::Hole {
                span: *span,
                name: intern("_"),
            },
            cst::Expr::Array { span, elements } => Expr::Array {
                span: *span,
                elements: elements.iter().map(|e| self.convert_expr(e)).collect(),
            },
            cst::Expr::Negate { span, expr } => Expr::Negate {
                span: *span,
                expr: Box::new(self.convert_expr(expr)),
            },
            cst::Expr::AsPattern {
                span,
                name,
                pattern,
            } => Expr::AsPattern {
                span: *span,
                name: Box::new(self.convert_expr(name)),
                pattern: Box::new(self.convert_expr(pattern)),
            },
        }
    }

    // --- Operator chain flattening and rebalancing ---

    fn convert_op_chain(
        &mut self,
        span: Span,
        left: &cst::Expr,
        op: &Spanned<QualifiedIdent>,
        right: &cst::Expr,
    ) -> Expr {
        // Flatten right-associative chain
        let mut operands: Vec<&cst::Expr> = vec![left];
        let mut operators: Vec<&Spanned<QualifiedIdent>> = vec![op];
        let mut current = right;
        while let cst::Expr::Op {
            left: rl,
            op: rop,
            right: rr,
            ..
        } = current
        {
            operands.push(rl.as_ref());
            operators.push(rop);
            current = rr.as_ref();
        }
        // If the rightmost expression is a TypeAnnotation, extract it.
        // In PureScript, `::` has the lowest precedence, so `a op b :: T` means
        // `(a op b) :: T`. But our grammar parses `::` within OperatorExpr, so
        // `right` of `a op b :: T` becomes `TypeAnnotation { expr: b, ty: T }`.
        // We extract the annotation and apply it to the whole chain result.
        let mut trailing_annotation: Option<&cst::TypeExpr> = None;
        if let cst::Expr::TypeAnnotation { expr: inner, ty, .. } = current {
            trailing_annotation = Some(ty);
            operands.push(inner.as_ref());
        } else {
            operands.push(current);
        }

        // Check for `_` holes in operator chains.
        // When in_parens is true, defer the error — the section may be valid after rebalancing.
        let has_wildcard_operand = operands.iter().any(|o| Self::is_wildcard(o));
        if has_wildcard_operand && !self.in_parens {
            for operand in &operands {
                if Self::is_wildcard(operand) {
                    self.errors.push(TypeError::IncorrectAnonymousArgument {
                        span: operand.span(),
                    });
                }
            }
        }

        // Convert all operands
        let mut ast_operands: Vec<Expr> = operands
            .iter()
            .map(|e| self.convert_expr(e))
            .collect();

        // Single operator: fast path
        if operators.len() == 1 {
            let right = ast_operands.pop().unwrap();
            let left = ast_operands.pop().unwrap();
            let result = self.build_op_app(span, &operators[0], left, right);
            // Single-op sections inside parens are handled by has_wildcard/desugar_wildcard_section.
            // If we got here with a wildcard and in_parens, it means the wildcard was in a
            // position that has_wildcard didn't catch (shouldn't happen for single-op).
            if let Some(ann_ty) = trailing_annotation {
                let ty = self.convert_type_expr(ann_ty);
                return Expr::TypeAnnotation { span, expr: Box::new(result), ty };
            }
            return result;
        }

        // Shunting-yard for multiple operators
        let mut output: Vec<Expr> = Vec::new();
        let mut op_stack: Vec<usize> = Vec::new();

        output.push(ast_operands.remove(0));

        for i in 0..operators.len() {
            let (assoc_i, prec_i) = self.get_fixity(operators[i].value.name);

            while let Some(&top_idx) = op_stack.last() {
                let (assoc_top, prec_top) = self.get_fixity(operators[top_idx].value.name);
                // Check for operator conflicts at the same precedence
                if prec_top == prec_i && assoc_top != assoc_i {
                    // Different associativity at the same precedence → mixed associativity error
                    self.errors.push(TypeError::MixedAssociativityError {
                        span: operators[i].span,
                    });
                } else if prec_top == prec_i
                    && assoc_top == Associativity::None
                    && assoc_i == Associativity::None
                {
                    // Both non-associative at same precedence → non-associative chaining error
                    self.errors.push(TypeError::NonAssociativeError {
                        span: operators[i].span,
                        op: operators[i].value.name,
                    });
                }
                let should_pop = prec_top > prec_i
                    || (prec_top == prec_i && assoc_i == Associativity::Left);
                if should_pop {
                    op_stack.pop();
                    let right = output.pop().unwrap();
                    let left = output.pop().unwrap();
                    output.push(self.build_op_app(span, operators[top_idx], left, right));
                } else {
                    break;
                }
            }

            op_stack.push(i);
            output.push(ast_operands.remove(0));
        }

        // Pop remaining operators
        while let Some(top_idx) = op_stack.pop() {
            let right = output.pop().unwrap();
            let left = output.pop().unwrap();
            output.push(self.build_op_app(span, operators[top_idx], left, right));
        }

        let result = output.pop().unwrap();

        // Post-rebalance section detection: after shunting-yard, check if `_` is a direct
        // operand of the top-level operator. This matches PureScript's removeBinaryNoParens.
        // After build_op_app, the structure is App(App(op, left), right).
        if !has_wildcard_operand || !self.in_parens {
            if let Some(ann_ty) = trailing_annotation {
                let ty = self.convert_type_expr(ann_ty);
                return Expr::TypeAnnotation { span, expr: Box::new(result), ty };
            }
            return result;
        }

        let wildcard_sym = interner::intern("_");
        // Destructure App(App(op, left), right) to check for holes
        if let Expr::App { span: outer_span, func: outer_func, arg: right_arg } = result {
            if let Expr::App { span: inner_span, func: op_func, arg: left_arg } = *outer_func {
                let left_is_hole = matches!(&*left_arg, Expr::Hole { name, .. } if *name == wildcard_sym);
                let right_is_hole = matches!(&*right_arg, Expr::Hole { name, .. } if *name == wildcard_sym);
                if left_is_hole || right_is_hole {
                    // Valid section after rebalancing — desugar to lambda
                    let param_name = interner::intern("$_arg");
                    let param_var = Box::new(Expr::Var {
                        span,
                        name: QualifiedIdent { module: None, name: param_name },
                        definition_site: DefinitionSite::Local(span),
                    });
                    let new_left = if left_is_hole { param_var.clone() } else { left_arg };
                    let new_right = if right_is_hole { param_var } else { right_arg };
                    let body = Expr::App {
                        span: outer_span,
                        func: Box::new(Expr::App {
                            span: inner_span,
                            func: op_func,
                            arg: new_left,
                        }),
                        arg: new_right,
                    };
                    return Expr::Lambda {
                        span,
                        binders: vec![Binder::Var {
                            span,
                            name: cst::Spanned { span, value: param_name },
                        }],
                        body: Box::new(body),
                    };
                }
                // _ not a direct operand after rebalancing — invalid section
                self.errors.push(TypeError::IncorrectAnonymousArgument { span });
                return Expr::App {
                    span: outer_span,
                    func: Box::new(Expr::App {
                        span: inner_span,
                        func: op_func,
                        arg: left_arg,
                    }),
                    arg: right_arg,
                };
            }
        }
        // Shouldn't reach here (convert_op_chain always produces App(App(...)))
        // but emit error for safety
        self.errors.push(TypeError::IncorrectAnonymousArgument { span });
        output.pop().unwrap_or(Expr::Hole { span, name: wildcard_sym })
    }

    fn build_op_app(
        &mut self,
        span: Span,
        op: &Spanned<QualifiedIdent>,
        left: Expr,
        right: Expr,
    ) -> Expr {
        let op_expr = if self.value_operator_targets.contains_key(&op.value.name) {
            // Declared operator (e.g. +, :, $)
            // Use the OPERATOR name (not target name) to avoid conflicts when
            // multiple operators map to the same target (e.g. $ → apply, <*> → apply).
            // The typechecker env has types registered under operator names.
            let def_site = self.resolve_operator_target(op.value.name, op.span);
            if self.function_op_aliases.contains(&op.value.name) {
                Expr::Var {
                    span: op.span,
                    name: op.value,
                    definition_site: def_site,
                }
            } else {
                Expr::Constructor {
                    span: op.span,
                    name: op.value,
                    definition_site: def_site,
                }
            }
        } else {
            // Backtick operator (e.g. `implies`, `compare`) — target is the name itself
            let def_site = self.resolve_value(&op.value, op.span);
            Expr::Var {
                span: op.span,
                name: op.value,
                definition_site: def_site,
            }
        };
        Expr::App {
            span,
            func: Box::new(Expr::App {
                span,
                func: Box::new(op_expr),
                arg: Box::new(left),
            }),
            arg: Box::new(right),
        }
    }

    fn get_fixity(&self, op_name: Symbol) -> (Associativity, u8) {
        self.value_fixities
            .get(&op_name)
            .copied()
            .unwrap_or((Associativity::Left, 9))
    }

    // --- Literal conversion ---

    fn convert_literal(&mut self, lit: &cst::Literal) -> Literal {
        match lit {
            cst::Literal::Int(n) => Literal::Int(*n),
            cst::Literal::Float(f) => Literal::Float(*f),
            cst::Literal::String(s) => Literal::String(s.clone()),
            cst::Literal::Char(c) => Literal::Char(*c),
            cst::Literal::Boolean(b) => Literal::Boolean(*b),
            cst::Literal::Array(elems) => {
                Literal::Array(elems.iter().map(|e| self.convert_expr(e)).collect())
            }
        }
    }

    // --- Type expression conversion ---

    fn convert_type_expr(&mut self, ty: &cst::TypeExpr) -> TypeExpr {
        match ty {
            cst::TypeExpr::Var { span, name } => TypeExpr::Var {
                span: *span,
                name: name.clone(),
            },
            cst::TypeExpr::Constructor { span, name } => TypeExpr::Constructor {
                span: *span,
                name: *name,
                definition_site: self.resolve_type(name, *span),
            },
            cst::TypeExpr::App {
                span,
                constructor,
                arg,
            } => TypeExpr::App {
                span: *span,
                constructor: Box::new(self.convert_type_expr(constructor)),
                arg: Box::new(self.convert_type_expr(arg)),
            },
            cst::TypeExpr::Function { span, from, to } => TypeExpr::Function {
                span: *span,
                from: Box::new(self.convert_type_expr(from)),
                to: Box::new(self.convert_type_expr(to)),
            },
            cst::TypeExpr::Forall { span, vars, ty } => TypeExpr::Forall {
                span: *span,
                vars: vars
                    .iter()
                    .map(|(v, visible, kind)| {
                        (
                            v.clone(),
                            *visible,
                            kind.as_ref().map(|k| Box::new(self.convert_type_expr(k))),
                        )
                    })
                    .collect(),
                ty: Box::new(self.convert_type_expr(ty)),
            },
            cst::TypeExpr::Constrained {
                span,
                constraints,
                ty,
            } => TypeExpr::Constrained {
                span: *span,
                constraints: constraints.iter().map(|c| self.convert_constraint(c)).collect(),
                ty: Box::new(self.convert_type_expr(ty)),
            },
            cst::TypeExpr::Record { span, fields } => TypeExpr::Record {
                span: *span,
                fields: fields.iter().map(|f| self.convert_type_field(f)).collect(),
            },
            cst::TypeExpr::Row {
                span,
                fields,
                tail,
                is_record,
            } => TypeExpr::Row {
                span: *span,
                fields: fields.iter().map(|f| self.convert_type_field(f)).collect(),
                tail: tail.as_ref().map(|t| Box::new(self.convert_type_expr(t))),
                is_record: *is_record,
            },
            cst::TypeExpr::Parens { ty, .. } => self.convert_type_expr(ty),
            cst::TypeExpr::Hole { span, name } => TypeExpr::Hole {
                span: *span,
                name: *name,
            },
            cst::TypeExpr::Wildcard { span } => TypeExpr::Wildcard { span: *span },
            cst::TypeExpr::TypeOp {
                span,
                left,
                op,
                right,
            } => {
                // Check for non-associative type operator chaining
                if let cst::TypeExpr::TypeOp { op: right_op, .. } = right.as_ref() {
                    let (assoc_l, prec_l) = self.type_fixities
                        .get(&op.value.name)
                        .copied()
                        .unwrap_or((Associativity::Left, 9));
                    let (assoc_r, prec_r) = self.type_fixities
                        .get(&right_op.value.name)
                        .copied()
                        .unwrap_or((Associativity::Left, 9));
                    if prec_l == prec_r
                        && (assoc_l == Associativity::None || assoc_r == Associativity::None)
                    {
                        self.errors.push(TypeError::NonAssociativeError {
                            span: right_op.span,
                            op: right_op.value.name,
                        });
                    }
                }
                let left_ty = self.convert_type_expr(left);
                let right_ty = self.convert_type_expr(right);
                let target = match self.type_operators.get(&op.value.name).copied() {
                    Some(t) => t,
                    None => {
                        self.errors.push(TypeError::UndefinedVariable {
                            span: op.span,
                            name: op.value.name,
                        });
                        op.value.name
                    }
                };
                let target_qi = QualifiedIdent {
                    module: None,
                    name: target,
                };
                let def_site = self.resolve_type(&target_qi, op.span);
                let ctor = TypeExpr::Constructor {
                    span: op.span,
                    name: target_qi,
                    definition_site: def_site,
                };
                TypeExpr::App {
                    span: *span,
                    constructor: Box::new(TypeExpr::App {
                        span: *span,
                        constructor: Box::new(ctor),
                        arg: Box::new(left_ty),
                    }),
                    arg: Box::new(right_ty),
                }
            }
            cst::TypeExpr::Kinded { span, ty, kind } => TypeExpr::Kinded {
                span: *span,
                ty: Box::new(self.convert_type_expr(ty)),
                kind: Box::new(self.convert_type_expr(kind)),
            },
            cst::TypeExpr::StringLiteral { span, value } => TypeExpr::StringLiteral {
                span: *span,
                value: value.clone(),
            },
            cst::TypeExpr::IntLiteral { span, value } => TypeExpr::IntLiteral {
                span: *span,
                value: *value,
            },
        }
    }

    fn convert_type_field(&mut self, field: &cst::TypeField) -> TypeField {
        TypeField {
            span: field.span,
            label: field.label.clone(),
            ty: self.convert_type_expr(&field.ty),
        }
    }

    fn convert_constraint(&mut self, c: &cst::Constraint) -> Constraint {
        Constraint {
            span: c.span,
            class: c.class,
            args: c.args.iter().map(|a| self.convert_type_expr(a)).collect(),
            definition_site: self.resolve_class(&c.class, c.span),
        }
    }

    // --- Binder conversion ---

    fn convert_binder(&mut self, binder: &cst::Binder) -> Binder {
        match binder {
            cst::Binder::Wildcard { span } => Binder::Wildcard { span: *span },
            cst::Binder::Var { span, name } => Binder::Var {
                span: *span,
                name: name.clone(),
            },
            cst::Binder::Literal { span, lit } => Binder::Literal {
                span: *span,
                lit: self.convert_literal(lit),
            },
            cst::Binder::Constructor { span, name, args } => Binder::Constructor {
                span: *span,
                name: *name,
                args: args.iter().map(|a| self.convert_binder(a)).collect(),
                definition_site: self.resolve_value(name, *span),
            },
            cst::Binder::Record { span, fields } => Binder::Record {
                span: *span,
                fields: fields
                    .iter()
                    .map(|f| RecordBinderField {
                        span: f.span,
                        label: f.label.clone(),
                        binder: f.binder.as_ref().map(|b| self.convert_binder(b)),
                    })
                    .collect(),
            },
            cst::Binder::As { span, name, binder } => Binder::As {
                span: *span,
                name: name.clone(),
                binder: Box::new(self.convert_binder(binder)),
            },
            cst::Binder::Parens { binder, .. } => self.convert_binder(binder),
            cst::Binder::Array { span, elements } => Binder::Array {
                span: *span,
                elements: elements.iter().map(|e| self.convert_binder(e)).collect(),
            },
            cst::Binder::Op {
                span,
                left,
                op,
                right,
            } => {
                // Operators aliasing functions (not constructors) are invalid in binder patterns
                if self.function_op_aliases.contains(&op.value.name) {
                    self.errors.push(TypeError::InvalidOperatorInBinder {
                        span: op.span,
                        op: op.value.name,
                    });
                }
                // Resolve operator to its target constructor (e.g. `:` → `Cons`)
                let left_b = self.convert_binder(left);
                let right_b = self.convert_binder(right);
                let mut target_name = match self.value_operator_targets.get(&op.value.name) {
                    Some(target) => *target,
                    None => {
                        self.errors.push(TypeError::UndefinedVariable {
                            span: op.span,
                            name: op.value.name,
                        });
                        op.value
                    }
                };
                // Propagate module qualifier (e.g. A.: → A.Cons)
                if target_name.module.is_none() {
                    target_name.module = op.value.module;
                }
                let def_site = self.resolve_operator_target(target_name.name, op.span);
                Binder::Constructor {
                    span: *span,
                    name: target_name,
                    args: vec![left_b, right_b],
                    definition_site: def_site,
                }
            }
            cst::Binder::Typed { span, binder, ty } => Binder::Typed {
                span: *span,
                binder: Box::new(self.convert_binder(binder)),
                ty: self.convert_type_expr(ty),
            },
        }
    }

    // --- Guarded expression conversion ---

    fn convert_guarded(&mut self, guarded: &cst::GuardedExpr) -> GuardedExpr {
        match guarded {
            cst::GuardedExpr::Unconditional(expr) => {
                GuardedExpr::Unconditional(Box::new(self.convert_expr(expr)))
            }
            cst::GuardedExpr::Guarded(guards) => GuardedExpr::Guarded(
                guards
                    .iter()
                    .map(|g| {
                        // Push a scope for pattern guard bindings so that variables
                        // bound by `| Pat <- expr` are visible in subsequent guards
                        // and the guard body.
                        self.push_scope();
                        // Pre-collect binder names from pattern guards so they're in
                        // scope for subsequent boolean guards and the body expression.
                        for p in &g.patterns {
                            if let cst::GuardPattern::Pattern(b, _) = p {
                                let mut names = Vec::new();
                                Self::collect_binder_names(b, &mut names);
                                for (n, s) in names {
                                    self.add_local(n, s);
                                }
                            }
                        }
                        let patterns = g
                            .patterns
                            .iter()
                            .map(|p| match p {
                                cst::GuardPattern::Boolean(e) => {
                                    GuardPattern::Boolean(Box::new(self.convert_expr(e)))
                                }
                                cst::GuardPattern::Pattern(b, e) => {
                                    let binder = self.convert_binder(b);
                                    let expr = self.convert_expr(e);
                                    GuardPattern::Pattern(binder, Box::new(expr))
                                }
                            })
                            .collect();
                        let expr = Box::new(self.convert_expr(&g.expr));
                        self.pop_scope();
                        Guard {
                            span: g.span,
                            patterns,
                            expr,
                        }
                    })
                    .collect(),
            ),
        }
    }

    // --- Let binding conversion ---

    fn convert_let_binding(&mut self, lb: &cst::LetBinding) -> LetBinding {
        match lb {
            cst::LetBinding::Value { span, binder, expr } => LetBinding::Value {
                span: *span,
                binder: self.convert_binder(binder),
                expr: self.convert_expr(expr),
            },
            cst::LetBinding::Signature { span, name, ty } => LetBinding::Signature {
                span: *span,
                name: name.clone(),
                ty: self.convert_type_expr(ty),
            },
        }
    }

    // --- Do statement conversion ---

    fn convert_do_statement(&mut self, stmt: &cst::DoStatement) -> DoStatement {
        match stmt {
            cst::DoStatement::Bind { span, binder, expr } => {
                let ast_expr = self.convert_expr(expr);
                // Register binder names AFTER converting the expression
                let mut names = Vec::new();
                Self::collect_binder_names(binder, &mut names);
                for (n, s) in &names {
                    self.add_local(*n, *s);
                }
                let ast_binder = self.convert_binder(binder);
                DoStatement::Bind {
                    span: *span,
                    binder: ast_binder,
                    expr: ast_expr,
                }
            }
            cst::DoStatement::Let { span, bindings } => {
                // Register names for subsequent statements
                for lb in bindings {
                    if let cst::LetBinding::Value { binder, .. } = lb {
                        let mut names = Vec::new();
                        Self::collect_binder_names(binder, &mut names);
                        for (n, s) in names {
                            self.add_local(n, s);
                        }
                    }
                }
                DoStatement::Let {
                    span: *span,
                    bindings: bindings.iter().map(|lb| self.convert_let_binding(lb)).collect(),
                }
            }
            cst::DoStatement::Discard { span, expr } => DoStatement::Discard {
                span: *span,
                expr: self.convert_expr(expr),
            },
        }
    }

    // --- Record field conversion ---

    fn convert_record_field(&mut self, f: &cst::RecordField) -> RecordField {
        RecordField {
            span: f.span,
            label: f.label.clone(),
            value: f.value.as_ref().map(|v| self.convert_expr(v)),
            type_ann: f.type_ann.as_ref().map(|t| self.convert_type_expr(t)),
            is_update: f.is_update,
        }
    }

    // --- Declaration conversion ---

    fn convert_decl(&mut self, decl: &cst::Decl) -> Decl {
        match decl {
            cst::Decl::Value {
                span,
                name,
                binders,
                guarded,
                where_clause,
            } => {
                self.push_scope();
                for b in binders {
                    let mut names = Vec::new();
                    Self::collect_binder_names(b, &mut names);
                    for (n, s) in names {
                        self.add_local(n, s);
                    }
                }
                // Register where clause names and check for overlapping bindings
                {
                    let mut seen: HashMap<Symbol, Vec<(crate::span::Span, bool)>> = HashMap::new();
                    let mut binding_order: Vec<Symbol> = Vec::new();
                    for lb in where_clause {
                        if let cst::LetBinding::Value { span: lb_span, binder, expr } = lb {
                            let mut names = Vec::new();
                            Self::collect_binder_names(binder, &mut names);
                            for (n, s) in &names {
                                self.add_local(*n, *s);
                            }
                            // Track for overlap detection
                            if let cst::Binder::Var { name: bname, .. } = binder {
                                let is_func = matches!(expr, cst::Expr::Lambda { .. });
                                seen.entry(bname.value).or_default().push((*lb_span, is_func));
                                binding_order.push(bname.value);
                            }
                        }
                    }
                    for (name, entries) in &seen {
                        if entries.len() > 1 {
                            let all_funcs = entries.iter().all(|(_, is_func)| *is_func);
                            if !all_funcs {
                                self.errors.push(TypeError::OverlappingNamesInLet {
                                    spans: entries.iter().map(|(s, _)| *s).collect(),
                                    name: *name,
                                });
                            } else {
                                let indices: Vec<usize> = binding_order.iter().enumerate()
                                    .filter(|(_, n)| **n == *name)
                                    .map(|(i, _)| i)
                                    .collect();
                                let is_adjacent = indices.windows(2).all(|w| w[1] == w[0] + 1);
                                if !is_adjacent {
                                    self.errors.push(TypeError::OverlappingNamesInLet {
                                        spans: entries.iter().map(|(s, _)| *s).collect(),
                                        name: *name,
                                    });
                                }
                            }
                        }
                    }
                }
                let ast_binders = binders.iter().map(|b| self.convert_binder(b)).collect();
                let ast_guarded = self.convert_guarded(guarded);
                let ast_where = where_clause
                    .iter()
                    .map(|lb| self.convert_let_binding(lb))
                    .collect();
                self.pop_scope();
                Decl::Value {
                    span: *span,
                    name: name.clone(),
                    binders: ast_binders,
                    guarded: ast_guarded,
                    where_clause: ast_where,
                }
            }
            cst::Decl::TypeSignature { span, name, ty } => Decl::TypeSignature {
                span: *span,
                name: name.clone(),
                ty: self.convert_type_expr(ty),
            },
            cst::Decl::Data {
                span,
                name,
                type_vars,
                constructors,
                kind_sig,
                is_role_decl,
                kind_type,
                type_var_kind_anns,
            } => Decl::Data {
                span: *span,
                name: name.clone(),
                type_vars: type_vars.clone(),
                constructors: constructors
                    .iter()
                    .map(|c| DataConstructor {
                        span: c.span,
                        name: c.name.clone(),
                        fields: c.fields.iter().map(|f| self.convert_type_expr(f)).collect(),
                    })
                    .collect(),
                kind_sig: *kind_sig,
                is_role_decl: *is_role_decl,
                kind_type: kind_type
                    .as_ref()
                    .map(|k| Box::new(self.convert_type_expr(k))),
                type_var_kind_anns: type_var_kind_anns
                    .iter()
                    .map(|a| a.as_ref().map(|k| Box::new(self.convert_type_expr(k))))
                    .collect(),
            },
            cst::Decl::TypeAlias {
                span,
                name,
                type_vars,
                ty,
                type_var_kind_anns,
            } => Decl::TypeAlias {
                span: *span,
                name: name.clone(),
                type_vars: type_vars.clone(),
                ty: self.convert_type_expr(ty),
                type_var_kind_anns: type_var_kind_anns
                    .iter()
                    .map(|a| a.as_ref().map(|k| Box::new(self.convert_type_expr(k))))
                    .collect(),
            },
            cst::Decl::Newtype {
                span,
                name,
                type_vars,
                constructor,
                ty,
                type_var_kind_anns,
            } => Decl::Newtype {
                span: *span,
                name: name.clone(),
                type_vars: type_vars.clone(),
                constructor: constructor.clone(),
                ty: self.convert_type_expr(ty),
                type_var_kind_anns: type_var_kind_anns
                    .iter()
                    .map(|a| a.as_ref().map(|k| Box::new(self.convert_type_expr(k))))
                    .collect(),
            },
            cst::Decl::Class {
                span,
                constraints,
                name,
                type_vars,
                fundeps,
                members,
                is_kind_sig,
                kind_type,
                type_var_kind_anns,
            } => Decl::Class {
                span: *span,
                constraints: constraints.iter().map(|c| self.convert_constraint(c)).collect(),
                name: name.clone(),
                type_vars: type_vars.clone(),
                fundeps: fundeps.clone(),
                members: members
                    .iter()
                    .map(|m| ClassMember {
                        span: m.span,
                        name: m.name.clone(),
                        ty: self.convert_type_expr(&m.ty),
                    })
                    .collect(),
                is_kind_sig: *is_kind_sig,
                kind_type: kind_type
                    .as_ref()
                    .map(|k| Box::new(self.convert_type_expr(k))),
                type_var_kind_anns: type_var_kind_anns
                    .iter()
                    .map(|a| a.as_ref().map(|k| Box::new(self.convert_type_expr(k))))
                    .collect(),
            },
            cst::Decl::Instance {
                span,
                name,
                constraints,
                class_name,
                types,
                members,
                chain,
            } => Decl::Instance {
                span: *span,
                name: name.clone(),
                constraints: constraints.iter().map(|c| self.convert_constraint(c)).collect(),
                class_name: *class_name,
                class_definition_site: self.resolve_class(class_name, *span),
                types: types.iter().map(|t| self.convert_type_expr(t)).collect(),
                members: members.iter().map(|d| self.convert_decl(d)).collect(),
                chain: *chain,
            },
            cst::Decl::Fixity {
                span,
                associativity,
                precedence,
                target,
                operator,
                is_type,
            } => {
                let target_def = if *is_type {
                    self.resolve_type(target, *span)
                } else {
                    self.resolve_value(target, *span)
                };
                Decl::Fixity {
                    span: *span,
                    associativity: *associativity,
                    precedence: *precedence,
                    target: *target,
                    target_definition_site: target_def,
                    operator: operator.clone(),
                    is_type: *is_type,
                }
            }
            cst::Decl::Foreign { span, name, ty } => Decl::Foreign {
                span: *span,
                name: name.clone(),
                ty: self.convert_type_expr(ty),
            },
            cst::Decl::ForeignData { span, name, kind } => Decl::ForeignData {
                span: *span,
                name: name.clone(),
                kind: self.convert_type_expr(kind),
            },
            cst::Decl::Derive {
                span,
                newtype,
                name,
                constraints,
                class_name,
                types,
            } => {
                // Use lenient class resolution for derive declarations — the typechecker
                // handles derive classes specially (e.g. Newtype, Eq, Ord) and they may
                // not be in the converter's class map.
                let class_definition_site = self.resolve_class_lenient(class_name, *span);
                Decl::Derive {
                    span: *span,
                    newtype: *newtype,
                    name: name.clone(),
                    constraints: constraints.iter().map(|c| self.convert_constraint(c)).collect(),
                    class_name: *class_name,
                    class_definition_site,
                    types: types.iter().map(|t| self.convert_type_expr(t)).collect(),
                }
            }
        }
    }
}