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

struct Converter {
    /// Module-level values (vars, constructors, methods) → definition site
    values: HashMap<Symbol, DefinitionSite>,
    /// Module-level type constructors → definition site
    types: HashMap<Symbol, DefinitionSite>,
    /// Module-level type class names → definition site
    classes: HashMap<Symbol, DefinitionSite>,

    /// Type-level operators: op symbol → target type name
    type_operators: HashMap<Symbol, Symbol>,
    /// Value-level operator fixities
    value_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// Operators that alias functions (not constructors)
    function_op_aliases: HashSet<Symbol>,

    /// Local variable scopes (pushed/popped during walk)
    local_scopes: Vec<HashMap<Symbol, Span>>,

    errors: Vec<TypeError>,
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
            value_fixities: HashMap::new(),
            function_op_aliases: HashSet::new(),
            local_scopes: Vec::new(),
            errors: Vec::new(),
        };

        // 1. Register Prim types
        conv.register_prim();

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
        }
        // Partial class
        self.classes.insert(intern("Partial"), site.clone());
    }

    fn process_imports(&mut self, module: &cst::Module, registry: &ModuleRegistry) {
        for import_decl in &module.imports {
            let module_exports = if is_prim_module(&import_decl.module) {
                // For explicit `import Prim`, just skip — Prim is always registered
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

            // Always import fixities and type operators
            for (op, fixity) in &module_exports.value_fixities {
                let key = Self::maybe_qualify(op.name, qualifier);
                self.value_fixities.insert(key, *fixity);
            }
            for (op, target) in &module_exports.type_operators {
                let key = Self::maybe_qualify(op.name, qualifier);
                self.type_operators.insert(key, target.name);
            }
            for op in &module_exports.function_op_aliases {
                self.function_op_aliases.insert(op.name);
            }
        }
    }

    fn import_all(
        &mut self,
        exports: &ModuleExports,
        qualifier: Option<Symbol>,
        site: &DefinitionSite,
    ) {
        for name in exports.values.keys() {
            let key = Self::maybe_qualify(name.name, qualifier);
            self.values.insert(key, site.clone());
        }
        for name in exports.data_constructors.keys() {
            let key = Self::maybe_qualify(name.name, qualifier);
            self.types.insert(key, site.clone());
        }
        for name in exports.class_param_counts.keys() {
            let key = Self::maybe_qualify(name.name, qualifier);
            self.classes.insert(key, site.clone());
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
                self.values.insert(key, site.clone());
            }
        }
        for name in exports.data_constructors.keys() {
            if !hidden.contains(&name.name) {
                let key = Self::maybe_qualify(name.name, qualifier);
                self.types.insert(key, site.clone());
            }
        }
        for name in exports.class_param_counts.keys() {
            if !hidden.contains(&name.name) {
                let key = Self::maybe_qualify(name.name, qualifier);
                self.classes.insert(key, site.clone());
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
                self.values.insert(key, site.clone());
            }
            cst::Import::Type(name, members) => {
                let key = Self::maybe_qualify(*name, qualifier);
                self.types.insert(key, site.clone());
                // Import constructors if (..) or explicit list
                if let Some(members) = members {
                    let qi = QualifiedIdent { module: None, name: *name };
                    if let Some(ctors) = exports.data_constructors.get(&qi) {
                        match members {
                            cst::DataMembers::All => {
                                for ctor in ctors {
                                    let k = Self::maybe_qualify(ctor.name, qualifier);
                                    self.values.insert(k, site.clone());
                                }
                            }
                            cst::DataMembers::Explicit(names) => {
                                for n in names {
                                    let k = Self::maybe_qualify(*n, qualifier);
                                    self.values.insert(k, site.clone());
                                }
                            }
                        }
                    }
                }
            }
            cst::Import::TypeOp(name) => {
                let key = Self::maybe_qualify(*name, qualifier);
                self.values.insert(key, site.clone());
            }
            cst::Import::Class(name) => {
                let key = Self::maybe_qualify(*name, qualifier);
                self.classes.insert(key, site.clone());
                // Import class methods
                for (method_name, _) in &exports.class_methods {
                    // Check if this method belongs to the imported class
                    let qi = QualifiedIdent { module: None, name: *name };
                    if exports.class_methods.get(method_name).map(|(cn, _)| cn) == Some(&qi) {
                        let k = Self::maybe_qualify(method_name.name, qualifier);
                        self.values.insert(k, site.clone());
                    }
                }
            }
        }
    }

    fn register_local_decls(&mut self, decls: &[cst::Decl]) {
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
                cst::Decl::Fixity {
                    span,
                    target,
                    operator,
                    is_type,
                    associativity,
                    precedence,
                    ..
                } => {
                    if *is_type {
                        self.type_operators.insert(operator.value, target.name);
                    } else {
                        self.value_fixities
                            .insert(operator.value, (*associativity, *precedence));
                        // Register operator as a value alias for the target
                        let target_site = self
                            .values
                            .get(&target.name)
                            .cloned()
                            .unwrap_or(DefinitionSite::Local(*span));
                        self.values.insert(operator.value, target_site);
                        // Check if target is a function (not a constructor)
                        // Constructors are uppercase; functions are lowercase or operators
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
                _ => {}
            }
        }
    }

    fn maybe_qualify(name: Symbol, qualifier: Option<Symbol>) -> Symbol {
        match qualifier {
            Some(q) => qualified_symbol(q, name),
            None => name,
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

    fn resolve_type(&mut self, name: &QualifiedIdent, span: Span) -> DefinitionSite {
        let key = match name.module {
            Some(m) => qualified_symbol(m, name.name),
            None => name.name,
        };
        match self.types.get(&key).cloned() {
            Some(site) => site,
            None => {
                self.errors.push(TypeError::UnknownType {
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
                self.errors.push(TypeError::UnknownClass {
                    span,
                    name: *name,
                });
                DefinitionSite::Local(span)
            }
        }
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
                let def_site = self.resolve_value(&op.value, *span);
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
            cst::Expr::Parens { expr, .. } => self.convert_expr(expr),
            cst::Expr::TypeAnnotation { span, expr, ty } => Expr::TypeAnnotation {
                span: *span,
                expr: Box::new(self.convert_expr(expr)),
                ty: self.convert_type_expr(ty),
            },
            cst::Expr::Hole { span, name } => Expr::Hole {
                span: *span,
                name: *name,
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
        operands.push(current);

        // Convert all operands
        let mut ast_operands: Vec<Expr> = operands
            .iter()
            .map(|e| self.convert_expr(e))
            .collect();

        // Single operator: fast path
        if operators.len() == 1 {
            let right = ast_operands.pop().unwrap();
            let left = ast_operands.pop().unwrap();
            return self.build_op_app(span, &operators[0], left, right);
        }

        // Shunting-yard for multiple operators
        let mut output: Vec<Expr> = Vec::new();
        let mut op_stack: Vec<usize> = Vec::new();

        output.push(ast_operands.remove(0));

        for i in 0..operators.len() {
            let (assoc_i, prec_i) = self.get_fixity(operators[i].value.name);

            while let Some(&top_idx) = op_stack.last() {
                let (_assoc_top, prec_top) = self.get_fixity(operators[top_idx].value.name);
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

        output.pop().unwrap()
    }

    fn build_op_app(
        &mut self,
        span: Span,
        op: &Spanned<QualifiedIdent>,
        left: Expr,
        right: Expr,
    ) -> Expr {
        let def_site = self.resolve_value(&op.value, op.span);
        let op_expr = if self.function_op_aliases.contains(&op.value.name) {
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
                // Binder operators are always constructors (e.g. `:` for NonEmptyList)
                let left_b = self.convert_binder(left);
                let right_b = self.convert_binder(right);
                let def_site = self.resolve_value(&op.value, op.span);
                Binder::Constructor {
                    span: *span,
                    name: op.value,
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
                    .map(|g| Guard {
                        span: g.span,
                        patterns: g
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
                            .collect(),
                        expr: Box::new(self.convert_expr(&g.expr)),
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
                // Register where clause names
                for lb in where_clause {
                    if let cst::LetBinding::Value { binder, .. } = lb {
                        let mut names = Vec::new();
                        Self::collect_binder_names(binder, &mut names);
                        for (n, s) in names {
                            self.add_local(n, s);
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
            } => Decl::Derive {
                span: *span,
                newtype: *newtype,
                name: name.clone(),
                constraints: constraints.iter().map(|c| self.convert_constraint(c)).collect(),
                class_name: *class_name,
                class_definition_site: self.resolve_class(class_name, *span),
                types: types.iter().map(|t| self.convert_type_expr(t)).collect(),
            },
        }
    }
}