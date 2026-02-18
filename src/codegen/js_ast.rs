/// Simple imperative JavaScript AST, analogous to PureScript's CoreImp AST.
/// Designed as a thin layer between the PureScript CST and textual JS output.

#[derive(Debug, Clone, PartialEq)]
pub enum JsExpr {
    NumericLit(f64),
    IntLit(i64),
    StringLit(String),
    BoolLit(bool),
    ArrayLit(Vec<JsExpr>),
    ObjectLit(Vec<(String, JsExpr)>),
    Var(String),
    /// Property access: `obj[key]` or `obj.field`
    Indexer(Box<JsExpr>, Box<JsExpr>),
    /// `function name?(params) { body }`
    Function(Option<String>, Vec<String>, Vec<JsStmt>),
    /// `callee(args...)`
    App(Box<JsExpr>, Vec<JsExpr>),
    Unary(JsUnaryOp, Box<JsExpr>),
    Binary(JsBinaryOp, Box<JsExpr>, Box<JsExpr>),
    InstanceOf(Box<JsExpr>, Box<JsExpr>),
    /// `new Ctor(args...)`
    New(Box<JsExpr>, Vec<JsExpr>),
    /// `cond ? then : else`
    Ternary(Box<JsExpr>, Box<JsExpr>, Box<JsExpr>),
    /// `$foreign.name` — reference to a foreign-imported binding
    ModuleAccessor(String, String),
    /// Raw JavaScript expression (escape hatch)
    RawJs(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum JsStmt {
    /// Expression statement
    Expr(JsExpr),
    /// `var name = init;` or `var name;`
    VarDecl(String, Option<JsExpr>),
    /// `target = value;`
    Assign(JsExpr, JsExpr),
    /// `return expr;`
    Return(JsExpr),
    /// `return;`
    ReturnVoid,
    /// `throw expr;`
    Throw(JsExpr),
    /// `if (cond) { then } else { else }`
    If(JsExpr, Vec<JsStmt>, Option<Vec<JsStmt>>),
    /// `{ stmts }`
    Block(Vec<JsStmt>),
    /// `for (var name = init; name < bound; name++) { body }`
    For(String, JsExpr, JsExpr, Vec<JsStmt>),
    /// `for (var name in obj) { body }`
    ForIn(String, JsExpr, Vec<JsStmt>),
    /// `while (cond) { body }`
    While(JsExpr, Vec<JsStmt>),
    /// `// comment` or `/* comment */`
    Comment(String),
    /// `import * as name from "path";`
    Import { name: String, path: String },
    /// `export { names... };`
    Export(Vec<String>),
    /// `export { names... } from "path";`
    ExportFrom(Vec<String>, String),
    /// Raw JS statement (escape hatch)
    RawJs(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JsUnaryOp {
    Not,
    Negate,
    BitwiseNot,
    Typeof,
    Void,
    New,
    Positive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JsBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
    StrictEq,
    StrictNeq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    ShiftLeft,
    ShiftRight,
    UnsignedShiftRight,
}

/// A complete JS module ready for printing.
#[derive(Debug, Clone)]
pub struct JsModule {
    pub imports: Vec<JsStmt>,
    pub body: Vec<JsStmt>,
    pub exports: Vec<String>,
    pub foreign_exports: Vec<String>,
    pub foreign_module_path: Option<String>,
}
