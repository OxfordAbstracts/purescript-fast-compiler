/// Simple imperative JavaScript/TypeScript AST, analogous to PureScript's CoreImp AST.
/// Designed as a thin layer between the PureScript CST and textual TS output.

/// TypeScript type annotation.
#[derive(Debug, Clone, PartialEq)]
pub enum TsType {
    /// `number`
    Number,
    /// `string`
    String,
    /// `boolean`
    Boolean,
    /// `void`
    Void,
    /// `any`
    Any,
    /// `Array<T>`
    Array(Box<TsType>),
    /// `(p1: T1, p2: T2) => R`
    Function(Vec<(std::string::String, TsType)>, Box<TsType>),
    /// `{ field1: T1; field2: T2 }`
    Object(Vec<(std::string::String, TsType)>),
    /// Generic type variable: `A`, `B`
    TypeVar(std::string::String),
    /// Named type reference: `Maybe<A>`, `Effect<void>`
    TypeRef(std::string::String, Vec<TsType>),
    /// Union type: `A | B | C`
    Union(Vec<TsType>),
    /// Literal string type: `"Nothing"`, `"Just"`
    StringLit(std::string::String),
    /// Generic function: `<A, B>(p1: T1) => R`
    GenericFunction(Vec<std::string::String>, Vec<(std::string::String, TsType)>, Box<TsType>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum JsExpr {
    NumericLit(f64),
    IntLit(i64),
    StringLit(std::string::String),
    BoolLit(bool),
    ArrayLit(Vec<JsExpr>),
    ObjectLit(Vec<(std::string::String, JsExpr)>),
    Var(std::string::String),
    /// Property access: `obj[key]` or `obj.field`
    Indexer(Box<JsExpr>, Box<JsExpr>),
    /// `function name?(params) { body }`
    /// Fields: name, params (name, optional type), return type, body
    Function(Option<std::string::String>, Vec<(std::string::String, Option<TsType>)>, Option<TsType>, Vec<JsStmt>),
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
    ModuleAccessor(std::string::String, std::string::String),
    /// Raw JavaScript expression (escape hatch)
    RawJs(std::string::String),
    /// Type assertion: `expr as Type`
    TypeAssertion(Box<JsExpr>, TsType),
}

#[derive(Debug, Clone, PartialEq)]
pub enum JsStmt {
    /// Expression statement
    Expr(JsExpr),
    /// `var name: Type = init;` or `var name;`
    VarDecl(std::string::String, Option<TsType>, Option<JsExpr>),
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
    For(std::string::String, JsExpr, JsExpr, Vec<JsStmt>),
    /// `for (var name in obj) { body }`
    ForIn(std::string::String, JsExpr, Vec<JsStmt>),
    /// `while (cond) { body }`
    While(JsExpr, Vec<JsStmt>),
    /// `// comment` or `/* comment */`
    Comment(std::string::String),
    /// `import * as name from "path";`
    Import { name: std::string::String, path: std::string::String },
    /// `export { names... };`
    Export(Vec<std::string::String>),
    /// `export { names... } from "path";`
    ExportFrom(Vec<std::string::String>, std::string::String),
    /// Raw JS statement (escape hatch)
    RawJs(std::string::String),
    /// `type Name<Params> = Type;`
    TypeDecl(std::string::String, Vec<std::string::String>, TsType),
    /// `interface Name<Params> { methods }` — fields are (name, type, optional)
    InterfaceDecl(std::string::String, Vec<std::string::String>, Vec<(std::string::String, TsType, bool)>),
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

/// A complete JS/TS module ready for printing.
#[derive(Debug, Clone)]
pub struct JsModule {
    pub imports: Vec<JsStmt>,
    pub body: Vec<JsStmt>,
    pub exports: Vec<std::string::String>,
    pub foreign_exports: Vec<std::string::String>,
    pub foreign_module_path: Option<std::string::String>,
}
