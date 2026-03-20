/// Pretty-printer for the JavaScript AST.
/// Produces readable ES module JavaScript with proper indentation and
/// precedence-aware parenthesization.

use super::common::is_valid_js_identifier;
use super::js_ast::*;

pub fn print_module(module: &JsModule) -> String {
    let mut p = Printer::new();
    p.print_module(module);
    p.output
}

struct Printer {
    output: String,
    indent: usize,
}

impl Printer {
    fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
        }
    }

    fn print_module(&mut self, module: &JsModule) {
        for stmt in &module.imports {
            self.print_stmt(stmt);
        }

        if let Some(ref path) = module.foreign_module_path {
            self.write("import * as $foreign from \"");
            self.write(path);
            self.writeln("\";");
        }

        // Print foreign re-exports first (export { ... } from "./foreign.js";)
        if !module.foreign_exports.is_empty() {
            if let Some(ref path) = module.foreign_module_path {
                let mut fe_sorted: Vec<&str> = module.foreign_exports.iter().map(|s| s.as_str()).collect();
                fe_sorted.sort();
                self.writeln("export {");
                for (i, name) in fe_sorted.iter().enumerate() {
                    self.write("    ");
                    self.write(name);
                    if i < fe_sorted.len() - 1 {
                        self.writeln(",");
                    } else {
                        self.newline();
                    }
                }
                self.write("} from \"");
                self.write(path);
                self.writeln("\";");
            }
        }

        for stmt in &module.body {
            self.print_stmt(stmt);
        }

        if !module.exports.is_empty() {
            // Regular exports (non-foreign)
            let regular_exports: Vec<(&str, Option<&str>)> = module.exports.iter()
                .filter(|(js_name, _)| !module.foreign_exports.contains(js_name))
                .map(|(js_name, ps_name)| (js_name.as_str(), ps_name.as_deref()))
                .collect();
            // Preserve source order (exports are collected in declaration order)
            if !regular_exports.is_empty() {
                self.writeln("export {");
                for (i, (js_name, ps_name)) in regular_exports.iter().enumerate() {
                    self.write("    ");
                    self.write(js_name);
                    if let Some(original) = ps_name {
                        self.write(" as ");
                        self.write(original);
                    }
                    if i < regular_exports.len() - 1 {
                        self.writeln(",");
                    } else {
                        self.newline();
                    }
                }
                self.writeln("};");
            }
        }

        // Print re-exports: export { name } from "module";
        for (module_path, names) in &module.reexports {
            // Sort re-export names alphabetically to match original compiler
            let mut sorted_names: Vec<&(String, Option<String>)> = names.iter().collect();
            sorted_names.sort_by_key(|(name, _)| name.as_str());
            self.writeln("export {");
            for (i, (name, _alias)) in sorted_names.iter().enumerate() {
                self.write("    ");
                self.write(name);
                if i < sorted_names.len() - 1 {
                    self.writeln(",");
                } else {
                    self.newline();
                }
            }
            self.write("} from \"");
            self.write(module_path);
            self.writeln("\";");
        }
    }

    fn print_stmt(&mut self, stmt: &JsStmt) {
        match stmt {
            JsStmt::Expr(expr) => {
                self.print_indent();
                self.print_expr(expr, 0);
                self.writeln(";");
            }
            JsStmt::VarDecl(name, init) => {
                self.print_indent();
                self.write("var ");
                self.write(name);
                if let Some(init) = init {
                    self.write(" = ");
                    // Add /* #__PURE__ */ annotation for module-level constant applications
                    if self.indent == 0 {
                        if let JsExpr::App(_, _) = init {
                            self.write("/* #__PURE__ */ ");
                        }
                    }
                    self.print_expr(init, 0);
                }
                self.writeln(";");
            }
            JsStmt::Assign(target, value) => {
                self.print_indent();
                self.print_expr(target, 0);
                self.write(" = ");
                self.print_expr(value, 0);
                self.writeln(";");
            }
            JsStmt::Return(expr) => {
                self.print_indent();
                self.write("return ");
                self.print_expr(expr, 0);
                self.writeln(";");
            }
            JsStmt::ReturnVoid => {
                self.print_indent();
                self.writeln("return;");
            }
            JsStmt::Throw(expr) => {
                self.print_indent();
                self.write("throw ");
                self.print_expr(expr, 0);
                self.writeln(";");
            }
            JsStmt::If(cond, then_block, else_block) => {
                self.print_indent();
                self.write("if (");
                self.print_expr(cond, 0);
                self.writeln(") {");
                self.indent += 1;
                for s in then_block {
                    self.print_stmt(s);
                }
                self.indent -= 1;
                if let Some(else_stmts) = else_block {
                    // Check if the else block is a single If statement (else-if chain)
                    if else_stmts.len() == 1 {
                        if let JsStmt::If(..) = &else_stmts[0] {
                            self.print_indent();
                            self.write("} else ");
                            // Print the if without indent (it adds its own)
                            let saved_indent = self.indent;
                            self.indent = 0;
                            self.print_stmt(&else_stmts[0]);
                            self.indent = saved_indent;
                            return;
                        }
                    }
                    self.print_indent();
                    self.writeln("} else {");
                    self.indent += 1;
                    for s in else_stmts {
                        self.print_stmt(s);
                    }
                    self.indent -= 1;
                }
                self.print_indent();
                self.writeln("}");
            }
            JsStmt::Block(stmts) => {
                self.print_indent();
                self.writeln("{");
                self.indent += 1;
                for s in stmts {
                    self.print_stmt(s);
                }
                self.indent -= 1;
                self.print_indent();
                self.writeln("}");
            }
            JsStmt::For(var, init, bound, body) => {
                self.print_indent();
                self.write("for (var ");
                self.write(var);
                self.write(" = ");
                self.print_expr(init, 0);
                self.write("; ");
                self.write(var);
                self.write(" < ");
                self.print_expr(bound, 0);
                self.write("; ");
                self.write(var);
                self.writeln("++) {");
                self.indent += 1;
                for s in body {
                    self.print_stmt(s);
                }
                self.indent -= 1;
                self.print_indent();
                self.writeln("}");
            }
            JsStmt::ForIn(var, obj, body) => {
                self.print_indent();
                self.write("for (var ");
                self.write(var);
                self.write(" in ");
                self.print_expr(obj, 0);
                self.writeln(") {");
                self.indent += 1;
                for s in body {
                    self.print_stmt(s);
                }
                self.indent -= 1;
                self.print_indent();
                self.writeln("}");
            }
            JsStmt::While(cond, body) => {
                self.print_indent();
                self.write("while (");
                self.print_expr(cond, 0);
                self.writeln(") {");
                self.indent += 1;
                for s in body {
                    self.print_stmt(s);
                }
                self.indent -= 1;
                self.print_indent();
                self.writeln("}");
            }
            JsStmt::Comment(text) => {
                self.print_indent();
                self.write("// ");
                self.writeln(text);
            }
            JsStmt::Import { name, path } => {
                self.print_indent();
                self.write("import * as ");
                self.write(name);
                self.write(" from \"");
                self.write(path);
                self.writeln("\";");
            }
            JsStmt::Export(names) => {
                self.print_indent();
                self.write("export { ");
                self.write(&names.join(", "));
                self.writeln(" };");
            }
            JsStmt::ExportFrom(names, path) => {
                self.print_indent();
                self.write("export { ");
                self.write(&names.join(", "));
                self.write(" } from \"");
                self.write(path);
                self.writeln("\";");
            }
            JsStmt::FunctionDecl(name, params, body) => {
                self.print_indent();
                self.write("function ");
                self.write(name);
                self.write("(");
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(param);
                }
                self.writeln(") {");
                self.indent += 1;
                for stmt in body {
                    self.print_stmt(stmt);
                }
                self.indent -= 1;
                self.print_indent();
                self.writeln("}");
            }
            JsStmt::RawJs(code) => {
                self.print_indent();
                self.writeln(code);
            }
        }
    }

    /// Print an expression, wrapping in parens if needed based on the
    /// surrounding precedence context.
    fn print_expr(&mut self, expr: &JsExpr, parent_prec: u8) {
        let prec = expr_precedence(expr);
        let needs_parens = prec < parent_prec;

        if needs_parens {
            self.write("(");
        }

        match expr {
            JsExpr::NumericLit(n) => {
                let s = if n.fract() == 0.0 && !n.is_infinite() && !n.is_nan() {
                    format!("{:.1}", n) // Force decimal point: 1.0
                } else {
                    format!("{}", n)
                };
                if *n < 0.0 {
                    self.write(&format!("({})", s));
                } else {
                    self.write(&s);
                }
            }
            JsExpr::IntLit(n) => {
                if *n < 0 {
                    self.write(&format!("({})", n));
                } else {
                    self.write(&format!("{}", n));
                }
            }
            JsExpr::StringLit(s) => {
                self.write("\"");
                self.write(&escape_js_string(s));
                self.write("\"");
            }
            JsExpr::BoolLit(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            JsExpr::ArrayLit(elems) => {
                self.write("[");
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(elem, 0);
                }
                self.write("]");
            }
            JsExpr::ObjectLit(fields) => {
                if fields.is_empty() {
                    self.write("{}");
                } else {
                    self.writeln("{");
                    self.indent += 1;
                    for (i, (key, value)) in fields.iter().enumerate() {
                        self.print_indent();
                        if is_valid_js_identifier(key) {
                            self.write(key);
                        } else {
                            self.write("\"");
                            self.write(&escape_js_string(key));
                            self.write("\"");
                        }
                        self.write(": ");
                        self.print_expr(value, 0);
                        if i < fields.len() - 1 {
                            self.write(",");
                        }
                        self.newline();
                    }
                    self.indent -= 1;
                    self.print_indent();
                    self.write("}");
                }
            }
            JsExpr::Var(name) => {
                self.write(name);
            }
            JsExpr::Indexer(obj, key) => {
                self.print_expr(obj, PREC_MEMBER);
                // Use dot notation for valid identifier string literals
                if let JsExpr::StringLit(s) = key.as_ref() {
                    if is_valid_js_identifier(s) {
                        self.write(".");
                        self.write(s);
                        if needs_parens {
                            self.write(")");
                        }
                        return;
                    }
                }
                self.write("[");
                self.print_expr(key, 0);
                self.write("]");
            }
            JsExpr::Function(name, params, body) => {
                self.write("function");
                if let Some(n) = name {
                    self.write(" ");
                    self.write(n);
                }
                self.write(" (");
                for (i, param_name) in params.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(param_name);
                }
                self.writeln(") {");
                self.indent += 1;
                for s in body {
                    self.print_stmt(s);
                }
                self.indent -= 1;
                self.print_indent();
                self.write("}");
            }
            JsExpr::App(callee, args) => {
                self.print_expr(callee, PREC_CALL);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(arg, 0);
                }
                self.write(")");
            }
            JsExpr::Unary(op, expr) => {
                self.write(unary_op_str(*op));
                let needs_space =
                    matches!(op, JsUnaryOp::Typeof | JsUnaryOp::Void | JsUnaryOp::New);
                if needs_space {
                    self.write(" ");
                }
                // Use PREC_UNARY + 1 to force parens around nested unary ops
                // (e.g., -(-x) must not become --x)
                self.print_expr(expr, PREC_UNARY + 1);
            }
            JsExpr::Binary(op, left, right) => {
                let op_prec = binary_op_precedence(*op);
                self.print_expr(left, op_prec);
                self.write(" ");
                self.write(binary_op_str(*op));
                self.write(" ");
                self.print_expr(right, op_prec + 1);
            }
            JsExpr::InstanceOf(expr, ty) => {
                self.print_expr(expr, PREC_RELATIONAL);
                self.write(" instanceof ");
                self.print_expr(ty, PREC_RELATIONAL + 1);
            }
            JsExpr::New(callee, args) => {
                self.write("new ");
                self.print_expr(callee, PREC_NEW);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(arg, 0);
                }
                self.write(")");
            }
            JsExpr::Ternary(cond, then_expr, else_expr) => {
                self.print_expr(cond, PREC_TERNARY + 1);
                self.write(" ? ");
                self.print_expr(then_expr, 0);
                self.write(" : ");
                self.print_expr(else_expr, 0);
            }
            JsExpr::ModuleAccessor(module, field) => {
                self.write(module);
                // Use bracket notation for names that aren't valid JS property identifiers,
                // JS reserved words (to match original PureScript compiler behavior),
                // or JS built-in globals.
                if is_valid_js_identifier(field) && !is_js_builtin_global(field) && !is_js_reserved_word(field) {
                    self.write(".");
                    self.write(field);
                } else {
                    self.write("[\"");
                    self.write(&escape_js_string(field));
                    self.write("\"]");
                }
            }
            JsExpr::RawJs(code) => {
                self.write(code);
            }
        }

        if needs_parens {
            self.write(")");
        }
    }

    fn write(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn writeln(&mut self, s: &str) {
        self.output.push_str(s);
        self.output.push('\n');
    }

    fn newline(&mut self) {
        self.output.push('\n');
    }

    fn print_indent(&mut self) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
    }
}

// Precedence levels (higher = binds tighter)
const PREC_TERNARY: u8 = 3;
const PREC_OR: u8 = 5;
const PREC_AND: u8 = 6;
const PREC_BITOR: u8 = 7;
const PREC_BITXOR: u8 = 8;
const PREC_BITAND: u8 = 9;
const PREC_EQUALITY: u8 = 10;
const PREC_RELATIONAL: u8 = 11;
const PREC_SHIFT: u8 = 12;
const PREC_ADDITIVE: u8 = 13;
const PREC_MULTIPLICATIVE: u8 = 14;
const PREC_UNARY: u8 = 15;
const PREC_NEW: u8 = 17;
const PREC_CALL: u8 = 18;
const PREC_MEMBER: u8 = 19;

fn expr_precedence(expr: &JsExpr) -> u8 {
    match expr {
        JsExpr::Ternary(..) => PREC_TERNARY,
        JsExpr::Binary(op, ..) => binary_op_precedence(*op),
        JsExpr::Unary(..) => PREC_UNARY,
        JsExpr::InstanceOf(..) => PREC_RELATIONAL,
        JsExpr::New(..) => PREC_NEW,
        JsExpr::App(..) => PREC_CALL,
        JsExpr::Indexer(..) | JsExpr::ModuleAccessor(..) => PREC_MEMBER,
        JsExpr::Function(..) => 1, // low precedence, usually needs wrapping
        _ => 20,                   // atoms: literals, vars, etc.
    }
}

fn binary_op_precedence(op: JsBinaryOp) -> u8 {
    match op {
        JsBinaryOp::Or => PREC_OR,
        JsBinaryOp::And => PREC_AND,
        JsBinaryOp::BitwiseOr => PREC_BITOR,
        JsBinaryOp::BitwiseXor => PREC_BITXOR,
        JsBinaryOp::BitwiseAnd => PREC_BITAND,
        JsBinaryOp::Eq | JsBinaryOp::Neq | JsBinaryOp::StrictEq | JsBinaryOp::StrictNeq => {
            PREC_EQUALITY
        }
        JsBinaryOp::Lt | JsBinaryOp::Lte | JsBinaryOp::Gt | JsBinaryOp::Gte => PREC_RELATIONAL,
        JsBinaryOp::ShiftLeft | JsBinaryOp::ShiftRight | JsBinaryOp::UnsignedShiftRight => {
            PREC_SHIFT
        }
        JsBinaryOp::Add | JsBinaryOp::Sub => PREC_ADDITIVE,
        JsBinaryOp::Mul | JsBinaryOp::Div | JsBinaryOp::Mod => PREC_MULTIPLICATIVE,
    }
}

fn unary_op_str(op: JsUnaryOp) -> &'static str {
    match op {
        JsUnaryOp::Not => "!",
        JsUnaryOp::Negate => "-",
        JsUnaryOp::BitwiseNot => "~",
        JsUnaryOp::Typeof => "typeof",
        JsUnaryOp::Void => "void",
        JsUnaryOp::New => "new",
        JsUnaryOp::Positive => "+",
    }
}

fn binary_op_str(op: JsBinaryOp) -> &'static str {
    match op {
        JsBinaryOp::Add => "+",
        JsBinaryOp::Sub => "-",
        JsBinaryOp::Mul => "*",
        JsBinaryOp::Div => "/",
        JsBinaryOp::Mod => "%",
        JsBinaryOp::Eq => "==",
        JsBinaryOp::Neq => "!=",
        JsBinaryOp::StrictEq => "===",
        JsBinaryOp::StrictNeq => "!==",
        JsBinaryOp::Lt => "<",
        JsBinaryOp::Lte => "<=",
        JsBinaryOp::Gt => ">",
        JsBinaryOp::Gte => ">=",
        JsBinaryOp::And => "&&",
        JsBinaryOp::Or => "||",
        JsBinaryOp::BitwiseAnd => "&",
        JsBinaryOp::BitwiseOr => "|",
        JsBinaryOp::BitwiseXor => "^",
        JsBinaryOp::ShiftLeft => "<<",
        JsBinaryOp::ShiftRight => ">>",
        JsBinaryOp::UnsignedShiftRight => ">>>",
    }
}

/// Check if a string is a JavaScript built-in global object name.
/// The original PureScript compiler uses bracket notation for these to avoid conflicts.
fn is_js_builtin_global(s: &str) -> bool {
    matches!(s, "Proxy" | "Reflect" | "Symbol")
}

/// Check if a string is a JS reserved word that can't be used as a dot-access property.
fn is_js_reserved_word(s: &str) -> bool {
    matches!(s,
        "break" | "case" | "catch" | "class" | "const" | "continue" | "debugger" | "default" |
        "delete" | "do" | "else" | "enum" | "export" | "extends" | "false" | "finally" |
        "for" | "function" | "if" | "import" | "in" | "instanceof" | "let" | "new" |
        "null" | "return" | "super" | "switch" | "this" | "throw" | "true" | "try" |
        "typeof" | "undefined" | "var" | "void" | "while" | "with" | "yield"
    )
}

/// Escape a string for use in a JS string literal.
/// Matches the PureScript compiler's escaping: uses \xHH for bytes 0x01-0x1F
/// and 0x80-0xFF, and \uHHHH for chars above 0xFF.
fn escape_js_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    // PureScript compiler outputs individual UTF-16 code units for non-BMP chars
    for ch in s.chars() {
        match ch {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\'' => result.push('\''),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '\0' => result.push_str("\\0"),
            c => {
                let cp = c as u32;
                if cp < 0x20 {
                    // Control chars as \xHH
                    result.push_str(&format!("\\x{:02x}", cp));
                } else if cp >= 0x80 && cp <= 0xFF {
                    // Latin-1 supplement as \xHH
                    result.push_str(&format!("\\x{:02x}", cp));
                } else if cp > 0xFF && cp <= 0xFFFF {
                    // BMP non-ASCII as \uHHHH
                    result.push_str(&format!("\\u{:04x}", cp));
                } else if cp >= 0xF0000 && cp <= 0xF07FF {
                    // Encoded lone surrogate (from lexer PUA mapping):
                    // Reverse: original = 0xD800 + (cp - 0xF0000)
                    let original = 0xD800 + (cp - 0xF0000);
                    result.push_str(&format!("\\u{:04x}", original));
                } else if cp > 0xFFFF {
                    // Non-BMP: encode as surrogate pair \uHHHH\uHHHH
                    let hi = ((cp - 0x10000) >> 10) + 0xD800;
                    let lo = ((cp - 0x10000) & 0x3FF) + 0xDC00;
                    result.push_str(&format!("\\u{:04x}\\u{:04x}", hi, lo));
                } else {
                    result.push(c);
                }
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_module() {
        let module = JsModule {
            imports: vec![JsStmt::Import {
                name: "Data_Maybe".to_string(),
                path: "../Data.Maybe/index.js".to_string(),
            }],
            body: vec![JsStmt::VarDecl(
                "foo".to_string(),
                Some(JsExpr::IntLit(42)),
            )],
            exports: vec![("foo".to_string(), None)],
            foreign_exports: vec![],
            foreign_module_path: None,
            reexports: vec![],
        };
        let output = print_module(&module);
        assert!(output.contains("import * as Data_Maybe from \"../Data.Maybe/index.js\";"));
        assert!(output.contains("var foo = 42;"));
        assert!(output.contains("export {\n    foo\n};"));
    }

    #[test]
    fn test_function_expr() {
        let f = JsExpr::Function(
            None,
            vec!["x".to_string()],
            vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
        );
        let module = JsModule {
            imports: vec![],
            body: vec![JsStmt::VarDecl("id".to_string(), Some(f))],
            exports: vec![],
            foreign_exports: vec![],
            foreign_module_path: None,
            reexports: vec![],
        };
        let output = print_module(&module);
        assert!(output.contains("function (x)"));
        assert!(output.contains("return x;"));
    }

    #[test]
    fn test_dot_notation_for_valid_identifiers() {
        let expr = JsExpr::Indexer(
            Box::new(JsExpr::Var("obj".to_string())),
            Box::new(JsExpr::StringLit("name".to_string())),
        );
        let mut p = Printer::new();
        p.print_expr(&expr, 0);
        assert_eq!(p.output, "obj.name");
    }

    #[test]
    fn test_bracket_notation_for_special_keys() {
        let expr = JsExpr::Indexer(
            Box::new(JsExpr::Var("obj".to_string())),
            Box::new(JsExpr::StringLit("my-key".to_string())),
        );
        let mut p = Printer::new();
        p.print_expr(&expr, 0);
        assert_eq!(p.output, "obj[\"my-key\"]");
    }

    #[test]
    fn test_escape_string() {
        assert_eq!(escape_js_string("hello\nworld"), "hello\\nworld");
        assert_eq!(escape_js_string("say \"hi\""), "say \\\"hi\\\"");
        assert_eq!(escape_js_string("back\\slash"), "back\\\\slash");
    }

    #[test]
    fn test_binary_precedence() {
        let expr = JsExpr::Binary(
            JsBinaryOp::Add,
            Box::new(JsExpr::Binary(
                JsBinaryOp::Mul,
                Box::new(JsExpr::IntLit(2)),
                Box::new(JsExpr::IntLit(3)),
            )),
            Box::new(JsExpr::IntLit(4)),
        );
        let mut p = Printer::new();
        p.print_expr(&expr, 0);
        assert_eq!(p.output, "2 * 3 + 4");
    }

    #[test]
    fn test_ternary() {
        let expr = JsExpr::Ternary(
            Box::new(JsExpr::Var("x".to_string())),
            Box::new(JsExpr::IntLit(1)),
            Box::new(JsExpr::IntLit(2)),
        );
        let mut p = Printer::new();
        p.print_expr(&expr, 0);
        assert_eq!(p.output, "x ? 1 : 2");
    }
}
