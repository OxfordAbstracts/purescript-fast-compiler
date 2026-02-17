//! JavaScript FFI module parsing.
//!
//! Parses JavaScript source files to extract export and import information
//! for validation against PureScript `foreign import` declarations.

use std::collections::HashSet;

use swc_common::input::StringInput;
use swc_common::sync::Lrc;
use swc_common::{FileName, SourceMap};
use swc_ecma_ast::*;
use swc_ecma_parser::{lexer::Lexer, Parser, Syntax};

/// Information extracted from a JavaScript foreign module.
#[derive(Debug, Default)]
pub struct ForeignModuleInfo {
    /// ES module exports: `export const foo`, `export { foo }`, `export default`
    pub es_exports: Vec<String>,
    /// CommonJS exports: `exports.foo = ...`, `module.exports = { foo }`
    pub cjs_exports: Vec<String>,
    /// ES module import source paths: `import ... from "mod"`
    pub es_imports: Vec<String>,
    /// CommonJS require paths: `require("mod")`
    pub cjs_imports: Vec<String>,
}

/// FFI validation error.
#[derive(Debug)]
pub enum FfiError {
    /// Pure CommonJS module (only `exports.*` style, no ES syntax)
    DeprecatedFFICommonJSModule,
    /// Declared `foreign import` but not exported in FFI
    MissingFFIImplementations { missing: Vec<String> },
    /// Exported in FFI but no corresponding `foreign import`
    UnusedFFIImplementations { unused: Vec<String> },
    /// CommonJS exports mixed with ES module syntax
    UnsupportedFFICommonJSExports { exports: Vec<String> },
    /// CommonJS imports (require) mixed with ES module syntax
    UnsupportedFFICommonJSImports { imports: Vec<String> },
    /// JS file could not be parsed
    ParseError { message: String },
}

/// Parse a JavaScript source string and extract foreign module info.
pub fn parse_foreign_module(source: &str) -> Result<ForeignModuleInfo, String> {
    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(FileName::Custom("foreign.js".into()).into(), source.to_string());

    let lexer = Lexer::new(
        Syntax::Es(Default::default()),
        Default::default(),
        StringInput::from(&*fm),
        None,
    );

    let mut parser = Parser::new_from(lexer);
    let module = parser
        .parse_module()
        .map_err(|e| format!("{:?}", e))?;

    let mut info = ForeignModuleInfo::default();

    for item in &module.body {
        match item {
            ModuleItem::ModuleDecl(decl) => extract_module_decl(&mut info, decl),
            ModuleItem::Stmt(stmt) => extract_stmt(&mut info, stmt),
        }
    }

    Ok(info)
}

/// Get the string value of a Str literal (which uses Wtf8Atom internally).
fn str_lit_value(s: &Str) -> String {
    s.value.to_string_lossy().into_owned()
}

/// Get the string value of an identifier's sym (which uses Atom, deref to str).
fn ident_name(ident: &Ident) -> String {
    // Atom implements Deref<Target=str>
    (*ident.sym).to_owned()
}

/// Get the string value of an IdentName's sym.
fn ident_name_str(ident: &IdentName) -> String {
    (*ident.sym).to_owned()
}

/// Extract export/import info from an ES module declaration.
fn extract_module_decl(info: &mut ForeignModuleInfo, decl: &ModuleDecl) {
    match decl {
        // `export const foo = ...`, `export function foo() {}`, `export class Foo {}`
        ModuleDecl::ExportDecl(export_decl) => {
            extract_decl_names(&export_decl.decl, &mut info.es_exports);
        }

        // `export { foo }`, `export { foo as bar }`, `export { foo } from "mod"`
        ModuleDecl::ExportNamed(named) => {
            if let Some(src) = &named.src {
                info.es_imports.push(str_lit_value(src));
            }
            for spec in &named.specifiers {
                match spec {
                    ExportSpecifier::Named(named_spec) => {
                        let name = named_spec
                            .exported
                            .as_ref()
                            .unwrap_or(&named_spec.orig);
                        info.es_exports.push(module_export_name_str(name));
                    }
                    ExportSpecifier::Default(default_spec) => {
                        info.es_exports.push(ident_name(&default_spec.exported));
                    }
                    ExportSpecifier::Namespace(ns_spec) => {
                        info.es_exports.push(module_export_name_str(&ns_spec.name));
                    }
                }
            }
        }

        // `export default function foo() {}`, `export default class Foo {}`
        ModuleDecl::ExportDefaultDecl(_) => {
            info.es_exports.push("default".to_string());
        }

        // `export default expression`
        ModuleDecl::ExportDefaultExpr(_) => {
            info.es_exports.push("default".to_string());
        }

        // `import ... from "mod"`
        ModuleDecl::Import(import_decl) => {
            info.es_imports.push(str_lit_value(&import_decl.src));
        }

        _ => {}
    }
}

/// Extract CJS exports/imports from a statement.
fn extract_stmt(info: &mut ForeignModuleInfo, stmt: &Stmt) {
    match stmt {
        // Expression statements: `exports.foo = ...`, `module.exports = { ... }`
        Stmt::Expr(expr_stmt) => {
            if let Expr::Assign(assign) = expr_stmt.expr.as_ref() {
                extract_cjs_assign(info, assign);
            }
        }

        // Variable declarations: `var x = require("mod")`
        Stmt::Decl(Decl::Var(var_decl)) => {
            for decl in &var_decl.decls {
                if let Some(init) = &decl.init {
                    if is_require_call(init) {
                        if let Some(module_path) = extract_require_path(init) {
                            info.cjs_imports.push(module_path);
                        }
                    }
                }
            }
        }

        _ => {}
    }
}

/// Extract CJS export names from an assignment expression.
fn extract_cjs_assign(info: &mut ForeignModuleInfo, assign: &AssignExpr) {
    if let AssignTarget::Simple(SimpleAssignTarget::Member(member)) = &assign.left {
        // `exports.NAME` or `exports["NAME"]`
        if is_ident(&member.obj, "exports") {
            if let Some(name) = extract_member_prop_name(&member.prop) {
                info.cjs_exports.push(name);
            }
        }
        // `module.exports = { ... }`
        else if is_ident(&member.obj, "module") {
            if matches_ident_prop(&member.prop, "exports") {
                if let Expr::Object(obj) = assign.right.as_ref() {
                    for prop in &obj.props {
                        if let PropOrSpread::Prop(prop) = prop {
                            if let Some(name) = extract_prop_key_name(prop) {
                                info.cjs_exports.push(name);
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Extract the string name from a member property.
fn extract_member_prop_name(prop: &MemberProp) -> Option<String> {
    match prop {
        MemberProp::Ident(ident) => Some(ident_name_str(ident)),
        MemberProp::Computed(computed) => {
            if let Expr::Lit(Lit::Str(s)) = computed.expr.as_ref() {
                Some(str_lit_value(s))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Check if a member property is an identifier with a specific name.
fn matches_ident_prop(prop: &MemberProp, name: &str) -> bool {
    matches!(prop, MemberProp::Ident(ident) if &*ident.sym == name)
}

/// Extract declared names from a JS declaration.
fn extract_decl_names(decl: &Decl, names: &mut Vec<String>) {
    match decl {
        Decl::Var(var_decl) => {
            for d in &var_decl.decls {
                if let Pat::Ident(ident) = &d.name {
                    names.push(ident_name(&ident.id));
                }
            }
        }
        Decl::Fn(fn_decl) => {
            names.push(ident_name(&fn_decl.ident));
        }
        Decl::Class(class_decl) => {
            names.push(ident_name(&class_decl.ident));
        }
        _ => {}
    }
}

/// Get the string value of a ModuleExportName.
fn module_export_name_str(name: &ModuleExportName) -> String {
    match name {
        ModuleExportName::Ident(ident) => ident_name(ident),
        ModuleExportName::Str(s) => str_lit_value(s),
    }
}

/// Check if an expression is an Ident with the given name.
fn is_ident(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Ident(ident) if &*ident.sym == name)
}

/// Check if an expression is a `require(...)` call.
fn is_require_call(expr: &Expr) -> bool {
    if let Expr::Call(call) = expr {
        if let Callee::Expr(callee) = &call.callee {
            return is_ident(callee, "require");
        }
    }
    false
}

/// Extract the module path from a `require("path")` call.
fn extract_require_path(expr: &Expr) -> Option<String> {
    if let Expr::Call(call) = expr {
        if let Some(arg) = call.args.first() {
            if let Expr::Lit(Lit::Str(s)) = arg.expr.as_ref() {
                return Some(str_lit_value(s));
            }
        }
    }
    None
}

/// Extract the key name from an object property.
fn extract_prop_key_name(prop: &Prop) -> Option<String> {
    match prop {
        Prop::KeyValue(kv) => prop_name_str(&kv.key),
        Prop::Shorthand(ident) => Some(ident_name(ident)),
        Prop::Method(method) => prop_name_str(&method.key),
        _ => None,
    }
}

/// Get the string value of a property name.
fn prop_name_str(key: &PropName) -> Option<String> {
    match key {
        PropName::Ident(ident) => Some(ident_name_str(ident)),
        PropName::Str(s) => Some(str_lit_value(s)),
        _ => None,
    }
}

// ===== Validation =====

/// Validate foreign imports against parsed JS module info.
pub fn validate_foreign_module(
    foreign_import_names: &[String],
    info: &ForeignModuleInfo,
) -> Vec<FfiError> {
    let mut errors = Vec::new();

    let has_es = !info.es_exports.is_empty() || !info.es_imports.is_empty();
    let has_cjs = !info.cjs_exports.is_empty() || !info.cjs_imports.is_empty();

    // Pure CJS module (no ES syntax at all) → deprecated
    if has_cjs && !has_es {
        errors.push(FfiError::DeprecatedFFICommonJSModule);
        return errors;
    }

    // ES module with CJS imports → unsupported
    if !info.cjs_imports.is_empty() {
        errors.push(FfiError::UnsupportedFFICommonJSImports {
            imports: info.cjs_imports.clone(),
        });
        return errors;
    }

    // ES module with CJS exports → unsupported
    if !info.cjs_exports.is_empty() {
        errors.push(FfiError::UnsupportedFFICommonJSExports {
            exports: info.cjs_exports.clone(),
        });
        return errors;
    }

    // Compare foreign import names against ES exports
    let export_set: HashSet<&str> = info.es_exports.iter().map(|s| s.as_str()).collect();
    let import_set: HashSet<&str> = foreign_import_names.iter().map(|s| s.as_str()).collect();

    let missing: Vec<String> = foreign_import_names
        .iter()
        .filter(|name| !export_set.contains(name.as_str()))
        .cloned()
        .collect();

    let unused: Vec<String> = info
        .es_exports
        .iter()
        .filter(|name| !import_set.contains(name.as_str()))
        .cloned()
        .collect();

    if !missing.is_empty() {
        errors.push(FfiError::MissingFFIImplementations { missing });
    }

    if !unused.is_empty() {
        errors.push(FfiError::UnusedFFIImplementations { unused });
    }

    errors
}
