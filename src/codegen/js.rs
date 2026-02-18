/// CST-to-JavaScript code generation.
///
/// Translates the PureScript CST directly to a JS AST, which is then
/// pretty-printed to ES module JavaScript. Mirrors the original PureScript
/// compiler's Language.PureScript.CodeGen.JS module.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use crate::cst::*;
use crate::interner::{self, Symbol};
use crate::lexer::token::Ident;
use crate::typechecker::check::{ModuleExports, ModuleRegistry};

use super::common::{any_name_to_js, ident_to_js, module_name_to_js};
use super::js_ast::*;

/// Context threaded through code generation for a single module.
struct CodegenCtx<'a> {
    /// The module being compiled
    module: &'a Module,
    /// This module's exports (from typechecking)
    exports: &'a ModuleExports,
    /// Registry of all typechecked modules
    #[allow(dead_code)]
    registry: &'a ModuleRegistry,
    /// Module name as dot-separated string (e.g. "Data.Maybe")
    #[allow(dead_code)]
    module_name: &'a str,
    /// Module name parts as symbols
    module_parts: &'a [Symbol],
    /// Set of names that are newtypes (newtype constructor erasure)
    newtype_names: &'a HashSet<Symbol>,
    /// Mapping from constructor name → (parent_type, type_vars, field_types)
    ctor_details: &'a HashMap<Symbol, (Symbol, Vec<Symbol>, Vec<crate::typechecker::types::Type>)>,
    /// Data type → constructor names (to determine sum vs product)
    data_constructors: &'a HashMap<Symbol, Vec<Symbol>>,
    /// Operators that alias functions (not constructors)
    function_op_aliases: &'a HashSet<Symbol>,
    /// Names of foreign imports in this module
    foreign_imports: HashSet<Symbol>,
    /// Import map: module_parts → JS variable name
    import_map: HashMap<Vec<Symbol>, String>,
    /// Counter for generating fresh variable names
    fresh_counter: Cell<usize>,
}

impl<'a> CodegenCtx<'a> {
    fn fresh_name(&self, prefix: &str) -> String {
        let n = self.fresh_counter.get();
        self.fresh_counter.set(n + 1);
        format!("${prefix}{n}")
    }
}

/// Generate a JS module from a typechecked PureScript module.
pub fn module_to_js(
    module: &Module,
    module_name: &str,
    module_parts: &[Symbol],
    exports: &ModuleExports,
    registry: &ModuleRegistry,
    has_ffi: bool,
) -> JsModule {
    let mut ctx = CodegenCtx {
        module,
        exports,
        registry,
        module_name,
        module_parts,
        newtype_names: &exports.newtype_names,
        ctor_details: &exports.ctor_details,
        data_constructors: &exports.data_constructors,
        function_op_aliases: &exports.function_op_aliases,
        foreign_imports: HashSet::new(),
        import_map: HashMap::new(),
        fresh_counter: Cell::new(0),
    };

    let mut exported_names: Vec<String> = Vec::new();
    let mut foreign_re_exports: Vec<String> = Vec::new();

    // Collect foreign imports
    for decl in &module.decls {
        if let Decl::Foreign { name, .. } = decl {
            ctx.foreign_imports.insert(name.value);
        }
    }

    // Build import statements
    let mut imports = Vec::new();
    for imp in &module.imports {
        let parts = &imp.module.parts;
        // Skip Prim imports
        if !parts.is_empty() {
            let first = interner::resolve(parts[0]).unwrap_or_default();
            if first == "Prim" {
                continue;
            }
        }
        // Skip self-imports
        if *parts == ctx.module_parts {
            continue;
        }
        if ctx.import_map.contains_key(parts) {
            continue;
        }

        let js_name = module_name_to_js(parts);
        let mod_name_str = parts
            .iter()
            .map(|s| interner::resolve(*s).unwrap_or_default())
            .collect::<Vec<_>>()
            .join(".");
        let path = format!("../{mod_name_str}/index.js");

        imports.push(JsStmt::Import {
            name: js_name.clone(),
            path,
        });
        ctx.import_map.insert(parts.clone(), js_name);
    }

    // Generate body declarations
    let mut body = Vec::new();
    let mut seen_values: HashSet<Symbol> = HashSet::new();
    let decl_groups = collect_decl_groups(&module.decls);

    for group in &decl_groups {
        match group {
            DeclGroup::Value(name_sym, decls) => {
                if seen_values.contains(name_sym) {
                    continue;
                }
                seen_values.insert(*name_sym);
                let stmts = gen_value_decl(&ctx, *name_sym, decls);
                body.extend(stmts);
                let js_name = ident_to_js(*name_sym);
                if is_exported(&ctx, *name_sym) {
                    exported_names.push(js_name);
                }
            }
            DeclGroup::Data(decl) => {
                if let Decl::Data { constructors, .. } = decl {
                    for ctor in constructors {
                        let ctor_js = ident_to_js(ctor.name.value);
                        if is_exported(&ctx, ctor.name.value) {
                            exported_names.push(ctor_js);
                        }
                    }
                }
                let stmts = gen_data_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Newtype(decl) => {
                if let Decl::Newtype { constructor, .. } = decl {
                    let ctor_js = ident_to_js(constructor.value);
                    if is_exported(&ctx, constructor.value) {
                        exported_names.push(ctor_js);
                    }
                }
                let stmts = gen_newtype_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Foreign(name_sym) => {
                let js_name = ident_to_js(*name_sym);
                body.push(JsStmt::VarDecl(
                    js_name.clone(),
                    Some(JsExpr::ModuleAccessor("$foreign".to_string(), js_name.clone())),
                ));
                if is_exported(&ctx, *name_sym) {
                    foreign_re_exports.push(js_name);
                }
            }
            DeclGroup::Instance(decl) => {
                if let Decl::Instance { name: Some(n), .. } = decl {
                    let inst_js = ident_to_js(n.value);
                    if is_exported(&ctx, n.value) {
                        exported_names.push(inst_js);
                    }
                }
                let stmts = gen_instance_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Class(_) | DeclGroup::TypeAlias | DeclGroup::Fixity
            | DeclGroup::TypeSig | DeclGroup::ForeignData | DeclGroup::Derive
            | DeclGroup::KindSig => {
                // These produce no JS output
            }
        }
    }

    let foreign_module_path = if has_ffi {
        Some("./foreign.js".to_string())
    } else {
        None
    };

    JsModule {
        imports,
        body,
        exports: exported_names,
        foreign_exports: foreign_re_exports,
        foreign_module_path,
    }
}

// ===== Declaration groups =====

#[allow(dead_code)]
enum DeclGroup<'a> {
    Value(Symbol, Vec<&'a Decl>),
    Data(&'a Decl),
    Newtype(&'a Decl),
    Foreign(Symbol),
    Instance(&'a Decl),
    Class(&'a Decl),
    TypeAlias,
    Fixity,
    TypeSig,
    ForeignData,
    Derive,
    KindSig,
}

fn collect_decl_groups(decls: &[Decl]) -> Vec<DeclGroup<'_>> {
    let mut groups: Vec<DeclGroup<'_>> = Vec::new();
    let mut value_map: HashMap<Symbol, Vec<&Decl>> = HashMap::new();
    let mut value_order: Vec<Symbol> = Vec::new();

    for decl in decls {
        match decl {
            Decl::Value { name, .. } => {
                let sym = name.value;
                if !value_map.contains_key(&sym) {
                    value_order.push(sym);
                }
                value_map.entry(sym).or_default().push(decl);
            }
            Decl::Data { kind_sig, is_role_decl, .. } => {
                if *kind_sig != KindSigSource::None {
                    groups.push(DeclGroup::KindSig);
                } else if *is_role_decl {
                    // role declarations produce no JS
                } else {
                    groups.push(DeclGroup::Data(decl));
                }
            }
            Decl::Newtype { .. } => groups.push(DeclGroup::Newtype(decl)),
            Decl::Foreign { name, .. } => groups.push(DeclGroup::Foreign(name.value)),
            Decl::Instance { .. } => groups.push(DeclGroup::Instance(decl)),
            Decl::Class { is_kind_sig, .. } => {
                if *is_kind_sig {
                    groups.push(DeclGroup::KindSig);
                } else {
                    groups.push(DeclGroup::Class(decl));
                }
            }
            Decl::TypeAlias { .. } => groups.push(DeclGroup::TypeAlias),
            Decl::Fixity { .. } => groups.push(DeclGroup::Fixity),
            Decl::TypeSignature { .. } => groups.push(DeclGroup::TypeSig),
            Decl::ForeignData { .. } => groups.push(DeclGroup::ForeignData),
            Decl::Derive { .. } => groups.push(DeclGroup::Derive),
        }
    }

    let result: Vec<DeclGroup<'_>> = groups;

    // Prepend value groups (they should come in source order)
    let mut final_result = Vec::new();
    for sym in value_order {
        if let Some(decls) = value_map.remove(&sym) {
            final_result.push(DeclGroup::Value(sym, decls));
        }
    }
    final_result.extend(result);
    final_result
}

// ===== Export checking =====

fn is_exported(ctx: &CodegenCtx, name: Symbol) -> bool {
    match &ctx.module.exports {
        None => true, // No export list means export everything
        Some(export_list) => {
            for export in &export_list.value.exports {
                match export {
                    Export::Value(ident) => {
                        if *ident == name {
                            return true;
                        }
                    }
                    Export::Type(_, Some(DataMembers::All)) => {
                        // Check if name is a constructor of this type
                        if ctx.ctor_details.contains_key(&name) {
                            return true;
                        }
                    }
                    Export::Type(_, Some(DataMembers::Explicit(ctors))) => {
                        if ctors.contains(&name) {
                            return true;
                        }
                    }
                    Export::Class(_) => {
                        // Class methods are exported as values
                        if ctx.exports.class_methods.contains_key(&name) {
                            return true;
                        }
                    }
                    Export::Module(_) => {
                        // Re-export entire module — handled separately
                        return true;
                    }
                    _ => {}
                }
            }
            false
        }
    }
}

// ===== Value declarations =====

fn gen_value_decl(ctx: &CodegenCtx, name: Symbol, decls: &[&Decl]) -> Vec<JsStmt> {
    let js_name = ident_to_js(name);

    if decls.len() == 1 {
        if let Decl::Value { binders, guarded, where_clause, .. } = decls[0] {
            if binders.is_empty() && where_clause.is_empty() {
                // Simple value: `name = expr`
                let expr = gen_guarded_expr(ctx, guarded);
                return vec![JsStmt::VarDecl(js_name, Some(expr))];
            }

            if where_clause.is_empty() {
                // Function with binders: `name a b = expr` → curried lambdas
                let body_expr = gen_guarded_expr_stmts(ctx, guarded);
                let func = gen_curried_function(ctx, binders, body_expr);
                return vec![JsStmt::VarDecl(js_name, Some(func))];
            }

            // Value/function with where clause: wrap in IIFE
            let mut iife_body = Vec::new();
            gen_let_bindings(ctx, where_clause, &mut iife_body);

            if binders.is_empty() {
                let expr = gen_guarded_expr(ctx, guarded);
                iife_body.push(JsStmt::Return(expr));
                let iife = JsExpr::App(
                    Box::new(JsExpr::Function(None, vec![], iife_body)),
                    vec![],
                );
                return vec![JsStmt::VarDecl(js_name, Some(iife))];
            } else {
                let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                iife_body.extend(body_stmts);
                let func = gen_curried_function_from_stmts(ctx, binders, iife_body);
                return vec![JsStmt::VarDecl(js_name, Some(func))];
            }
        }
    }

    // Multi-equation function: compile like case expression
    // name p1 p2 = e1; name q1 q2 = e2  →  function(x) { if (match p1) ... }
    gen_multi_equation(ctx, &js_name, decls)
}

fn gen_multi_equation(ctx: &CodegenCtx, js_name: &str, decls: &[&Decl]) -> Vec<JsStmt> {
    // Determine arity from first equation
    let arity = if let Decl::Value { binders, .. } = decls[0] {
        binders.len()
    } else {
        0
    };

    if arity == 0 {
        // Should not happen for multi-equation, but handle gracefully
        if let Decl::Value { guarded, .. } = decls[0] {
            let expr = gen_guarded_expr(ctx, guarded);
            return vec![JsStmt::VarDecl(js_name.to_string(), Some(expr))];
        }
        return vec![];
    }

    let params: Vec<String> = (0..arity).map(|i| ctx.fresh_name(&format!("arg{i}_"))).collect();

    let mut body = Vec::new();
    for decl in decls {
        if let Decl::Value { binders, guarded, where_clause, .. } = decl {
            let mut alt_body = Vec::new();
            if !where_clause.is_empty() {
                gen_let_bindings(ctx, where_clause, &mut alt_body);
            }

            let result_stmts = gen_guarded_expr_stmts(ctx, guarded);

            // Build pattern match condition
            let (cond, bindings) = gen_binders_match(ctx, binders, &params);
            alt_body.extend(bindings);
            alt_body.extend(result_stmts);

            if let Some(cond) = cond {
                body.push(JsStmt::If(cond, alt_body, None));
            } else {
                // Unconditional match (all wildcards/vars)
                body.extend(alt_body);
            }
        }
    }

    body.push(JsStmt::Throw(JsExpr::App(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit(format!("Failed pattern match in {}", js_name))],
    )));

    // Build curried function
    let mut result = body;
    for param in params.iter().rev() {
        result = vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![param.clone()],
            result,
        ))];
    }

    // Unwrap outermost: it's `return function(p0) { ... }`, we want just the function
    if let Some(JsStmt::Return(func)) = result.into_iter().next() {
        vec![JsStmt::VarDecl(js_name.to_string(), Some(func))]
    } else {
        vec![]
    }
}

// ===== Data declarations =====

fn gen_data_decl(_ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Data { constructors, .. } = decl else { return vec![] };

    let mut stmts = Vec::new();
    for ctor in constructors {
        let ctor_js = ident_to_js(ctor.name.value);
        let n_fields = ctor.fields.len();

        if n_fields == 0 {
            // Nullary constructor: IIFE that creates a singleton
            let iife_body = vec![
                JsStmt::Expr(JsExpr::Function(
                    Some(ctor_js.clone()),
                    vec![],
                    vec![],
                )),
                JsStmt::Assign(
                    JsExpr::Indexer(
                        Box::new(JsExpr::Var(ctor_js.clone())),
                        Box::new(JsExpr::StringLit("value".to_string())),
                    ),
                    JsExpr::New(Box::new(JsExpr::Var(ctor_js.clone())), vec![]),
                ),
                JsStmt::Return(JsExpr::Var(ctor_js.clone())),
            ];
            let iife = JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            );
            stmts.push(JsStmt::VarDecl(ctor_js.clone(), Some(iife)));
        } else {
            // N-ary constructor: IIFE with constructor function + curried create
            let field_names: Vec<String> = (0..n_fields)
                .map(|i| format!("value{i}"))
                .collect();

            // Constructor body: this.value0 = value0; ...
            let ctor_body: Vec<JsStmt> = field_names
                .iter()
                .map(|f| {
                    JsStmt::Assign(
                        JsExpr::Indexer(
                            Box::new(JsExpr::Var("this".to_string())),
                            Box::new(JsExpr::StringLit(f.clone())),
                        ),
                        JsExpr::Var(f.clone()),
                    )
                })
                .collect();

            // Curried create function
            let create_body = JsExpr::New(
                Box::new(JsExpr::Var(ctor_js.clone())),
                field_names.iter().map(|f| JsExpr::Var(f.clone())).collect(),
            );

            let mut create_func: JsExpr = create_body;
            for f in field_names.iter().rev() {
                create_func = JsExpr::Function(
                    None,
                    vec![f.clone()],
                    vec![JsStmt::Return(create_func)],
                );
            }

            let iife_body = vec![
                JsStmt::Expr(JsExpr::Function(
                    Some(ctor_js.clone()),
                    field_names.clone(),
                    ctor_body,
                )),
                JsStmt::Assign(
                    JsExpr::Indexer(
                        Box::new(JsExpr::Var(ctor_js.clone())),
                        Box::new(JsExpr::StringLit("create".to_string())),
                    ),
                    create_func,
                ),
                JsStmt::Return(JsExpr::Var(ctor_js.clone())),
            ];

            let iife = JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            );
            stmts.push(JsStmt::VarDecl(ctor_js, Some(iife)));
        }
    }

    stmts
}

// ===== Newtype declarations =====

fn gen_newtype_decl(_ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Newtype { constructor, .. } = decl else { return vec![] };
    let ctor_js = ident_to_js(constructor.value);

    // Newtype constructor is identity: create = function(x) { return x; }
    let create = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );

    let iife_body = vec![
        JsStmt::Expr(JsExpr::Function(Some(ctor_js.clone()), vec![], vec![])),
        JsStmt::Assign(
            JsExpr::Indexer(
                Box::new(JsExpr::Var(ctor_js.clone())),
                Box::new(JsExpr::StringLit("create".to_string())),
            ),
            create,
        ),
        JsStmt::Return(JsExpr::Var(ctor_js.clone())),
    ];

    let iife = JsExpr::App(
        Box::new(JsExpr::Function(None, vec![], iife_body)),
        vec![],
    );

    vec![JsStmt::VarDecl(ctor_js, Some(iife))]
}

// ===== Instance declarations =====

fn gen_instance_decl(ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Instance { name, members, .. } = decl else { return vec![] };

    // Instances become object literals with method implementations
    let instance_name = match name {
        Some(n) => ident_to_js(n.value),
        None => ctx.fresh_name("instance_"),
    };

    let mut fields = Vec::new();
    for member in members {
        if let Decl::Value { name: method_name, binders, guarded, where_clause, .. } = member {
            let method_js = ident_to_js(method_name.value);
            let method_expr = if binders.is_empty() && where_clause.is_empty() {
                gen_guarded_expr(ctx, guarded)
            } else if where_clause.is_empty() {
                let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                gen_curried_function(ctx, binders, body_stmts)
            } else {
                let mut iife_body = Vec::new();
                gen_let_bindings(ctx, where_clause, &mut iife_body);
                if binders.is_empty() {
                    let expr = gen_guarded_expr(ctx, guarded);
                    iife_body.push(JsStmt::Return(expr));
                    JsExpr::App(
                        Box::new(JsExpr::Function(None, vec![], iife_body)),
                        vec![],
                    )
                } else {
                    let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                    iife_body.extend(body_stmts);
                    gen_curried_function_from_stmts(ctx, binders, iife_body)
                }
            };
            fields.push((method_js, method_expr));
        }
    }

    let obj = JsExpr::ObjectLit(fields);
    vec![JsStmt::VarDecl(instance_name, Some(obj))]
}

// ===== Expression translation =====

fn gen_expr(ctx: &CodegenCtx, expr: &Expr) -> JsExpr {
    match expr {
        Expr::Var { name, .. } => gen_qualified_ref(ctx, name),

        Expr::Constructor { name, .. } => {
            let ctor_name = name.name;
            // Check if nullary (use .value) or n-ary (use .create)
            if let Some((_, _, fields)) = ctx.ctor_details.get(&ctor_name) {
                if fields.is_empty() {
                    // Nullary: Ctor.value
                    let base = gen_qualified_ref_raw(ctx, name);
                    JsExpr::Indexer(
                        Box::new(base),
                        Box::new(JsExpr::StringLit("value".to_string())),
                    )
                } else {
                    // N-ary: Ctor.create
                    let base = gen_qualified_ref_raw(ctx, name);
                    JsExpr::Indexer(
                        Box::new(base),
                        Box::new(JsExpr::StringLit("create".to_string())),
                    )
                }
            } else if ctx.newtype_names.contains(&ctor_name) {
                // Newtype constructor: Ctor.create (identity)
                let base = gen_qualified_ref_raw(ctx, name);
                JsExpr::Indexer(
                    Box::new(base),
                    Box::new(JsExpr::StringLit("create".to_string())),
                )
            } else {
                gen_qualified_ref_raw(ctx, name)
            }
        }

        Expr::Literal { lit, .. } => gen_literal(ctx, lit),

        Expr::App { func, arg, .. } => {
            let f = gen_expr(ctx, func);
            let a = gen_expr(ctx, arg);
            JsExpr::App(Box::new(f), vec![a])
        }

        Expr::VisibleTypeApp { func, .. } => {
            // Type applications are erased at runtime
            gen_expr(ctx, func)
        }

        Expr::Lambda { binders, body, .. } => {
            let body_expr = gen_expr(ctx, body);
            gen_curried_function(ctx, binders, vec![JsStmt::Return(body_expr)])
        }

        Expr::Op { left, op, right, .. } => {
            // Resolve operator to function application: op(left)(right)
            let op_ref = gen_qualified_ref(ctx, &op.value);
            let l = gen_expr(ctx, left);
            let r = gen_expr(ctx, right);
            JsExpr::App(
                Box::new(JsExpr::App(Box::new(op_ref), vec![l])),
                vec![r],
            )
        }

        Expr::OpParens { op, .. } => gen_qualified_ref(ctx, &op.value),

        Expr::If { cond, then_expr, else_expr, .. } => {
            let c = gen_expr(ctx, cond);
            let t = gen_expr(ctx, then_expr);
            let e = gen_expr(ctx, else_expr);
            JsExpr::Ternary(Box::new(c), Box::new(t), Box::new(e))
        }

        Expr::Case { exprs, alts, .. } => gen_case_expr(ctx, exprs, alts),

        Expr::Let { bindings, body, .. } => {
            let mut iife_body = Vec::new();
            gen_let_bindings(ctx, bindings, &mut iife_body);
            let body_expr = gen_expr(ctx, body);
            iife_body.push(JsStmt::Return(body_expr));
            JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            )
        }

        Expr::Do { statements, module: qual_mod, .. } => {
            gen_do_expr(ctx, statements, qual_mod.as_ref())
        }

        Expr::Ado { statements, result, module: qual_mod, .. } => {
            gen_ado_expr(ctx, statements, result, qual_mod.as_ref())
        }

        Expr::Record { fields, .. } => {
            let js_fields: Vec<(String, JsExpr)> = fields
                .iter()
                .map(|f| {
                    let label = interner::resolve(f.label.value).unwrap_or_default();
                    let value = match &f.value {
                        Some(v) => gen_expr(ctx, v),
                        None => {
                            // Punned field: { x } means { x: x }
                            JsExpr::Var(ident_to_js(f.label.value))
                        }
                    };
                    (label, value)
                })
                .collect();
            JsExpr::ObjectLit(js_fields)
        }

        Expr::RecordAccess { expr, field, .. } => {
            let obj = gen_expr(ctx, expr);
            let label = interner::resolve(field.value).unwrap_or_default();
            JsExpr::Indexer(Box::new(obj), Box::new(JsExpr::StringLit(label)))
        }

        Expr::RecordUpdate { expr, updates, .. } => {
            gen_record_update(ctx, expr, updates)
        }

        Expr::Parens { expr, .. } => gen_expr(ctx, expr),

        Expr::TypeAnnotation { expr, .. } => gen_expr(ctx, expr),

        Expr::Hole { name, .. } => {
            // Holes should have been caught by the typechecker, but emit an error at runtime
            let hole_name = interner::resolve(*name).unwrap_or_default();
            JsExpr::App(
                Box::new(JsExpr::Var("Error".to_string())),
                vec![JsExpr::StringLit(format!("Hole: {hole_name}"))],
            )
        }

        Expr::Array { elements, .. } => {
            let elems: Vec<JsExpr> = elements.iter().map(|e| gen_expr(ctx, e)).collect();
            JsExpr::ArrayLit(elems)
        }

        Expr::Negate { expr, .. } => {
            let e = gen_expr(ctx, expr);
            JsExpr::Unary(JsUnaryOp::Negate, Box::new(e))
        }

        Expr::AsPattern { name, .. } => {
            // This shouldn't appear in expression position normally
            gen_expr(ctx, name)
        }
    }
}

fn gen_literal(ctx: &CodegenCtx, lit: &Literal) -> JsExpr {
    match lit {
        Literal::Int(n) => JsExpr::IntLit(*n),
        Literal::Float(n) => JsExpr::NumericLit(*n),
        Literal::String(s) => JsExpr::StringLit(s.clone()),
        Literal::Char(c) => JsExpr::StringLit(c.to_string()),
        Literal::Boolean(b) => JsExpr::BoolLit(*b),
        Literal::Array(elems) => {
            let js_elems: Vec<JsExpr> = elems.iter().map(|e| gen_expr(ctx, e)).collect();
            JsExpr::ArrayLit(js_elems)
        }
    }
}

// ===== Qualified references =====

fn gen_qualified_ref(ctx: &CodegenCtx, qident: &QualifiedIdent) -> JsExpr {
    let name = qident.name;

    // Check if it's a foreign import in the current module
    if qident.module.is_none() && ctx.foreign_imports.contains(&name) {
        let js_name = ident_to_js(name);
        return JsExpr::ModuleAccessor("$foreign".to_string(), js_name);
    }

    gen_qualified_ref_raw(ctx, qident)
}

fn gen_qualified_ref_raw(ctx: &CodegenCtx, qident: &QualifiedIdent) -> JsExpr {
    let js_name = ident_to_js(qident.name);

    match &qident.module {
        None => JsExpr::Var(js_name),
        Some(mod_sym) => {
            // Look up the module in import map
            // The module qualifier is a single symbol containing the alias
            let mod_str = interner::resolve(*mod_sym).unwrap_or_default();
            // Find the actual import by looking at qualified imports
            for imp in &ctx.module.imports {
                if let Some(ref qual) = imp.qualified {
                    let qual_str = qual.parts
                        .iter()
                        .map(|s| interner::resolve(*s).unwrap_or_default())
                        .collect::<Vec<_>>()
                        .join(".");
                    if qual_str == mod_str {
                        if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                            return JsExpr::ModuleAccessor(js_mod.clone(), js_name);
                        }
                    }
                }
                // Also check if module name directly matches
                let imp_name = imp.module.parts
                    .iter()
                    .map(|s| interner::resolve(*s).unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(".");
                if imp_name == mod_str {
                    if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                        return JsExpr::ModuleAccessor(js_mod.clone(), js_name);
                    }
                }
            }
            // Fallback: use the module name directly
            let js_mod = any_name_to_js(&mod_str.replace('.', "_"));
            JsExpr::ModuleAccessor(js_mod, js_name)
        }
    }
}

// ===== Guarded expressions =====

fn gen_guarded_expr(ctx: &CodegenCtx, guarded: &GuardedExpr) -> JsExpr {
    match guarded {
        GuardedExpr::Unconditional(expr) => gen_expr(ctx, expr),
        GuardedExpr::Guarded(guards) => {
            // Convert guards into nested ternaries
            gen_guards_expr(ctx, guards)
        }
    }
}

fn gen_guarded_expr_stmts(ctx: &CodegenCtx, guarded: &GuardedExpr) -> Vec<JsStmt> {
    match guarded {
        GuardedExpr::Unconditional(expr) => {
            vec![JsStmt::Return(gen_expr(ctx, expr))]
        }
        GuardedExpr::Guarded(guards) => gen_guards_stmts(ctx, guards),
    }
}

fn gen_guards_expr(ctx: &CodegenCtx, guards: &[Guard]) -> JsExpr {
    // Build nested ternary: cond1 ? e1 : cond2 ? e2 : error
    let mut result = JsExpr::App(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    );

    for guard in guards.iter().rev() {
        let cond = gen_guard_condition(ctx, &guard.patterns);
        let body = gen_expr(ctx, &guard.expr);
        result = JsExpr::Ternary(Box::new(cond), Box::new(body), Box::new(result));
    }

    result
}

fn gen_guards_stmts(ctx: &CodegenCtx, guards: &[Guard]) -> Vec<JsStmt> {
    let mut stmts = Vec::new();
    for guard in guards {
        let cond = gen_guard_condition(ctx, &guard.patterns);
        let body = gen_expr(ctx, &guard.expr);
        stmts.push(JsStmt::If(
            cond,
            vec![JsStmt::Return(body)],
            None,
        ));
    }
    stmts.push(JsStmt::Throw(JsExpr::App(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )));
    stmts
}

fn gen_guard_condition(ctx: &CodegenCtx, patterns: &[GuardPattern]) -> JsExpr {
    let mut conditions: Vec<JsExpr> = Vec::new();
    for pattern in patterns {
        match pattern {
            GuardPattern::Boolean(expr) => {
                conditions.push(gen_expr(ctx, expr));
            }
            GuardPattern::Pattern(_binder, expr) => {
                // Pattern guard: `pat <- expr` becomes a check + binding
                // For now, just evaluate the expression (simplified)
                conditions.push(gen_expr(ctx, expr));
            }
        }
    }

    if conditions.len() == 1 {
        conditions.into_iter().next().unwrap()
    } else {
        conditions
            .into_iter()
            .reduce(|a, b| JsExpr::Binary(JsBinaryOp::And, Box::new(a), Box::new(b)))
            .unwrap_or(JsExpr::BoolLit(true))
    }
}

// ===== Curried functions =====

fn gen_curried_function(ctx: &CodegenCtx, binders: &[Binder], body: Vec<JsStmt>) -> JsExpr {
    if binders.is_empty() {
        // No binders: return IIFE
        return JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], body)),
            vec![],
        );
    }

    // Build from inside out
    let mut current_body = body;

    for binder in binders.iter().rev() {
        match binder {
            Binder::Var { name, .. } => {
                let param = ident_to_js(name.value);
                current_body = vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![param],
                    current_body,
                ))];
            }
            Binder::Wildcard { .. } => {
                let param = ctx.fresh_name("_");
                current_body = vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![param],
                    current_body,
                ))];
            }
            _ => {
                // Complex binder: introduce a parameter and pattern match
                let param = ctx.fresh_name("v");
                let mut match_body = Vec::new();
                let (cond, bindings) = gen_binder_match(ctx, binder, &JsExpr::Var(param.clone()));
                match_body.extend(bindings);

                if let Some(cond) = cond {
                    let then_body = current_body.clone();
                    match_body.push(JsStmt::If(cond, then_body, None));
                    match_body.push(JsStmt::Throw(JsExpr::App(
                        Box::new(JsExpr::Var("Error".to_string())),
                        vec![JsExpr::StringLit("Failed pattern match".to_string())],
                    )));
                } else {
                    match_body.extend(current_body.clone());
                }

                current_body = vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![param],
                    match_body,
                ))];
            }
        }
    }

    // Unwrap the outermost Return
    if current_body.len() == 1 {
        if let JsStmt::Return(func) = &current_body[0] {
            return func.clone();
        }
    }
    JsExpr::Function(None, vec![], current_body)
}

fn gen_curried_function_from_stmts(
    ctx: &CodegenCtx,
    binders: &[Binder],
    body: Vec<JsStmt>,
) -> JsExpr {
    gen_curried_function(ctx, binders, body)
}

// ===== Let bindings =====

fn gen_let_bindings(ctx: &CodegenCtx, bindings: &[LetBinding], stmts: &mut Vec<JsStmt>) {
    for binding in bindings {
        match binding {
            LetBinding::Value { binder, expr, .. } => {
                let val = gen_expr(ctx, expr);
                match binder {
                    Binder::Var { name, .. } => {
                        let js_name = ident_to_js(name.value);
                        stmts.push(JsStmt::VarDecl(js_name, Some(val)));
                    }
                    _ => {
                        // Pattern binding: destructure
                        let tmp = ctx.fresh_name("v");
                        stmts.push(JsStmt::VarDecl(tmp.clone(), Some(val)));
                        let (_, bindings) = gen_binder_match(ctx, binder, &JsExpr::Var(tmp));
                        stmts.extend(bindings);
                    }
                }
            }
            LetBinding::Signature { .. } => {
                // Type signatures produce no JS
            }
        }
    }
}

// ===== Case expressions =====

fn gen_case_expr(ctx: &CodegenCtx, scrutinees: &[Expr], alts: &[CaseAlternative]) -> JsExpr {
    // Introduce temp vars for scrutinees
    let scrut_names: Vec<String> = (0..scrutinees.len())
        .map(|i| ctx.fresh_name(&format!("case{i}_")))
        .collect();

    let mut iife_body: Vec<JsStmt> = scrut_names
        .iter()
        .zip(scrutinees.iter())
        .map(|(name, expr)| JsStmt::VarDecl(name.clone(), Some(gen_expr(ctx, expr))))
        .collect();

    for alt in alts {
        let (cond, bindings) = gen_binders_match(ctx, &alt.binders, &scrut_names);
        let mut alt_body = Vec::new();
        alt_body.extend(bindings);

        let result_stmts = gen_guarded_expr_stmts(ctx, &alt.result);
        alt_body.extend(result_stmts);

        if let Some(cond) = cond {
            iife_body.push(JsStmt::If(cond, alt_body, None));
        } else {
            iife_body.extend(alt_body);
            // Unconditional match — no need to check further alternatives
            break;
        }
    }

    iife_body.push(JsStmt::Throw(JsExpr::App(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )));

    JsExpr::App(
        Box::new(JsExpr::Function(None, vec![], iife_body)),
        vec![],
    )
}

// ===== Pattern matching =====

/// Generate match conditions and variable bindings for a list of binders
/// against a list of scrutinee variable names.
fn gen_binders_match(
    ctx: &CodegenCtx,
    binders: &[Binder],
    scrut_names: &[String],
) -> (Option<JsExpr>, Vec<JsStmt>) {
    let mut conditions: Vec<JsExpr> = Vec::new();
    let mut all_bindings: Vec<JsStmt> = Vec::new();

    for (binder, name) in binders.iter().zip(scrut_names.iter()) {
        let (cond, bindings) = gen_binder_match(ctx, binder, &JsExpr::Var(name.clone()));
        if let Some(c) = cond {
            conditions.push(c);
        }
        all_bindings.extend(bindings);
    }

    let combined_cond = if conditions.is_empty() {
        None
    } else if conditions.len() == 1 {
        Some(conditions.into_iter().next().unwrap())
    } else {
        Some(
            conditions
                .into_iter()
                .reduce(|a, b| JsExpr::Binary(JsBinaryOp::And, Box::new(a), Box::new(b)))
                .unwrap(),
        )
    };

    (combined_cond, all_bindings)
}

/// Generate match condition and bindings for a single binder against a scrutinee expression.
fn gen_binder_match(
    ctx: &CodegenCtx,
    binder: &Binder,
    scrutinee: &JsExpr,
) -> (Option<JsExpr>, Vec<JsStmt>) {
    match binder {
        Binder::Wildcard { .. } => (None, vec![]),

        Binder::Var { name, .. } => {
            let js_name = ident_to_js(name.value);
            (
                None,
                vec![JsStmt::VarDecl(js_name, Some(scrutinee.clone()))],
            )
        }

        Binder::Literal { lit, .. } => {
            let cond = match lit {
                Literal::Int(n) => JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::IntLit(*n)),
                ),
                Literal::Float(n) => JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::NumericLit(*n)),
                ),
                Literal::String(s) => JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::StringLit(s.clone())),
                ),
                Literal::Char(c) => JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::StringLit(c.to_string())),
                ),
                Literal::Boolean(b) => JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::BoolLit(*b)),
                ),
                Literal::Array(_) => {
                    // Array literal in binder is not standard, skip condition
                    JsExpr::BoolLit(true)
                }
            };
            (Some(cond), vec![])
        }

        Binder::Constructor { name, args, .. } => {
            let ctor_name = name.name;

            // Check if this is a newtype constructor (erased)
            if ctx.newtype_names.contains(&ctor_name) {
                if args.len() == 1 {
                    return gen_binder_match(ctx, &args[0], scrutinee);
                }
                return (None, vec![]);
            }

            let mut conditions = Vec::new();
            let mut bindings = Vec::new();

            // Determine if we need an instanceof check (sum types)
            let is_sum = if let Some((parent, _, _)) = ctx.ctor_details.get(&ctor_name) {
                ctx.data_constructors
                    .get(parent)
                    .map_or(false, |ctors| ctors.len() > 1)
            } else {
                false
            };

            if is_sum {
                let ctor_ref = gen_qualified_ref_raw(ctx, name);
                conditions.push(JsExpr::InstanceOf(
                    Box::new(scrutinee.clone()),
                    Box::new(ctor_ref),
                ));
            }

            // Bind constructor fields
            for (i, arg) in args.iter().enumerate() {
                let field_access = JsExpr::Indexer(
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::StringLit(format!("value{i}"))),
                );
                let (sub_cond, sub_bindings) = gen_binder_match(ctx, arg, &field_access);
                if let Some(c) = sub_cond {
                    conditions.push(c);
                }
                bindings.extend(sub_bindings);
            }

            let combined = if conditions.is_empty() {
                None
            } else if conditions.len() == 1 {
                Some(conditions.into_iter().next().unwrap())
            } else {
                Some(
                    conditions
                        .into_iter()
                        .reduce(|a, b| JsExpr::Binary(JsBinaryOp::And, Box::new(a), Box::new(b)))
                        .unwrap(),
                )
            };

            (combined, bindings)
        }

        Binder::Record { fields, .. } => {
            let mut conditions = Vec::new();
            let mut bindings = Vec::new();

            for field in fields {
                let label = interner::resolve(field.label.value).unwrap_or_default();
                let field_access = JsExpr::Indexer(
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::StringLit(label.clone())),
                );

                match &field.binder {
                    Some(b) => {
                        let (sub_cond, sub_bindings) = gen_binder_match(ctx, b, &field_access);
                        if let Some(c) = sub_cond {
                            conditions.push(c);
                        }
                        bindings.extend(sub_bindings);
                    }
                    None => {
                        // Punned: { x } means bind x to scrutinee.x
                        let js_name = ident_to_js(field.label.value);
                        bindings.push(JsStmt::VarDecl(js_name, Some(field_access)));
                    }
                }
            }

            let combined = combine_conditions(conditions);
            (combined, bindings)
        }

        Binder::As { name, binder, .. } => {
            let js_name = ident_to_js(name.value);
            let mut bindings = vec![JsStmt::VarDecl(js_name, Some(scrutinee.clone()))];
            let (cond, sub_bindings) = gen_binder_match(ctx, binder, scrutinee);
            bindings.extend(sub_bindings);
            (cond, bindings)
        }

        Binder::Parens { binder, .. } => gen_binder_match(ctx, binder, scrutinee),

        Binder::Array { elements, .. } => {
            let mut conditions = Vec::new();
            let mut bindings = Vec::new();

            // Check array length
            conditions.push(JsExpr::Binary(
                JsBinaryOp::StrictEq,
                Box::new(JsExpr::Indexer(
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::StringLit("length".to_string())),
                )),
                Box::new(JsExpr::IntLit(elements.len() as i64)),
            ));

            // Match each element
            for (i, elem) in elements.iter().enumerate() {
                let elem_access = JsExpr::Indexer(
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::IntLit(i as i64)),
                );
                let (sub_cond, sub_bindings) = gen_binder_match(ctx, elem, &elem_access);
                if let Some(c) = sub_cond {
                    conditions.push(c);
                }
                bindings.extend(sub_bindings);
            }

            let combined = combine_conditions(conditions);
            (combined, bindings)
        }

        Binder::Op { left, op, right, .. } => {
            // Operator binder: desugar to constructor match
            // e.g. `x : xs` → `Cons x xs`
            let op_name = &op.value;

            // Check if this is a constructor operator
            let is_function_op = ctx.function_op_aliases.contains(&op_name.name);

            if !is_function_op {
                // Constructor operator — treat as constructor binder with 2 args
                let ctor_binder = Binder::Constructor {
                    span: binder.span(),
                    name: op_name.clone(),
                    args: vec![*left.clone(), *right.clone()],
                };
                return gen_binder_match(ctx, &ctor_binder, scrutinee);
            }

            // Function operator in pattern — not really valid but handle gracefully
            (None, vec![])
        }

        Binder::Typed { binder, .. } => {
            // Type annotations are erased
            gen_binder_match(ctx, binder, scrutinee)
        }
    }
}

fn combine_conditions(conditions: Vec<JsExpr>) -> Option<JsExpr> {
    if conditions.is_empty() {
        None
    } else if conditions.len() == 1 {
        Some(conditions.into_iter().next().unwrap())
    } else {
        Some(
            conditions
                .into_iter()
                .reduce(|a, b| JsExpr::Binary(JsBinaryOp::And, Box::new(a), Box::new(b)))
                .unwrap(),
        )
    }
}

// ===== Record update =====

fn gen_record_update(ctx: &CodegenCtx, base: &Expr, updates: &[RecordUpdate]) -> JsExpr {
    // Shallow copy + overwrite: (function() { var $copy = {}; for (var k in base) { $copy[k] = base[k]; } $copy.field = new_value; return $copy; })()
    let base_expr = gen_expr(ctx, base);
    let copy_name = ctx.fresh_name("copy");
    let src_name = ctx.fresh_name("src");

    let mut iife_body = vec![
        JsStmt::VarDecl(src_name.clone(), Some(base_expr)),
        JsStmt::VarDecl(copy_name.clone(), Some(JsExpr::ObjectLit(vec![]))),
        JsStmt::ForIn(
            "k".to_string(),
            JsExpr::Var(src_name.clone()),
            vec![JsStmt::Assign(
                JsExpr::Indexer(
                    Box::new(JsExpr::Var(copy_name.clone())),
                    Box::new(JsExpr::Var("k".to_string())),
                ),
                JsExpr::Indexer(
                    Box::new(JsExpr::Var(src_name.clone())),
                    Box::new(JsExpr::Var("k".to_string())),
                ),
            )],
        ),
    ];

    for update in updates {
        let label = interner::resolve(update.label.value).unwrap_or_default();
        let value = gen_expr(ctx, &update.value);
        iife_body.push(JsStmt::Assign(
            JsExpr::Indexer(
                Box::new(JsExpr::Var(copy_name.clone())),
                Box::new(JsExpr::StringLit(label)),
            ),
            value,
        ));
    }

    iife_body.push(JsStmt::Return(JsExpr::Var(copy_name)));

    JsExpr::App(
        Box::new(JsExpr::Function(None, vec![], iife_body)),
        vec![],
    )
}

// ===== Do notation =====

fn gen_do_expr(ctx: &CodegenCtx, statements: &[DoStatement], qual_mod: Option<&Ident>) -> JsExpr {
    // Do notation desugars to bind chains:
    // do { x <- a; b } → bind(a)(function(x) { return b; })
    // do { a; b } → discard(a)(b) or bind(a)(function(_) { return b; })

    let bind_ref = make_qualified_ref(ctx, qual_mod, "bind");

    if statements.is_empty() {
        return JsExpr::Var("undefined".to_string());
    }

    gen_do_stmts(ctx, statements, &bind_ref, qual_mod)
}

fn gen_do_stmts(
    ctx: &CodegenCtx,
    statements: &[DoStatement],
    bind_ref: &JsExpr,
    qual_mod: Option<&Ident>,
) -> JsExpr {
    if statements.len() == 1 {
        match &statements[0] {
            DoStatement::Discard { expr, .. } => return gen_expr(ctx, expr),
            DoStatement::Bind { expr, .. } => {
                return gen_expr(ctx, expr);
            }
            DoStatement::Let { .. } => {
                return JsExpr::Var("undefined".to_string());
            }
        }
    }

    let (first, rest) = statements.split_first().unwrap();

    match first {
        DoStatement::Discard { expr, .. } => {
            let action = gen_expr(ctx, expr);
            let rest_expr = gen_do_stmts(ctx, rest, bind_ref, qual_mod);
            // bind(action)(function(_) { return rest; })
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(bind_ref.clone()),
                    vec![action],
                )),
                vec![JsExpr::Function(
                    None,
                    vec![ctx.fresh_name("_")],
                    vec![JsStmt::Return(rest_expr)],
                )],
            )
        }
        DoStatement::Bind { binder, expr, .. } => {
            let action = gen_expr(ctx, expr);
            let rest_expr = gen_do_stmts(ctx, rest, bind_ref, qual_mod);

            let param = match binder {
                Binder::Var { name, .. } => ident_to_js(name.value),
                _ => ctx.fresh_name("v"),
            };

            let mut body = Vec::new();

            // If complex binder, add destructuring
            if !matches!(binder, Binder::Var { .. } | Binder::Wildcard { .. }) {
                let (_, bindings) = gen_binder_match(ctx, binder, &JsExpr::Var(param.clone()));
                body.extend(bindings);
            }
            body.push(JsStmt::Return(rest_expr));

            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(bind_ref.clone()),
                    vec![action],
                )),
                vec![JsExpr::Function(None, vec![param], body)],
            )
        }
        DoStatement::Let { bindings, .. } => {
            // Let bindings in do: wrap rest in an IIFE with the bindings
            let rest_expr = gen_do_stmts(ctx, rest, bind_ref, qual_mod);
            let mut iife_body = Vec::new();
            gen_let_bindings(ctx, bindings, &mut iife_body);
            iife_body.push(JsStmt::Return(rest_expr));
            JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            )
        }
    }
}

// ===== Ado notation =====

fn gen_ado_expr(
    ctx: &CodegenCtx,
    statements: &[DoStatement],
    result: &Expr,
    qual_mod: Option<&Ident>,
) -> JsExpr {
    // Ado desugars to apply/map chains
    let map_ref = make_qualified_ref(ctx, qual_mod, "map");
    let apply_ref = make_qualified_ref(ctx, qual_mod, "apply");

    if statements.is_empty() {
        // ado in expr → pure(expr)
        let pure_ref = make_qualified_ref(ctx, qual_mod, "pure");
        let result_expr = gen_expr(ctx, result);
        return JsExpr::App(Box::new(pure_ref), vec![result_expr]);
    }

    let result_expr = gen_expr(ctx, result);

    // Build a function that takes all bound variables and produces the result
    let mut params = Vec::new();
    for stmt in statements {
        if let DoStatement::Bind { binder, .. } = stmt {
            match binder {
                Binder::Var { name, .. } => params.push(ident_to_js(name.value)),
                _ => params.push(ctx.fresh_name("v")),
            }
        }
    }

    // Start with map(fn)(first_action), then apply each subsequent action
    let mut current = if let Some(DoStatement::Bind { expr, .. }) = statements.first() {
        let action = gen_expr(ctx, expr);
        let all_params = params.clone();
        let func = gen_curried_lambda(&all_params, result_expr);
        JsExpr::App(
            Box::new(JsExpr::App(Box::new(map_ref), vec![func])),
            vec![action],
        )
    } else {
        return gen_expr(ctx, result);
    };

    for stmt in statements.iter().skip(1) {
        if let DoStatement::Bind { expr, .. } = stmt {
            let action = gen_expr(ctx, expr);
            current = JsExpr::App(
                Box::new(JsExpr::App(Box::new(apply_ref.clone()), vec![current])),
                vec![action],
            );
        }
    }

    current
}

fn gen_curried_lambda(params: &[String], body: JsExpr) -> JsExpr {
    if params.is_empty() {
        return body;
    }

    let mut result = body;
    for param in params.iter().rev() {
        result = JsExpr::Function(
            None,
            vec![param.clone()],
            vec![JsStmt::Return(result)],
        );
    }
    result
}

fn make_qualified_ref(_ctx: &CodegenCtx, qual_mod: Option<&Ident>, name: &str) -> JsExpr {
    if let Some(mod_sym) = qual_mod {
        let mod_str = interner::resolve(*mod_sym).unwrap_or_default();
        let js_mod = any_name_to_js(&mod_str.replace('.', "_"));
        JsExpr::ModuleAccessor(js_mod, any_name_to_js(name))
    } else {
        // Unqualified: look for it in scope
        JsExpr::Var(any_name_to_js(name))
    }
}

