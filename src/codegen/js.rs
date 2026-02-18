/// CST-to-JavaScript code generation.
///
/// Translates the PureScript CST directly to a JS AST, which is then
/// pretty-printed to ES module JavaScript. Mirrors the original PureScript
/// compiler's Language.PureScript.CodeGen.JS module.

use std::cell::{Cell, RefCell};
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
    registry: &'a ModuleRegistry,
    /// Module name as dot-separated string (e.g. "Data.Maybe")
    #[allow(dead_code)]
    module_name: &'a str,
    /// Module name parts as symbols
    #[allow(dead_code)]
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
    /// Names declared locally in this module (values, constructors, instances)
    local_names: HashSet<Symbol>,
    /// Import map: module_parts → JS variable name
    import_map: HashMap<Vec<Symbol>, String>,
    /// Unqualified name → source module parts (for cross-module reference resolution)
    name_source: HashMap<Symbol, Vec<Symbol>>,
    /// Operator → (target_module_parts, target_function_name) for resolving operators
    operator_targets: HashMap<Symbol, (Option<Vec<Symbol>>, Symbol)>,
    /// Counter for generating fresh variable names
    fresh_counter: Cell<usize>,
    /// Maps class method symbol → dict expression, set while generating constrained function bodies.
    /// e.g. `myShow` → `JsExpr::Var("dictMyShow")` when inside `showValue :: MyShow a => a -> String`.
    /// For superclass methods, stores chained accessors like `dictAlternative.Applicative0().Apply0()`.
    constraint_dicts: RefCell<HashMap<Symbol, JsExpr>>,
    /// Maps class name → dict expression. Used by `find_dict_for_class` to resolve dicts
    /// for classes that may have no methods (e.g. `Alternative` which only has superclass constraints).
    class_dicts: RefCell<HashMap<Symbol, JsExpr>>,
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
    // Phase 1: Collect local names
    let mut local_names: HashSet<Symbol> = HashSet::new();
    let mut foreign_imports_set: HashSet<Symbol> = HashSet::new();
    for decl in &module.decls {
        match decl {
            Decl::Value { name, .. } => { local_names.insert(name.value); }
            Decl::Data { constructors, .. } => {
                for ctor in constructors {
                    local_names.insert(ctor.name.value);
                }
            }
            Decl::Newtype { constructor, .. } => { local_names.insert(constructor.value); }
            Decl::Foreign { name, .. } => {
                local_names.insert(name.value);
                foreign_imports_set.insert(name.value);
            }
            Decl::Instance { name: Some(n), .. } => { local_names.insert(n.value); }
            _ => {}
        }
    }

    // Phase 2: Build name resolution map (unqualified name → source module)
    let mut name_source: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    let mut import_map: HashMap<Vec<Symbol>, String> = HashMap::new();
    let mut operator_targets: HashMap<Symbol, (Option<Vec<Symbol>>, Symbol)> = HashMap::new();

    // Collect operator → target from local fixity declarations
    for decl in &module.decls {
        if let Decl::Fixity { target, operator, is_type: false, .. } = decl {
            let target_module = target.module.map(|m| {
                let mod_str = interner::resolve(m).unwrap_or_default();
                mod_str.split('.').map(|s| interner::intern(s)).collect::<Vec<_>>()
            });
            operator_targets.insert(operator.value, (target_module, target.name));
        }
    }

    // Build import map and resolve unqualified names from imports
    let mut imports = Vec::new();
    for imp in &module.imports {
        let parts = &imp.module.parts;
        // Skip Prim imports (built-in types, no JS module)
        if !parts.is_empty() {
            let first = interner::resolve(parts[0]).unwrap_or_default();
            if first == "Prim" {
                continue;
            }
        }
        // Skip self-imports
        if *parts == module_parts {
            continue;
        }

        // Register import JS variable name
        if !import_map.contains_key(parts) {
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
            import_map.insert(parts.clone(), js_name);
        }

        // Resolve names from this import into name_source map
        if let Some(imp_exports) = registry.lookup(parts) {
            match &imp.imports {
                None => {
                    // Open import: `import Data.Maybe` — all exported names come from here
                    // Only register if not already claimed by a more specific import
                    for name in imp_exports.values.keys() {
                        if !local_names.contains(name) {
                            name_source.entry(*name).or_insert_with(|| parts.clone());
                        }
                    }
                    for name in imp_exports.ctor_details.keys() {
                        if !local_names.contains(name) {
                            name_source.entry(*name).or_insert_with(|| parts.clone());
                        }
                    }
                    for name in imp_exports.class_methods.keys() {
                        if !local_names.contains(name) {
                            name_source.entry(*name).or_insert_with(|| parts.clone());
                        }
                    }
                    // Also import operator targets
                    for (op, target) in &imp_exports.operator_targets {
                        operator_targets.entry(*op).or_insert_with(|| target.clone());
                    }
                }
                Some(ImportList::Explicit(items)) => {
                    for item in items {
                        match item {
                            Import::Value(name) => {
                                if !local_names.contains(name) {
                                    name_source.insert(*name, parts.clone());
                                }
                                // Operators are parsed as Import::Value (e.g. `(<$>)`).
                                // If this name is an operator with a target, propagate it.
                                if let Some(target) = imp_exports.operator_targets.get(name) {
                                    operator_targets.entry(*name).or_insert_with(|| target.clone());
                                }
                            }
                            Import::Type(type_name, members) => {
                                // The type itself doesn't produce JS, but its constructors do
                                if let Some(DataMembers::All) = members {
                                    if let Some(ctors) = imp_exports.data_constructors.get(type_name) {
                                        for ctor in ctors {
                                            if !local_names.contains(ctor) {
                                                name_source.insert(*ctor, parts.clone());
                                            }
                                        }
                                    }
                                } else if let Some(DataMembers::Explicit(ctors)) = members {
                                    for ctor in ctors {
                                        if !local_names.contains(ctor) {
                                            name_source.insert(*ctor, parts.clone());
                                        }
                                    }
                                }
                            }
                            Import::Class(class_name) => {
                                // Import class methods
                                for (method, (cls, _)) in &imp_exports.class_methods {
                                    if *cls == *class_name && !local_names.contains(method) {
                                        name_source.insert(*method, parts.clone());
                                    }
                                }
                            }
                            Import::TypeOp(_) => {}
                        }
                    }
                }
                Some(ImportList::Hiding(items)) => {
                    let hidden: HashSet<Symbol> = items.iter().filter_map(|item| {
                        match item {
                            Import::Value(name) => Some(*name),
                            _ => None,
                        }
                    }).collect();
                    for name in imp_exports.values.keys() {
                        if !hidden.contains(name) && !local_names.contains(name) {
                            name_source.entry(*name).or_insert_with(|| parts.clone());
                        }
                    }
                    for name in imp_exports.ctor_details.keys() {
                        if !hidden.contains(name) && !local_names.contains(name) {
                            name_source.entry(*name).or_insert_with(|| parts.clone());
                        }
                    }
                    for name in imp_exports.class_methods.keys() {
                        if !hidden.contains(name) && !local_names.contains(name) {
                            name_source.entry(*name).or_insert_with(|| parts.clone());
                        }
                    }
                    // Propagate operator targets that aren't hidden
                    for (op, target) in &imp_exports.operator_targets {
                        if !hidden.contains(op) {
                            operator_targets.entry(*op).or_insert_with(|| target.clone());
                        }
                    }
                }
            }
        }
    }

    // Supplement operator_targets from operator_class_targets (more thoroughly propagated).
    // This ensures operators like <$> → map resolve even if operator_targets propagation missed them.
    for (op, method) in &exports.operator_class_targets {
        operator_targets.entry(*op).or_insert_with(|| (None, *method));
    }
    for imp in &module.imports {
        if let Some(imp_exports) = registry.lookup(&imp.module.parts) {
            for (op, method) in &imp_exports.operator_class_targets {
                operator_targets.entry(*op).or_insert_with(|| (None, *method));
            }
        }
    }

    let ctx = CodegenCtx {
        module,
        exports,
        registry,
        module_name,
        module_parts,
        newtype_names: &exports.newtype_names,
        ctor_details: &exports.ctor_details,
        data_constructors: &exports.data_constructors,
        function_op_aliases: &exports.function_op_aliases,
        foreign_imports: foreign_imports_set,
        local_names,
        import_map,
        name_source,
        operator_targets,
        fresh_counter: Cell::new(0),
        constraint_dicts: RefCell::new(HashMap::new()),
        class_dicts: RefCell::new(HashMap::new()),
    };

    let mut exported_names: Vec<String> = Vec::new();
    let mut foreign_re_exports: Vec<String> = Vec::new();

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

// ===== Constraint dictionary helpers =====

/// Look up the superclasses of a class from local exports or imported modules.
/// Returns Vec<(superclass_class_name, index)> matching the purs accessor convention.
fn lookup_superclasses(ctx: &CodegenCtx, class_name: Symbol) -> Vec<(Symbol, usize)> {
    if let Some(supers) = ctx.exports.class_superclasses.get(&class_name) {
        return supers.clone();
    }
    for imp in &ctx.module.imports {
        if let Some(imp_exports) = ctx.registry.lookup(&imp.module.parts) {
            if let Some(supers) = imp_exports.class_superclasses.get(&class_name) {
                return supers.clone();
            }
        }
    }
    Vec::new()
}

/// Recursively populate `dicts` with method → dict_expr mappings for `class_name`
/// and all its transitive superclasses.
///
/// For the root constraint, `dict_expr` is `JsExpr::Var("dictAlternative")`.
/// For superclasses, it chains accessors: `dictAlternative["Applicative0"]()`.
fn resolve_superclass_chain(
    ctx: &CodegenCtx,
    class_name: Symbol,
    dict_expr: JsExpr,
    dicts: &mut HashMap<Symbol, JsExpr>,
    class_dicts: &mut HashMap<Symbol, JsExpr>,
    visited: &mut HashSet<Symbol>,
) {
    if !visited.insert(class_name) {
        return;
    }

    // Map the class itself to its dict expression (for classes with no methods, like Alternative)
    class_dicts.entry(class_name).or_insert_with(|| dict_expr.clone());

    // Map all methods of this class to dict_expr
    for (method, (cls, _)) in &ctx.exports.class_methods {
        if *cls == class_name {
            dicts.entry(*method).or_insert_with(|| dict_expr.clone());
        }
    }
    for imp in &ctx.module.imports {
        if let Some(imp_exports) = ctx.registry.lookup(&imp.module.parts) {
            for (method, (cls, _)) in &imp_exports.class_methods {
                if *cls == class_name {
                    dicts.entry(*method).or_insert_with(|| dict_expr.clone());
                }
            }
        }
    }

    // Recurse into superclasses
    let superclasses = lookup_superclasses(ctx, class_name);
    for (sc_class, sc_index) in superclasses {
        let sc_name_str = interner::resolve(sc_class).unwrap_or_default();
        let accessor_name = format!("{sc_name_str}{sc_index}");
        // Build: dict_expr["Superclass0"]()
        let sc_expr = JsExpr::App(
            Box::new(JsExpr::Indexer(
                Box::new(dict_expr.clone()),
                Box::new(JsExpr::StringLit(accessor_name)),
            )),
            vec![],
        );
        resolve_superclass_chain(ctx, sc_class, sc_expr, dicts, class_dicts, visited);
    }
}

/// Populate `ctx.constraint_dicts` from a list of (class_name, type_args) constraints.
/// Returns the ordered list of dict parameter names to prepend to the function.
///
/// For each constraint, generates a parameter name like `dictMyShow` and recursively maps
/// all methods of the class and its superclasses to the appropriate dict expressions.
fn setup_constraint_dicts(
    ctx: &CodegenCtx,
    constraints: &[(Symbol, Vec<crate::typechecker::types::Type>)],
) -> Vec<String> {
    let mut dict_params: Vec<String> = Vec::new();
    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
    let mut new_dicts: HashMap<Symbol, JsExpr> = HashMap::new();

    for (class_name, _type_args) in constraints {
        let class_str = interner::resolve(*class_name).unwrap_or_default();
        let base_name = format!("dict{class_str}");
        let count = dict_name_counts.entry(base_name.clone()).or_insert(0);
        let dict_var = if *count == 0 {
            base_name.clone()
        } else {
            format!("{base_name}{count}")
        };
        *count += 1;
        dict_params.push(dict_var.clone());

        let dict_expr = JsExpr::Var(dict_var);
        let mut visited = HashSet::new();
        let mut new_class_dicts: HashMap<Symbol, JsExpr> = HashMap::new();
        resolve_superclass_chain(ctx, *class_name, dict_expr, &mut new_dicts, &mut new_class_dicts, &mut visited);
        ctx.class_dicts.borrow_mut().extend(new_class_dicts);
    }

    *ctx.constraint_dicts.borrow_mut() = new_dicts;
    dict_params
}

/// Same as `setup_constraint_dicts` but takes CST `Constraint` objects (for instance declarations).
fn setup_constraint_dicts_from_cst(
    ctx: &CodegenCtx,
    constraints: &[crate::cst::Constraint],
) -> Vec<String> {
    let mut dict_params: Vec<String> = Vec::new();
    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
    let mut new_dicts: HashMap<Symbol, JsExpr> = HashMap::new();

    for constraint in constraints {
        let class_name = constraint.class.name;
        let class_str = interner::resolve(class_name).unwrap_or_default();
        let base_name = format!("dict{class_str}");
        let count = dict_name_counts.entry(base_name.clone()).or_insert(0);
        let dict_var = if *count == 0 {
            base_name.clone()
        } else {
            format!("{base_name}{count}")
        };
        *count += 1;
        dict_params.push(dict_var.clone());

        let dict_expr = JsExpr::Var(dict_var);
        let mut visited = HashSet::new();
        let mut new_class_dicts: HashMap<Symbol, JsExpr> = HashMap::new();
        resolve_superclass_chain(ctx, class_name, dict_expr, &mut new_dicts, &mut new_class_dicts, &mut visited);
        ctx.class_dicts.borrow_mut().extend(new_class_dicts);
    }

    *ctx.constraint_dicts.borrow_mut() = new_dicts;
    dict_params
}

/// Wrap a JS expression in curried dict-parameter lambdas.
/// `dict_params = ["dictShow", "dictEq"]` wraps `expr` as:
/// `function(dictShow) { return function(dictEq) { return expr; }; }`
fn wrap_expr_with_dict_params(expr: JsExpr, dict_params: &[String]) -> JsExpr {
    let mut result = expr;
    for dict_var in dict_params.iter().rev() {
        result = JsExpr::Function(
            None,
            vec![dict_var.clone()],
            vec![JsStmt::Return(result)],
        );
    }
    result
}

// ===== Value declarations =====

fn gen_value_decl(ctx: &CodegenCtx, name: Symbol, decls: &[&Decl]) -> Vec<JsStmt> {
    // Set up constraint dicts if this function has type class constraints.
    let dict_params = match ctx.exports.signature_constraints.get(&name) {
        Some(constraints) if !constraints.is_empty() => {
            setup_constraint_dicts(ctx, constraints)
        }
        _ => vec![],
    };

    let stmts = gen_value_decl_inner(ctx, name, decls);

    // Clear constraint dicts after body generation.
    ctx.constraint_dicts.borrow_mut().clear();
    ctx.class_dicts.borrow_mut().clear();

    if dict_params.is_empty() {
        return stmts;
    }

    // Wrap each generated VarDecl's expression with the dict param lambdas.
    stmts
        .into_iter()
        .map(|stmt| match stmt {
            JsStmt::VarDecl(n, Some(expr)) => {
                JsStmt::VarDecl(n, Some(wrap_expr_with_dict_params(expr, &dict_params)))
            }
            other => other,
        })
        .collect()
}

fn gen_value_decl_inner(ctx: &CodegenCtx, name: Symbol, decls: &[&Decl]) -> Vec<JsStmt> {
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
    let Decl::Instance { name, members, constraints, .. } = decl else { return vec![] };

    // Set up constraint dicts for instance constraints (e.g. `instance (Eq a) => Show (Maybe a)`).
    // This lets method bodies inside the instance dispatch to constraint dicts automatically.
    let dict_params = if !constraints.is_empty() {
        setup_constraint_dicts_from_cst(ctx, constraints)
    } else {
        vec![]
    };

    // Instances become object literals with method implementations
    let instance_name = match name {
        Some(n) => ident_to_js(n.value),
        None => ctx.fresh_name("instance_"),
    };

    // Group member equations by method name to handle multi-equation instance methods.
    // e.g. `describe true = "true"; describe false = "false"` → single `describe` field.
    let mut method_groups: HashMap<Symbol, Vec<&Decl>> = HashMap::new();
    let mut method_order: Vec<Symbol> = Vec::new();
    for member in members {
        if let Decl::Value { name: method_name, .. } = member {
            if !method_groups.contains_key(&method_name.value) {
                method_order.push(method_name.value);
            }
            method_groups.entry(method_name.value).or_default().push(member);
        }
    }

    let mut fields = Vec::new();
    for method_name_sym in method_order {
        let method_js = ident_to_js(method_name_sym);
        let method_decls = method_groups.remove(&method_name_sym).unwrap_or_default();

        let method_expr = if method_decls.len() == 1 {
            // Single-equation: generate directly.
            if let Decl::Value { binders, guarded, where_clause, .. } = method_decls[0] {
                if binders.is_empty() && where_clause.is_empty() {
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
                }
            } else {
                continue;
            }
        } else {
            // Multi-equation: reuse gen_multi_equation and extract the function expression.
            let stmts = gen_multi_equation(ctx, &method_js, &method_decls);
            match stmts.into_iter().next() {
                Some(JsStmt::VarDecl(_, Some(expr))) => expr,
                _ => JsExpr::Var("undefined".to_string()),
            }
        };

        fields.push((method_js, method_expr));
    }

    // Clear constraint dicts after building the instance body.
    ctx.constraint_dicts.borrow_mut().clear();
    ctx.class_dicts.borrow_mut().clear();

    let obj = JsExpr::ObjectLit(fields);

    // Wrap in dict-param lambdas if the instance has constraints.
    let instance_expr = if dict_params.is_empty() {
        obj
    } else {
        wrap_expr_with_dict_params(obj, &dict_params)
    };

    vec![JsStmt::VarDecl(instance_name, Some(instance_expr))]
}

// ===== Call-site dictionary passing =====

/// Look up the type constraints for a function from local exports or imported modules.
fn lookup_function_constraints(
    ctx: &CodegenCtx,
    name: Symbol,
) -> Vec<(Symbol, Vec<crate::typechecker::types::Type>)> {
    if let Some(constraints) = ctx.exports.signature_constraints.get(&name) {
        return constraints.clone();
    }
    for imp in &ctx.module.imports {
        if let Some(imp_exports) = ctx.registry.lookup(&imp.module.parts) {
            if let Some(constraints) = imp_exports.signature_constraints.get(&name) {
                return constraints.clone();
            }
        }
    }
    Vec::new()
}

/// Find a dictionary expression for a given class by checking class_dicts first (handles
/// classes with no methods like Alternative), then falling back to searching constraint_dicts
/// for any method belonging to that class.
fn find_dict_for_class(ctx: &CodegenCtx, class_name: Symbol) -> Option<JsExpr> {
    // Direct class→dict lookup (handles classes with no methods)
    {
        let cd = ctx.class_dicts.borrow();
        if let Some(dict_expr) = cd.get(&class_name) {
            return Some(dict_expr.clone());
        }
    }

    // Fallback: find via method mapping
    let dicts = ctx.constraint_dicts.borrow();
    for (method, (cls, _)) in &ctx.exports.class_methods {
        if *cls == class_name {
            if let Some(dict_expr) = dicts.get(method) {
                return Some(dict_expr.clone());
            }
        }
    }
    for imp in &ctx.module.imports {
        if let Some(imp_exports) = ctx.registry.lookup(&imp.module.parts) {
            for (method, (cls, _)) in &imp_exports.class_methods {
                if *cls == class_name {
                    if let Some(dict_expr) = dicts.get(method) {
                        return Some(dict_expr.clone());
                    }
                }
            }
        }
    }
    None
}

/// If `name` refers to a constrained function, wrap `base_expr` with dictionary argument
/// applications. For example, `many` with constraints `[Alternative, Lazy]` becomes
/// `many(dictAlternative)(dictLazy)`.
fn maybe_insert_dict_args(ctx: &CodegenCtx, name: Symbol, base_expr: JsExpr) -> JsExpr {
    // Don't insert dicts for class methods (already dispatched through dict.method)
    {
        let dicts = ctx.constraint_dicts.borrow();
        if dicts.contains_key(&name) {
            return base_expr;
        }
    }

    // Look up if this function has constraints
    let constraints = lookup_function_constraints(ctx, name);
    if constraints.is_empty() {
        return base_expr;
    }

    // Try to resolve each constraint to a dictionary expression from current scope
    let mut result = base_expr;
    for (class_name, _type_args) in &constraints {
        if let Some(dict_expr) = find_dict_for_class(ctx, *class_name) {
            result = JsExpr::App(Box::new(result), vec![dict_expr]);
        }
        // If we can't find a dict, skip it — partial application will still
        // be correct for the dicts we can resolve.
    }
    result
}

// ===== Expression translation =====

fn gen_expr(ctx: &CodegenCtx, expr: &Expr) -> JsExpr {
    match expr {
        Expr::Var { name, .. } => {
            let base = gen_qualified_ref(ctx, name);
            maybe_insert_dict_args(ctx, name.name, base)
        }

        Expr::Constructor { name, .. } => {
            let ctor_name = name.name;
            let base = gen_qualified_ref(ctx, name);

            // Determine accessor: .value for nullary, .create for n-ary
            let is_nullary = if let Some((_, _, fields)) = ctx.ctor_details.get(&ctor_name) {
                fields.is_empty()
            } else {
                // Check in imported modules
                is_nullary_ctor_from_imports(ctx, ctor_name)
            };

            let is_newtype = ctx.newtype_names.contains(&ctor_name)
                || is_newtype_from_imports(ctx, ctor_name);

            if is_newtype {
                JsExpr::Indexer(
                    Box::new(base),
                    Box::new(JsExpr::StringLit("create".to_string())),
                )
            } else if is_nullary {
                JsExpr::Indexer(
                    Box::new(base),
                    Box::new(JsExpr::StringLit("value".to_string())),
                )
            } else {
                JsExpr::Indexer(
                    Box::new(base),
                    Box::new(JsExpr::StringLit("create".to_string())),
                )
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
            let op_ref = resolve_operator(ctx, &op.value);
            let l = gen_expr(ctx, left);
            let r = gen_expr(ctx, right);
            JsExpr::App(
                Box::new(JsExpr::App(Box::new(op_ref), vec![l])),
                vec![r],
            )
        }

        Expr::OpParens { op, .. } => resolve_operator(ctx, &op.value),

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

/// Resolve a qualified or unqualified reference to a JS expression.
/// For unqualified names, uses the name resolution map to find the source module.
fn gen_qualified_ref(ctx: &CodegenCtx, qident: &QualifiedIdent) -> JsExpr {
    let name = qident.name;
    let js_name = ident_to_js(name);

    if let Some(mod_sym) = &qident.module {
        // Already qualified — resolve through import map
        return resolve_module_ref(ctx, *mod_sym, &js_name);
    }

    // Unqualified: check local first, then imports

    // Foreign imports: $foreign.name
    if ctx.foreign_imports.contains(&name) {
        return JsExpr::ModuleAccessor("$foreign".to_string(), js_name);
    }

    // Constraint dicts: if inside a constrained function and this name is a class method,
    // emit `dictExpr["methodName"]` instead of a bare reference.
    {
        let dicts = ctx.constraint_dicts.borrow();
        if let Some(dict_expr) = dicts.get(&name) {
            return JsExpr::Indexer(
                Box::new(dict_expr.clone()),
                Box::new(JsExpr::StringLit(js_name)),
            );
        }
    }

    // Local names: bare variable
    if ctx.local_names.contains(&name) {
        return JsExpr::Var(js_name);
    }

    // Cross-module: look up in name resolution map
    if let Some(source_parts) = ctx.name_source.get(&name) {
        if let Some(js_mod) = ctx.import_map.get(source_parts) {
            return JsExpr::ModuleAccessor(js_mod.clone(), js_name);
        }
    }

    // Fallback: emit as bare variable (may be a lambda-bound or let-bound name)
    JsExpr::Var(js_name)
}

/// Check if a constructor from an imported module is nullary.
fn is_nullary_ctor_from_imports(ctx: &CodegenCtx, ctor_name: Symbol) -> bool {
    if let Some(source_parts) = ctx.name_source.get(&ctor_name) {
        if let Some(exports) = ctx.registry.lookup(source_parts) {
            if let Some((_, _, fields)) = exports.ctor_details.get(&ctor_name) {
                return fields.is_empty();
            }
        }
    }
    // Default: assume non-nullary (safer — produces .create)
    false
}

/// Check if a constructor from an imported module belongs to a sum type (multiple constructors).
fn is_sum_ctor_from_imports(ctx: &CodegenCtx, ctor_name: Symbol) -> bool {
    if let Some(source_parts) = ctx.name_source.get(&ctor_name) {
        if let Some(exports) = ctx.registry.lookup(source_parts) {
            if let Some((parent, _, _)) = exports.ctor_details.get(&ctor_name) {
                return exports.data_constructors
                    .get(parent)
                    .map_or(false, |ctors| ctors.len() > 1);
            }
        }
    }
    // Default: assume sum type (safer — produces instanceof check)
    true
}

/// Check if a constructor from an imported module is a newtype.
fn is_newtype_from_imports(ctx: &CodegenCtx, ctor_name: Symbol) -> bool {
    if let Some(source_parts) = ctx.name_source.get(&ctor_name) {
        if let Some(exports) = ctx.registry.lookup(source_parts) {
            return exports.newtype_names.contains(&ctor_name);
        }
    }
    false
}

/// Resolve an operator to its target function reference.
/// Operators like `<>` are resolved to their aliased function (e.g., `append`)
/// via the module's fixity declarations.
fn resolve_operator(ctx: &CodegenCtx, op_qident: &QualifiedIdent) -> JsExpr {
    let op_name = op_qident.name;

    // Look up in operator targets map (built from fixity declarations)
    if let Some((target_module, target_fn)) = ctx.operator_targets.get(&op_name) {
        let js_name = ident_to_js(*target_fn);

        // Check constraint dicts: operator may alias a class method (e.g. `<>` → `append`).
        {
            let dicts = ctx.constraint_dicts.borrow();
            if let Some(dict_expr) = dicts.get(target_fn) {
                return JsExpr::Indexer(
                    Box::new(dict_expr.clone()),
                    Box::new(JsExpr::StringLit(js_name)),
                );
            }
        }

        if let Some(mod_parts) = target_module {
            // Explicitly qualified target: e.g., `Data.Semigroup.append`
            if let Some(js_mod) = ctx.import_map.get(mod_parts) {
                return JsExpr::ModuleAccessor(js_mod.clone(), js_name);
            }
        }

        // Unqualified target: resolve through name_source
        if ctx.local_names.contains(target_fn) {
            return JsExpr::Var(js_name);
        }
        if let Some(source_parts) = ctx.name_source.get(target_fn) {
            if let Some(js_mod) = ctx.import_map.get(source_parts) {
                return JsExpr::ModuleAccessor(js_mod.clone(), js_name);
            }
        }

        return JsExpr::Var(js_name);
    }

    // If the operator is already qualified (e.g., from a qualified import), resolve directly
    if op_qident.module.is_some() {
        return gen_qualified_ref(ctx, op_qident);
    }

    // Fallback: emit the mangled operator name as a variable reference
    // This handles cases where the operator is locally defined or lambda-bound
    JsExpr::Var(ident_to_js(op_name))
}

/// Resolve a module qualifier symbol to a JS module accessor.
fn resolve_module_ref(ctx: &CodegenCtx, mod_sym: Symbol, js_name: &str) -> JsExpr {
    let mod_str = interner::resolve(mod_sym).unwrap_or_default();
    // Check qualified imports (import X as Y)
    for imp in &ctx.module.imports {
        if let Some(ref qual) = imp.qualified {
            let qual_str = qual.parts
                .iter()
                .map(|s| interner::resolve(*s).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".");
            if qual_str == mod_str {
                if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), js_name.to_string());
                }
            }
        }
        // Also check direct module name match
        let imp_name = imp.module.parts
            .iter()
            .map(|s| interner::resolve(*s).unwrap_or_default())
            .collect::<Vec<_>>()
            .join(".");
        if imp_name == mod_str {
            if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                return JsExpr::ModuleAccessor(js_mod.clone(), js_name.to_string());
            }
        }
    }
    // Fallback
    let js_mod = any_name_to_js(&mod_str.replace('.', "_"));
    JsExpr::ModuleAccessor(js_mod, js_name.to_string())
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

            // Check if this is a newtype constructor (erased) — local or imported
            let is_newtype = ctx.newtype_names.contains(&ctor_name)
                || is_newtype_from_imports(ctx, ctor_name);
            if is_newtype {
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
                // Check imported modules
                is_sum_ctor_from_imports(ctx, ctor_name)
            };

            if is_sum {
                let ctor_ref = gen_qualified_ref(ctx, name);
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

