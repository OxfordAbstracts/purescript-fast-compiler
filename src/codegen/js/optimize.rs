use std::collections::{HashMap, HashSet};

use super::*;

/// Scan a function body for `method(dictParam)` or `method(dictParam.Super0())`
/// applications that appear inside nested functions, and hoist them to
/// `var method1 = method(dictParam);` bindings at the top of the body.
/// Only hoists when the dict app is used inside an inner lambda, not when
/// it's the direct return value.
/// Top-down hoisting pass for instance constraint wrapping.
/// Walks the nested function tree from outermost to innermost, hoisting dict apps
/// at each level using a shared counter. This ensures outer scopes get lower numbers.
/// `base_names` maps hoisted var names back to their original method names,
/// so cascading applications (e.g., method1(dict)) still use the original counter key.
/// Hoist dict applications out of nested expressions into top-level bindings.
/// Dict apps where the callee Var matches an excluded name are not hoisted.
/// Used to prevent hoisting calls to sibling constrained functions which could
/// cause infinite mutual recursion at init time.
pub(crate) fn hoist_dict_apps_top_down_with_excluded(
    expr: &mut JsExpr,
    counter: &mut HashMap<String, usize>,
    base_names: &mut HashMap<String, String>,
    bare_names: &mut HashSet<String>,
    enclosing_name: Option<&str>,
    reserved_names: &HashSet<String>,
    excluded_callees: &HashSet<String>,
) {
    if let JsExpr::Function(_, params, body) = expr {
        if params.len() == 1 && params[0].starts_with("dict") {
            let dict_param = params[0].clone();
            let old_body = std::mem::take(body);
            // Collect dict apps with a temporary counter, then fix names using base_names
            let mut temp_counter: HashMap<String, usize> = HashMap::new();
            let mut hoisted: Vec<(JsExpr, String)> = Vec::new();
            collect_dict_apps_nested(&dict_param, &old_body, &mut hoisted, &mut temp_counter, 0);
            // Exclude self-references: don't hoist expressions that reference the enclosing function
            if let Some(self_name) = enclosing_name {
                hoisted.retain(|(expr, _)| {
                    !js_expr_contains_var(expr, self_name)
                });
            }
            // Exclude calls to sibling constrained functions (prevent mutual recursion)
            if !excluded_callees.is_empty() {
                hoisted.retain(|(expr, _)| {
                    if let Some(callee_name) = extract_base_method_name_from_app(expr) {
                        !excluded_callees.contains(&callee_name)
                    } else {
                        true
                    }
                });
            }

            if hoisted.is_empty() {
                *body = old_body;
            } else {
                // Collect all VarDecl names used in the body (including nested functions)
                // to avoid naming hoisted vars with conflicting names.
                let mut body_var_names = HashSet::new();
                collect_all_var_decl_names_from_stmts(&old_body, &mut body_var_names);
                let mut effective_reserved = reserved_names.clone();
                effective_reserved.extend(body_var_names);
                let reserved_names = &effective_reserved;

                // Fix method names: resolve through base_names and use shared counter
                let mut unique: Vec<(JsExpr, String)> = Vec::new();
                for (expr, _raw_name) in hoisted {
                    if unique.iter().any(|(e, _)| *e == expr) {
                        continue;
                    }
                    // Get the method name extracted from the expression
                    let raw_method = if let Some(m) = is_dict_app(&dict_param, &expr) { m } else { continue };
                    // Resolve to base name (e.g., heytingAlgebraRecordCons1 → heytingAlgebraRecordCons)
                    // Escape the name so primed identifiers (e.g. composePull') become valid JS names.
                    let raw_base = base_names.get(&raw_method).cloned().unwrap_or_else(|| raw_method.clone());
                    let base = any_name_to_js(&raw_base);
                    let count = counter.entry(base.clone()).or_insert(0);
                    *count += 1;
                    let is_mod_acc = is_dict_app_module_accessor(&expr);
                    // Naming convention:
                    // - Module accessor first occurrence: bare name (no suffix) unless conflicts with field name
                    // - Module accessor subsequent: suffix = count
                    // - Non-module-accessor after a bare: suffix = count - 1
                    // - Non-module-accessor without preceding bare: suffix = count
                    let would_be_bare = is_mod_acc && *count == 1;
                    let mut hoisted_name = if would_be_bare && !reserved_names.contains(&base) && !is_js_reserved(&base) && !is_js_builtin(&base) {
                        bare_names.insert(base.clone());
                        base.clone()
                    } else {
                        // If bare would have been used but is reserved, still mark as bare
                        // so the count-1 offset applies to subsequent names
                        if would_be_bare {
                            bare_names.insert(base.clone());
                        }
                        if !is_mod_acc && bare_names.contains(&base) {
                            format!("{base}{}", *count - 1)
                        } else {
                            format!("{base}{count}")
                        }
                    };
                    // Skip reserved names (module-level vars, instance method names, JS reserved words)
                    while reserved_names.contains(&hoisted_name) || is_js_reserved(&hoisted_name) || is_js_builtin(&hoisted_name) {
                        *count += 1;
                        hoisted_name = if bare_names.contains(&base) {
                            format!("{base}{}", *count - 1)
                        } else {
                            format!("{base}{count}")
                        };
                    }
                    // Track base name for cascading
                    base_names.insert(hoisted_name.clone(), base);
                    unique.push((expr, hoisted_name));
                }

                // Save original expressions for body replacement (before CSE modifies them)
                let original_unique = unique.clone();

                // CSE: extract shared arguments across hoisted dict apps.
                // If two+ hoisted vars share the same complex argument (e.g., dictRing.Semiring0()),
                // extract it into its own variable.
                extract_shared_hoisted_args(&mut unique, counter, base_names, bare_names, reserved_names);

                let mut new_body = Vec::new();
                for (expr, name) in &unique {
                    new_body.push(JsStmt::VarDecl(name.clone(), Some(expr.clone())));
                }
                // Replace dict apps in the body using the ORIGINAL (pre-CSE) expressions
                let replaced: Vec<JsStmt> = old_body.into_iter()
                    .map(|s| replace_dict_apps_stmt(s, &original_unique))
                    .collect();
                new_body.extend(replaced);

                // Post-process: fold constant dict args into hoisted vars.
                // If a hoisted var is used ONLY in thunk return values as `v(arg1)(arg2)...`
                // where args don't reference the current dict_param, fold the args
                // into the VarDecl and replace the usage with just `v`.
                fold_constant_dict_args_into_hoisted(&dict_param, &mut new_body);

                *body = new_body;
            }
        }
        // Recurse into the body to process inner function layers.
        // Pass down hoisted names as reserved to prevent inner scopes from shadowing them.
        let mut extended_reserved;
        let effective_reserved = if let Some(_hoisted_names) = body.iter().filter_map(|s| {
            if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
        }).next() {
            // There are hoisted var decls - collect all of them as reserved
            extended_reserved = reserved_names.clone();
            for stmt in body.iter() {
                if let JsStmt::VarDecl(name, _) = stmt {
                    extended_reserved.insert(name.clone());
                }
            }
            &extended_reserved
        } else {
            reserved_names
        };
        for stmt in body.iter_mut() {
            hoist_dict_apps_top_down_stmt_with_excluded(stmt, counter, base_names, bare_names, enclosing_name, effective_reserved, excluded_callees);
        }
    }
}

pub(crate) fn hoist_dict_apps_top_down_stmt_with_excluded(
    stmt: &mut JsStmt,
    counter: &mut HashMap<String, usize>,
    base_names: &mut HashMap<String, String>,
    bare_names: &mut HashSet<String>,
    enclosing_name: Option<&str>,
    reserved_names: &HashSet<String>,
    excluded_callees: &HashSet<String>,
) {
    match stmt {
        JsStmt::Return(expr) => hoist_dict_apps_top_down_with_excluded(expr, counter, base_names, bare_names, enclosing_name, reserved_names, excluded_callees),
        JsStmt::VarDecl(name, Some(expr)) => hoist_dict_apps_top_down_with_excluded(expr, counter, base_names, bare_names, Some(name.as_str()), reserved_names, excluded_callees),
        _ => {}
    }
}

/// Extract shared arguments from hoisted dict applications.
/// When 2+ hoisted vars share the same complex argument (e.g., `dictRing.Semiring0()`),
/// extract it into its own variable (e.g., `var Semiring0 = dictRing.Semiring0()`)
/// and replace the argument in the hoisted exprs with a Var reference.
pub(crate) fn extract_shared_hoisted_args(
    unique: &mut Vec<(JsExpr, String)>,
    counter: &mut HashMap<String, usize>,
    base_names: &mut HashMap<String, String>,
    bare_names: &mut HashSet<String>,
    reserved_names: &HashSet<String>,
) {
    // Collect arguments from hoisted dict apps: App(callee, [arg]) where arg is complex
    let mut args_seen: Vec<(JsExpr, usize)> = Vec::new();
    for (expr, _) in unique.iter() {
        if let JsExpr::App(_, args) = expr {
            if args.len() == 1 {
                let arg = &args[0];
                // Only extract complex args (not simple vars)
                if !matches!(arg, JsExpr::Var(_)) {
                    if let Some(entry) = args_seen.iter_mut().find(|(a, _)| a == arg) {
                        entry.1 += 1;
                    } else {
                        args_seen.push((arg.clone(), 1));
                    }
                }
            }
        }
    }

    // For each arg appearing 2+ times, extract it
    let mut extracted: Vec<(JsExpr, String)> = Vec::new();
    for (arg, count) in &args_seen {
        if *count < 2 {
            continue;
        }
        // Get name hint from the arg expression (last accessor in a chain)
        let name_hint = extract_name_hint(arg);
        if name_hint.is_empty() {
            continue;
        }

        // Generate the variable name using the same naming scheme
        let base = base_names.get(&name_hint).cloned().unwrap_or_else(|| name_hint.clone());
        let cnt = counter.entry(base.clone()).or_insert(0);
        *cnt += 1;
        let is_first = *cnt == 1;
        let mut var_name = if is_first && !reserved_names.contains(&base) {
            bare_names.insert(base.clone());
            base.clone()
        } else {
            if is_first {
                bare_names.insert(base.clone());
            }
            format!("{base}{cnt}")
        };
        while reserved_names.contains(&var_name) {
            *cnt += 1;
            var_name = format!("{base}{cnt}");
        }
        base_names.insert(var_name.clone(), base);
        extracted.push((arg.clone(), var_name));
    }

    if extracted.is_empty() {
        return;
    }

    // Replace the shared args in the hoisted expressions
    for (expr, _) in unique.iter_mut() {
        if let JsExpr::App(_, args) = expr {
            if args.len() == 1 {
                for (shared_arg, var_name) in &extracted {
                    if &args[0] == shared_arg {
                        args[0] = JsExpr::Var(var_name.clone());
                        break;
                    }
                }
            }
        }
    }

    // Prepend extracted vars before the existing hoisted vars
    let mut new_unique: Vec<(JsExpr, String)> = Vec::new();
    for (arg, name) in extracted {
        new_unique.push((arg, name));
    }
    new_unique.extend(unique.drain(..));
    *unique = new_unique;
}

/// Extract a name hint from an expression for CSE variable naming.
/// For accessor chains like `dictRing.Semiring0()`, returns "Semiring0".
/// For `((d.CommutativeRing0()).Ring0()).Semiring0()`, returns "Semiring0".
pub(crate) fn extract_name_hint(expr: &JsExpr) -> String {
    match expr {
        // `expr.field()` → field name
        JsExpr::App(callee, args) if args.is_empty() => {
            if let JsExpr::Indexer(_, key) = callee.as_ref() {
                if let JsExpr::StringLit(s) = key.as_ref() {
                    return s.clone();
                }
            }
            String::new()
        }
        // `expr.field` → field name
        JsExpr::Indexer(_, key) => {
            if let JsExpr::StringLit(s) = key.as_ref() {
                return s.clone();
            }
            String::new()
        }
        _ => String::new(),
    }
}

/// Fold constant dict args into hoisted VarDecls.
/// When a hoisted var `v` appears ONLY inside thunk functions (Function([], [Return(App(v, args)...)]))
/// and the extra args don't reference the current dict_param, fold them into the VarDecl:
///   var v = expr;  +  thunk: function() { return v(arg1)(arg2); }
/// becomes:
///   var v = expr(arg1)(arg2);  +  thunk: function() { return v; }
pub(crate) fn fold_constant_dict_args_into_hoisted(dict_param: &str, stmts: &mut Vec<JsStmt>) {
    // Find hoisted VarDecls (they come first)
    let hoisted_names: Vec<String> = stmts.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, Some(_)) = s { Some(name.clone()) } else { None }
    }).collect();

    for hoisted_name in &hoisted_names {
        // Find all usages of this hoisted var in the body — returns extra args to fold in
        if let Some((extra_args, full_usage_expr)) = find_foldable_usage(dict_param, hoisted_name, stmts) {
            // Update the VarDecl: append extra args to the original init
            for stmt in stmts.iter_mut() {
                if let JsStmt::VarDecl(name, Some(init)) = stmt {
                    if name == hoisted_name {
                        // Wrap init with the extra args: init(arg1)(arg2)...
                        let mut new_init = init.clone();
                        for arg in &extra_args {
                            new_init = JsExpr::App(Box::new(new_init), vec![arg.clone()]);
                        }
                        *init = new_init;
                        break;
                    }
                }
            }
            // Replace the usage with just the var name
            replace_app_with_var_in_stmts(stmts, hoisted_name, &full_usage_expr);
        }
    }
}

/// Find a single foldable usage of a hoisted var: the var is used inside a thunk body
/// (Function([], [Return(App...)])) where additional args don't reference dict_param.
/// Returns (extra_args, full_usage_expr) if foldable.
pub(crate) fn find_foldable_usage(dict_param: &str, var_name: &str, stmts: &[JsStmt]) -> Option<(Vec<JsExpr>, JsExpr)> {
    // Look for the var used in the body (skip the VarDecl itself)
    let mut found: Option<(Vec<JsExpr>, JsExpr)> = None;
    let mut count = 0;
    for stmt in stmts {
        find_foldable_in_stmt(dict_param, var_name, stmt, &mut found, &mut count);
    }
    // Only fold if there's exactly one usage
    if count == 1 { found } else { None }
}

pub(crate) fn find_foldable_in_stmt(dict_param: &str, var_name: &str, stmt: &JsStmt, found: &mut Option<(Vec<JsExpr>, JsExpr)>, count: &mut usize) {
    match stmt {
        JsStmt::VarDecl(name, _) if name == var_name => {} // skip the hoisted VarDecl itself
        JsStmt::Return(expr) => find_foldable_in_expr(dict_param, var_name, expr, found, count),
        JsStmt::VarDecl(_, Some(expr)) => find_foldable_in_expr(dict_param, var_name, expr, found, count),
        JsStmt::Expr(expr) => find_foldable_in_expr(dict_param, var_name, expr, found, count),
        _ => {}
    }
}

pub(crate) fn find_foldable_in_expr(dict_param: &str, var_name: &str, expr: &JsExpr, found: &mut Option<(Vec<JsExpr>, JsExpr)>, count: &mut usize) {
    match expr {
        JsExpr::Var(name) if name == var_name => { *count += 1; } // bare usage, not foldable
        JsExpr::App(callee, args) => {
            // Check if this is `var_name(arg1)(arg2)...`
            if let Some(extra_args) = extract_app_chain_args(var_name, expr) {
                if !extra_args.is_empty() && extra_args.iter().all(|a| is_dict_like_arg(a) && !expr_contains_var(a, dict_param)) {
                    *count += 1;
                    if found.is_none() {
                        *found = Some((extra_args, expr.clone()));
                    }
                    return;
                }
            }
            find_foldable_in_expr(dict_param, var_name, callee, found, count);
            for arg in args { find_foldable_in_expr(dict_param, var_name, arg, found, count); }
        }
        JsExpr::Function(_, params, body) => {
            // Only look inside thunk functions (no params)
            if params.is_empty() {
                for s in body { find_foldable_in_stmt(dict_param, var_name, s, found, count); }
            }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields { find_foldable_in_expr(dict_param, var_name, val, found, count); }
        }
        _ => {}
    }
}

/// Extract the extra args from an App chain: `var_name(arg1)(arg2)` → vec![arg1, arg2]
pub(crate) fn extract_app_chain_args(var_name: &str, expr: &JsExpr) -> Option<Vec<JsExpr>> {
    match expr {
        JsExpr::Var(name) if name == var_name => Some(vec![]),
        JsExpr::App(callee, args) => {
            let mut chain = extract_app_chain_args(var_name, callee)?;
            chain.extend(args.clone());
            Some(chain)
        }
        _ => None,
    }
}

/// Check if an expression contains a reference to a specific variable
pub(crate) fn expr_contains_var(expr: &JsExpr, var_name: &str) -> bool {
    match expr {
        JsExpr::Var(name) => name == var_name,
        JsExpr::App(callee, args) => expr_contains_var(callee, var_name) || args.iter().any(|a| expr_contains_var(a, var_name)),
        JsExpr::Indexer(a, b) => expr_contains_var(a, var_name) || expr_contains_var(b, var_name),
        JsExpr::Function(_, _, body) => body.iter().any(|s| stmt_contains_var(s, var_name)),
        _ => false,
    }
}

pub(crate) fn stmt_contains_var(stmt: &JsStmt, var_name: &str) -> bool {
    match stmt {
        JsStmt::Return(expr) | JsStmt::VarDecl(_, Some(expr)) | JsStmt::Expr(expr) => expr_contains_var(expr, var_name),
        _ => false,
    }
}

/// Replace App chain `var_name(args...)` with just `Var(var_name)` in statements,
/// where the App chain matches the folded expression.
pub(crate) fn replace_app_with_var_in_stmts(stmts: &mut [JsStmt], var_name: &str, folded_expr: &JsExpr) {
    for stmt in stmts.iter_mut() {
        replace_app_with_var_in_stmt(stmt, var_name, folded_expr);
    }
}

pub(crate) fn replace_app_with_var_in_stmt(stmt: &mut JsStmt, var_name: &str, folded_expr: &JsExpr) {
    match stmt {
        JsStmt::VarDecl(name, _) if name == var_name => {} // skip VarDecl
        JsStmt::Return(expr) => replace_app_with_var_in_expr(expr, var_name, folded_expr),
        JsStmt::VarDecl(_, Some(expr)) => replace_app_with_var_in_expr(expr, var_name, folded_expr),
        JsStmt::Expr(expr) => replace_app_with_var_in_expr(expr, var_name, folded_expr),
        _ => {}
    }
}

pub(crate) fn replace_app_with_var_in_expr(expr: &mut JsExpr, var_name: &str, folded_expr: &JsExpr) {
    if expr == folded_expr {
        *expr = JsExpr::Var(var_name.to_string());
        return;
    }
    match expr {
        JsExpr::App(callee, args) => {
            replace_app_with_var_in_expr(callee, var_name, folded_expr);
            for arg in args { replace_app_with_var_in_expr(arg, var_name, folded_expr); }
        }
        JsExpr::Function(_, _, body) => {
            for s in body { replace_app_with_var_in_stmt(s, var_name, folded_expr); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields { replace_app_with_var_in_expr(val, var_name, folded_expr); }
        }
        _ => {}
    }
}

/// Collect field names from ObjectLit directly returned at this function level.
/// Check if an expression references dict-prefixed variables other than the given one.
/// Used to prevent hoisting expressions that depend on deeper-scope dict params.
pub(crate) fn expr_references_other_dicts(dict_param: &str, expr: &JsExpr) -> bool {
    match expr {
        JsExpr::Var(name) => name.starts_with("dict") && name != dict_param,
        JsExpr::App(callee, args) => {
            expr_references_other_dicts(dict_param, callee)
                || args.iter().any(|a| expr_references_other_dicts(dict_param, a))
        }
        JsExpr::Indexer(obj, key) => {
            expr_references_other_dicts(dict_param, obj)
                || expr_references_other_dicts(dict_param, key)
        }
        JsExpr::Binary(_, l, r) => {
            expr_references_other_dicts(dict_param, l)
                || expr_references_other_dicts(dict_param, r)
        }
        JsExpr::Unary(_, e) => expr_references_other_dicts(dict_param, e),
        _ => false,
    }
}

/// Check if an expression is a dict application: `method(dictParam)` or
/// `method(dictParam.Superclass0())` or a superclass chain access `dictParam.Superclass0()`.
/// Check if a JsExpr contains any `Var(name)` matching the given name.
/// Used to detect self-referencing expressions that shouldn't be hoisted eagerly.
pub(crate) fn js_expr_contains_var(expr: &JsExpr, name: &str) -> bool {
    match expr {
        JsExpr::Var(v) => v == name,
        JsExpr::App(callee, args) => {
            js_expr_contains_var(callee, name) || args.iter().any(|a| js_expr_contains_var(a, name))
        }
        JsExpr::Indexer(obj, field) => {
            js_expr_contains_var(obj, name) || js_expr_contains_var(field, name)
        }
        JsExpr::ArrayLit(elems) => elems.iter().any(|e| js_expr_contains_var(e, name)),
        JsExpr::ObjectLit(fields) => fields.iter().any(|(_, e)| js_expr_contains_var(e, name)),
        JsExpr::Unary(_, e) => js_expr_contains_var(e, name),
        JsExpr::Binary(_, l, r) => js_expr_contains_var(l, name) || js_expr_contains_var(r, name),
        JsExpr::InstanceOf(l, r) => js_expr_contains_var(l, name) || js_expr_contains_var(r, name),
        JsExpr::Ternary(c, t, e) => {
            js_expr_contains_var(c, name) || js_expr_contains_var(t, name) || js_expr_contains_var(e, name)
        }
        JsExpr::New(callee, args) => {
            js_expr_contains_var(callee, name) || args.iter().any(|a| js_expr_contains_var(a, name))
        }
        JsExpr::Function(_, _, body) => body.iter().any(|s| js_stmt_contains_var(s, name)),
        _ => false,
    }
}

pub(crate) fn js_stmt_contains_var(stmt: &JsStmt, name: &str) -> bool {
    match stmt {
        JsStmt::Expr(e) | JsStmt::Return(e) | JsStmt::Throw(e) => js_expr_contains_var(e, name),
        JsStmt::VarDecl(_, init) => init.as_ref().map_or(false, |e| js_expr_contains_var(e, name)),
        JsStmt::Assign(target, val) => js_expr_contains_var(target, name) || js_expr_contains_var(val, name),
        JsStmt::If(cond, then_b, else_b) => {
            js_expr_contains_var(cond, name)
                || then_b.iter().any(|s| js_stmt_contains_var(s, name))
                || else_b.as_ref().map_or(false, |stmts| stmts.iter().any(|s| js_stmt_contains_var(s, name)))
        }
        JsStmt::While(cond, body) | JsStmt::For(_, cond, _, body) => {
            js_expr_contains_var(cond, name) || body.iter().any(|s| js_stmt_contains_var(s, name))
        }
        JsStmt::ForIn(_, obj, body) => {
            js_expr_contains_var(obj, name) || body.iter().any(|s| js_stmt_contains_var(s, name))
        }
        JsStmt::Block(stmts) | JsStmt::FunctionDecl(_, _, stmts) => {
            stmts.iter().any(|s| js_stmt_contains_var(s, name))
        }
        JsStmt::ReturnVoid | JsStmt::Comment(_) | JsStmt::RawJs(_)
        | JsStmt::Import { .. } | JsStmt::Export(_) | JsStmt::ExportFrom(_, _) => false,
    }
}

/// Recursively collect all VarDecl names from a list of statements,
/// including inside nested functions and control flow.
fn collect_all_var_decl_names_from_stmts(stmts: &[JsStmt], names: &mut HashSet<String>) {
    for stmt in stmts {
        collect_all_var_decl_names_from_stmt(stmt, names);
    }
}

fn collect_all_var_decl_names_from_stmt(stmt: &JsStmt, names: &mut HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(name, expr) => {
            names.insert(name.clone());
            if let Some(e) = expr { collect_all_var_decl_names_from_expr(e, names); }
        }
        JsStmt::Return(expr) => collect_all_var_decl_names_from_expr(expr, names),
        JsStmt::Expr(expr) => collect_all_var_decl_names_from_expr(expr, names),
        JsStmt::Assign(target, expr) => {
            collect_all_var_decl_names_from_expr(target, names);
            collect_all_var_decl_names_from_expr(expr, names);
        }
        JsStmt::If(cond, then_body, else_body) => {
            collect_all_var_decl_names_from_expr(cond, names);
            for s in then_body { collect_all_var_decl_names_from_stmt(s, names); }
            if let Some(stmts) = else_body {
                for s in stmts { collect_all_var_decl_names_from_stmt(s, names); }
            }
        }
        JsStmt::Block(stmts) => {
            for s in stmts { collect_all_var_decl_names_from_stmt(s, names); }
        }
        _ => {}
    }
}

fn collect_all_var_decl_names_from_expr(expr: &JsExpr, names: &mut HashSet<String>) {
    match expr {
        JsExpr::Function(_, _, body) => {
            collect_all_var_decl_names_from_stmts(body, names);
        }
        JsExpr::App(callee, args) => {
            collect_all_var_decl_names_from_expr(callee, names);
            for a in args { collect_all_var_decl_names_from_expr(a, names); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_all_var_decl_names_from_expr(v, names); }
        }
        JsExpr::Ternary(a, b, c) => {
            collect_all_var_decl_names_from_expr(a, names);
            collect_all_var_decl_names_from_expr(b, names);
            collect_all_var_decl_names_from_expr(c, names);
        }
        JsExpr::ArrayLit(items) => {
            for i in items { collect_all_var_decl_names_from_expr(i, names); }
        }
        JsExpr::Binary(_, l, r) | JsExpr::Indexer(l, r) | JsExpr::InstanceOf(l, r) => {
            collect_all_var_decl_names_from_expr(l, names);
            collect_all_var_decl_names_from_expr(r, names);
        }
        JsExpr::Unary(_, e) => {
            collect_all_var_decl_names_from_expr(e, names);
        }
        JsExpr::New(callee, args) => {
            collect_all_var_decl_names_from_expr(callee, names);
            for a in args { collect_all_var_decl_names_from_expr(a, names); }
        }
        _ => {}
    }
}

pub(crate) fn is_dict_app(dict_param: &str, expr: &JsExpr) -> Option<String> {
    if let JsExpr::App(callee, args) = expr {
        if args.len() == 1 && is_dict_ref(dict_param, &args[0]) {
            // Extract method name from callee, handling phantom () chains on callee side
            // E.g., heytingAlgebraRecord()(dictRef) — callee is App(Var("heytingAlgebraRecord"), [])
            if let Some(name) = extract_base_method_name(callee) {
                return Some(name);
            }
        }
        // Also match phantom () calls chained AFTER a dict application:
        // method(dictParam)()  =  App(App(callee, [dictRef]), [])
        if args.is_empty() {
            // Check for superclass chain access: dictParam.Superclass0()
            if let JsExpr::Indexer(obj, field) = callee.as_ref() {
                if is_dict_ref(dict_param, obj) {
                    if let JsExpr::StringLit(field_name) = field.as_ref() {
                        return Some(field_name.clone());
                    }
                }
            }
            return is_dict_app(dict_param, callee);
        }
    }
    None
}

/// Extract the base callee Var name from a dict app expression (the function being called).
/// E.g., `App(Var("processLeft"), [Var("dictShow")])` → Some("processLeft")
/// `App(ModuleAccessor("Data_Show", "show"), [Var("dictShow")])` → None (module accessor, not Var)
pub(crate) fn extract_base_method_name_from_app(expr: &JsExpr) -> Option<String> {
    if let JsExpr::App(callee, _) = expr {
        // Only match Var callees (not ModuleAccessor or Indexer)
        match callee.as_ref() {
            JsExpr::Var(name) => Some(name.clone()),
            JsExpr::App(inner, _) => {
                // Handle phantom () chains: App(App(Var("f"), [dict]), [])
                extract_base_method_name_from_app(callee)
            }
            _ => None,
        }
    } else {
        None
    }
}

/// Extract the base method name from a callee expression, unwrapping any application chains.
/// E.g., Var("foo") → "foo", ModuleAccessor(_, "foo") → "foo",
/// App(Var("foo"), []) → "foo" (phantom-applied),
/// App(App(ModuleAccessor(_, "foo"), [arg1]), []) → "foo" (partially applied + phantom)
pub(crate) fn extract_base_method_name(expr: &JsExpr) -> Option<String> {
    match expr {
        JsExpr::Var(name) => Some(name.clone()),
        JsExpr::ModuleAccessor(_, name) => Some(name.clone()),
        JsExpr::App(inner_callee, _) => {
            extract_base_method_name(inner_callee)
        }
        _ => None,
    }
}

/// Check if an expression refers to the dict param: either `dictParam` itself
/// or `dictParam.Superclass0()`.
pub(crate) fn is_dict_ref(dict_param: &str, expr: &JsExpr) -> bool {
    match expr {
        JsExpr::Var(name) => name == dict_param,
        // dictParam.Superclass0() or chained: (dictParam.Ring0()).Semiring0()
        JsExpr::App(callee, args) if args.is_empty() => {
            if let JsExpr::Indexer(obj, _) = callee.as_ref() {
                // obj could be Var(dictParam) or another chained access
                return is_dict_ref(dict_param, obj);
            }
            false
        }
        _ => false,
    }
}

/// Check if a dict app expression has a ModuleAccessor as the innermost callee,
/// or is a superclass chain access (dictParam.Field()).
/// Handles phantom () chains: App(App(ModuleAccessor(..), [dict]), []) → true
pub(crate) fn is_dict_app_module_accessor(expr: &JsExpr) -> bool {
    match expr {
        JsExpr::App(callee, args) => {
            if args.is_empty() {
                // Could be a superclass access: dictParam.Field()
                if let JsExpr::Indexer(_, _) = callee.as_ref() {
                    return true;
                }
                // Phantom () call — recurse into callee
                is_dict_app_module_accessor(callee)
            } else {
                matches!(callee.as_ref(), JsExpr::ModuleAccessor(..))
            }
        }
        _ => false,
    }
}

/// Check if an App chain expression is a "extended dict app" — a dict app at the core
/// with additional applications on top where ALL outer args are dict-like
/// (dict params, superclass accessor results, or phantom thunks).
/// Returns the method name from the innermost dict app if found.
/// E.g., `ordRecordCons(dictRef)()(dictIsSymbol)(Ord0)` where dictIsSymbol and Ord0
/// are dict parameters/accessors → returns Some("ordRecordCons").
/// Check if an argument is "dict-like" — something that could be a dict parameter,
/// a superclass accessor result, or a phantom thunk call.
pub(crate) fn is_dict_like_arg(arg: &JsExpr) -> bool {
    match arg {
        // Dict parameter: dictFoo
        JsExpr::Var(name) => name.starts_with("dict") || name.ends_with("0") || name.ends_with("1"),
        // Superclass accessor: dictFoo.Bar0() or dictFoo["Bar0"]()
        JsExpr::App(callee, inner_args) if inner_args.is_empty() => {
            match callee.as_ref() {
                JsExpr::Indexer(obj, _) => is_dict_like_arg(obj),
                // Could also be a thunk call
                _ => is_dict_like_arg(callee),
            }
        }
        _ => false,
    }
}

/// Recursively collect dict applications from statements, tracking function nesting depth.
/// When `include_depth_zero` is true, hoists apps at all depths (for instance bodies).
/// When false, only hoists at depth > 0 (inside nested functions).
pub(crate) fn collect_dict_apps_nested(dict_param: &str, stmts: &[JsStmt], hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize) {
    collect_dict_apps_nested_ex(dict_param, stmts, hoisted, counter, depth, false);
}

pub(crate) fn collect_dict_apps_nested_ex(dict_param: &str, stmts: &[JsStmt], hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize, include_depth_zero: bool) {
    for stmt in stmts {
        collect_dict_apps_stmt_nested_ex(dict_param, stmt, hoisted, counter, depth, include_depth_zero);
    }
}

pub(crate) fn collect_dict_apps_stmt_nested_ex(dict_param: &str, stmt: &JsStmt, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize, include_depth_zero: bool) {
    match stmt {
        JsStmt::Return(expr) => collect_dict_apps_expr_nested_ex(dict_param, expr, hoisted, counter, depth, include_depth_zero),
        JsStmt::VarDecl(_, Some(expr)) => collect_dict_apps_expr_nested_ex(dict_param, expr, hoisted, counter, depth, include_depth_zero),
        JsStmt::If(cond, then_body, else_body) => {
            collect_dict_apps_expr_nested_ex(dict_param, cond, hoisted, counter, depth, include_depth_zero);
            collect_dict_apps_nested_ex(dict_param, then_body, hoisted, counter, depth, include_depth_zero);
            if let Some(else_stmts) = else_body {
                collect_dict_apps_nested_ex(dict_param, else_stmts, hoisted, counter, depth, include_depth_zero);
            }
        }
        JsStmt::Expr(expr) => collect_dict_apps_expr_nested_ex(dict_param, expr, hoisted, counter, depth, include_depth_zero),
        _ => {}
    }
}

pub(crate) fn collect_dict_apps_expr_nested_ex(dict_param: &str, expr: &JsExpr, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize, include_depth_zero: bool) {
    if let Some(method_name) = is_dict_app(dict_param, expr) {
        if depth > 0 || include_depth_zero {
            // Only hoist if inside a nested function AND expression doesn't reference
            // dict params from deeper scopes (which would be out of scope when hoisted)
            if expr_references_other_dicts(dict_param, expr) {
                // Don't hoist — recurse to find simpler hoistable subexpressions
                match expr {
                    JsExpr::App(callee, args) => {
                        collect_dict_apps_expr_nested_ex(dict_param, callee, hoisted, counter, depth, include_depth_zero);
                        for arg in args {
                            collect_dict_apps_expr_nested_ex(dict_param, arg, hoisted, counter, depth, include_depth_zero);
                        }
                    }
                    _ => {}
                }
                return;
            }
            if !hoisted.iter().any(|(e, _)| e == expr) {
                let count = counter.entry(method_name.clone()).or_insert(0);
                *count += 1;
                // For module accessors (imported methods), use bare name for first occurrence
                // For local methods, always use numbered name (method1, method2, ...)
                let is_module_accessor = is_dict_app_module_accessor(expr);
                let escaped_method = any_name_to_js(&method_name);
                let hoisted_name = if is_module_accessor && *count == 1 {
                    escaped_method
                } else {
                    format!("{escaped_method}{count}")
                };
                hoisted.push((expr.clone(), hoisted_name));
            }
        }
        return; // Don't recurse into the dict app itself
    }

    match expr {
        JsExpr::App(callee, args) => {
            // Check if this is an "extended dict app" — a dict app buried inside additional
            // application layers where ALL outer args are dict-like (dict vars, dict accessors, or phantom thunks).
            // e.g., ordRecordCons(dictRef)()(dictIsSymbol)(Ord0) where Ord0 is a dict accessor result.
            // Only hoist the full chain if all outer args are "dict-like".
            // Extended dict app check removed — handled by pre-hoisting in gen_superclass_accessors
            collect_dict_apps_expr_nested_ex(dict_param, callee, hoisted, counter, depth, include_depth_zero);
            for arg in args {
                collect_dict_apps_expr_nested_ex(dict_param, arg, hoisted, counter, depth, include_depth_zero);
            }
        }
        JsExpr::Function(_, _, body) => {
            // Entering a nested function — increment depth
            collect_dict_apps_nested_ex(dict_param, body, hoisted, counter, depth + 1, include_depth_zero);
        }
        JsExpr::Ternary(a, b, c) => {
            collect_dict_apps_expr_nested_ex(dict_param, a, hoisted, counter, depth, include_depth_zero);
            collect_dict_apps_expr_nested_ex(dict_param, b, hoisted, counter, depth, include_depth_zero);
            collect_dict_apps_expr_nested_ex(dict_param, c, hoisted, counter, depth, include_depth_zero);
        }
        JsExpr::ArrayLit(items) => {
            for item in items {
                collect_dict_apps_expr_nested_ex(dict_param, item, hoisted, counter, depth, include_depth_zero);
            }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields {
                collect_dict_apps_expr_nested_ex(dict_param, val, hoisted, counter, depth, include_depth_zero);
            }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) => {
            collect_dict_apps_expr_nested_ex(dict_param, a, hoisted, counter, depth, include_depth_zero);
            collect_dict_apps_expr_nested_ex(dict_param, b, hoisted, counter, depth, include_depth_zero);
        }
        JsExpr::Unary(_, a) | JsExpr::InstanceOf(a, _) => {
            collect_dict_apps_expr_nested_ex(dict_param, a, hoisted, counter, depth, include_depth_zero);
        }
        JsExpr::New(callee, args) => {
            collect_dict_apps_expr_nested_ex(dict_param, callee, hoisted, counter, depth, include_depth_zero);
            for arg in args {
                collect_dict_apps_expr_nested_ex(dict_param, arg, hoisted, counter, depth, include_depth_zero);
            }
        }
        _ => {}
    }
}

pub(crate) fn replace_dict_apps_stmt(stmt: JsStmt, hoisted: &[(JsExpr, String)]) -> JsStmt {
    match stmt {
        JsStmt::Return(expr) => JsStmt::Return(replace_dict_apps_expr(expr, hoisted)),
        JsStmt::VarDecl(name, Some(expr)) => JsStmt::VarDecl(name, Some(replace_dict_apps_expr(expr, hoisted))),
        JsStmt::If(cond, then_body, else_body) => {
            JsStmt::If(
                replace_dict_apps_expr(cond, hoisted),
                then_body.into_iter().map(|s| replace_dict_apps_stmt(s, hoisted)).collect(),
                else_body.map(|stmts| stmts.into_iter().map(|s| replace_dict_apps_stmt(s, hoisted)).collect()),
            )
        }
        JsStmt::Expr(expr) => JsStmt::Expr(replace_dict_apps_expr(expr, hoisted)),
        other => other,
    }
}

pub(crate) fn replace_dict_apps_expr(expr: JsExpr, hoisted: &[(JsExpr, String)]) -> JsExpr {
    // Check if this entire expression matches a hoisted dict app
    for (hoisted_expr, hoisted_name) in hoisted {
        if &expr == hoisted_expr {
            return JsExpr::Var(hoisted_name.clone());
        }
    }

    match expr {
        JsExpr::App(callee, args) => {
            JsExpr::App(
                Box::new(replace_dict_apps_expr(*callee, hoisted)),
                args.into_iter().map(|a| replace_dict_apps_expr(a, hoisted)).collect(),
            )
        }
        JsExpr::Function(name, params, body) => {
            // Don't replace inside functions that shadow a dict param used in hoisted exprs.
            // This prevents inner `function(dictShow)` from having its body incorrectly
            // rewritten when an outer `function(dictShow)` hoisted the same expression.
            let shadowed_hoisted: Vec<&(JsExpr, String)> = hoisted.iter().filter(|(expr, _)| {
                // Check if any param in this function shadows a variable used in the hoisted expr
                params.iter().any(|p| js_expr_contains_var(expr, p))
            }).collect();
            if shadowed_hoisted.is_empty() {
                JsExpr::Function(
                    name,
                    params,
                    body.into_iter().map(|s| replace_dict_apps_stmt(s, hoisted)).collect(),
                )
            } else {
                // Filter out shadowed hoisted entries for this scope
                let filtered: Vec<(JsExpr, String)> = hoisted.iter()
                    .filter(|(expr, _)| !params.iter().any(|p| js_expr_contains_var(expr, p)))
                    .cloned()
                    .collect();
                if filtered.is_empty() {
                    JsExpr::Function(name, params, body)
                } else {
                    JsExpr::Function(
                        name,
                        params,
                        body.into_iter().map(|s| replace_dict_apps_stmt(s, &filtered)).collect(),
                    )
                }
            }
        }
        JsExpr::Ternary(a, b, c) => {
            JsExpr::Ternary(
                Box::new(replace_dict_apps_expr(*a, hoisted)),
                Box::new(replace_dict_apps_expr(*b, hoisted)),
                Box::new(replace_dict_apps_expr(*c, hoisted)),
            )
        }
        JsExpr::ArrayLit(items) => {
            JsExpr::ArrayLit(items.into_iter().map(|i| replace_dict_apps_expr(i, hoisted)).collect())
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(fields.into_iter().map(|(k, v)| (k, replace_dict_apps_expr(v, hoisted))).collect())
        }
        JsExpr::Indexer(a, b) => {
            JsExpr::Indexer(
                Box::new(replace_dict_apps_expr(*a, hoisted)),
                Box::new(replace_dict_apps_expr(*b, hoisted)),
            )
        }
        JsExpr::Binary(op, a, b) => {
            JsExpr::Binary(
                op,
                Box::new(replace_dict_apps_expr(*a, hoisted)),
                Box::new(replace_dict_apps_expr(*b, hoisted)),
            )
        }
        JsExpr::Unary(op, a) => {
            JsExpr::Unary(op, Box::new(replace_dict_apps_expr(*a, hoisted)))
        }
        JsExpr::New(callee, args) => {
            JsExpr::New(
                Box::new(replace_dict_apps_expr(*callee, hoisted)),
                args.into_iter().map(|a| replace_dict_apps_expr(a, hoisted)).collect(),
            )
        }
        JsExpr::InstanceOf(a, b) => {
            JsExpr::InstanceOf(
                Box::new(replace_dict_apps_expr(*a, hoisted)),
                Box::new(replace_dict_apps_expr(*b, hoisted)),
            )
        }
        other => other,
    }
}

/// Hoist constant dict applications from inside function bodies to module level.
/// The original PureScript compiler extracts expressions like
/// `Control_Category.identity(Control_Category.categoryFn)` from function bodies
/// into module-level `var identity = ...` declarations.
pub(crate) fn hoist_module_level_constants(body: &mut Vec<JsStmt>, imported_class_methods: &HashSet<String>, parametric_instances: &HashSet<String>) {
    // 1. Collect module-level var names
    let module_vars: HashSet<String> = body.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
    }).collect();

    // 1b. Identify which module-level vars are class accessor functions
    // Pattern: function(dict) { return dict.X; } or function(dict) { return dict["X"]; }
    let class_accessors: HashSet<String> = body.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, Some(init)) = s {
            if is_class_accessor_pattern(init) {
                return Some(name.clone());
            }
        }
        None
    }).collect();

    // 1c. Identify module-level vars that are functions (parametric dicts like
    // `semigroupListT = function(dictApplicative) { ... }`). These should NOT
    // be used as constant dict args for hoisting because they need to be called
    // with constraint arguments first.
    let function_vars: HashSet<String> = body.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, Some(JsExpr::Function(_, params, _))) = s {
            if !params.is_empty() {
                return Some(name.clone());
            }
        }
        None
    }).collect();

    // 2. Walk declarations to find hoistable expressions inside function bodies
    let mut hoistables: Vec<(JsExpr, String)> = Vec::new(); // (expr, assigned_name)
    let mut hoistable_keys: HashSet<String> = HashSet::new(); // debug-string keys for O(1) dedup
    let mut used_names: HashSet<String> = module_vars.clone();

    for stmt in body.iter() {
        if let JsStmt::VarDecl(name, Some(init)) = stmt {
            find_module_hoistable_in_expr(init, &module_vars, &function_vars, &class_accessors, imported_class_methods, parametric_instances, &mut hoistables, &mut hoistable_keys, &mut used_names, 0, name);
        }
    }

    if hoistables.is_empty() { return; }

    // 3. FIRST, rename function-level hoisted vars that conflict with module-level hoisted names.
    // This must happen BEFORE step 4 (replacement), because after renaming, all function-level
    // refs become e.g. `show1`, then the module-level replacement correctly creates `show` refs.
    let hoisted_names: HashSet<String> = hoistables.iter().map(|(_, n)| n.clone()).collect();
    for stmt in body.iter_mut() {
        if let JsStmt::VarDecl(_, Some(init)) = stmt {
            rename_conflicting_function_hoists(init, &hoisted_names);
        }
    }

    // 4. Replace inline uses with var references
    // Build a HashMap<debug_key, name> for O(1) lookup instead of linear scan
    let hoistable_map: HashMap<String, String> = hoistables.iter()
        .map(|(expr, name)| (format!("{:?}", expr), name.clone()))
        .collect();
    for stmt in body.iter_mut() {
        if let JsStmt::VarDecl(_, Some(init)) = stmt {
            *init = replace_module_hoistable_expr(init.clone(), &hoistable_map);
        }
    }

    // 4. Insert hoisted vars at the beginning of body
    // (the body will be topo-sorted later, but these simple constant expressions
    // have their dependencies already at module level)
    for (expr, name) in hoistables.into_iter().rev() {
        body.insert(0, JsStmt::VarDecl(name, Some(expr)));
    }
}

/// Rename function-level hoisted vars inside function bodies that conflict with
/// newly created module-level hoisted var names.
/// E.g., if module-level creates `var show = ...`, a function-level
/// `var show = Data_Show.show(dictShow)` inside a function body gets renamed to `show1`.
pub(crate) fn rename_conflicting_function_hoists(expr: &mut JsExpr, conflicting_names: &HashSet<String>) {
    match expr {
        JsExpr::Function(_, _, body) => {
            // Look for VarDecl at the start of the body whose names conflict
            let mut renames: Vec<(String, String)> = Vec::new();
            for stmt in body.iter_mut() {
                if let JsStmt::VarDecl(name, _) = stmt {
                    if conflicting_names.contains(name.as_str()) {
                        // Find a non-conflicting name: name1, name2, ...
                        let base = name.clone();
                        for i in 1.. {
                            let candidate = format!("{base}{i}");
                            if !conflicting_names.contains(&candidate) {
                                renames.push((base.clone(), candidate.clone()));
                                *name = candidate;
                                break;
                            }
                        }
                    }
                }
                // Only check VarDecls at the start (before non-VarDecl stmts)
                if !matches!(stmt, JsStmt::VarDecl(..)) {
                    break;
                }
            }
            // Apply renames to the rest of the function body
            if !renames.is_empty() {
                for stmt in body.iter_mut() {
                    for (old_name, new_name) in &renames {
                        rename_var_in_stmt(stmt, old_name, new_name);
                    }
                }
            }
            // Recurse into nested expressions in the body
            for stmt in body.iter_mut() {
                rename_conflicting_in_stmt(stmt, conflicting_names);
            }
        }
        JsExpr::App(callee, args) => {
            rename_conflicting_function_hoists(callee, conflicting_names);
            for arg in args {
                rename_conflicting_function_hoists(arg, conflicting_names);
            }
        }
        JsExpr::Ternary(a, b, c) => {
            rename_conflicting_function_hoists(a, conflicting_names);
            rename_conflicting_function_hoists(b, conflicting_names);
            rename_conflicting_function_hoists(c, conflicting_names);
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields {
                rename_conflicting_function_hoists(val, conflicting_names);
            }
        }
        JsExpr::ArrayLit(items) => {
            for item in items {
                rename_conflicting_function_hoists(item, conflicting_names);
            }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            rename_conflicting_function_hoists(a, conflicting_names);
            rename_conflicting_function_hoists(b, conflicting_names);
        }
        JsExpr::Unary(_, a) | JsExpr::New(a, _) => {
            rename_conflicting_function_hoists(a, conflicting_names);
        }
        _ => {}
    }
}

pub(crate) fn rename_conflicting_in_stmt(stmt: &mut JsStmt, conflicting_names: &HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) => rename_conflicting_function_hoists(expr, conflicting_names),
        JsStmt::Return(expr) | JsStmt::Expr(expr) | JsStmt::Throw(expr) => {
            rename_conflicting_function_hoists(expr, conflicting_names);
        }
        JsStmt::Assign(target, val) => {
            rename_conflicting_function_hoists(target, conflicting_names);
            rename_conflicting_function_hoists(val, conflicting_names);
        }
        JsStmt::If(cond, then_body, else_body) => {
            rename_conflicting_function_hoists(cond, conflicting_names);
            for s in then_body { rename_conflicting_in_stmt(s, conflicting_names); }
            if let Some(stmts) = else_body {
                for s in stmts { rename_conflicting_in_stmt(s, conflicting_names); }
            }
        }
        JsStmt::Block(stmts) => {
            for s in stmts { rename_conflicting_in_stmt(s, conflicting_names); }
        }
        _ => {}
    }
}

pub(crate) fn rename_var_in_stmt(stmt: &mut JsStmt, old: &str, new: &str) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) => rename_var_in_expr(expr, old, new),
        JsStmt::Return(expr) | JsStmt::Expr(expr) | JsStmt::Throw(expr) => {
            rename_var_in_expr(expr, old, new);
        }
        JsStmt::Assign(target, val) => {
            rename_var_in_expr(target, old, new);
            rename_var_in_expr(val, old, new);
        }
        JsStmt::If(cond, then_body, else_body) => {
            rename_var_in_expr(cond, old, new);
            for s in then_body { rename_var_in_stmt(s, old, new); }
            if let Some(stmts) = else_body {
                for s in stmts { rename_var_in_stmt(s, old, new); }
            }
        }
        JsStmt::Block(stmts) => {
            for s in stmts { rename_var_in_stmt(s, old, new); }
        }
        JsStmt::For(_, init, bound, body) => {
            rename_var_in_expr(init, old, new);
            rename_var_in_expr(bound, old, new);
            for s in body { rename_var_in_stmt(s, old, new); }
        }
        JsStmt::ForIn(_, obj, body) => {
            rename_var_in_expr(obj, old, new);
            for s in body { rename_var_in_stmt(s, old, new); }
        }
        JsStmt::While(cond, body) => {
            rename_var_in_expr(cond, old, new);
            for s in body { rename_var_in_stmt(s, old, new); }
        }
        _ => {}
    }
}

pub(crate) fn rename_var_in_expr(expr: &mut JsExpr, old: &str, new: &str) {
    match expr {
        JsExpr::Var(name) if name == old => *name = new.to_string(),
        JsExpr::Function(_, params, body) => {
            // Don't rename if a parameter shadows
            if params.iter().any(|p| p == old) { return; }
            for s in body { rename_var_in_stmt(s, old, new); }
        }
        JsExpr::App(callee, args) => {
            rename_var_in_expr(callee, old, new);
            for arg in args { rename_var_in_expr(arg, old, new); }
        }
        JsExpr::Ternary(a, b, c) => {
            rename_var_in_expr(a, old, new);
            rename_var_in_expr(b, old, new);
            rename_var_in_expr(c, old, new);
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields { rename_var_in_expr(val, old, new); }
        }
        JsExpr::ArrayLit(items) => {
            for item in items { rename_var_in_expr(item, old, new); }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            rename_var_in_expr(a, old, new);
            rename_var_in_expr(b, old, new);
        }
        JsExpr::Unary(_, a) => rename_var_in_expr(a, old, new),
        JsExpr::New(callee, args) => {
            rename_var_in_expr(callee, old, new);
            for arg in args { rename_var_in_expr(arg, old, new); }
        }
        _ => {}
    }
}

/// Collect base names of dict applications that would be module-level hoistable
/// but will be optimized away by subsequent passes (string concat, boolean ops, etc.).
/// These "phantom" names affect the original compiler's Renamer naming because the
/// original compiler does CSE before optimization.
pub(crate) fn collect_phantom_module_level_names(body: &[JsStmt]) -> HashSet<String> {
    let module_vars: HashSet<String> = body.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
    }).collect();

    let mut phantoms = HashSet::new();
    for stmt in body {
        if let JsStmt::VarDecl(_, Some(init)) = stmt {
            collect_phantom_names_in_expr(init, &module_vars, &mut phantoms, 0);
        }
    }
    phantoms
}

pub(crate) fn collect_phantom_names_in_expr(expr: &JsExpr, module_vars: &HashSet<String>, phantoms: &mut HashSet<String>, depth: usize) {
    // At depth > 0 (inside a function), look for dict apps with constant module-level args
    // that will be optimized away by subsequent passes
    if depth > 0 {
        if let JsExpr::App(callee, args) = expr {
            let empty_set = HashSet::new();
            if args.len() == 1 && args.iter().all(|a| is_constant_ref(a, module_vars, &empty_set, &empty_set)) {
                if let JsExpr::ModuleAccessor(_, method) = callee.as_ref() {
                    if let JsExpr::ModuleAccessor(_, inst) = &args[0] {
                        if is_inlinable_primop(method, inst) || is_optimizable_dict_app(method, inst) {
                            phantoms.insert(method.clone());
                        }
                    }
                }
            }
        }
        // Detect `(-x) | 0` pattern which is generated from `negate(ringInt)(x)`.
        // Our compiler directly generates this instead of going through Data_Ring.negate,
        // but the original compiler's CSE would have extracted `negate(ringInt)` at module
        // level, making "negate" a phantom name.
        if let JsExpr::Binary(JsBinaryOp::BitwiseOr, lhs, rhs) = expr {
            if matches!(lhs.as_ref(), JsExpr::Unary(JsUnaryOp::Negate, _))
                && matches!(rhs.as_ref(), JsExpr::IntLit(0))
            {
                phantoms.insert("negate".to_string());
            }
        }
    }
    match expr {
        JsExpr::Function(_, _, body) => {
            for stmt in body {
                collect_phantom_names_in_stmt(stmt, module_vars, phantoms, depth + 1);
            }
        }
        JsExpr::App(callee, args) => {
            collect_phantom_names_in_expr(callee, module_vars, phantoms, depth);
            for arg in args { collect_phantom_names_in_expr(arg, module_vars, phantoms, depth); }
        }
        JsExpr::Ternary(a, b, c) => {
            collect_phantom_names_in_expr(a, module_vars, phantoms, depth);
            collect_phantom_names_in_expr(b, module_vars, phantoms, depth);
            collect_phantom_names_in_expr(c, module_vars, phantoms, depth);
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields { collect_phantom_names_in_expr(val, module_vars, phantoms, depth); }
        }
        JsExpr::ArrayLit(items) => {
            for item in items { collect_phantom_names_in_expr(item, module_vars, phantoms, depth); }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) => {
            collect_phantom_names_in_expr(a, module_vars, phantoms, depth);
            collect_phantom_names_in_expr(b, module_vars, phantoms, depth);
        }
        JsExpr::Unary(_, a) => collect_phantom_names_in_expr(a, module_vars, phantoms, depth),
        _ => {}
    }
}

pub(crate) fn collect_phantom_names_in_stmt(stmt: &JsStmt, module_vars: &HashSet<String>, phantoms: &mut HashSet<String>, depth: usize) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) | JsStmt::Return(expr) | JsStmt::Expr(expr) | JsStmt::Throw(expr) => {
            collect_phantom_names_in_expr(expr, module_vars, phantoms, depth);
        }
        JsStmt::If(cond, then_body, else_body) => {
            collect_phantom_names_in_expr(cond, module_vars, phantoms, depth);
            for s in then_body { collect_phantom_names_in_stmt(s, module_vars, phantoms, depth); }
            if let Some(stmts) = else_body {
                for s in stmts { collect_phantom_names_in_stmt(s, module_vars, phantoms, depth); }
            }
        }
        _ => {}
    }
}

/// After module-level hoisting, rename inner function-level hoisted vars
/// whose names conflict with module-level names or phantom module-level names.
/// Uses the callee's method name as the base for finding the next available suffix.
pub(crate) fn rename_inner_hoists_for_module_level(body: &mut Vec<JsStmt>, phantom_names: &HashSet<String>) {
    // Collect ALL module-level var names
    let module_names: HashSet<String> = body.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
    }).collect();

    // Build conflict set: module-level names + phantom names
    let mut conflict_set: HashSet<String> = module_names;
    conflict_set.extend(phantom_names.iter().cloned());

    // Walk each declaration's function body
    for stmt in body.iter_mut() {
        if let JsStmt::VarDecl(_, Some(init)) = stmt {
            rename_inner_hoists_in_expr(init, &conflict_set);
        }
    }
}

pub(crate) fn rename_inner_hoists_in_expr(expr: &mut JsExpr, conflict_set: &HashSet<String>) {
    if let JsExpr::Function(_, _, body) = expr {
        let mut renames: Vec<(String, String)> = Vec::new();

        // Find VarDecl at top of function body that conflict with module-level names
        for stmt in body.iter() {
            if let JsStmt::VarDecl(name, Some(init)) = stmt {
                if conflict_set.contains(name.as_str()) {
                    // Determine base name from the init expression (callee method name)
                    if let Some(base) = extract_hoisted_base_name(init) {
                        // Find next available name after all conflicting names with this base
                        let new_name = find_next_name_after_conflicts(&base, conflict_set);
                        if new_name != *name {
                            renames.push((name.clone(), new_name));
                        }
                    }
                }
            }
            // Only check leading VarDecls (hoisted vars are at the top)
            if !matches!(stmt, JsStmt::VarDecl(..)) {
                break;
            }
        }

        // Apply renames
        if !renames.is_empty() {
            // First rename VarDecl names
            for stmt in body.iter_mut() {
                if let JsStmt::VarDecl(name, _) = stmt {
                    for (old, new) in &renames {
                        if name == old {
                            *name = new.clone();
                        }
                    }
                }
            }
            // Then rename all references in the body
            for (old, new) in &renames {
                for stmt in body.iter_mut() {
                    rename_var_in_stmt(stmt, old, new);
                }
            }
        }

        // Recurse into nested expressions in the body, extending the conflict set
        // with VarDecl names from this scope to prevent inner renames from shadowing them.
        let mut inner_conflict_set = conflict_set.clone();
        for stmt in body.iter() {
            if let JsStmt::VarDecl(name, _) = stmt {
                inner_conflict_set.insert(name.clone());
            }
        }
        for stmt in body.iter_mut() {
            rename_inner_hoists_in_stmt(stmt, &inner_conflict_set);
        }
    } else {
        // Recurse into other expression types
        match expr {
            JsExpr::App(callee, args) => {
                rename_inner_hoists_in_expr(callee, conflict_set);
                for arg in args { rename_inner_hoists_in_expr(arg, conflict_set); }
            }
            JsExpr::Ternary(a, b, c) => {
                rename_inner_hoists_in_expr(a, conflict_set);
                rename_inner_hoists_in_expr(b, conflict_set);
                rename_inner_hoists_in_expr(c, conflict_set);
            }
            JsExpr::ObjectLit(fields) => {
                for (_, val) in fields { rename_inner_hoists_in_expr(val, conflict_set); }
            }
            JsExpr::ArrayLit(items) => {
                for item in items { rename_inner_hoists_in_expr(item, conflict_set); }
            }
            JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
                rename_inner_hoists_in_expr(a, conflict_set);
                rename_inner_hoists_in_expr(b, conflict_set);
            }
            JsExpr::Unary(_, a) | JsExpr::New(a, _) => {
                rename_inner_hoists_in_expr(a, conflict_set);
            }
            _ => {}
        }
    }
}

pub(crate) fn rename_inner_hoists_in_stmt(stmt: &mut JsStmt, conflict_set: &HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) => rename_inner_hoists_in_expr(expr, conflict_set),
        JsStmt::Return(expr) | JsStmt::Expr(expr) | JsStmt::Throw(expr) => {
            rename_inner_hoists_in_expr(expr, conflict_set);
        }
        JsStmt::If(_, then_body, else_body) => {
            for s in then_body { rename_inner_hoists_in_stmt(s, conflict_set); }
            if let Some(stmts) = else_body {
                for s in stmts { rename_inner_hoists_in_stmt(s, conflict_set); }
            }
        }
        JsStmt::Block(stmts) => {
            for s in stmts { rename_inner_hoists_in_stmt(s, conflict_set); }
        }
        _ => {}
    }
}

/// Extract the base name from a hoisted dict app's init expression.
/// E.g., `eq(dictEq)` → "eq", `Data_Show.show(dictShow)` → "show"
pub(crate) fn extract_hoisted_base_name(expr: &JsExpr) -> Option<String> {
    match expr {
        JsExpr::App(callee, _) => {
            match callee.as_ref() {
                JsExpr::Var(name) => Some(name.clone()),
                JsExpr::ModuleAccessor(_, name) => Some(name.clone()),
                JsExpr::App(inner_callee, _) => extract_hoisted_base_name_from_callee(inner_callee),
                _ => None,
            }
        }
        _ => None,
    }
}

pub(crate) fn extract_hoisted_base_name_from_callee(expr: &JsExpr) -> Option<String> {
    match expr {
        JsExpr::Var(name) => Some(name.clone()),
        JsExpr::ModuleAccessor(_, name) => Some(name.clone()),
        JsExpr::App(inner, _) => extract_hoisted_base_name_from_callee(inner),
        _ => None,
    }
}

/// Find the next available name for a base, skipping all names in the conflict set.
/// E.g., base "eq" with conflict set {eq, eq1, eq2} → "eq3"
pub(crate) fn find_next_name_after_conflicts(base: &str, conflict_set: &HashSet<String>) -> String {
    if !conflict_set.contains(base) && !is_js_reserved(base) && !is_js_builtin(base) {
        return base.to_string();
    }
    for i in 1.. {
        let candidate = format!("{base}{i}");
        if !conflict_set.contains(&candidate) && !is_js_reserved(&candidate) && !is_js_builtin(&candidate) {
            return candidate;
        }
    }
    unreachable!()
}

/// Check if an expression is a class method accessor pattern:
/// `function(dict) { return dict.X; }` or `function(dict) { return dict["X"]; }`
pub(crate) fn is_class_accessor_pattern(expr: &JsExpr) -> bool {
    if let JsExpr::Function(None, params, body) = expr {
        if params.len() == 1 && body.len() == 1 {
            if let JsStmt::Return(JsExpr::Indexer(obj, _)) = &body[0] {
                if let JsExpr::Var(name) = obj.as_ref() {
                    return *name == params[0];
                }
            }
        }
    }
    false
}

/// Check if an expression is a "constant" reference (module-level var or module accessor).
pub(crate) fn is_constant_ref(expr: &JsExpr, module_vars: &HashSet<String>, function_vars: &HashSet<String>, parametric_instances: &HashSet<String>) -> bool {
    match expr {
        // Imported module accessors: exclude parametric instances that need constraint args
        JsExpr::ModuleAccessor(_, name) => !parametric_instances.contains(name),
        // Module-level vars that are functions (parametric dicts) should not be
        // treated as constant refs — they need constraint args before use as dicts.
        JsExpr::Var(name) => module_vars.contains(name) && !function_vars.contains(name),
        _ => false,
    }
}

/// Extract the "method name" from an expression for naming the hoisted var.
pub(crate) fn extract_method_name(expr: &JsExpr) -> Option<String> {
    match expr {
        JsExpr::ModuleAccessor(_, name) => Some(name.clone()),
        JsExpr::Var(name) => Some(name.clone()),
        _ => None,
    }
}

/// Check if a (method, instance) pair is a known primop that the original PureScript
/// compiler inlines as a native JS operator. These applications should NOT be hoisted
/// because the original compiler eliminates them entirely via primop inlining.
pub(crate) fn is_optimizable_dict_app(method: &str, instance: &str) -> bool {
    match method {
        // String concat: append(semigroupString) → +
        "append" => instance == "semigroupString",
        _ => false,
    }
}

pub(crate) fn is_inlinable_primop(method: &str, instance: &str) -> bool {
    match method {
        // HeytingAlgebra Boolean → boolean operators
        "conj" | "disj" | "not" | "ff" | "tt" | "implies" =>
            instance == "heytingAlgebraBoolean",
        // Semiring Int/Number → arithmetic
        "add" | "zero" | "one" | "mul" =>
            matches!(instance, "semiringInt" | "semiringNumber"),
        // Ring Int/Number → subtraction
        "sub" | "negate" =>
            matches!(instance, "ringInt" | "ringNumber"),
        // EuclideanRing Number → division (Int div/mod are NOT inlined by original compiler)
        "div" =>
            matches!(instance, "euclideanRingNumber"),
        // Ord comparisons on primitives (but NOT compare, eq — those are hoisted)
        "lessThan" | "lessThanOrEq" | "greaterThan" | "greaterThanOrEq" =>
            matches!(instance, "ordInt" | "ordNumber" | "ordString" | "ordChar"),
        _ => false,
    }
}

/// Check if a name is a JavaScript reserved word or keyword.
/// Find the first available name for a hoisted var, avoiding conflicts.
/// Returns None if the base name is a JS reserved word.
pub(crate) fn find_available_name(base: &str, used_names: &HashSet<String>) -> Option<String> {
    if is_js_reserved(base) || is_js_builtin(base) {
        return None;
    }
    if !used_names.contains(base) {
        return Some(base.to_string());
    }
    for i in 1.. {
        let candidate = format!("{base}{i}");
        if !used_names.contains(&candidate) {
            return Some(candidate);
        }
    }
    unreachable!()
}

/// Recursively find hoistable constant dict applications inside function bodies.
/// `depth` tracks function nesting: 0 = top level, 1+ = inside function body.
pub(crate) fn find_module_hoistable_in_expr(
    expr: &JsExpr,
    module_vars: &HashSet<String>,
    function_vars: &HashSet<String>,
    class_accessors: &HashSet<String>,
    imported_class_methods: &HashSet<String>,
    parametric_instances: &HashSet<String>,
    hoistables: &mut Vec<(JsExpr, String)>,
    hoistable_keys: &mut HashSet<String>,
    used_names: &mut HashSet<String>,
    depth: usize,
    enclosing_decl: &str,
) {
    // Safety cap: stop collecting hoistables if we already have too many
    const MAX_HOISTABLES: usize = 500;
    if hoistables.len() >= MAX_HOISTABLES {
        return;
    }

    // Check if this expression is a hoistable constant dict application
    if depth > 0 {
        if let JsExpr::App(callee, args) = expr {
            // Don't hoist if any arg references the enclosing declaration (self-reference)
            let refs_self = args.iter().any(|a| matches!(a, JsExpr::Var(n) if n == enclosing_decl));
            let args_all_constant = args.len() <= 1 && args.iter().all(|a| is_constant_ref(a, module_vars, function_vars, parametric_instances));

            // Only hoist when we're confident this is a dict application, not an
            // expression that the original compiler would inline as a native operator:
            // 1. Zero-arg ModuleAccessor calls: Module.method() — phantom parameter unwrappers
            // 2. One-arg ModuleAccessor calls where method is a known class method
            // 3. Local class accessor applied to module-level instance: accessor(instance)
            // Skip hoisting if this is a known primop that the original compiler inlines
            let is_inlinable = if let (JsExpr::ModuleAccessor(_, method), [arg]) = (callee.as_ref(), args.as_slice()) {
                match arg {
                    JsExpr::ModuleAccessor(_, inst) | JsExpr::Var(inst) =>
                        is_inlinable_primop(method, inst),
                    _ => false,
                }
            } else if let (JsExpr::Var(method), [arg]) = (callee.as_ref(), args.as_slice()) {
                match arg {
                    JsExpr::ModuleAccessor(_, inst) | JsExpr::Var(inst) =>
                        is_inlinable_primop(method, inst),
                    _ => false,
                }
            } else {
                false
            };

            let is_hoistable = !is_inlinable && match callee.as_ref() {
                JsExpr::ModuleAccessor(_, _method) => {
                    // Module accessor calls with constant args can be hoisted
                    // This covers class methods, phantom param calls, and regular functions
                    // applied to constant instances (e.g., notEq(eqOrdering))
                    true
                },
                JsExpr::Var(name) => class_accessors.contains(name), // Local class accessor
                _ => false,
            };

            if is_hoistable && args_all_constant && !refs_self {
                // Check if already registered (O(1) via HashSet instead of linear scan)
                let key = format!("{:?}", expr);
                if !hoistable_keys.contains(&key) {
                    if let Some(base_name) = extract_method_name(callee) {
                        let base_name = crate::codegen::common::any_name_to_js(&base_name);
                        if let Some(name) = find_available_name(&base_name, used_names) {
                            used_names.insert(name.clone());
                            hoistable_keys.insert(key);
                            hoistables.push((expr.clone(), name));
                        }
                    }
                }
                return; // Don't recurse into the hoisted expression itself
            }
        }
    }

    // Recurse into sub-expressions
    match expr {
        JsExpr::Function(_, _, body_stmts) => {
            for stmt in body_stmts {
                find_module_hoistable_in_stmt(stmt, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth + 1, enclosing_decl);
            }
        }
        JsExpr::App(callee, args) => {
            find_module_hoistable_in_expr(callee, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for arg in args {
                find_module_hoistable_in_expr(arg, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        JsExpr::Ternary(a, b, c) => {
            find_module_hoistable_in_expr(a, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(b, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(c, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsExpr::ArrayLit(items) => {
            for item in items {
                find_module_hoistable_in_expr(item, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields {
                find_module_hoistable_in_expr(val, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            find_module_hoistable_in_expr(a, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(b, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsExpr::Unary(_, a) => {
            find_module_hoistable_in_expr(a, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsExpr::New(callee, args) => {
            find_module_hoistable_in_expr(callee, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for arg in args {
                find_module_hoistable_in_expr(arg, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        _ => {}
    }
}

pub(crate) fn find_module_hoistable_in_stmt(
    stmt: &JsStmt,
    module_vars: &HashSet<String>,
    function_vars: &HashSet<String>,
    class_accessors: &HashSet<String>,
    imported_class_methods: &HashSet<String>,
    parametric_instances: &HashSet<String>,
    hoistables: &mut Vec<(JsExpr, String)>,
    hoistable_keys: &mut HashSet<String>,
    used_names: &mut HashSet<String>,
    depth: usize,
    enclosing_decl: &str,
) {
    match stmt {
        JsStmt::Return(expr) | JsStmt::Expr(expr) | JsStmt::Throw(expr) => {
            find_module_hoistable_in_expr(expr, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsStmt::VarDecl(_, Some(expr)) => {
            find_module_hoistable_in_expr(expr, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsStmt::Assign(target, val) => {
            find_module_hoistable_in_expr(target, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(val, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsStmt::If(cond, then_body, else_body) => {
            find_module_hoistable_in_expr(cond, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in then_body { find_module_hoistable_in_stmt(s, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
            if let Some(stmts) = else_body {
                for s in stmts { find_module_hoistable_in_stmt(s, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
            }
        }
        JsStmt::Block(stmts) => {
            for s in stmts { find_module_hoistable_in_stmt(s, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        JsStmt::For(_, init, bound, body_stmts) => {
            find_module_hoistable_in_expr(init, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(bound, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in body_stmts { find_module_hoistable_in_stmt(s, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        JsStmt::ForIn(_, obj, body_stmts) => {
            find_module_hoistable_in_expr(obj, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in body_stmts { find_module_hoistable_in_stmt(s, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        JsStmt::While(cond, body_stmts) => {
            find_module_hoistable_in_expr(cond, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in body_stmts { find_module_hoistable_in_stmt(s, module_vars, function_vars, class_accessors, imported_class_methods, parametric_instances, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        _ => {}
    }
}

/// Replace hoistable expressions with var references throughout an expression tree.
/// Uses a HashMap keyed by Debug string for O(1) lookup instead of linear scan.
pub(crate) fn replace_module_hoistable_expr(expr: JsExpr, hoistable_map: &HashMap<String, String>) -> JsExpr {
    // Check if this entire expression matches a hoistable
    let key = format!("{:?}", &expr);
    if let Some(hoisted_name) = hoistable_map.get(&key) {
        return JsExpr::Var(hoisted_name.clone());
    }

    match expr {
        JsExpr::App(callee, args) => {
            JsExpr::App(
                Box::new(replace_module_hoistable_expr(*callee, hoistable_map)),
                args.into_iter().map(|a| replace_module_hoistable_expr(a, hoistable_map)).collect(),
            )
        }
        JsExpr::Function(name, params, body) => {
            JsExpr::Function(
                name,
                params,
                body.into_iter().map(|s| replace_module_hoistable_stmt(s, hoistable_map)).collect(),
            )
        }
        JsExpr::Ternary(a, b, c) => {
            JsExpr::Ternary(
                Box::new(replace_module_hoistable_expr(*a, hoistable_map)),
                Box::new(replace_module_hoistable_expr(*b, hoistable_map)),
                Box::new(replace_module_hoistable_expr(*c, hoistable_map)),
            )
        }
        JsExpr::ArrayLit(items) => {
            JsExpr::ArrayLit(items.into_iter().map(|i| replace_module_hoistable_expr(i, hoistable_map)).collect())
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(fields.into_iter().map(|(k, v)| (k, replace_module_hoistable_expr(v, hoistable_map))).collect())
        }
        JsExpr::Indexer(a, b) => {
            JsExpr::Indexer(
                Box::new(replace_module_hoistable_expr(*a, hoistable_map)),
                Box::new(replace_module_hoistable_expr(*b, hoistable_map)),
            )
        }
        JsExpr::Binary(op, a, b) => {
            JsExpr::Binary(
                op,
                Box::new(replace_module_hoistable_expr(*a, hoistable_map)),
                Box::new(replace_module_hoistable_expr(*b, hoistable_map)),
            )
        }
        JsExpr::Unary(op, a) => {
            JsExpr::Unary(op, Box::new(replace_module_hoistable_expr(*a, hoistable_map)))
        }
        JsExpr::InstanceOf(a, b) => {
            JsExpr::InstanceOf(
                Box::new(replace_module_hoistable_expr(*a, hoistable_map)),
                Box::new(replace_module_hoistable_expr(*b, hoistable_map)),
            )
        }
        JsExpr::New(callee, args) => {
            JsExpr::New(
                Box::new(replace_module_hoistable_expr(*callee, hoistable_map)),
                args.into_iter().map(|a| replace_module_hoistable_expr(a, hoistable_map)).collect(),
            )
        }
        other => other,
    }
}

pub(crate) fn replace_module_hoistable_stmt(stmt: JsStmt, hoistable_map: &HashMap<String, String>) -> JsStmt {
    match stmt {
        JsStmt::Return(expr) => JsStmt::Return(replace_module_hoistable_expr(expr, hoistable_map)),
        JsStmt::Expr(expr) => JsStmt::Expr(replace_module_hoistable_expr(expr, hoistable_map)),
        JsStmt::Throw(expr) => JsStmt::Throw(replace_module_hoistable_expr(expr, hoistable_map)),
        JsStmt::VarDecl(name, Some(expr)) => JsStmt::VarDecl(name, Some(replace_module_hoistable_expr(expr, hoistable_map))),
        JsStmt::Assign(target, val) => JsStmt::Assign(
            replace_module_hoistable_expr(target, hoistable_map),
            replace_module_hoistable_expr(val, hoistable_map),
        ),
        JsStmt::If(cond, then_body, else_body) => {
            JsStmt::If(
                replace_module_hoistable_expr(cond, hoistable_map),
                then_body.into_iter().map(|s| replace_module_hoistable_stmt(s, hoistable_map)).collect(),
                else_body.map(|stmts| stmts.into_iter().map(|s| replace_module_hoistable_stmt(s, hoistable_map)).collect()),
            )
        }
        JsStmt::Block(stmts) => {
            JsStmt::Block(stmts.into_iter().map(|s| replace_module_hoistable_stmt(s, hoistable_map)).collect())
        }
        JsStmt::For(var, init, bound, body) => {
            JsStmt::For(
                var,
                replace_module_hoistable_expr(init, hoistable_map),
                replace_module_hoistable_expr(bound, hoistable_map),
                body.into_iter().map(|s| replace_module_hoistable_stmt(s, hoistable_map)).collect(),
            )
        }
        JsStmt::ForIn(var, obj, body) => {
            JsStmt::ForIn(
                var,
                replace_module_hoistable_expr(obj, hoistable_map),
                body.into_iter().map(|s| replace_module_hoistable_stmt(s, hoistable_map)).collect(),
            )
        }
        JsStmt::While(cond, body) => {
            JsStmt::While(
                replace_module_hoistable_expr(cond, hoistable_map),
                body.into_iter().map(|s| replace_module_hoistable_stmt(s, hoistable_map)).collect(),
            )
        }
        other => other,
    }
}

/// Convert fully-saturated `Ctor.create(a)(b)` into `new Ctor(a, b)`.
/// Reorder where-clause bindings: reverse source order, preserving dependencies.
/// The original PureScript compiler processes where bindings in reverse order
/// but ensures that any binding that depends on another comes after it.
pub(crate) fn reorder_where_bindings(stmts: &mut [JsStmt]) {
    let n = stmts.len();
    if n <= 1 { return; }

    // Collect binding names and their indices
    let binding_names: Vec<Option<String>> = stmts.iter().map(|s| {
        if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
    }).collect();

    // Collect which binding names each stmt references
    let mut deps: Vec<HashSet<usize>> = Vec::with_capacity(n);
    for (i, stmt) in stmts.iter().enumerate() {
        let mut refs = HashSet::new();
        if let JsStmt::VarDecl(_, Some(init)) = stmt {
            let mut var_refs = HashSet::new();
            collect_var_refs_in_expr(init, &mut var_refs);
            for (j, bn) in binding_names.iter().enumerate() {
                if i != j {
                    if let Some(name) = bn {
                        if var_refs.contains(name) {
                            refs.insert(j);
                        }
                    }
                }
            }
        }
        deps.push(refs);
    }

    // Level-based topological sort: emit bindings level by level.
    // Within each level, use reverse alphabetical order by binding name
    // (matching the original PureScript compiler's CoreFn ordering).
    let mut emitted = vec![false; n];
    let mut order: Vec<usize> = Vec::with_capacity(n);

    loop {
        let mut level: Vec<usize> = Vec::new();
        for i in 0..n {
            if !emitted[i] && deps[i].iter().all(|d| emitted[*d]) {
                level.push(i);
            }
        }
        if level.is_empty() { break; }
        // Sort by binding name in reverse alphabetical order
        level.sort_by(|a, b| {
            let name_a = binding_names[*a].as_deref().unwrap_or("");
            let name_b = binding_names[*b].as_deref().unwrap_or("");
            name_b.cmp(name_a)
        });
        for &i in &level {
            emitted[i] = true;
        }
        order.extend(level);
    }
    // Handle any remaining (circular deps) — preserve source order
    // so that function definitions come before their call sites
    for i in 0..n {
        if !emitted[i] {
            order.push(i);
        }
    }

    // Reorder stmts in place
    let stmts_copy: Vec<JsStmt> = stmts.to_vec();
    for (target, &source) in order.iter().enumerate() {
        stmts[target] = stmts_copy[source].clone();
    }
}

/// Collect all Var names referenced in a JS expression
pub(crate) fn collect_var_refs_in_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
    match expr {
        JsExpr::Var(name) => { refs.insert(name.clone()); }
        JsExpr::App(callee, args) => {
            collect_var_refs_in_expr(callee, refs);
            for arg in args { collect_var_refs_in_expr(arg, refs); }
        }
        JsExpr::Function(_, _, body) => {
            for s in body { collect_var_refs_in_stmt(s, refs); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_var_refs_in_expr(v, refs); }
        }
        JsExpr::ArrayLit(items) => {
            for item in items { collect_var_refs_in_expr(item, refs); }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            collect_var_refs_in_expr(a, refs);
            collect_var_refs_in_expr(b, refs);
        }
        JsExpr::Unary(_, a) | JsExpr::New(a, _) => {
            collect_var_refs_in_expr(a, refs);
        }
        JsExpr::Ternary(a, b, c) => {
            collect_var_refs_in_expr(a, refs);
            collect_var_refs_in_expr(b, refs);
            collect_var_refs_in_expr(c, refs);
        }
        JsExpr::ModuleAccessor(_, _) | JsExpr::NumericLit(_) | JsExpr::IntLit(_) |
        JsExpr::StringLit(_) | JsExpr::BoolLit(_) | JsExpr::RawJs(_) => {}
    }
}

pub(crate) fn collect_var_refs_in_stmt(stmt: &JsStmt, refs: &mut HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(_, Some(e)) | JsStmt::Return(e) | JsStmt::Expr(e) | JsStmt::Throw(e) => {
            collect_var_refs_in_expr(e, refs);
        }
        JsStmt::Assign(a, b) => {
            collect_var_refs_in_expr(a, refs);
            collect_var_refs_in_expr(b, refs);
        }
        JsStmt::If(c, t, e) => {
            collect_var_refs_in_expr(c, refs);
            for s in t { collect_var_refs_in_stmt(s, refs); }
            if let Some(stmts) = e { for s in stmts { collect_var_refs_in_stmt(s, refs); } }
        }
        JsStmt::Block(stmts) => { for s in stmts { collect_var_refs_in_stmt(s, refs); } }
        _ => {}
    }
}

/// Recursively collects curried args and checks if the base is a `.create` accessor.
/// Processes the entire expression tree deeply, converting all Ctor.create(a)(b) to new Ctor(a, b).
pub(crate) fn uncurry_create_to_new(expr: JsExpr, ctor_arities: &HashMap<String, usize>) -> JsExpr {
    // First, try to uncurry at this level
    let expr = uncurry_create_to_new_shallow(expr, ctor_arities);
    // Then recurse into sub-expressions
    match expr {
        JsExpr::Function(name, params, body) => {
            JsExpr::Function(name, params, body.into_iter().map(|s| uncurry_create_to_new_stmt(s, ctor_arities)).collect())
        }
        JsExpr::App(callee, args) => {
            JsExpr::App(
                Box::new(uncurry_create_to_new(*callee, ctor_arities)),
                args.into_iter().map(|e| uncurry_create_to_new(e, ctor_arities)).collect(),
            )
        }
        JsExpr::New(callee, args) => {
            JsExpr::New(
                Box::new(uncurry_create_to_new(*callee, ctor_arities)),
                args.into_iter().map(|e| uncurry_create_to_new(e, ctor_arities)).collect(),
            )
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(fields.into_iter().map(|(k, v)| (k, uncurry_create_to_new(v, ctor_arities))).collect())
        }
        JsExpr::ArrayLit(items) => {
            JsExpr::ArrayLit(items.into_iter().map(|e| uncurry_create_to_new(e, ctor_arities)).collect())
        }
        JsExpr::Ternary(a, b, c) => {
            JsExpr::Ternary(
                Box::new(uncurry_create_to_new(*a, ctor_arities)),
                Box::new(uncurry_create_to_new(*b, ctor_arities)),
                Box::new(uncurry_create_to_new(*c, ctor_arities)),
            )
        }
        JsExpr::Binary(op, a, b) => {
            JsExpr::Binary(op, Box::new(uncurry_create_to_new(*a, ctor_arities)), Box::new(uncurry_create_to_new(*b, ctor_arities)))
        }
        JsExpr::Unary(op, a) => {
            JsExpr::Unary(op, Box::new(uncurry_create_to_new(*a, ctor_arities)))
        }
        JsExpr::Indexer(a, b) => {
            JsExpr::Indexer(Box::new(uncurry_create_to_new(*a, ctor_arities)), Box::new(uncurry_create_to_new(*b, ctor_arities)))
        }
        other => other,
    }
}

pub(crate) fn uncurry_create_to_new_stmt(stmt: JsStmt, ctor_arities: &HashMap<String, usize>) -> JsStmt {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => JsStmt::VarDecl(name, Some(uncurry_create_to_new(expr, ctor_arities))),
        JsStmt::Return(expr) => JsStmt::Return(uncurry_create_to_new(expr, ctor_arities)),
        JsStmt::Expr(expr) => JsStmt::Expr(uncurry_create_to_new(expr, ctor_arities)),
        JsStmt::Throw(expr) => JsStmt::Throw(uncurry_create_to_new(expr, ctor_arities)),
        JsStmt::Assign(a, b) => JsStmt::Assign(uncurry_create_to_new(a, ctor_arities), uncurry_create_to_new(b, ctor_arities)),
        JsStmt::If(cond, then_b, else_b) => JsStmt::If(
            uncurry_create_to_new(cond, ctor_arities),
            then_b.into_iter().map(|s| uncurry_create_to_new_stmt(s, ctor_arities)).collect(),
            else_b.map(|stmts| stmts.into_iter().map(|s| uncurry_create_to_new_stmt(s, ctor_arities)).collect()),
        ),
        JsStmt::Block(stmts) => JsStmt::Block(stmts.into_iter().map(|s| uncurry_create_to_new_stmt(s, ctor_arities)).collect()),
        JsStmt::For(v, init, bound, body) => JsStmt::For(
            v, uncurry_create_to_new(init, ctor_arities), uncurry_create_to_new(bound, ctor_arities),
            body.into_iter().map(|s| uncurry_create_to_new_stmt(s, ctor_arities)).collect(),
        ),
        JsStmt::While(cond, body) => JsStmt::While(
            uncurry_create_to_new(cond, ctor_arities),
            body.into_iter().map(|s| uncurry_create_to_new_stmt(s, ctor_arities)).collect(),
        ),
        other => other,
    }
}

/// Shallow uncurry: collects curried args at this level only.
pub(crate) fn uncurry_create_to_new_shallow(expr: JsExpr, ctor_arities: &HashMap<String, usize>) -> JsExpr {
    // Collect curried args: App(App(App(base, a), b), c) → (base, [a, b, c])
    let mut args = Vec::new();
    let mut current = expr;
    loop {
        match current {
            JsExpr::App(callee, mut call_args) if call_args.len() == 1 => {
                args.push(call_args.pop().unwrap());
                current = *callee;
            }
            _ => break,
        }
    }
    if args.is_empty() {
        return current;
    }
    args.reverse();
    // Check if base is Ctor.create (Indexer with "create") and arity matches
    if let JsExpr::Indexer(ctor, key) = &current {
        if let JsExpr::StringLit(s) = key.as_ref() {
            if s == "create" {
                // Extract constructor name to check arity
                let ctor_name = match ctor.as_ref() {
                    JsExpr::ModuleAccessor(_, name) => Some(name.as_str()),
                    JsExpr::Var(name) => Some(name.as_str()),
                    _ => None,
                };
                let arity_matches = ctor_name
                    .and_then(|name| ctor_arities.get(name))
                    .map_or(false, |arity| args.len() == *arity);
                if arity_matches {
                    return JsExpr::New(ctor.clone(), args);
                }
            }
        }
    }
    // Not a create call — reconstruct
    let mut result = current;
    for arg in args {
        result = JsExpr::App(Box::new(result), vec![arg]);
    }
    result
}

/// Check if a JS expression references a constructor (.value or .create or new Ctor)
/// at the expression level (not inside nested function bodies).
/// Used to determine if a top-level binding needs IIFE wrapping.
pub(crate) fn references_constructor(expr: &JsExpr) -> bool {
    match expr {
        JsExpr::Indexer(_, key) => {
            if let JsExpr::StringLit(s) = key.as_ref() {
                s == "value" || s == "create"
            } else {
                false
            }
        }
        JsExpr::New(_, _) => true,
        JsExpr::App(callee, args) => {
            references_constructor(callee) || args.iter().any(references_constructor)
        }
        JsExpr::ObjectLit(fields) => {
            fields.iter().any(|(_, v)| references_constructor_shallow(v))
        }
        _ => false,
    }
}

/// Shallow check: detects constructor refs in an expression without descending
/// into nested function bodies. Used for object literal field values where we
/// only care about direct references, not references inside lambdas.
pub(crate) fn references_constructor_shallow(expr: &JsExpr) -> bool {
    match expr {
        JsExpr::Indexer(_, key) => {
            if let JsExpr::StringLit(s) = key.as_ref() {
                s == "value" || s == "create"
            } else {
                false
            }
        }
        JsExpr::New(_, _) => true,
        JsExpr::App(callee, args) => {
            references_constructor_shallow(callee) || args.iter().any(references_constructor_shallow)
        }
        // Don't descend into function bodies
        JsExpr::Function(_, _, _) => false,
        _ => false,
    }
}

/// Optimize string concatenation:
/// `Data_Semigroup.append(Data_Semigroup.semigroupString)(a)(b)` → `a + b`
/// Also handles hoisted: `var append = Data_Semigroup.append(Data_Semigroup.semigroupString);`
/// followed by `append(a)(b)` → `a + b`
pub(crate) fn optimize_string_concat_stmt(stmt: JsStmt) -> JsStmt {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => {
            JsStmt::VarDecl(name, Some(optimize_string_concat_expr(expr)))
        }
        JsStmt::Return(expr) => JsStmt::Return(optimize_string_concat_expr(expr)),
        JsStmt::Expr(expr) => JsStmt::Expr(optimize_string_concat_expr(expr)),
        JsStmt::If(cond, then_body, else_body) => JsStmt::If(
            optimize_string_concat_expr(cond),
            then_body.into_iter().map(optimize_string_concat_stmt).collect(),
            else_body.map(|b| b.into_iter().map(optimize_string_concat_stmt).collect()),
        ),
        JsStmt::Throw(expr) => JsStmt::Throw(optimize_string_concat_expr(expr)),
        JsStmt::Assign(lhs, rhs) => JsStmt::Assign(
            optimize_string_concat_expr(lhs),
            optimize_string_concat_expr(rhs),
        ),
        other => other,
    }
}

pub(crate) fn optimize_string_concat_expr(expr: JsExpr) -> JsExpr {
    // Pattern: App(App(App(ModuleAccessor("...", "append"), ModuleAccessor("...", "semigroupString")), a), b)
    // → Binary(Add, a, b)
    match expr {
        JsExpr::App(callee, args) if args.len() == 1 => {
            // Check for append(semigroupString)(a)(b) — 3-level nested App
            if is_string_append_call(&callee, &args) {
                // Unwrap: App(App(App(append, semigroupString), a), b)
                let b = args.into_iter().next().unwrap();
                if let JsExpr::App(_inner_callee, inner_args) = *callee {
                    let a = inner_args.into_iter().next().unwrap();
                    let a = optimize_string_concat_expr(a);
                    let b = optimize_string_concat_expr(b);
                    return JsExpr::Binary(JsBinaryOp::Add, Box::new(a), Box::new(b));
                }
                unreachable!()
            }
            let callee = optimize_string_concat_expr(*callee);
            let args: Vec<JsExpr> = args.into_iter().map(optimize_string_concat_expr).collect();
            JsExpr::App(Box::new(callee), args)
        }
        JsExpr::App(callee, args) => {
            let callee = optimize_string_concat_expr(*callee);
            let args: Vec<JsExpr> = args.into_iter().map(optimize_string_concat_expr).collect();
            JsExpr::App(Box::new(callee), args)
        }
        JsExpr::Function(name, params, body) => {
            let body: Vec<JsStmt> = body.into_iter().map(optimize_string_concat_stmt).collect();
            JsExpr::Function(name, params, body)
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(fields.into_iter().map(|(k, v)| (k, optimize_string_concat_expr(v))).collect())
        }
        JsExpr::Binary(op, l, r) => {
            JsExpr::Binary(op, Box::new(optimize_string_concat_expr(*l)), Box::new(optimize_string_concat_expr(*r)))
        }
        JsExpr::Ternary(c, t, e) => {
            JsExpr::Ternary(Box::new(optimize_string_concat_expr(*c)), Box::new(optimize_string_concat_expr(*t)), Box::new(optimize_string_concat_expr(*e)))
        }
        other => other,
    }
}

pub(crate) fn is_semigroup_append(expr: &JsExpr) -> bool {
    matches!(expr, JsExpr::ModuleAccessor(_, field) if field == "append")
}

pub(crate) fn is_semigroup_string(expr: &JsExpr) -> bool {
    matches!(expr, JsExpr::ModuleAccessor(_, field) if field == "semigroupString")
}

/// Check if an expression is `App(App(append, semigroupString), a)` applied to `[b]`
pub(crate) fn is_string_append_call(callee: &JsExpr, _args: &[JsExpr]) -> bool {
    // callee should be App(App(append, semigroupString), a)
    if let JsExpr::App(inner, inner_args) = callee {
        if inner_args.len() == 1 {
            if let JsExpr::App(base, base_args) = inner.as_ref() {
                return base_args.len() == 1 && is_semigroup_append(base) && is_semigroup_string(&base_args[0]);
            }
        }
    }
    false
}

/// Optimize boolean operations:
/// conj(heytingAlgebraBoolean)(a)(b) → a && b
/// disj(heytingAlgebraBoolean)(a)(b) → a || b
pub(crate) fn optimize_boolean_ops_stmt(stmt: JsStmt) -> JsStmt {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => JsStmt::VarDecl(name, Some(optimize_boolean_ops_expr(expr))),
        JsStmt::Return(expr) => JsStmt::Return(optimize_boolean_ops_expr(expr)),
        JsStmt::Expr(expr) => JsStmt::Expr(optimize_boolean_ops_expr(expr)),
        JsStmt::Throw(expr) => JsStmt::Throw(optimize_boolean_ops_expr(expr)),
        JsStmt::If(cond, then_body, else_body) => JsStmt::If(
            optimize_boolean_ops_expr(cond),
            then_body.into_iter().map(optimize_boolean_ops_stmt).collect(),
            else_body.map(|b| b.into_iter().map(optimize_boolean_ops_stmt).collect()),
        ),
        JsStmt::Assign(lhs, rhs) => JsStmt::Assign(optimize_boolean_ops_expr(lhs), optimize_boolean_ops_expr(rhs)),
        other => other,
    }
}

pub(crate) fn optimize_boolean_ops_expr(expr: JsExpr) -> JsExpr {
    match expr {
        JsExpr::App(callee, args) if args.len() == 1 => {
            // Check for conj/disj(heytingAlgebraBoolean)(a)(b)
            if let Some((op, a, b)) = is_boolean_op_call(&callee, &args) {
                let a = optimize_boolean_ops_expr(a);
                let b = optimize_boolean_ops_expr(b);
                return JsExpr::Binary(op, Box::new(a), Box::new(b));
            }
            let callee = optimize_boolean_ops_expr(*callee);
            let args: Vec<JsExpr> = args.into_iter().map(optimize_boolean_ops_expr).collect();
            JsExpr::App(Box::new(callee), args)
        }
        JsExpr::App(callee, args) => {
            let callee = optimize_boolean_ops_expr(*callee);
            let args: Vec<JsExpr> = args.into_iter().map(optimize_boolean_ops_expr).collect();
            JsExpr::App(Box::new(callee), args)
        }
        JsExpr::Function(name, params, body) => {
            JsExpr::Function(name, params, body.into_iter().map(optimize_boolean_ops_stmt).collect())
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(fields.into_iter().map(|(k, v)| (k, optimize_boolean_ops_expr(v))).collect())
        }
        JsExpr::Binary(op, l, r) => {
            JsExpr::Binary(op, Box::new(optimize_boolean_ops_expr(*l)), Box::new(optimize_boolean_ops_expr(*r)))
        }
        JsExpr::Ternary(c, t, e) => {
            JsExpr::Ternary(
                Box::new(optimize_boolean_ops_expr(*c)),
                Box::new(optimize_boolean_ops_expr(*t)),
                Box::new(optimize_boolean_ops_expr(*e)),
            )
        }
        JsExpr::New(callee, args) => {
            JsExpr::New(
                Box::new(optimize_boolean_ops_expr(*callee)),
                args.into_iter().map(optimize_boolean_ops_expr).collect(),
            )
        }
        other => other,
    }
}

/// Check if an expression is Module.conj(Module.heytingAlgebraBoolean)(a)(b)
/// Only matches fully-qualified (ModuleAccessor) references, not local refs.
/// Returns (operator, a, b) if matched.
pub(crate) fn is_boolean_op_call(callee: &JsExpr, args: &[JsExpr]) -> Option<(JsBinaryOp, JsExpr, JsExpr)> {
    // callee: App(App(conj/disj, heytingAlgebraBoolean), a), args: [b]
    if let JsExpr::App(inner, inner_args) = callee {
        if inner_args.len() == 1 {
            if let JsExpr::App(base, base_args) = inner.as_ref() {
                if base_args.len() == 1 && is_heyting_boolean_qualified(&base_args[0]) {
                    let op = match base.as_ref() {
                        JsExpr::ModuleAccessor(_, name) if name == "conj" => Some(JsBinaryOp::And),
                        JsExpr::ModuleAccessor(_, name) if name == "disj" => Some(JsBinaryOp::Or),
                        _ => None,
                    };
                    if let Some(op) = op {
                        let a = inner_args[0].clone();
                        let b = args[0].clone();
                        return Some((op, a, b));
                    }
                }
            }
        }
    }
    None
}

pub(crate) fn is_heyting_boolean_qualified(expr: &JsExpr) -> bool {
    matches!(expr, JsExpr::ModuleAccessor(_, name) if name == "heytingAlgebraBoolean")
}

/// Inline common numeric, comparison, and constant operations.
/// Matches the original PureScript compiler's `inlineCommonOperators` and `inlineCommonValues`.
pub(crate) fn optimize_common_ops_stmt(stmt: JsStmt) -> JsStmt {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => JsStmt::VarDecl(name, Some(optimize_common_ops_expr(expr))),
        JsStmt::Return(expr) => JsStmt::Return(optimize_common_ops_expr(expr)),
        JsStmt::If(cond, then_stmts, else_stmts) => JsStmt::If(
            optimize_common_ops_expr(cond),
            then_stmts.into_iter().map(optimize_common_ops_stmt).collect(),
            else_stmts.map(|s| s.into_iter().map(optimize_common_ops_stmt).collect()),
        ),
        JsStmt::Throw(expr) => JsStmt::Throw(optimize_common_ops_expr(expr)),
        JsStmt::Expr(expr) => JsStmt::Expr(optimize_common_ops_expr(expr)),
        JsStmt::ForIn(v, expr, body) => JsStmt::ForIn(
            v, optimize_common_ops_expr(expr),
            body.into_iter().map(optimize_common_ops_stmt).collect(),
        ),
        JsStmt::While(cond, body) => JsStmt::While(
            optimize_common_ops_expr(cond),
            body.into_iter().map(optimize_common_ops_stmt).collect(),
        ),
        other => other,
    }
}

pub(crate) fn optimize_common_ops_expr(expr: JsExpr) -> JsExpr {
    match expr {
        JsExpr::App(callee, args) if args.len() == 1 => {
            // Check for binary ops: method(dict)(a)(b) — outermost App has [b]
            if let Some(result) = try_inline_binary_op(&callee, &args) {
                return optimize_common_ops_expr(result);
            }
            // Check for unary ops: negate(dict)(a) or not(dict)(a)
            if let Some(result) = try_inline_unary_op(&callee, &args) {
                return optimize_common_ops_expr(result);
            }
            let callee = optimize_common_ops_expr(*callee);
            let args: Vec<JsExpr> = args.into_iter().map(optimize_common_ops_expr).collect();
            JsExpr::App(Box::new(callee), args)
        }
        JsExpr::App(callee, args) if args.is_empty() => {
            // Check for nullary constants: zero(dict)() or one(dict)()
            // Pattern: App(App(method, dict), []) — method(dict)
            if let Some(result) = try_inline_constant(&callee) {
                return result;
            }
            let callee = optimize_common_ops_expr(*callee);
            JsExpr::App(Box::new(callee), args)
        }
        JsExpr::App(callee, args) => {
            let callee = optimize_common_ops_expr(*callee);
            let args: Vec<JsExpr> = args.into_iter().map(optimize_common_ops_expr).collect();
            JsExpr::App(Box::new(callee), args)
        }
        JsExpr::Function(name, params, body) => {
            JsExpr::Function(name, params, body.into_iter().map(optimize_common_ops_stmt).collect())
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(fields.into_iter().map(|(k, v)| (k, optimize_common_ops_expr(v))).collect())
        }
        JsExpr::Binary(op, l, r) => {
            JsExpr::Binary(op, Box::new(optimize_common_ops_expr(*l)), Box::new(optimize_common_ops_expr(*r)))
        }
        JsExpr::Unary(op, x) => {
            JsExpr::Unary(op, Box::new(optimize_common_ops_expr(*x)))
        }
        JsExpr::Ternary(c, t, e) => {
            JsExpr::Ternary(
                Box::new(optimize_common_ops_expr(*c)),
                Box::new(optimize_common_ops_expr(*t)),
                Box::new(optimize_common_ops_expr(*e)),
            )
        }
        JsExpr::New(callee, args) => {
            JsExpr::New(
                Box::new(optimize_common_ops_expr(*callee)),
                args.into_iter().map(optimize_common_ops_expr).collect(),
            )
        }
        JsExpr::ArrayLit(items) => {
            JsExpr::ArrayLit(items.into_iter().map(optimize_common_ops_expr).collect())
        }
        JsExpr::Indexer(obj, idx) => {
            JsExpr::Indexer(Box::new(optimize_common_ops_expr(*obj)), Box::new(optimize_common_ops_expr(*idx)))
        }
        other => other,
    }
}

/// Check for method(dict) — returns the method name and whether the dict is for a specific type.
pub(crate) fn extract_method_and_dict(expr: &JsExpr) -> Option<(&str, &str, &str)> {
    // Pattern: App(ModuleAccessor(module, method), [ModuleAccessor(_, dict)])
    if let JsExpr::App(callee, args) = expr {
        if args.len() == 1 {
            if let (JsExpr::ModuleAccessor(_, method), JsExpr::ModuleAccessor(_, dict)) = (callee.as_ref(), &args[0]) {
                return Some(("", method.as_str(), dict.as_str()));
            }
        }
    }
    None
}

/// Try to inline a binary operation: method(dict)(a)(b) → a OP b
pub(crate) fn try_inline_binary_op(callee: &JsExpr, args: &[JsExpr]) -> Option<JsExpr> {
    // callee = App(App(method, dict), a), args = [b]
    if let JsExpr::App(inner, inner_args) = callee {
        if inner_args.len() == 1 {
            if let Some((_, method, dict)) = extract_method_and_dict(inner) {
                let a = inner_args[0].clone();
                let b = args[0].clone();
                // Number binary ops → direct operator
                let number_op = match (method, dict) {
                    ("add", "semiringNumber") => Some(JsBinaryOp::Add),
                    ("mul", "semiringNumber") => Some(JsBinaryOp::Mul),
                    ("sub", "ringNumber") => Some(JsBinaryOp::Sub),
                    ("div", "euclideanRingNumber") => Some(JsBinaryOp::Div),
                    // Comparison ops
                    ("eq", d) if is_eq_dict(d) => Some(JsBinaryOp::StrictEq),
                    ("notEq", d) if is_eq_dict(d) => Some(JsBinaryOp::StrictNeq),
                    ("lessThan", d) if is_ord_dict(d) => Some(JsBinaryOp::Lt),
                    ("lessThanOrEq", d) if is_ord_dict(d) => Some(JsBinaryOp::Lte),
                    ("greaterThan", d) if is_ord_dict(d) => Some(JsBinaryOp::Gt),
                    ("greaterThanOrEq", d) if is_ord_dict(d) => Some(JsBinaryOp::Gte),
                    _ => None,
                };
                if let Some(op) = number_op {
                    return Some(JsExpr::Binary(op, Box::new(a), Box::new(b)));
                }
                // Int binary ops → (a OP b) | 0
                let int_op = match (method, dict) {
                    ("add", "semiringInt") => Some(JsBinaryOp::Add),
                    ("mul", "semiringInt") => Some(JsBinaryOp::Mul),
                    ("sub", "ringInt") => Some(JsBinaryOp::Sub),
                    _ => None,
                };
                if let Some(op) = int_op {
                    return Some(JsExpr::Binary(
                        JsBinaryOp::BitwiseOr,
                        Box::new(JsExpr::Binary(op, Box::new(a), Box::new(b))),
                        Box::new(JsExpr::IntLit(0)),
                    ));
                }
            }
        }
    }
    None
}

/// Try to inline a unary operation: negate(dict)(a) → -a
pub(crate) fn try_inline_unary_op(callee: &JsExpr, args: &[JsExpr]) -> Option<JsExpr> {
    // callee = App(method, dict), args = [a]
    if let Some((_, method, dict)) = extract_method_and_dict(callee) {
        let a = args[0].clone();
        match (method, dict) {
            ("negate", "ringNumber") => {
                return Some(JsExpr::Unary(JsUnaryOp::Negate, Box::new(a)));
            }
            ("negate", "ringInt") => {
                return Some(JsExpr::Binary(
                    JsBinaryOp::BitwiseOr,
                    Box::new(JsExpr::Unary(JsUnaryOp::Negate, Box::new(a))),
                    Box::new(JsExpr::IntLit(0)),
                ));
            }
            ("not", "heytingAlgebraBoolean") => {
                return Some(JsExpr::Unary(JsUnaryOp::Not, Box::new(a)));
            }
            _ => {}
        }
    }
    None
}

/// Try to inline a constant: zero(semiringInt) → 0, one(semiringNumber) → 1, etc.
pub(crate) fn try_inline_constant(callee: &JsExpr) -> Option<JsExpr> {
    if let Some((_, method, dict)) = extract_method_and_dict(callee) {
        match (method, dict) {
            ("zero", "semiringInt") | ("zero", "semiringNumber") => return Some(JsExpr::IntLit(0)),
            ("one", "semiringInt") | ("one", "semiringNumber") => return Some(JsExpr::IntLit(1)),
            ("bottom", "boundedBoolean") => return Some(JsExpr::BoolLit(false)),
            ("top", "boundedBoolean") => return Some(JsExpr::BoolLit(true)),
            _ => {}
        }
    }
    None
}

pub(crate) fn is_eq_dict(dict: &str) -> bool {
    matches!(dict, "eqInt" | "eqNumber" | "eqString" | "eqChar" | "eqBoolean")
}

pub(crate) fn is_ord_dict(dict: &str) -> bool {
    matches!(dict, "ordInt" | "ordNumber" | "ordString" | "ordChar" | "ordBoolean")
}

/// Inline trivial alias bindings: if `var x = y;` where y is a simple variable
/// that's a function parameter (not another where binding), replace all
/// subsequent uses of `x` with `y` and remove the binding.
pub(crate) fn inline_trivial_aliases(stmts: &mut Vec<JsStmt>) {
    let mut var_aliases: Vec<(String, String)> = Vec::new(); // (alias_name, target_name)
    let mut expr_aliases: Vec<(String, JsExpr)> = Vec::new(); // (alias_name, target_expr) for module accessors
    let mut to_remove: Vec<usize> = Vec::new();

    // First pass: find trivial alias bindings
    let binding_names: HashSet<String> = stmts.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
    }).collect();

    for (i, stmt) in stmts.iter().enumerate() {
        if let JsStmt::VarDecl(name, Some(expr)) = stmt {
            match expr {
                JsExpr::Var(target) => {
                    // Only inline if target is NOT another where binding (it's a param)
                    if !binding_names.contains(target) || var_aliases.iter().any(|(_, t)| t == target) {
                        var_aliases.push((name.clone(), target.clone()));
                        to_remove.push(i);
                    }
                }
                JsExpr::ModuleAccessor(_, _) => {
                    // Inline module accessor aliases like `var coerce = $foreign.unsafeCoerce`
                    expr_aliases.push((name.clone(), expr.clone()));
                    to_remove.push(i);
                }
                _ => {}
            }
        }
    }

    if var_aliases.is_empty() && expr_aliases.is_empty() {
        return;
    }

    // Remove alias bindings (in reverse to preserve indices)
    for i in to_remove.into_iter().rev() {
        stmts.remove(i);
    }

    // Replace var alias occurrences
    for (alias_name, target_name) in &var_aliases {
        for stmt in stmts.iter_mut() {
            substitute_var_in_stmt(stmt, alias_name, target_name);
        }
    }

    // Replace expr alias occurrences
    for (alias_name, target_expr) in &expr_aliases {
        for stmt in stmts.iter_mut() {
            substitute_var_with_expr_in_stmt(stmt, alias_name, target_expr);
        }
    }
}
