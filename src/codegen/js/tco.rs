
use super::*;

/// Recursively apply `inline_trivial_aliases` to all function bodies in a statement.
pub(crate) fn substitute_var_in_stmt(stmt: &mut JsStmt, from: &str, to: &str) {
    match stmt {
        JsStmt::Return(expr) => substitute_var_in_expr(expr, from, to),
        JsStmt::VarDecl(_, Some(expr)) => substitute_var_in_expr(expr, from, to),
        JsStmt::Expr(expr) => substitute_var_in_expr(expr, from, to),
        JsStmt::If(cond, then_body, else_body) => {
            substitute_var_in_expr(cond, from, to);
            for s in then_body { substitute_var_in_stmt(s, from, to); }
            if let Some(stmts) = else_body {
                for s in stmts { substitute_var_in_stmt(s, from, to); }
            }
        }
        JsStmt::Assign(lhs, rhs) => {
            substitute_var_in_expr(lhs, from, to);
            substitute_var_in_expr(rhs, from, to);
        }
        _ => {}
    }
}

pub(crate) fn substitute_var_in_expr(expr: &mut JsExpr, from: &str, to: &str) {
    match expr {
        JsExpr::Var(name) if name == from => { *name = to.to_string(); }
        JsExpr::App(callee, args) => {
            substitute_var_in_expr(callee, from, to);
            for arg in args { substitute_var_in_expr(arg, from, to); }
        }
        JsExpr::Function(_, params, body) => {
            // Don't substitute if the param name shadows `from`
            if params.iter().any(|p| p == from) { return; }
            for s in body { substitute_var_in_stmt(s, from, to); }
        }
        JsExpr::Ternary(a, b, c) => {
            substitute_var_in_expr(a, from, to);
            substitute_var_in_expr(b, from, to);
            substitute_var_in_expr(c, from, to);
        }
        JsExpr::ArrayLit(items) => {
            for item in items { substitute_var_in_expr(item, from, to); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields { substitute_var_in_expr(val, from, to); }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) => {
            substitute_var_in_expr(a, from, to);
            substitute_var_in_expr(b, from, to);
        }
        JsExpr::Unary(_, a) => { substitute_var_in_expr(a, from, to); }
        JsExpr::InstanceOf(a, b) => {
            substitute_var_in_expr(a, from, to);
            substitute_var_in_expr(b, from, to);
        }
        JsExpr::New(callee, args) => {
            substitute_var_in_expr(callee, from, to);
            for arg in args { substitute_var_in_expr(arg, from, to); }
        }
        _ => {}
    }
}

/// Count how many times `Var(name)` appears in a slice of statements.
/// Does NOT descend into function bodies (the variable is local to the current scope).
pub(crate) fn count_var_in_stmts(stmts: &[JsStmt], name: &str) -> usize {
    stmts.iter().map(|s| count_var_in_stmt(s, name)).sum()
}

pub(crate) fn count_var_in_stmt(stmt: &JsStmt, name: &str) -> usize {
    match stmt {
        JsStmt::Return(expr) => count_var_in_expr(expr, name),
        JsStmt::VarDecl(_, Some(expr)) => count_var_in_expr(expr, name),
        JsStmt::VarDecl(_, None) => 0,
        JsStmt::Expr(expr) => count_var_in_expr(expr, name),
        JsStmt::If(cond, then_body, else_body) => {
            count_var_in_expr(cond, name)
                + count_var_in_stmts(then_body, name)
                + else_body.as_ref().map_or(0, |stmts| count_var_in_stmts(stmts, name))
        }
        JsStmt::Assign(lhs, rhs) => count_var_in_expr(lhs, name) + count_var_in_expr(rhs, name),
        JsStmt::Throw(expr) => count_var_in_expr(expr, name),
        JsStmt::Block(stmts) => count_var_in_stmts(stmts, name),
        JsStmt::For(_, init, bound, body) => {
            count_var_in_expr(init, name) + count_var_in_expr(bound, name) + count_var_in_stmts(body, name)
        }
        JsStmt::ForIn(_, obj, body) => count_var_in_expr(obj, name) + count_var_in_stmts(body, name),
        JsStmt::While(cond, body) => count_var_in_expr(cond, name) + count_var_in_stmts(body, name),
        _ => 0,
    }
}

pub(crate) fn count_var_in_expr(expr: &JsExpr, name: &str) -> usize {
    match expr {
        JsExpr::Var(v) if v == name => 1,
        JsExpr::App(callee, args) => {
            count_var_in_expr(callee, name) + args.iter().map(|a| count_var_in_expr(a, name)).sum::<usize>()
        }
        JsExpr::Function(_, params, body) => {
            // Don't count if the function parameter shadows this variable
            if params.iter().any(|p| p == name) { 0 }
            else { count_var_in_stmts(body, name) }
        }
        JsExpr::Ternary(a, b, c) => {
            count_var_in_expr(a, name) + count_var_in_expr(b, name) + count_var_in_expr(c, name)
        }
        JsExpr::ArrayLit(items) => items.iter().map(|i| count_var_in_expr(i, name)).sum(),
        JsExpr::ObjectLit(fields) => fields.iter().map(|(_, v)| count_var_in_expr(v, name)).sum(),
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            count_var_in_expr(a, name) + count_var_in_expr(b, name)
        }
        JsExpr::Unary(_, a) => count_var_in_expr(a, name),
        JsExpr::New(callee, args) => {
            count_var_in_expr(callee, name) + args.iter().map(|a| count_var_in_expr(a, name)).sum::<usize>()
        }
        _ => 0,
    }
}

/// Substitute all occurrences of `Var(from)` with `replacement` expression in a statement.
/// Does NOT descend into function bodies whose params shadow `from`.
pub(crate) fn substitute_var_with_expr_in_stmt(stmt: &mut JsStmt, from: &str, replacement: &JsExpr) {
    match stmt {
        JsStmt::Return(expr) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::VarDecl(_, Some(expr)) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::Expr(expr) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::If(cond, then_body, else_body) => {
            substitute_var_with_expr_in_expr(cond, from, replacement);
            substitute_var_in_stmts_with_shadowing(then_body, from, replacement);
            if let Some(stmts) = else_body {
                substitute_var_in_stmts_with_shadowing(stmts, from, replacement);
            }
        }
        JsStmt::Assign(lhs, rhs) => {
            substitute_var_with_expr_in_expr(lhs, from, replacement);
            substitute_var_with_expr_in_expr(rhs, from, replacement);
        }
        JsStmt::Throw(expr) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::Block(stmts) => {
            substitute_var_in_stmts_with_shadowing(stmts, from, replacement);
        }
        JsStmt::For(_, init, bound, body) => {
            substitute_var_with_expr_in_expr(init, from, replacement);
            substitute_var_with_expr_in_expr(bound, from, replacement);
            substitute_var_in_stmts_with_shadowing(body, from, replacement);
        }
        JsStmt::ForIn(_, obj, body) => {
            substitute_var_with_expr_in_expr(obj, from, replacement);
            substitute_var_in_stmts_with_shadowing(body, from, replacement);
        }
        JsStmt::While(cond, body) => {
            substitute_var_with_expr_in_expr(cond, from, replacement);
            substitute_var_in_stmts_with_shadowing(body, from, replacement);
        }
        _ => {}
    }
}

/// Substitute in a statement list, stopping for a given variable once a VarDecl shadows it.
/// This prevents replacing local variables with module-level lazy bindings.
fn substitute_var_in_stmts_with_shadowing(stmts: &mut [JsStmt], from: &str, replacement: &JsExpr) {
    for s in stmts {
        // If this statement declares a variable with the same name, substitute in its init
        // expression but don't continue into subsequent statements (the local shadows `from`).
        if let JsStmt::VarDecl(name, _) = s {
            if name == from {
                // Substitute in the init expression only
                if let JsStmt::VarDecl(_, Some(ref mut init)) = s {
                    substitute_var_with_expr_in_expr(init, from, replacement);
                }
                return; // Stop: subsequent stmts see the local `name`, not the outer `from`
            }
        }
        substitute_var_with_expr_in_stmt(s, from, replacement);
    }
}

pub(crate) fn substitute_var_with_expr_in_expr(expr: &mut JsExpr, from: &str, replacement: &JsExpr) {
    match expr {
        JsExpr::Var(name) if name == from => {
            *expr = replacement.clone();
        }
        JsExpr::App(callee, args) => {
            substitute_var_with_expr_in_expr(callee, from, replacement);
            for arg in args { substitute_var_with_expr_in_expr(arg, from, replacement); }
        }
        JsExpr::Function(_, params, body) => {
            if params.iter().any(|p| p == from) { return; }
            substitute_var_in_stmts_with_shadowing(body, from, replacement);
        }
        JsExpr::Ternary(a, b, c) => {
            substitute_var_with_expr_in_expr(a, from, replacement);
            substitute_var_with_expr_in_expr(b, from, replacement);
            substitute_var_with_expr_in_expr(c, from, replacement);
        }
        JsExpr::ArrayLit(items) => {
            for item in items { substitute_var_with_expr_in_expr(item, from, replacement); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields { substitute_var_with_expr_in_expr(val, from, replacement); }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) => {
            substitute_var_with_expr_in_expr(a, from, replacement);
            substitute_var_with_expr_in_expr(b, from, replacement);
        }
        JsExpr::Unary(_, a) => { substitute_var_with_expr_in_expr(a, from, replacement); }
        JsExpr::InstanceOf(a, b) => {
            substitute_var_with_expr_in_expr(a, from, replacement);
            substitute_var_with_expr_in_expr(b, from, replacement);
        }
        JsExpr::New(callee, args) => {
            substitute_var_with_expr_in_expr(callee, from, replacement);
            for arg in args { substitute_var_with_expr_in_expr(arg, from, replacement); }
        }
        _ => {}
    }
}

/// Inline field access bindings like `var x = v["value0"];` when `x` is used exactly once
/// in subsequent statements. Replaces the single use with the field access and removes the VarDecl.
/// Only inlines when the scrutinee is a simple Var and the field is a "valueN" pattern.
pub(crate) fn inline_field_access_bindings(stmts: &mut Vec<JsStmt>) {
    let mut to_inline: Vec<(usize, String, JsExpr)> = Vec::new(); // (index, var_name, replacement_expr)

    for (i, stmt) in stmts.iter().enumerate() {
        if let JsStmt::VarDecl(name, Some(JsExpr::Indexer(scrutinee, key))) = stmt {
            // Only inline when scrutinee is a simple Var
            if let JsExpr::Var(_) = scrutinee.as_ref() {
                // Only inline for "valueN" field accesses
                if let JsExpr::StringLit(field) = key.as_ref() {
                    if !field.starts_with("value") {
                        continue;
                    }
                } else {
                    continue;
                }
            } else {
                continue;
            }

            let replacement = JsExpr::Indexer(scrutinee.clone(), key.clone());

            // Count uses in remaining stmts (not including this binding)
            let remaining = &stmts[i + 1..];
            let use_count = count_var_in_stmts(remaining, name);

            if use_count == 0 {
                continue;
            }

            // Check that no other VarDecl's init expression uses this variable
            // (to avoid reordering issues with dependent bindings)
            let mut used_in_other_init = false;
            for (j, other_stmt) in stmts.iter().enumerate() {
                if j == i { continue; }
                if let JsStmt::VarDecl(_, Some(init_expr)) = other_stmt {
                    if count_var_in_expr(init_expr, name) > 0 {
                        used_in_other_init = true;
                        break;
                    }
                }
            }
            if used_in_other_init {
                continue;
            }

            to_inline.push((i, name.clone(), replacement));
        }
    }

    if to_inline.is_empty() {
        return;
    }

    // Apply in reverse order to preserve indices
    for (idx, var_name, replacement) in to_inline.into_iter().rev() {
        // Substitute in remaining stmts
        for stmt in stmts.iter_mut().skip(idx + 1) {
            substitute_var_with_expr_in_stmt(stmt, &var_name, &replacement);
        }
        // Remove the VarDecl
        stmts.remove(idx);
    }
}

/// Recursively apply `inline_field_access_bindings` to all function bodies in a statement.
pub(crate) fn inline_field_access_in_stmt(stmt: &mut JsStmt) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) => inline_field_access_in_expr(expr),
        JsStmt::Return(expr) => inline_field_access_in_expr(expr),
        JsStmt::Expr(expr) => inline_field_access_in_expr(expr),
        JsStmt::Throw(expr) => inline_field_access_in_expr(expr),
        JsStmt::Assign(a, b) => {
            inline_field_access_in_expr(a);
            inline_field_access_in_expr(b);
        }
        JsStmt::If(cond, then_body, else_body) => {
            inline_field_access_in_expr(cond);
            inline_field_access_bindings(then_body);
            for s in then_body.iter_mut() { inline_field_access_in_stmt(s); }
            if let Some(stmts) = else_body {
                inline_field_access_bindings(stmts);
                for s in stmts.iter_mut() { inline_field_access_in_stmt(s); }
            }
        }
        JsStmt::Block(stmts) => {
            inline_field_access_bindings(stmts);
            for s in stmts.iter_mut() { inline_field_access_in_stmt(s); }
        }
        JsStmt::For(_, init, bound, body) => {
            inline_field_access_in_expr(init);
            inline_field_access_in_expr(bound);
            for s in body { inline_field_access_in_stmt(s); }
        }
        JsStmt::ForIn(_, obj, body) => {
            inline_field_access_in_expr(obj);
            for s in body { inline_field_access_in_stmt(s); }
        }
        JsStmt::While(cond, body) => {
            inline_field_access_in_expr(cond);
            for s in body { inline_field_access_in_stmt(s); }
        }
        _ => {}
    }
}

pub(crate) fn inline_field_access_in_expr(expr: &mut JsExpr) {
    match expr {
        JsExpr::Function(_, _, body) => {
            // Apply the optimization to this function's body
            inline_field_access_bindings(body);
            // Then recurse into the body for nested functions
            for s in body { inline_field_access_in_stmt(s); }
        }
        JsExpr::App(callee, args) => {
            inline_field_access_in_expr(callee);
            for arg in args { inline_field_access_in_expr(arg); }
        }
        JsExpr::Ternary(a, b, c) => {
            inline_field_access_in_expr(a);
            inline_field_access_in_expr(b);
            inline_field_access_in_expr(c);
        }
        JsExpr::ArrayLit(items) => {
            for item in items { inline_field_access_in_expr(item); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields { inline_field_access_in_expr(val); }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            inline_field_access_in_expr(a);
            inline_field_access_in_expr(b);
        }
        JsExpr::Unary(_, a) => { inline_field_access_in_expr(a); }
        JsExpr::New(callee, args) => {
            inline_field_access_in_expr(callee);
            for arg in args { inline_field_access_in_expr(arg); }
        }
        _ => {}
    }
}

// ===== Mutual Recursion Inlining for TCO =====

/// Scan top-level statements for functions with where-bound helpers that form
/// mutual recursion groups. Inline the helpers at call sites so the parent
/// function becomes self-recursive, enabling standard TCO.
///
/// Example: `f x y = g (x+2) (y-1) where g x' y' = if y'<=0 then x' else f x' y'`
/// After inlining g: `f x y = if (y-1)<=0 then (x+2) else f (x+2) (y-1)`
pub(crate) fn inline_mutual_recursion_for_tco(stmts: &mut Vec<JsStmt>) {
    for stmt in stmts.iter_mut() {
        // Look for VarDecl(name, Some(Function(...))) or VarDecl(name, IIFE wrapping function decls)
        if let JsStmt::VarDecl(name, Some(expr)) = stmt {
            // Handle IIFE: (function() { var f = ...; return f(0); })()
            if let JsExpr::App(callee, _) = expr {
                if let JsExpr::Function(None, params, body) = callee.as_mut() {
                    if params.is_empty() {
                        // Inside the IIFE, look for function VarDecls
                        inline_mutual_recursion_in_iife_body(body);
                    }
                }
            }
            // Handle direct function: var f = function(x) { ... }
            else if matches!(expr, JsExpr::Function(_, _, _)) {
                let fn_name = name.clone();
                try_inline_where_bound_mutual_recursion(&fn_name, expr);
            }
        }
    }
}

/// Inside an IIFE body, find function VarDecls and try mutual recursion inlining,
/// then apply TCO to any functions that became self-recursive.
pub(crate) fn inline_mutual_recursion_in_iife_body(body: &mut Vec<JsStmt>) {
    // Find function names declared in this IIFE
    let fn_names: Vec<String> = body.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, Some(JsExpr::Function(_, _, _))) = s {
            Some(name.clone())
        } else {
            None
        }
    }).collect();

    for stmt in body.iter_mut() {
        if let JsStmt::VarDecl(name, Some(expr)) = stmt {
            if matches!(expr, JsExpr::Function(_, _, _)) && fn_names.contains(name) {
                try_inline_where_bound_mutual_recursion(name, expr);
            }
        }
    }

    // After inlining, apply TCO to functions that may now be self-recursive
    apply_tco_if_applicable(body);
}

/// Try to inline where-bound functions that form mutual recursion with the parent function.
/// This transforms mutual recursion into self-recursion for TCO.
pub(crate) fn try_inline_where_bound_mutual_recursion(fn_name: &str, expr: &mut JsExpr) {
    // Unwrap curried function to find the innermost body
    let (all_params, _) = unwrap_curried_fn(expr);
    let arity = all_params.len();
    if arity == 0 { return; }

    // Already self-recursive? No need to inline.
    if is_tail_recursive(fn_name, arity, expr) { return; }

    // Collect all param names flattened
    let parent_params: Vec<String> = all_params.iter().flatten().cloned().collect();

    // Get the innermost body and look for where-bound functions
    let innermost_body = get_innermost_body_mut(expr, arity);

    // Collect names of where-bound functions that are self-recursive BEFORE TCO.
    // Also detect already-TCO'd functions (their $tco_loop body may call the parent).
    let self_recursive_fns: Vec<String> = innermost_body.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, Some(fn_expr)) = s {
            if matches!(fn_expr, JsExpr::Function(_, _, _)) {
                let (params, _) = unwrap_curried_fn(fn_expr);
                let fn_arity = params.len();
                if fn_arity > 0 && is_tail_recursive(name, fn_arity, fn_expr) {
                    return Some(name.clone());
                }
                // Check if already TCO'd (has $tco_loop pattern)
                if fn_arity > 0 && is_already_tco(fn_expr) {
                    return Some(name.clone());
                }
            }
        }
        None
    }).collect();

    // Check for mutual TCO pattern: self-recursive where-fn that also calls parent.
    // This requires two-phase TCO (e.g., tco3: g is self-recursive AND calls f).
    // Handle both pre-TCO and already-TCO'd functions.
    let mutual_tco_fns: Vec<(String, usize)> = self_recursive_fns.iter().filter_map(|sr_name| {
        for stmt in innermost_body.iter() {
            if let JsStmt::VarDecl(name, Some(fn_expr)) = stmt {
                if name == sr_name {
                    let (params, fn_body) = unwrap_curried_fn(fn_expr);
                    let fn_arity = params.len();
                    // Check pre-TCO body
                    if body_has_tail_call(fn_name, arity, fn_body) {
                        return Some((sr_name.clone(), fn_arity));
                    }
                    // Check already-TCO'd $tco_loop body
                    if let Some(tco_body) = get_tco_loop_body(fn_expr) {
                        if body_has_tail_call(fn_name, arity, tco_body) {
                            return Some((sr_name.clone(), fn_arity));
                        }
                    }
                }
            }
        }
        None
    }).collect();

    if !mutual_tco_fns.is_empty() {
        // Two-phase mutual TCO
        apply_mutual_tco(fn_name, expr, &all_params, &mutual_tco_fns);
        return;
    }

    // Apply TCO to any where-bound functions that are already self-recursive.
    apply_tco_if_applicable(innermost_body);

    // Try inlining iteratively (tco2 needs multiple rounds: f→g→h→f)
    // Pass self_recursive_fns so they are excluded from inlining.
    for _ in 0..5 {
        if !try_inline_one_level(fn_name, arity, &parent_params, &self_recursive_fns, innermost_body) {
            break;
        }
    }

    // Recurse into where-bound functions to handle nested mutual recursion
    // (e.g., tco3: tco3 has where-bound f, and f has where-bound g with f↔g mutual recursion)
    for stmt in innermost_body.iter_mut() {
        if let JsStmt::VarDecl(name, Some(fn_expr)) = stmt {
            if matches!(fn_expr, JsExpr::Function(_, _, _)) {
                let nested_name = name.clone();
                try_inline_where_bound_mutual_recursion(&nested_name, fn_expr);
            }
        }
    }
}

/// Check if a function expression has already been TCO'd (has the $tco_loop/while pattern).
pub(crate) fn is_already_tco(expr: &JsExpr) -> bool {
    // Navigate to innermost function body
    let mut current = expr;
    loop {
        if let JsExpr::Function(_, _, body) = current {
            if let Some(JsStmt::Return(inner)) = body.last() {
                if matches!(inner, JsExpr::Function(_, _, _)) {
                    current = inner;
                    continue;
                }
            }
            // Check if body has FunctionDecl("$tco_loop", ...) and While(...)
            return body.iter().any(|s| matches!(s, JsStmt::FunctionDecl(n, _, _) if n == "$tco_loop"));
        }
        return false;
    }
}

/// Get the $tco_loop body from an already-TCO'd function expression.
pub(crate) fn get_tco_loop_body(expr: &JsExpr) -> Option<&[JsStmt]> {
    let mut current = expr;
    loop {
        if let JsExpr::Function(_, _, body) = current {
            if let Some(JsStmt::Return(inner)) = body.last() {
                if matches!(inner, JsExpr::Function(_, _, _)) {
                    current = inner;
                    continue;
                }
            }
            for stmt in body.iter() {
                if let JsStmt::FunctionDecl(name, _, fn_body) = stmt {
                    if name == "$tco_loop" {
                        return Some(fn_body);
                    }
                }
            }
            return None;
        }
        return None;
    }
}

/// Get mutable reference to the $tco_loop body from an already-TCO'd function expression.
pub(crate) fn get_tco_loop_body_mut(expr: &mut JsExpr) -> Option<&mut Vec<JsStmt>> {
    // Navigate to innermost function
    let mut current = expr as *mut JsExpr;
    loop {
        unsafe {
            if let JsExpr::Function(_, _, body) = &mut *current {
                if let Some(JsStmt::Return(inner)) = body.last_mut() {
                    if matches!(inner, JsExpr::Function(_, _, _)) {
                        current = inner as *mut JsExpr;
                        continue;
                    }
                }
                for stmt in body.iter_mut() {
                    if let JsStmt::FunctionDecl(name, _, fn_body) = stmt {
                        if name == "$tco_loop" {
                            return Some(fn_body);
                        }
                    }
                }
                return None;
            }
            return None;
        }
    }
}

/// Two-phase mutual TCO for cases where a where-bound function is both
/// self-recursive AND calls the parent function.
///
/// Handles both pre-TCO and already-TCO'd functions:
/// - Pre-TCO: Phase 1 loopifies g's body, Phase 2 applies standard TCO to g
/// - Already-TCO'd: Modifies g's $tco_loop body to add parent var assignments
///
/// Uses $__tco_done as parent's done flag to avoid shadowing by g's $tco_done.
pub(crate) fn apply_mutual_tco(
    fn_name: &str,
    expr: &mut JsExpr,
    all_param_layers: &[Vec<String>],
    mutual_fns: &[(String, usize)],
) {
    let arity = all_param_layers.len();
    let inner_params: Vec<String> = all_param_layers.last().unwrap().clone();
    let outer_params: Vec<String> = all_param_layers[..arity-1].iter().flatten().cloned().collect();

    let body = get_innermost_body_mut(expr, arity);

    // Phase 1: Modify mutual fn bodies for parent's while loop.
    for (mfn_name, mfn_arity) in mutual_fns {
        for stmt in body.iter_mut() {
            if let JsStmt::VarDecl(name, Some(fn_expr)) = stmt {
                if name == mfn_name {
                    if is_already_tco(fn_expr) {
                        // Already TCO'd: modify the $tco_loop body in-place
                        modify_tco_loop_for_parent(
                            fn_name, arity, &outer_params, &inner_params,
                            fn_expr,
                        );
                    } else {
                        // Pre-TCO: loopify from scratch, then Phase 2 will TCO g
                        loopify_mutual_fn_body_for_parent(
                            fn_name, arity, &outer_params, &inner_params,
                            mfn_name, *mfn_arity,
                            fn_expr,
                        );
                    }
                }
            }
        }
    }

    // Build f's TCO while-loop structure
    let old_body = std::mem::take(body);
    let mut tco_body = Vec::new();

    // var $tco_var_X = $copy_X; for outer params
    for param in &outer_params {
        tco_body.push(JsStmt::VarDecl(
            format!("$tco_var_{param}"),
            Some(JsExpr::Var(format!("$copy_{param}"))),
        ));
    }

    // var $__tco_done = false; (unique name to avoid shadowing by g's $tco_done)
    tco_body.push(JsStmt::VarDecl("$__tco_done".to_string(), Some(JsExpr::BoolLit(false))));

    // var $tco_result;
    tco_body.push(JsStmt::VarDecl("$tco_result".to_string(), None));

    // function $tco_loop(params...) { old_body }
    let loop_params: Vec<String> = if outer_params.is_empty() {
        inner_params.clone()
    } else {
        let mut lp = outer_params.clone();
        lp.extend(inner_params.clone());
        lp
    };
    tco_body.push(JsStmt::FunctionDecl(
        "$tco_loop".to_string(),
        loop_params,
        old_body,
    ));

    // while (!$__tco_done) { $tco_result = $tco_loop(args); }
    let while_cond = JsExpr::Unary(JsUnaryOp::Not, Box::new(JsExpr::Var("$__tco_done".to_string())));
    let loop_call_args: Vec<JsExpr> = if outer_params.is_empty() {
        inner_params.iter().map(|p| JsExpr::Var(format!("$copy_{p}"))).collect()
    } else {
        let mut args: Vec<JsExpr> = outer_params.iter().map(|p| JsExpr::Var(format!("$tco_var_{p}"))).collect();
        args.extend(inner_params.iter().map(|p| JsExpr::Var(format!("$copy_{p}"))));
        args
    };
    tco_body.push(JsStmt::While(
        while_cond,
        vec![JsStmt::Assign(
            JsExpr::Var("$tco_result".to_string()),
            JsExpr::App(
                Box::new(JsExpr::Var("$tco_loop".to_string())),
                loop_call_args,
            ),
        )],
    ));

    // return $tco_result;
    tco_body.push(JsStmt::Return(JsExpr::Var("$tco_result".to_string())));

    *body = tco_body;

    // Rename f's params to $copy_ versions
    rename_params_to_copy(expr, arity, 0);

    // Phase 2: Apply standard TCO to mutual fns that weren't already TCO'd.
    let body = get_innermost_body_mut(expr, arity);
    for stmt in body.iter_mut() {
        if let JsStmt::FunctionDecl(name, _, fn_body) = stmt {
            if name == "$tco_loop" {
                apply_tco_if_applicable(fn_body);
                break;
            }
        }
    }
}

/// Modify an already-TCO'd function's $tco_loop body for parent's while loop.
/// In the $tco_loop:
/// - `$tco_done = true; return parent_call;` → replace return with parent var assignments + ReturnVoid
/// - `$tco_done = true; return value;` (base case) → add $__tco_done = true before $tco_done
pub(crate) fn modify_tco_loop_for_parent(
    parent_name: &str,
    parent_arity: usize,
    parent_outer_params: &[String],
    parent_inner_params: &[String],
    fn_expr: &mut JsExpr,
) {
    if let Some(tco_body) = get_tco_loop_body_mut(fn_expr) {
        modify_tco_stmts_for_parent(
            parent_name, parent_arity, parent_outer_params, parent_inner_params,
            tco_body,
        );
    }
}

/// Recursively modify statements in a $tco_loop body for parent mutual TCO.
pub(crate) fn modify_tco_stmts_for_parent(
    parent_name: &str,
    parent_arity: usize,
    parent_outer_params: &[String],
    parent_inner_params: &[String],
    stmts: &mut Vec<JsStmt>,
) {
    let mut i = 0;
    while i < stmts.len() {
        match &stmts[i] {
            JsStmt::Return(expr) => {
                if is_self_call(parent_name, parent_arity, expr) {
                    // g→f call: replace return with parent var assignments + ReturnVoid
                    // The preceding $tco_done=true stays (exits g's loop)
                    let args = extract_self_call_args(parent_arity, expr);
                    let mut new_stmts = Vec::new();
                    for (j, param) in parent_outer_params.iter().enumerate() {
                        new_stmts.push(JsStmt::Assign(
                            JsExpr::Var(format!("$tco_var_{param}")),
                            args[j].clone(),
                        ));
                    }
                    for (j, param) in parent_inner_params.iter().enumerate() {
                        new_stmts.push(JsStmt::Assign(
                            JsExpr::Var(format!("$copy_{param}")),
                            args[parent_outer_params.len() + j].clone(),
                        ));
                    }
                    new_stmts.push(JsStmt::ReturnVoid);
                    stmts.splice(i..=i, new_stmts);
                    return; // Done with this branch
                } else {
                    // Non-parent return (base case): add $__tco_done = true before $tco_done
                    // Look for preceding $tco_done = true
                    if i > 0 {
                        if let JsStmt::Assign(JsExpr::Var(ref vname), JsExpr::BoolLit(true)) = stmts[i-1] {
                            if vname == "$tco_done" {
                                stmts.insert(i-1, JsStmt::Assign(
                                    JsExpr::Var("$__tco_done".to_string()),
                                    JsExpr::BoolLit(true),
                                ));
                                return; // Done with this branch
                            }
                        }
                    }
                    i += 1;
                }
            }
            JsStmt::ReturnVoid => {
                // This is a self-call (g→g) that was already TCO'd to var assignments + ReturnVoid.
                // Leave unchanged.
                i += 1;
            }
            JsStmt::If(_, _, _) => {
                if let JsStmt::If(_, then_body, else_body) = &mut stmts[i] {
                    modify_tco_stmts_for_parent(
                        parent_name, parent_arity, parent_outer_params, parent_inner_params,
                        then_body,
                    );
                    if let Some(else_stmts) = else_body {
                        modify_tco_stmts_for_parent(
                            parent_name, parent_arity, parent_outer_params, parent_inner_params,
                            else_stmts,
                        );
                    }
                }
                i += 1;
            }
            _ => { i += 1; }
        }
    }
}

/// Loopify a mutual function's body for the parent's while loop (Phase 1, pre-TCO case).
/// - Calls to parent → $tco_var/$copy assignments + ReturnVoid
/// - Self-calls → left unchanged (Phase 2 will handle)
/// - Non-recursive returns → $__tco_done = true + return value
pub(crate) fn loopify_mutual_fn_body_for_parent(
    parent_name: &str,
    parent_arity: usize,
    parent_outer_params: &[String],
    parent_inner_params: &[String],
    self_name: &str,
    self_arity: usize,
    fn_expr: &mut JsExpr,
) {
    let inner_body = get_innermost_body_mut(fn_expr, self_arity);
    let old_stmts = std::mem::take(inner_body);
    *inner_body = loopify_stmts_for_parent(
        parent_name, parent_arity, parent_outer_params, parent_inner_params,
        self_name, self_arity,
        &old_stmts,
    );
}

/// Transform statements for parent's while loop (Phase 1 loopification, pre-TCO case).
pub(crate) fn loopify_stmts_for_parent(
    parent_name: &str,
    parent_arity: usize,
    parent_outer_params: &[String],
    parent_inner_params: &[String],
    self_name: &str,
    self_arity: usize,
    stmts: &[JsStmt],
) -> Vec<JsStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            JsStmt::Return(expr) => {
                if is_self_call(parent_name, parent_arity, expr) {
                    let args = extract_self_call_args(parent_arity, expr);
                    for (i, param) in parent_outer_params.iter().enumerate() {
                        result.push(JsStmt::Assign(
                            JsExpr::Var(format!("$tco_var_{param}")),
                            args[i].clone(),
                        ));
                    }
                    for (i, param) in parent_inner_params.iter().enumerate() {
                        result.push(JsStmt::Assign(
                            JsExpr::Var(format!("$copy_{param}")),
                            args[parent_outer_params.len() + i].clone(),
                        ));
                    }
                    result.push(JsStmt::ReturnVoid);
                } else if is_self_call(self_name, self_arity, expr) {
                    result.push(stmt.clone());
                } else {
                    result.push(JsStmt::Assign(
                        JsExpr::Var("$__tco_done".to_string()),
                        JsExpr::BoolLit(true),
                    ));
                    result.push(JsStmt::Return(expr.clone()));
                }
            }
            JsStmt::If(cond, then_body, else_body) => {
                let new_then = loopify_stmts_for_parent(
                    parent_name, parent_arity, parent_outer_params, parent_inner_params,
                    self_name, self_arity, then_body,
                );
                let new_else = else_body.as_ref().map(|e| {
                    loopify_stmts_for_parent(
                        parent_name, parent_arity, parent_outer_params, parent_inner_params,
                        self_name, self_arity, e,
                    )
                });
                result.push(JsStmt::If(cond.clone(), new_then, new_else));
            }
            _ => {
                result.push(stmt.clone());
            }
        }
    }
    result
}

/// Try to inline one level of where-bound function calls in the body's tail position.
/// Returns true if any inlining was done.
///
/// Two directions of inlining:
/// 1. Inline where-bound function into parent's tail calls (e.g., tco4: replace g(y-1) with f(x+2)(y-1))
/// 2. Inline parent into where-bound function's tail calls to parent (e.g., tco1: replace f(x')(y') with g(x'+2)(y'-1))
pub(crate) fn try_inline_one_level(fn_name: &str, arity: usize, parent_params: &[String], self_recursive_fns: &[String], body: &mut Vec<JsStmt>) -> bool {
    // Collect where-bound function info: (name, params_per_level, body)
    let mut where_fns: Vec<(String, Vec<Vec<String>>, Vec<JsStmt>)> = Vec::new();
    for stmt in body.iter() {
        if let JsStmt::VarDecl(name, Some(expr)) = stmt {
            if let JsExpr::Function(_, _, _) = expr {
                let (params, fn_body) = unwrap_curried_fn(expr);
                if !params.is_empty() {
                    where_fns.push((name.clone(), params, fn_body.to_vec()));
                }
            }
        }
    }
    if where_fns.is_empty() { return false; }

    // Find where-bound functions that contain tail calls back to fn_name
    let fns_calling_parent: Vec<String> = where_fns.iter()
        .filter(|(_, _params, fn_body)| {
            body_has_tail_call_to_any(fn_name, arity, fn_body, &where_fns)
        })
        .map(|(name, _, _)| name.clone())
        .collect();

    if fns_calling_parent.is_empty() { return false; }

    // Filter: don't inline where-bound functions that are already self-recursive.
    // They should get their own TCO transformation (already done by apply_tco_if_applicable above).
    // We use the pre-computed self_recursive_fns list since TCO may have already transformed them.
    let fns_to_inline: Vec<String> = fns_calling_parent.iter()
        .filter(|name| !self_recursive_fns.contains(name))
        .cloned()
        .collect();

    // Direction 1: Inline where-bound functions into parent's tail calls
    let mut did_inline = false;
    if !fns_to_inline.is_empty() {
        inline_where_calls_in_stmts(body, &where_fns, &fns_to_inline, &mut did_inline);
    }

    // Direction 2: If the parent's body is just "return g(args...)" (only VarDecls + one return),
    // inline the parent into where-bound functions' calls to the parent.
    // This handles patterns like: f(x)(y) = g(x)(h(y)) where g calls f
    if !did_inline {
        // Check if body is: VarDecls... + Return(call to where-bound fn)
        let tail_return = body.last();
        if let Some(JsStmt::Return(ret_expr)) = tail_return {
            // Find which where-bound function is being called in the return
            let mut found_wfn = None;
            for (wfn_name, wfn_params, _) in &where_fns {
                let wfn_arity = wfn_params.len();
                if is_self_call(wfn_name, wfn_arity, ret_expr) {
                    found_wfn = Some((wfn_name.clone(), wfn_arity));
                    break;
                }
            }
            if let Some((_wfn_name, _wfn_arity)) = found_wfn {
                // Parent f(x)(y) = VarDecls... ; return g(expr1(x,y), expr2(x,y))
                // We have parent_params = [x, y] and the return expression references them.
                // Clone the non-VarDecl tail (everything from first non-VarDecl to end)
                let parent_tail_stmts: Vec<JsStmt> = body.iter()
                    .filter(|s| !matches!(s, JsStmt::VarDecl(n, Some(JsExpr::Function(_, _, _))) if where_fns.iter().any(|(wn, _, _)| wn == n)))
                    .cloned()
                    .collect();

                // Now replace calls to fn_name inside where-bound functions' bodies
                for stmt in body.iter_mut() {
                    if let JsStmt::VarDecl(_name, Some(expr)) = stmt {
                        if !matches!(expr, JsExpr::Function(_, _, _)) { continue; }
                        let (params, _) = unwrap_curried_fn(expr);
                        let fn_arity = params.len();
                        if fn_arity == 0 { continue; }
                        let inner_body = get_innermost_body_mut(expr, fn_arity);
                        replace_parent_calls_with_expanded(
                            fn_name, arity, parent_params, &parent_tail_stmts,
                            inner_body, &mut did_inline
                        );
                    }
                }
            }
        }
    }

    did_inline
}

/// Replace calls to parent function in tail positions with the parent's expanded body.
/// For each call f(a1)(a2), substitute parent_params → call_args in parent_tail_stmts.
pub(crate) fn replace_parent_calls_with_expanded(
    parent_name: &str,
    parent_arity: usize,
    parent_params: &[String],
    parent_tail_stmts: &[JsStmt],
    stmts: &mut Vec<JsStmt>,
    did_inline: &mut bool,
) {
    let mut i = 0;
    while i < stmts.len() {
        match &stmts[i] {
            JsStmt::Return(expr) => {
                if is_self_call(parent_name, parent_arity, expr) {
                    let call_args = extract_self_call_args(parent_arity, expr);
                    // Build substitution: parent_params[j] → call_args[j]
                    let subst: Vec<(String, JsExpr)> = parent_params.iter()
                        .zip(call_args.iter())
                        .map(|(p, a)| (p.clone(), a.clone()))
                        .collect();
                    // Apply substitution to parent_tail_stmts and splice in
                    let expanded: Vec<JsStmt> = parent_tail_stmts.iter()
                        .map(|s| substitute_vars_in_stmt(s, &subst))
                        .collect();
                    stmts.splice(i..=i, expanded);
                    *did_inline = true;
                    return;
                }
                i += 1;
            }
            JsStmt::If(_, _, _) => {
                if let JsStmt::If(_, then_body, else_body) = &mut stmts[i] {
                    replace_parent_calls_with_expanded(
                        parent_name, parent_arity, parent_params, parent_tail_stmts,
                        then_body, did_inline
                    );
                    if let Some(else_stmts) = else_body {
                        replace_parent_calls_with_expanded(
                            parent_name, parent_arity, parent_params, parent_tail_stmts,
                            else_stmts, did_inline
                        );
                    }
                }
                i += 1;
            }
            _ => { i += 1; }
        }
    }
}

/// Substitute variable references in a JsExpr according to the given mapping.
pub(crate) fn substitute_vars_in_expr(expr: &JsExpr, subst: &[(String, JsExpr)]) -> JsExpr {
    match expr {
        JsExpr::Var(name) => {
            for (from, to) in subst {
                if name == from {
                    return to.clone();
                }
            }
            expr.clone()
        }
        JsExpr::App(callee, args) => {
            JsExpr::App(
                Box::new(substitute_vars_in_expr(callee, subst)),
                args.iter().map(|a| substitute_vars_in_expr(a, subst)).collect(),
            )
        }
        JsExpr::Binary(op, l, r) => {
            JsExpr::Binary(
                op.clone(),
                Box::new(substitute_vars_in_expr(l, subst)),
                Box::new(substitute_vars_in_expr(r, subst)),
            )
        }
        JsExpr::Unary(op, inner) => {
            JsExpr::Unary(op.clone(), Box::new(substitute_vars_in_expr(inner, subst)))
        }
        JsExpr::Indexer(obj, idx) => {
            JsExpr::Indexer(
                Box::new(substitute_vars_in_expr(obj, subst)),
                Box::new(substitute_vars_in_expr(idx, subst)),
            )
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(
                fields.iter().map(|(k, v)| (k.clone(), substitute_vars_in_expr(v, subst))).collect(),
            )
        }
        JsExpr::ArrayLit(items) => {
            JsExpr::ArrayLit(items.iter().map(|i| substitute_vars_in_expr(i, subst)).collect())
        }
        JsExpr::Ternary(cond, then_e, else_e) => {
            JsExpr::Ternary(
                Box::new(substitute_vars_in_expr(cond, subst)),
                Box::new(substitute_vars_in_expr(then_e, subst)),
                Box::new(substitute_vars_in_expr(else_e, subst)),
            )
        }
        JsExpr::Function(name, params, body) => {
            // Don't substitute into function params that shadow
            let shadowed: Vec<(String, JsExpr)> = subst.iter()
                .filter(|(n, _)| !params.contains(n))
                .cloned()
                .collect();
            JsExpr::Function(
                name.clone(),
                params.clone(),
                body.iter().map(|s| substitute_vars_in_stmt(s, &shadowed)).collect(),
            )
        }
        _ => expr.clone(),
    }
}

/// Substitute variable references in a JsStmt.
pub(crate) fn substitute_vars_in_stmt(stmt: &JsStmt, subst: &[(String, JsExpr)]) -> JsStmt {
    match stmt {
        JsStmt::VarDecl(name, init) => {
            JsStmt::VarDecl(
                name.clone(),
                init.as_ref().map(|e| substitute_vars_in_expr(e, subst)),
            )
        }
        JsStmt::Return(expr) => {
            JsStmt::Return(substitute_vars_in_expr(expr, subst))
        }
        JsStmt::If(cond, then_body, else_body) => {
            JsStmt::If(
                substitute_vars_in_expr(cond, subst),
                then_body.iter().map(|s| substitute_vars_in_stmt(s, subst)).collect(),
                else_body.as_ref().map(|stmts| stmts.iter().map(|s| substitute_vars_in_stmt(s, subst)).collect()),
            )
        }
        JsStmt::Expr(expr) => {
            JsStmt::Expr(substitute_vars_in_expr(expr, subst))
        }
        JsStmt::Throw(expr) => {
            JsStmt::Throw(substitute_vars_in_expr(expr, subst))
        }
        JsStmt::While(cond, body) => {
            JsStmt::While(
                substitute_vars_in_expr(cond, subst),
                body.iter().map(|s| substitute_vars_in_stmt(s, subst)).collect(),
            )
        }
        JsStmt::Assign(target, value) => {
            JsStmt::Assign(
                substitute_vars_in_expr(target, subst),
                substitute_vars_in_expr(value, subst),
            )
        }
        JsStmt::Block(body) => {
            JsStmt::Block(body.iter().map(|s| substitute_vars_in_stmt(s, subst)).collect())
        }
        JsStmt::ReturnVoid => JsStmt::ReturnVoid,
        _ => stmt.clone(),
    }
}

/// Check if a body has tail calls to fn_name or to any where-bound function that
/// eventually calls fn_name.
pub(crate) fn body_has_tail_call_to_any(
    fn_name: &str,
    fn_arity: usize,
    stmts: &[JsStmt],
    where_fns: &[(String, Vec<Vec<String>>, Vec<JsStmt>)],
) -> bool {
    for stmt in stmts {
        match stmt {
            JsStmt::Return(expr) => {
                if is_self_call(fn_name, fn_arity, expr) {
                    return true;
                }
                // Check if it's a call to a where-bound function
                for (wfn_name, wfn_params, _) in where_fns {
                    let wfn_arity = wfn_params.len();
                    if is_self_call(wfn_name, wfn_arity, expr) {
                        return true;
                    }
                }
            }
            JsStmt::If(_, then_body, else_body) => {
                if body_has_tail_call_to_any(fn_name, fn_arity, then_body, where_fns) {
                    return true;
                }
                if let Some(else_stmts) = else_body {
                    if body_has_tail_call_to_any(fn_name, fn_arity, else_stmts, where_fns) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Inline calls to where-bound functions at tail positions in the given statements.
pub(crate) fn inline_where_calls_in_stmts(
    stmts: &mut Vec<JsStmt>,
    where_fns: &[(String, Vec<Vec<String>>, Vec<JsStmt>)],
    fns_to_inline: &[String],
    did_inline: &mut bool,
) {
    let mut i = 0;
    while i < stmts.len() {
        match &mut stmts[i] {
            JsStmt::Return(expr) => {
                // Check if this return calls a where-bound function we should inline
                for (wfn_name, wfn_params, wfn_body) in where_fns {
                    if !fns_to_inline.contains(wfn_name) { continue; }
                    let wfn_arity = wfn_params.len();
                    if is_self_call(wfn_name, wfn_arity, expr) {
                        // Extract call arguments
                        let args = extract_self_call_args(wfn_arity, expr);
                        // Build a substitution from params to args
                        let all_wfn_params: Vec<String> = wfn_params.iter().flatten().cloned().collect();
                        // Create inlined body: var param = arg; ... body ...
                        let mut inlined = Vec::new();
                        for (param, arg) in all_wfn_params.iter().zip(args.iter()) {
                            inlined.push(JsStmt::VarDecl(param.clone(), Some(arg.clone())));
                        }
                        inlined.extend(wfn_body.iter().cloned());
                        // Replace this return with the inlined body
                        stmts.splice(i..=i, inlined);
                        *did_inline = true;
                        return; // Restart since stmts changed
                    }
                }
                i += 1;
            }
            JsStmt::If(_, then_body, else_body) => {
                inline_where_calls_in_stmts(then_body, where_fns, fns_to_inline, did_inline);
                if let Some(else_stmts) = else_body {
                    inline_where_calls_in_stmts(else_stmts, where_fns, fns_to_inline, did_inline);
                }
                i += 1;
            }
            _ => { i += 1; }
        }
    }
}

// ===== Tail Call Optimization =====

/// Check if a function is tail-recursive and apply TCO transformation.
/// Called on `VarDecl(name, Some(Function(...)))` statements.
/// Transforms tail-recursive functions into while-loop form.
pub(crate) fn apply_tco_if_applicable(stmts: &mut Vec<JsStmt>) {
    let mut i = 0;
    while i < stmts.len() {
        let should_transform = if let JsStmt::VarDecl(name, Some(expr)) = &stmts[i] {
            // Unwrap curried function to find the innermost body
            let (all_params, _body) = unwrap_curried_fn(expr);
            if all_params.is_empty() {
                false
            } else {
                // Count total arity (number of currying levels)
                let arity = all_params.len();
                // Skip TCO for functions with dict wrapper layers at the top level.
                // The original compiler doesn't TCO class-constrained functions like
                // gcd :: Eq a => EuclideanRing a => a -> a -> a at module level.
                let has_dict_layers = has_dict_wrapper_layers(expr);
                if has_dict_layers {
                    false
                } else {
                    // Check if the body contains tail-recursive calls to this function
                    is_tail_recursive(name, arity, expr)
                }
            }
        } else {
            false
        };

        if should_transform {
            if let JsStmt::VarDecl(name, Some(expr)) = &mut stmts[i] {
                // DEBUG: dump body before TCO
                if name == "go" {
                    let (all_params, body) = unwrap_curried_fn(expr);
                    let arity = all_params.len();
                    let has_base = body_has_non_recursive_return(name, arity, body);
                    let has_tail = body_has_tail_call(name, arity, body);
                    let _ = (has_base, has_tail);
                }
                transform_tco(name.clone(), expr);
            }
        }
        i += 1;
    }
}

/// Check if a curried function has dict wrapper layers (intermediate function layers
/// with VarDecl statements before returning the next function). These indicate
/// class-constrained functions like `gcd(dictEq)(dictER)(a)(b)`.
pub(crate) fn has_dict_wrapper_layers(expr: &JsExpr) -> bool {
    let mut current = expr;
    loop {
        if let JsExpr::Function(_, _params, body) = current {
            let has_var_decls = body.iter().any(|s| matches!(s, JsStmt::VarDecl(..)));
            if let Some(JsStmt::Return(inner)) = body.last() {
                if matches!(inner, JsExpr::Function(_, _, _)) {
                    if has_var_decls {
                        return true;
                    }
                    current = inner;
                    continue;
                }
            }
        }
        return false;
    }
}

/// Unwrap curried function layers to get all params and the innermost body.
/// Skips VarDecl statements (e.g., from dict hoisting) to find inner returns.
pub(crate) fn unwrap_curried_fn(expr: &JsExpr) -> (Vec<Vec<String>>, &[JsStmt]) {
    let mut all_params: Vec<Vec<String>> = Vec::new();
    let mut current = expr;
    loop {
        match current {
            JsExpr::Function(_, params, body) => {
                all_params.push(params.clone());
                // Look through the body for a return of another function,
                // skipping VarDecl statements (dict hoisting creates these)
                let last = body.last();
                if let Some(JsStmt::Return(inner)) = last {
                    if matches!(inner, JsExpr::Function(_, _, _)) {
                        current = inner;
                        continue;
                    }
                }
                return (all_params, body);
            }
            _ => return (all_params, &[]),
        }
    }
}

/// Check if a function body contains self-calls in tail position.
pub(crate) fn is_tail_recursive(fn_name: &str, arity: usize, expr: &JsExpr) -> bool {
    // Get the innermost body
    let mut current = expr;
    for _ in 0..arity {
        if let JsExpr::Function(_, _, body) = current {
            // Skip VarDecls to find the return of an inner function
            if let Some(JsStmt::Return(inner)) = body.last() {
                if matches!(inner, JsExpr::Function(_, _, _)) {
                    current = inner;
                    continue;
                }
            }
            // Check this body for tail calls
            return body_has_tail_call(fn_name, arity, body);
        }
    }
    false
}

pub(crate) fn body_has_tail_call(fn_name: &str, arity: usize, stmts: &[JsStmt]) -> bool {
    // Check if fn_name is re-declared (shadowed) by a VarDecl in this scope.
    // If so, any calls to fn_name are to the shadow, not self-recursive.
    for stmt in stmts {
        if let JsStmt::VarDecl(name, _) = stmt {
            if name == fn_name {
                return false;
            }
        }
    }
    for stmt in stmts {
        match stmt {
            JsStmt::Return(expr) => {
                if is_self_call(fn_name, arity, expr) {
                    return true;
                }
            }
            JsStmt::If(_, then_body, else_body) => {
                if body_has_tail_call(fn_name, arity, then_body) {
                    return true;
                }
                if let Some(else_stmts) = else_body {
                    if body_has_tail_call(fn_name, arity, else_stmts) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Check if an expression is a fully-applied self-call: `fn_name(a)(b)...(z)` with `arity` applications.
pub(crate) fn is_self_call(fn_name: &str, arity: usize, expr: &JsExpr) -> bool {
    let mut current = expr;
    let mut apps_to_unwrap = arity;
    loop {
        if apps_to_unwrap == 0 {
            return matches!(current, JsExpr::Var(name) if name == fn_name);
        }
        match current {
            JsExpr::App(callee, args) if args.len() == 1 => {
                apps_to_unwrap -= 1;
                current = callee;
            }
            _ => return false,
        }
    }
}

/// Extract arguments from a fully-applied self-call.
/// Returns the arguments in order: [arg1, arg2, ..., argN] for fn(arg1)(arg2)...(argN).
pub(crate) fn extract_self_call_args(arity: usize, expr: &JsExpr) -> Vec<JsExpr> {
    let mut args = Vec::new();
    let mut current = expr;
    for _ in 0..arity {
        if let JsExpr::App(callee, call_args) = current {
            args.push(call_args[0].clone());
            current = callee;
        }
    }
    args.reverse();
    args
}

/// Transform a tail-recursive function into TCO while-loop form.
pub(crate) fn transform_tco(fn_name: String, expr: &mut JsExpr) {
    // Collect all curried param layers, tracking which are dict layers
    let mut param_layers: Vec<Vec<String>> = Vec::new();
    let mut dict_layer_count = 0; // number of dict wrapper layers (have VarDecls)
    let mut current = &*expr;
    loop {
        if let JsExpr::Function(_, params, body) = current {
            param_layers.push(params.clone());
            // Check if this layer has VarDecls (dict wrapper layer)
            let has_var_decls = body.iter().any(|s| matches!(s, JsStmt::VarDecl(..)));
            if let Some(JsStmt::Return(inner)) = body.last() {
                if matches!(inner, JsExpr::Function(_, _, _)) {
                    if has_var_decls {
                        dict_layer_count += 1;
                    }
                    current = inner;
                    continue;
                }
            }
            break;
        }
        return;
    }

    let arity = param_layers.len();
    if arity == 0 { return; }

    // Get all params flattened
    let all_params: Vec<String> = param_layers.iter().flatten().cloned().collect();

    // Separate dict params (from dict wrapper layers) from non-dict outer params.
    // Dict params are constant across iterations and stay as-is.
    let inner_params: Vec<String> = param_layers.last().unwrap().clone();
    let non_dict_outer_params: Vec<String> = param_layers[dict_layer_count..param_layers.len()-1].iter().flatten().cloned().collect();
    // outer_params includes dict params for correct arg indexing in loopify
    let outer_params: Vec<String> = param_layers[..param_layers.len()-1].iter().flatten().cloned().collect();

    // Get the innermost body
    let innermost_body = get_innermost_body_mut(expr, arity);
    let old_body = std::mem::take(innermost_body);

    // Check if there's any non-recursive return (determines if we need $tco_done)
    let has_base_case = body_has_non_recursive_return(&fn_name, arity, &old_body);

    // Transform the body: replace tail calls with variable mutations
    // Use dict_layer_count to know which args are dict (constant) vs non-dict (mutable)
    let loop_body = loopify_stmts_with_dicts(&fn_name, arity, &all_params, &outer_params, &inner_params, &old_body, has_base_case, dict_layer_count);

    // Build the TCO structure in the innermost function body
    let mut tco_body = Vec::new();

    // var $tco_var_X = $copy_X; for non-dict outer params only
    for param in &non_dict_outer_params {
        tco_body.push(JsStmt::VarDecl(
            format!("$tco_var_{param}"),
            Some(JsExpr::Var(format!("$copy_{param}"))),
        ));
    }

    if has_base_case {
        // var $tco_done = false;
        tco_body.push(JsStmt::VarDecl("$tco_done".to_string(), Some(JsExpr::BoolLit(false))));
    }

    // var $tco_result;
    tco_body.push(JsStmt::VarDecl("$tco_result".to_string(), None));

    // function $tco_loop(params...) { body }
    // Dict params are passed through as-is (from the enclosing scope)
    let loop_params: Vec<String> = if non_dict_outer_params.is_empty() {
        inner_params.clone()
    } else {
        let mut lp: Vec<String> = non_dict_outer_params.iter().cloned().collect();
        lp.extend(inner_params.clone());
        lp
    };
    tco_body.push(JsStmt::FunctionDecl(
        "$tco_loop".to_string(),
        loop_params,
        loop_body,
    ));

    // while (!$tco_done) { $tco_result = $tco_loop(args); }
    let while_cond = if has_base_case {
        JsExpr::Unary(JsUnaryOp::Not, Box::new(JsExpr::Var("$tco_done".to_string())))
    } else {
        JsExpr::Unary(JsUnaryOp::Not, Box::new(JsExpr::BoolLit(false)))
    };
    let loop_call_args: Vec<JsExpr> = if non_dict_outer_params.is_empty() {
        inner_params.iter().map(|p| JsExpr::Var(format!("$copy_{p}"))).collect()
    } else {
        let mut args: Vec<JsExpr> = non_dict_outer_params.iter().map(|p| JsExpr::Var(format!("$tco_var_{p}"))).collect();
        args.extend(inner_params.iter().map(|p| JsExpr::Var(format!("$copy_{p}"))));
        args
    };
    tco_body.push(JsStmt::While(
        while_cond,
        vec![JsStmt::Assign(
            JsExpr::Var("$tco_result".to_string()),
            JsExpr::App(
                Box::new(JsExpr::Var("$tco_loop".to_string())),
                loop_call_args,
            ),
        )],
    ));

    // return $tco_result;
    tco_body.push(JsStmt::Return(JsExpr::Var("$tco_result".to_string())));

    // Replace the innermost function body
    *innermost_body = tco_body;

    // Rename params to $copy_ versions in all function layers
    rename_params_to_copy(expr, arity, dict_layer_count);
}

pub(crate) fn get_innermost_body_mut(expr: &mut JsExpr, depth: usize) -> &mut Vec<JsStmt> {
    let mut current = expr as *mut JsExpr;
    for level in 0..depth {
        let is_last = level == depth - 1;
        // SAFETY: we have exclusive access to the expression tree and only
        // traverse downward, never aliasing.
        unsafe {
            if let JsExpr::Function(_, _, body) = &mut *current {
                if is_last {
                    return &mut *body;
                }
                // Skip VarDecls to find the return of an inner function
                if let Some(JsStmt::Return(inner)) = body.last_mut() {
                    current = inner as *mut JsExpr;
                    continue;
                }
                return &mut *body;
            }
        }
    }
    unreachable!()
}

pub(crate) fn rename_params_to_copy(expr: &mut JsExpr, depth: usize, skip_layers: usize) {
    let mut current = expr;
    for level in 0..depth {
        if let JsExpr::Function(_, params, body) = current {
            // Only rename params in non-dict layers (skip_layers controls how many to skip)
            if level >= skip_layers {
                let old_params: Vec<String> = params.clone();
                for param in params.iter_mut() {
                    *param = format!("$copy_{param}");
                }
                // Also rename occurrences of old param names in this function's body
                // statements (excluding the last Return(Function(...)) which is the next layer).
                // This fixes proxy dict checks like `dictFoo = $proxy_dict(dictFoo, ...)` that
                // reference the parameter by its old name after TCO renames it to $copy_dictFoo.
                let body_len = body.len();
                let stmts_to_rename = if level < depth - 1 {
                    // Don't rename in the last Return(inner function) — that's the next layer
                    &mut body[..body_len.saturating_sub(1)]
                } else {
                    body.as_mut_slice()
                };
                for (old, new) in old_params.iter().zip(params.iter()) {
                    for stmt in stmts_to_rename.iter_mut() {
                        substitute_var_in_stmt(stmt, old, new);
                    }
                }
            }
            if level < depth - 1 {
                // Skip VarDecls to find the return of an inner function
                if let Some(JsStmt::Return(inner)) = body.last_mut() {
                    current = inner;
                    continue;
                }
            }
            break;
        }
    }
}

pub(crate) fn body_has_non_recursive_return(fn_name: &str, arity: usize, stmts: &[JsStmt]) -> bool {
    for stmt in stmts {
        match stmt {
            JsStmt::Return(expr) => {
                if !is_self_call(fn_name, arity, expr) {
                    return true;
                }
            }
            JsStmt::If(_, then_body, else_body) => {
                if body_has_non_recursive_return(fn_name, arity, then_body) {
                    return true;
                }
                if let Some(else_stmts) = else_body {
                    if body_has_non_recursive_return(fn_name, arity, else_stmts) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

pub(crate) fn loopify_stmts_with_dicts(
    fn_name: &str,
    arity: usize,
    all_params: &[String],
    outer_params: &[String],
    inner_params: &[String],
    stmts: &[JsStmt],
    has_base_case: bool,
    dict_param_count: usize,
) -> Vec<JsStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            JsStmt::Return(expr) => {
                if is_self_call(fn_name, arity, expr) {
                    // Replace tail call with variable mutations
                    let args = extract_self_call_args(arity, expr);
                    // Skip dict args (they're constant across iterations)
                    let non_dict_start = dict_param_count;
                    for (i, param) in outer_params.iter().skip(dict_param_count).enumerate() {
                        result.push(JsStmt::Assign(
                            JsExpr::Var(format!("$tco_var_{param}")),
                            args[non_dict_start + i].clone(),
                        ));
                    }
                    for (i, param) in inner_params.iter().enumerate() {
                        result.push(JsStmt::Assign(
                            JsExpr::Var(format!("$copy_{param}")),
                            args[outer_params.len() + i].clone(),
                        ));
                    }
                    result.push(JsStmt::ReturnVoid);
                } else {
                    // Base case return: set $tco_done = true
                    if has_base_case {
                        result.push(JsStmt::Assign(
                            JsExpr::Var("$tco_done".to_string()),
                            JsExpr::BoolLit(true),
                        ));
                    }
                    result.push(JsStmt::Return(expr.clone()));
                }
            }
            JsStmt::If(cond, then_body, else_body) => {
                let new_then = loopify_stmts_with_dicts(fn_name, arity, all_params, outer_params, inner_params, then_body, has_base_case, dict_param_count);
                let new_else = else_body.as_ref().map(|e| {
                    loopify_stmts_with_dicts(fn_name, arity, all_params, outer_params, inner_params, e, has_base_case, dict_param_count)
                });
                result.push(JsStmt::If(cond.clone(), new_then, new_else));
            }
            JsStmt::Throw(_) => {
                // Keep throws as-is
                result.push(stmt.clone());
            }
            _ => {
                result.push(stmt.clone());
            }
        }
    }
    result
}

/// Inline patterns like `var x = <expr>; return x;` → `return <expr>;`
/// Also handles `var x = <expr>; <other stmts using x once>`.
pub(crate) fn inline_single_use_bindings(stmts: &mut Vec<JsStmt>) {
    // Eliminate var-to-var aliases: `var a = v;` → substitute a with v in subsequent stmts
    // This handles newtype constructor erasure where `(Newtype a)` pattern creates `var a = v;`
    let mut i = 0;
    while i < stmts.len() {
        let alias = if let JsStmt::VarDecl(ref name, Some(JsExpr::Var(ref source))) = stmts[i] {
            Some((name.clone(), source.clone()))
        } else {
            None
        };
        if let Some((alias_name, source_name)) = alias {
            // Don't inline if the source variable is reassigned in a later statement,
            // as the substitution would reference the wrong value.
            // E.g., `var a = v; var v = v.value1; ... a ...` → a should be original v, not new v.
            let source_shadowed = stmts[i+1..].iter().any(|s| {
                if let JsStmt::VarDecl(ref decl_name, _) = s {
                    *decl_name == source_name
                } else {
                    false
                }
            });
            if source_shadowed {
                i += 1;
                continue;
            }
            // Remove the alias and substitute in remaining statements
            stmts.remove(i);
            for stmt in stmts.iter_mut().skip(i) {
                substitute_var_in_stmt(stmt, &alias_name, &source_name);
            }
            // Don't increment i — check the new stmt at position i
        } else {
            i += 1;
        }
    }

    // Eliminate single-use property access bindings: `var a = v.value0;` → inline a with v.value0
    // Safe because property accesses on constructor results are pure,
    // BUT only if the root variable of the access is not reassigned before the use site.
    let mut i = 0;
    while i < stmts.len() {
        let inline_expr = if let JsStmt::VarDecl(ref name, Some(ref init)) = stmts[i] {
            if is_pure_field_access(init) {
                let use_count = count_var_uses_in_stmts(&stmts[i+1..], name);
                if use_count == 1 {
                    // Check that the root variable of the field access chain is not
                    // reassigned by any VarDecl between here and the use site.
                    // E.g., for `var k = v.value0; var v = v.value1; ... k ...`,
                    // inlining k to v.value0 would be wrong because v gets reassigned.
                    let root_var = field_access_root(init);
                    let root_shadowed = root_var.map_or(false, |root| {
                        stmts[i+1..].iter().any(|s| {
                            if let JsStmt::VarDecl(ref decl_name, _) = s {
                                decl_name == root
                            } else {
                                false
                            }
                        })
                    });
                    if root_shadowed {
                        None
                    } else {
                        Some((name.clone(), init.clone()))
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };
        if let Some((alias_name, replacement)) = inline_expr {
            stmts.remove(i);
            for stmt in stmts.iter_mut().skip(i) {
                substitute_expr_in_stmt(stmt, &alias_name, &replacement);
            }
        } else {
            i += 1;
        }
    }

    // Simple case: last two statements are `var x = <expr>; return x;`
    loop {
        let len = stmts.len();
        if len < 2 {
            break;
        }
        let last_is_return_var = if let JsStmt::Return(JsExpr::Var(ref ret_name)) = stmts[len - 1] {
            Some(ret_name.clone())
        } else {
            None
        };
        if let Some(ret_name) = last_is_return_var {
            if let JsStmt::VarDecl(ref binding_name, Some(_)) = stmts[len - 2] {
                if binding_name == &ret_name {
                    // Replace: var x = <expr>; return x; → return <expr>;
                    if let JsStmt::VarDecl(_, Some(init)) = stmts.remove(len - 2) {
                        stmts[len - 2] = JsStmt::Return(init);
                        continue;
                    }
                }
            }
        }
        break;
    }
}

/// Check if an expression is a pure property access (safe to inline).
/// Matches: `v.field`, `v["field"]`, `v.field.field2` (chained)
pub(crate) fn is_pure_field_access(expr: &JsExpr) -> bool {
    match expr {
        JsExpr::Indexer(obj, _key) => {
            matches!(obj.as_ref(), JsExpr::Var(_)) || is_pure_field_access(obj)
        }
        _ => false,
    }
}

/// Extract the root variable name from a field access chain.
/// E.g., `v.value0` → "v", `v.value0.value1` → "v"
fn field_access_root(expr: &JsExpr) -> Option<&str> {
    match expr {
        JsExpr::Var(name) => Some(name.as_str()),
        JsExpr::Indexer(obj, _) => field_access_root(obj),
        _ => None,
    }
}

/// Count how many times a variable name is used in a list of statements.
pub(crate) fn count_var_uses_in_stmts(stmts: &[JsStmt], name: &str) -> usize {
    stmts.iter().map(|s| count_var_uses_in_stmt(s, name)).sum()
}

pub(crate) fn count_var_uses_in_stmt(stmt: &JsStmt, name: &str) -> usize {
    match stmt {
        JsStmt::Return(expr) => count_var_uses_in_expr(expr, name),
        JsStmt::VarDecl(_, Some(expr)) => count_var_uses_in_expr(expr, name),
        JsStmt::Assign(target, val) => count_var_uses_in_expr(target, name) + count_var_uses_in_expr(val, name),
        JsStmt::If(cond, then_body, else_body) => {
            count_var_uses_in_expr(cond, name)
                + count_var_uses_in_stmts(then_body, name)
                + else_body.as_ref().map_or(0, |stmts| count_var_uses_in_stmts(stmts, name))
        }
        JsStmt::Expr(expr) | JsStmt::Throw(expr) => count_var_uses_in_expr(expr, name),
        _ => 0,
    }
}

pub(crate) fn count_var_uses_in_expr(expr: &JsExpr, name: &str) -> usize {
    match expr {
        JsExpr::Var(n) => if n == name { 1 } else { 0 },
        JsExpr::App(callee, args) => {
            count_var_uses_in_expr(callee, name)
                + args.iter().map(|a| count_var_uses_in_expr(a, name)).sum::<usize>()
        }
        JsExpr::Function(_, _, body) => count_var_uses_in_stmts(body, name),
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            count_var_uses_in_expr(a, name) + count_var_uses_in_expr(b, name)
        }
        JsExpr::Unary(_, a) => count_var_uses_in_expr(a, name),
        JsExpr::Ternary(a, b, c) => {
            count_var_uses_in_expr(a, name) + count_var_uses_in_expr(b, name) + count_var_uses_in_expr(c, name)
        }
        JsExpr::ArrayLit(items) => items.iter().map(|i| count_var_uses_in_expr(i, name)).sum(),
        JsExpr::ObjectLit(fields) => fields.iter().map(|(_, v)| count_var_uses_in_expr(v, name)).sum(),
        JsExpr::New(callee, args) => {
            count_var_uses_in_expr(callee, name)
                + args.iter().map(|a| count_var_uses_in_expr(a, name)).sum::<usize>()
        }
        _ => 0,
    }
}

/// Substitute a variable name with an expression in a statement.
pub(crate) fn substitute_expr_in_stmt(stmt: &mut JsStmt, name: &str, replacement: &JsExpr) {
    match stmt {
        JsStmt::Return(expr) => {
            let new = substitute_expr_in_expr(expr.clone(), name, replacement);
            *expr = new;
        }
        JsStmt::VarDecl(_, Some(expr)) => {
            let new = substitute_expr_in_expr(expr.clone(), name, replacement);
            *expr = new;
        }
        JsStmt::If(cond, then_body, else_body) => {
            let new = substitute_expr_in_expr(cond.clone(), name, replacement);
            *cond = new;
            for s in then_body.iter_mut() {
                substitute_expr_in_stmt(s, name, replacement);
            }
            if let Some(stmts) = else_body {
                for s in stmts.iter_mut() {
                    substitute_expr_in_stmt(s, name, replacement);
                }
            }
        }
        JsStmt::Expr(expr) => {
            let new = substitute_expr_in_expr(expr.clone(), name, replacement);
            *expr = new;
        }
        JsStmt::Throw(expr) => {
            let new = substitute_expr_in_expr(expr.clone(), name, replacement);
            *expr = new;
        }
        _ => {}
    }
}

pub(crate) fn substitute_expr_in_expr(expr: JsExpr, name: &str, replacement: &JsExpr) -> JsExpr {
    match expr {
        JsExpr::Var(ref n) if n == name => replacement.clone(),
        JsExpr::App(callee, args) => JsExpr::App(
            Box::new(substitute_expr_in_expr(*callee, name, replacement)),
            args.into_iter().map(|a| substitute_expr_in_expr(a, name, replacement)).collect(),
        ),
        JsExpr::Function(fn_name, params, body) => {
            // Don't substitute into functions that shadow the name
            if params.iter().any(|p| p == name) {
                JsExpr::Function(fn_name, params, body)
            } else {
                let new_body: Vec<JsStmt> = body.into_iter().map(|mut s| {
                    substitute_expr_in_stmt(&mut s, name, replacement);
                    s
                }).collect();
                JsExpr::Function(fn_name, params, new_body)
            }
        }
        JsExpr::Indexer(a, b) => JsExpr::Indexer(
            Box::new(substitute_expr_in_expr(*a, name, replacement)),
            Box::new(substitute_expr_in_expr(*b, name, replacement)),
        ),
        JsExpr::Binary(op, a, b) => JsExpr::Binary(op,
            Box::new(substitute_expr_in_expr(*a, name, replacement)),
            Box::new(substitute_expr_in_expr(*b, name, replacement)),
        ),
        JsExpr::Unary(op, a) => JsExpr::Unary(op,
            Box::new(substitute_expr_in_expr(*a, name, replacement)),
        ),
        JsExpr::Ternary(a, b, c) => JsExpr::Ternary(
            Box::new(substitute_expr_in_expr(*a, name, replacement)),
            Box::new(substitute_expr_in_expr(*b, name, replacement)),
            Box::new(substitute_expr_in_expr(*c, name, replacement)),
        ),
        JsExpr::ArrayLit(items) => JsExpr::ArrayLit(
            items.into_iter().map(|i| substitute_expr_in_expr(i, name, replacement)).collect(),
        ),
        JsExpr::ObjectLit(fields) => JsExpr::ObjectLit(
            fields.into_iter().map(|(k, v)| (k, substitute_expr_in_expr(v, name, replacement))).collect(),
        ),
        JsExpr::New(callee, args) => JsExpr::New(
            Box::new(substitute_expr_in_expr(*callee, name, replacement)),
            args.into_iter().map(|a| substitute_expr_in_expr(a, name, replacement)).collect(),
        ),
        JsExpr::InstanceOf(a, b) => JsExpr::InstanceOf(
            Box::new(substitute_expr_in_expr(*a, name, replacement)),
            Box::new(substitute_expr_in_expr(*b, name, replacement)),
        ),
        other => other,
    }
}
