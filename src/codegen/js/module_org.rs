use std::collections::{HashMap, HashSet};

use crate::interner::{self, Symbol};
use crate::names::{ClassName, Qualified};

use super::*;
use super::super::common::ident_to_js;

/// Try to inline a let expression at the top level of a value declaration.
/// Instead of `var x = (function() { var a = 1; return a; })()`,
/// generates `var x = 1` when the body is a simple variable reference.
pub(crate) fn try_inline_let_value(
    ctx: &CodegenCtx,
    name: &str,
    expr: &Expr,
    constraints: Option<&Vec<(Qualified<ClassName>, Vec<crate::typechecker::types::Type>)>>,
) -> Option<Vec<JsStmt>> {
    let Expr::Let { bindings, body, .. } = expr else { return None };
    // Only inline if no constraints (constraints add function wrapping)
    if constraints.map_or(false, |c| !c.is_empty()) { return None; }

    // Collect binding names and check for module-level conflicts
    let mut binding_names: Vec<String> = Vec::new();
    for lb in bindings.iter() {
        if let LetBinding::Value { binder, .. } = lb {
            let mut names = HashSet::new();
            collect_binder_names(binder, &mut names);
            for sym in &names {
                binding_names.push(ident_to_js(*sym));
            }
        }
    }
    // If any binding name conflicts with an already-inlined name, use IIFE wrapping
    {
        let existing = ctx.module_level_let_names.borrow();
        if binding_names.iter().any(|n| existing.contains(n)) {
            return None;
        }
    }

    let prev_bindings = ctx.local_bindings.borrow().clone();
    for lb in bindings.iter() {
        if let LetBinding::Value { binder, .. } = lb {
            collect_binder_names(binder, &mut ctx.local_bindings.borrow_mut());
        }
    }

    // Generate let binding statements
    let mut stmts = Vec::new();
    gen_let_bindings(ctx, bindings, &mut stmts);
    let body_expr = gen_expr(ctx, body);
    *ctx.local_bindings.borrow_mut() = prev_bindings;

    // If the body is a simple variable reference to one of the let bindings,
    // replace the last binding's name with the target name (inline it).
    if let JsExpr::Var(ref var_name) = body_expr {
        // Find the binding that matches the body variable
        for i in (0..stmts.len()).rev() {
            if let JsStmt::VarDecl(ref binding_name, ref init) = stmts[i] {
                if binding_name == var_name {
                    // Replace binding name with target name, drop the rest that follow
                    let init = init.clone();
                    stmts[i] = JsStmt::VarDecl(name.to_string(), init);
                    stmts.truncate(i + 1);
                    // Register surviving let binding names at module level
                    register_module_level_names(ctx, &stmts, name);
                    return Some(stmts);
                }
            }
        }
    }

    stmts.push(JsStmt::VarDecl(name.to_string(), Some(body_expr)));
    // Register surviving let binding names at module level
    register_module_level_names(ctx, &stmts, name);
    Some(stmts)
}

/// Collect all module names referenced via ModuleAccessor in a list of statements.
pub(crate) fn collect_used_modules(body: &[JsStmt]) -> HashSet<String> {
    let mut used = HashSet::new();
    for stmt in body {
        collect_used_modules_stmt(stmt, &mut used);
    }
    used
}

pub(crate) fn collect_used_modules_stmt(stmt: &JsStmt, used: &mut HashSet<String>) {
    match stmt {
        JsStmt::Expr(e) => collect_used_modules_expr(e, used),
        JsStmt::VarDecl(_, Some(e)) => collect_used_modules_expr(e, used),
        JsStmt::VarDecl(_, None) => {}
        JsStmt::Assign(target, value) => {
            collect_used_modules_expr(target, used);
            collect_used_modules_expr(value, used);
        }
        JsStmt::Return(e) | JsStmt::Throw(e) => collect_used_modules_expr(e, used),
        JsStmt::ReturnVoid => {}
        JsStmt::If(cond, then_stmts, else_stmts) => {
            collect_used_modules_expr(cond, used);
            for s in then_stmts { collect_used_modules_stmt(s, used); }
            if let Some(els) = else_stmts {
                for s in els { collect_used_modules_stmt(s, used); }
            }
        }
        JsStmt::Block(stmts) => {
            for s in stmts { collect_used_modules_stmt(s, used); }
        }
        JsStmt::For(_, init, bound, body) => {
            collect_used_modules_expr(init, used);
            collect_used_modules_expr(bound, used);
            for s in body { collect_used_modules_stmt(s, used); }
        }
        JsStmt::ForIn(_, obj, body) => {
            collect_used_modules_expr(obj, used);
            for s in body { collect_used_modules_stmt(s, used); }
        }
        JsStmt::While(cond, body) => {
            collect_used_modules_expr(cond, used);
            for s in body { collect_used_modules_stmt(s, used); }
        }
        JsStmt::FunctionDecl(_, _, body) => {
            for s in body { collect_used_modules_stmt(s, used); }
        }
        JsStmt::Comment(_) | JsStmt::Import { .. } | JsStmt::Export(_)
        | JsStmt::ExportFrom(_, _) | JsStmt::RawJs(_) => {}
    }
}

pub(crate) fn collect_used_modules_expr(expr: &JsExpr, used: &mut HashSet<String>) {
    match expr {
        JsExpr::ModuleAccessor(module, _) => { used.insert(module.clone()); }
        JsExpr::App(callee, args) => {
            collect_used_modules_expr(callee, used);
            for a in args { collect_used_modules_expr(a, used); }
        }
        JsExpr::Function(_, _, body) => {
            for s in body { collect_used_modules_stmt(s, used); }
        }
        JsExpr::ArrayLit(elems) => {
            for e in elems { collect_used_modules_expr(e, used); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_used_modules_expr(v, used); }
        }
        JsExpr::Indexer(obj, key) => {
            collect_used_modules_expr(obj, used);
            collect_used_modules_expr(key, used);
        }
        JsExpr::Unary(_, e) => collect_used_modules_expr(e, used),
        JsExpr::Binary(_, l, r) => {
            collect_used_modules_expr(l, used);
            collect_used_modules_expr(r, used);
        }
        JsExpr::InstanceOf(l, r) => {
            collect_used_modules_expr(l, used);
            collect_used_modules_expr(r, used);
        }
        JsExpr::New(callee, args) => {
            collect_used_modules_expr(callee, used);
            for a in args { collect_used_modules_expr(a, used); }
        }
        JsExpr::Ternary(c, t, e) => {
            collect_used_modules_expr(c, used);
            collect_used_modules_expr(t, used);
            collect_used_modules_expr(e, used);
        }
        JsExpr::NumericLit(_) | JsExpr::IntLit(_) | JsExpr::StringLit(_)
        | JsExpr::BoolLit(_) | JsExpr::Var(_) | JsExpr::RawJs(_) => {}
    }
}

/// Check if a statement is a constructor IIFE declaration.
/// Constructor IIFEs look like: var Ctor = (function() { function Ctor(...) { this.value0 = ... }; ... return Ctor; })()
/// They are self-contained and have no external dependencies, so they can always go first.
pub(crate) fn is_constructor_iife(stmt: &JsStmt) -> bool {
    if let JsStmt::VarDecl(name, Some(JsExpr::App(callee, args))) = stmt {
        if args.is_empty() {
            if let JsExpr::Function(None, params, body) = callee.as_ref() {
                if params.is_empty() && !body.is_empty() {
                    // Check if first statement is a function declaration with same name
                    // or is a function expression statement with same name
                    if let Some(first) = body.first() {
                        match first {
                            JsStmt::Expr(JsExpr::Function(Some(fn_name), _, _)) => {
                                return fn_name == name;
                            }
                            JsStmt::FunctionDecl(fn_name, _, _) => {
                                return fn_name == name;
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }
    false
}

/// Topologically sort VarDecl statements so dependencies come first.
/// Non-VarDecl statements maintain their relative position.
pub(crate) fn topo_sort_body(body: Vec<JsStmt>) -> Vec<JsStmt> {
    // Build dependency graph for VarDecl statements
    let mut decl_indices: HashMap<String, usize> = HashMap::new();
    for (i, stmt) in body.iter().enumerate() {
        if let JsStmt::VarDecl(name, _) = stmt {
            decl_indices.insert(name.clone(), i);
        }
    }

    // For each VarDecl, find which other VarDecls it eagerly references.
    // Only collect references that are evaluated immediately (not inside lambdas).
    // Deferred references (inside function bodies) are safe as forward references
    // and must NOT create ordering constraints — otherwise mutually-recursive
    // instance dictionaries (e.g. Effect's applicativeEffect/applyEffect/monadEffect)
    // get ordered incorrectly.
    // Build a map of instance-dict-like declarations: for each VarDecl that is an
    // ObjectLit, record which vars are returned by its zero-arg function fields
    // (superclass accessors). These are "indirect deps" — if X eagerly uses Y,
    // and Y is an instance dict with accessor Z() returning W, then X transitively
    // depends on W being defined before Y's accessors are called.
    // Track which declarations are ObjectLits (instance dicts) for cycle avoidance.
    let mut object_lit_decls: HashSet<String> = HashSet::new();
    let mut dict_accessor_returns: HashMap<String, HashSet<String>> = HashMap::new();
    for stmt in &body {
        if let JsStmt::VarDecl(name, Some(JsExpr::ObjectLit(fields))) = stmt {
            object_lit_decls.insert(name.clone());
            let mut accessor_vars = HashSet::new();
            for (_, val) in fields {
                // Match: function() { return someVar; }
                if let JsExpr::Function(_, params, body_stmts) = val {
                    if params.is_empty() {
                        if let Some(JsStmt::Return(JsExpr::Var(v))) = body_stmts.first() {
                            accessor_vars.insert(v.clone());
                        }
                    }
                }
            }
            if !accessor_vars.is_empty() {
                dict_accessor_returns.insert(name.clone(), accessor_vars);
            }
        }
    }

    // Build a map of ALL variable refs from each VarDecl function body (including nested functions).
    // This is used to determine that function A needs function B to be defined before A,
    // because A's body (possibly deeply nested) references B.
    let mut function_body_refs: HashMap<String, HashSet<String>> = HashMap::new();
    for stmt in &body {
        if let JsStmt::VarDecl(name, Some(JsExpr::Function(_, params, fn_body))) = stmt {
            let mut body_refs = HashSet::new();
            for s in fn_body {
                collect_all_var_refs_stmt(s, &mut body_refs);
            }
            // Remove params
            for p in params {
                body_refs.remove(p);
            }
            // Remove self-references
            body_refs.remove(name);
            if !body_refs.is_empty() {
                function_body_refs.insert(name.clone(), body_refs);
            }
        }
    }

    let mut decl_refs: Vec<HashSet<String>> = Vec::new();
    for stmt in &body {
        let mut refs = HashSet::new();
        if let JsStmt::VarDecl(name, Some(expr)) = stmt {
            collect_eager_refs_expr(expr, &mut refs);

            // For VarDecl functions (not ObjectLits/dicts), add body refs as direct deps.
            // When the function is called at runtime, its body refs need to be initialized.
            // `var F = function(...) { ... compose(x) ... }` needs `compose` to be defined.
            // We skip ObjectLit (instance dict) VarDecls to avoid cycles from mutual recursion.
            if let JsExpr::Function(_, _, _) = expr {
                if let Some(body_refs) = function_body_refs.get(name) {
                    refs.extend(body_refs.iter().cloned());
                }
            }

            // For IIFEs, scan local function definitions for refs to module-level
            // plain function declarations (not instance dicts/ObjectLits).
            // Local functions inside IIFEs are called within the IIFE (which executes
            // immediately), so their references are effectively eager.
            if let JsExpr::App(f, _) = expr {
                if let JsExpr::Function(_, _, iife_body) = f.as_ref() {
                    for iife_stmt in iife_body {
                        if let JsStmt::VarDecl(local_name, Some(JsExpr::Function(_, params, fn_body))) = iife_stmt {
                            let mut fn_refs = HashSet::new();
                            for s in fn_body {
                                collect_all_refs_stmt(s, &mut fn_refs);
                            }
                            for p in params {
                                fn_refs.remove(p);
                            }
                            fn_refs.remove(local_name);
                            // Only keep refs that are module-level function declarations
                            // (not instance dicts), to avoid creating cycles between
                            // mutually-recursive instance dict IIFEs.
                            for r in fn_refs {
                                if function_body_refs.contains_key(&r) {
                                    refs.insert(r);
                                }
                            }
                        }
                    }
                }
            }

            // For eagerly-evaluated expressions (not functions, not object literals),
            // also collect refs from nested lambda bodies to module-level declarations.
            // This handles cases like:
            //   var test = runState("")(bind(f)(function() { ... get1 ... pure ... }))
            // where lambda bodies reference vars that need to be defined before `test`.
            // Exclude ObjectLit (instance dict) declarations to avoid creating cycles
            // between mutually-recursive instance dict IIFEs.
            if !matches!(expr, JsExpr::Function(_, _, _) | JsExpr::ObjectLit(_)) {
                let mut all_refs = HashSet::new();
                collect_all_var_refs_expr(expr, &mut all_refs);
                all_refs.remove(name);
                for r in all_refs {
                    if decl_indices.contains_key(&r) && !object_lit_decls.contains(&r) {
                        refs.insert(r);
                    }
                }
            }

            // Add transitive deps through instance dict accessors (multi-level):
            // if this decl eagerly references a dict D, and D has accessor
            // fields that return vars V1, V2, ..., add those as deps too.
            // Follow the chain transitively: V1 might also be a dict with accessors.
            let mut transitive: HashSet<String> = HashSet::new();
            let mut worklist: Vec<String> = refs.iter().cloned().collect();
            let mut visited_for_transitive: HashSet<String> = HashSet::new();
            while let Some(r) = worklist.pop() {
                if !visited_for_transitive.insert(r.clone()) { continue; }
                if let Some(accessor_vars) = dict_accessor_returns.get(&r) {
                    for v in accessor_vars {
                        transitive.insert(v.clone());
                        worklist.push(v.clone());
                    }
                }
                // Add transitive deps through function calls:
                // if this decl eagerly references a function F, and F's body
                // references vars V1, V2, ..., add those as deps too.
                if let Some(body_refs) = function_body_refs.get(&r) {
                    for v in body_refs {
                        transitive.insert(v.clone());
                    }
                }
            }
            refs.extend(transitive);
        }
        decl_refs.push(refs);
    }

    // Simple topological sort using DFS.
    // Visit nodes in reverse-alphabetical order to match the original compiler's
    // tie-breaking for independent declarations.
    let n = body.len();
    let mut visited = vec![false; n];
    let mut in_stack = vec![false; n];
    let mut order = Vec::with_capacity(n);

    fn visit(
        i: usize,
        body: &[JsStmt],
        decl_indices: &HashMap<String, usize>,
        decl_refs: &[HashSet<String>],
        visited: &mut [bool],
        in_stack: &mut [bool],
        order: &mut Vec<usize>,
    ) {
        if visited[i] { return; }
        if in_stack[i] { return; } // cycle — skip to avoid infinite loop
        in_stack[i] = true;

        // Visit dependencies in sorted order for determinism
        let mut deps: Vec<usize> = decl_refs[i].iter()
            .filter_map(|dep_name| decl_indices.get(dep_name).copied())
            .filter(|&dep_idx| dep_idx != i)
            .collect();
        deps.sort();
        deps.dedup();

        for dep_idx in deps {
            visit(dep_idx, body, decl_indices, decl_refs, visited, in_stack, order);
        }

        in_stack[i] = false;
        visited[i] = true;
        order.push(i);
    }

    // Build iteration order: reverse-alphabetical by name for VarDecls.
    // This matches the original PureScript compiler's tie-breaking order
    // for independent declarations in the topological sort.
    let mut indices_by_name: Vec<(usize, String)> = Vec::new();
    let mut other_indices: Vec<usize> = Vec::new();
    for i in 0..n {
        if let JsStmt::VarDecl(name, _) = &body[i] {
            indices_by_name.push((i, name.clone()));
        } else {
            other_indices.push(i);
        }
    }
    indices_by_name.sort_by(|a, b| b.1.cmp(&a.1));

    for &(i, _) in &indices_by_name {
        visit(i, &body, &decl_indices, &decl_refs, &mut visited, &mut in_stack, &mut order);
    }
    for i in other_indices {
        if !visited[i] {
            order.push(i);
        }
    }

    // Rebuild body in topological order
    let mut body_vec: Vec<Option<JsStmt>> = body.into_iter().map(Some).collect();
    let mut result = Vec::with_capacity(n);
    for idx in order {
        if let Some(stmt) = body_vec[idx].take() {
            result.push(stmt);
        }
    }
    // Add any remaining (shouldn't happen but safety)
    for stmt in body_vec {
        if let Some(s) = stmt {
            result.push(s);
        }
    }
    result
}

/// Collect ALL variable references from an expression, including inside nested functions.
/// Used for function body dependency analysis in the topo sort.
pub(crate) fn collect_all_var_refs_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
    match expr {
        JsExpr::Var(name) => { refs.insert(name.clone()); }
        JsExpr::App(f, args) => {
            collect_all_var_refs_expr(f, refs);
            for a in args { collect_all_var_refs_expr(a, refs); }
        }
        JsExpr::Function(_, params, body) => {
            let mut inner_refs = HashSet::new();
            for s in body { collect_all_var_refs_stmt(s, &mut inner_refs); }
            for p in params { inner_refs.remove(p); }
            refs.extend(inner_refs);
        }
        JsExpr::ArrayLit(elems) => {
            for e in elems { collect_all_var_refs_expr(e, refs); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_all_var_refs_expr(v, refs); }
        }
        JsExpr::Indexer(a, b) => {
            collect_all_var_refs_expr(a, refs);
            collect_all_var_refs_expr(b, refs);
        }
        JsExpr::Unary(_, e) => collect_all_var_refs_expr(e, refs),
        JsExpr::Binary(_, a, b) => {
            collect_all_var_refs_expr(a, refs);
            collect_all_var_refs_expr(b, refs);
        }
        JsExpr::Ternary(c, t, e) => {
            collect_all_var_refs_expr(c, refs);
            collect_all_var_refs_expr(t, refs);
            collect_all_var_refs_expr(e, refs);
        }
        JsExpr::InstanceOf(a, b) => {
            collect_all_var_refs_expr(a, refs);
            collect_all_var_refs_expr(b, refs);
        }
        JsExpr::New(f, args) => {
            collect_all_var_refs_expr(f, refs);
            for a in args { collect_all_var_refs_expr(a, refs); }
        }
        JsExpr::ModuleAccessor(_, _) | JsExpr::NumericLit(_) | JsExpr::IntLit(_)
        | JsExpr::StringLit(_) | JsExpr::BoolLit(_) | JsExpr::RawJs(_) => {}
    }
}

/// Collect ALL variable references from a statement, including inside nested functions.
pub(crate) fn collect_all_var_refs_stmt(stmt: &JsStmt, refs: &mut HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => {
            collect_all_var_refs_expr(expr, refs);
            refs.remove(name);
        }
        JsStmt::VarDecl(_, None) => {}
        JsStmt::Return(expr) | JsStmt::Throw(expr) | JsStmt::Expr(expr) => {
            collect_all_var_refs_expr(expr, refs);
        }
        JsStmt::Assign(target, expr) => {
            collect_all_var_refs_expr(target, refs);
            collect_all_var_refs_expr(expr, refs);
        }
        JsStmt::If(cond, then_stmts, else_stmts) => {
            collect_all_var_refs_expr(cond, refs);
            for s in then_stmts { collect_all_var_refs_stmt(s, refs); }
            if let Some(else_s) = else_stmts {
                for s in else_s { collect_all_var_refs_stmt(s, refs); }
            }
        }
        JsStmt::Block(stmts) | JsStmt::While(_, stmts) => {
            for s in stmts { collect_all_var_refs_stmt(s, refs); }
        }
        JsStmt::For(var_name, init, bound, body_stmts) => {
            collect_all_var_refs_expr(init, refs);
            collect_all_var_refs_expr(bound, refs);
            for s in body_stmts { collect_all_var_refs_stmt(s, refs); }
            refs.remove(var_name);
        }
        JsStmt::ForIn(var_name, expr, body_stmts) => {
            collect_all_var_refs_expr(expr, refs);
            for s in body_stmts { collect_all_var_refs_stmt(s, refs); }
            refs.remove(var_name);
        }
        JsStmt::FunctionDecl(name, params, body_stmts) => {
            let mut inner = HashSet::new();
            for s in body_stmts { collect_all_var_refs_stmt(s, &mut inner); }
            for p in params { inner.remove(p); }
            inner.remove(name);
            refs.extend(inner);
        }
        JsStmt::ReturnVoid | JsStmt::Comment(_) | JsStmt::RawJs(_) => {}
        JsStmt::Import { .. } | JsStmt::Export(_) | JsStmt::ExportFrom(_, _) => {}
    }
}

/// Collect only eagerly-evaluated variable references from an expression.
/// Skips references inside function bodies (those are deferred and safe as forward refs).
pub(crate) fn collect_eager_refs_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
    match expr {
        JsExpr::Var(name) => { refs.insert(name.clone()); }
        JsExpr::App(f, args) => {
            // Special case: IIFE — (function(...) { body })(...) is eagerly evaluated,
            // so we need to collect refs from the function body too.
            if let JsExpr::Function(_, params, body) = f.as_ref() {
                for a in args { collect_eager_refs_expr(a, refs); }
                // Collect eager refs from the IIFE body (statements)
                for stmt in body {
                    collect_eager_refs_stmt_eager(stmt, refs);
                }
                // Remove params (they shadow outer vars)
                for p in params {
                    refs.remove(p);
                }
            } else {
                collect_eager_refs_expr(f, refs);
                for a in args { collect_eager_refs_expr(a, refs); }
            }
        }
        JsExpr::Function(_, _, _) => {
            // Don't descend into function bodies — those refs are deferred
        }
        JsExpr::ArrayLit(elems) => {
            for e in elems { collect_eager_refs_expr(e, refs); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_eager_refs_expr(v, refs); }
        }
        JsExpr::Indexer(a, b) => {
            collect_eager_refs_expr(a, refs);
            collect_eager_refs_expr(b, refs);
        }
        JsExpr::Unary(_, e) => collect_eager_refs_expr(e, refs),
        JsExpr::Binary(_, a, b) => {
            collect_eager_refs_expr(a, refs);
            collect_eager_refs_expr(b, refs);
        }
        JsExpr::Ternary(c, t, e) => {
            collect_eager_refs_expr(c, refs);
            collect_eager_refs_expr(t, refs);
            collect_eager_refs_expr(e, refs);
        }
        JsExpr::InstanceOf(a, b) => {
            collect_eager_refs_expr(a, refs);
            collect_eager_refs_expr(b, refs);
        }
        JsExpr::New(f, args) => {
            collect_eager_refs_expr(f, refs);
            for a in args { collect_eager_refs_expr(a, refs); }
        }
        JsExpr::ModuleAccessor(_, _) | JsExpr::NumericLit(_) | JsExpr::IntLit(_)
        | JsExpr::StringLit(_) | JsExpr::BoolLit(_) | JsExpr::RawJs(_) => {}
    }
}

/// Collect eager refs from a statement (used for IIFE bodies).
pub(crate) fn collect_eager_refs_stmt_eager(stmt: &JsStmt, refs: &mut HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => {
            collect_eager_refs_expr(expr, refs);
            refs.remove(name);
        }
        JsStmt::VarDecl(_, None) => {}
        JsStmt::Return(expr) | JsStmt::Throw(expr) | JsStmt::Expr(expr) => {
            collect_eager_refs_expr(expr, refs);
        }
        JsStmt::Assign(target, expr) => {
            collect_eager_refs_expr(target, refs);
            collect_eager_refs_expr(expr, refs);
        }
        JsStmt::If(cond, then_stmts, else_stmts) => {
            collect_eager_refs_expr(cond, refs);
            for s in then_stmts { collect_eager_refs_stmt_eager(s, refs); }
            if let Some(else_s) = else_stmts {
                for s in else_s { collect_eager_refs_stmt_eager(s, refs); }
            }
        }
        JsStmt::Block(stmts) | JsStmt::While(_, stmts) => {
            for s in stmts { collect_eager_refs_stmt_eager(s, refs); }
        }
        _ => {}
    }
}

/// Collect ALL variable references from an expression, including inside function bodies.
pub(crate) fn collect_all_refs_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
    match expr {
        JsExpr::Var(name) => { refs.insert(name.clone()); }
        JsExpr::App(f, args) => {
            collect_all_refs_expr(f, refs);
            for a in args { collect_all_refs_expr(a, refs); }
        }
        JsExpr::Function(_, params, body) => {
            // Collect refs from function body too (unlike collect_eager_refs)
            for stmt in body {
                collect_all_refs_stmt(stmt, refs);
            }
            // Remove params (they shadow outer vars)
            for p in params {
                refs.remove(p);
            }
        }
        JsExpr::ArrayLit(elems) => {
            for e in elems { collect_all_refs_expr(e, refs); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_all_refs_expr(v, refs); }
        }
        JsExpr::Indexer(a, b) => {
            collect_all_refs_expr(a, refs);
            collect_all_refs_expr(b, refs);
        }
        JsExpr::Unary(_, e) => collect_all_refs_expr(e, refs),
        JsExpr::Binary(_, a, b) => {
            collect_all_refs_expr(a, refs);
            collect_all_refs_expr(b, refs);
        }
        JsExpr::Ternary(c, t, e) => {
            collect_all_refs_expr(c, refs);
            collect_all_refs_expr(t, refs);
            collect_all_refs_expr(e, refs);
        }
        JsExpr::InstanceOf(a, b) => {
            collect_all_refs_expr(a, refs);
            collect_all_refs_expr(b, refs);
        }
        JsExpr::New(f, args) => {
            collect_all_refs_expr(f, refs);
            for a in args { collect_all_refs_expr(a, refs); }
        }
        JsExpr::ModuleAccessor(_, _) | JsExpr::NumericLit(_) | JsExpr::IntLit(_)
        | JsExpr::StringLit(_) | JsExpr::BoolLit(_) | JsExpr::RawJs(_) => {}
    }
}

/// Collect ALL variable references from a statement, including inside function bodies.
pub(crate) fn collect_all_refs_stmt(stmt: &JsStmt, refs: &mut HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => {
            collect_all_refs_expr(expr, refs);
            // Remove the declared name (it's a local binding, not a reference)
            refs.remove(name);
        }
        JsStmt::VarDecl(_, None) => {}
        JsStmt::Return(expr) | JsStmt::Throw(expr) | JsStmt::Expr(expr) => {
            collect_all_refs_expr(expr, refs);
        }
        JsStmt::Assign(target, expr) => {
            collect_all_refs_expr(target, refs);
            collect_all_refs_expr(expr, refs);
        }
        JsStmt::If(cond, then_stmts, else_stmts) => {
            collect_all_refs_expr(cond, refs);
            for s in then_stmts { collect_all_refs_stmt(s, refs); }
            if let Some(else_s) = else_stmts {
                for s in else_s { collect_all_refs_stmt(s, refs); }
            }
        }
        JsStmt::Block(stmts) | JsStmt::While(_, stmts) => {
            for s in stmts { collect_all_refs_stmt(s, refs); }
        }
        JsStmt::For(var, init, bound, stmts) => {
            collect_all_refs_expr(init, refs);
            collect_all_refs_expr(bound, refs);
            for s in stmts { collect_all_refs_stmt(s, refs); }
            refs.remove(var);
        }
        JsStmt::ForIn(var, obj, stmts) => {
            collect_all_refs_expr(obj, refs);
            for s in stmts { collect_all_refs_stmt(s, refs); }
            refs.remove(var);
        }
        JsStmt::FunctionDecl(_, _, body) => {
            for s in body { collect_all_refs_stmt(s, refs); }
        }
        JsStmt::ReturnVoid | JsStmt::Comment(_) | JsStmt::Import { .. }
        | JsStmt::Export(_) | JsStmt::ExportFrom(_, _) | JsStmt::RawJs(_) => {}
    }
}


/// Extract head type constructor from CST type expressions.
pub(crate) fn extract_head_type_con_from_cst(types: &[crate::cst::TypeExpr], type_op_targets: &HashMap<Symbol, Symbol>) -> Option<Symbol> {
    // Try all type args for multi-parameter type classes (e.g., MonadState s (State s))
    types.iter().find_map(|t| extract_head_from_type_expr(t, type_op_targets))
}

pub(crate) fn extract_head_from_type_expr(te: &crate::cst::TypeExpr, type_op_targets: &HashMap<Symbol, Symbol>) -> Option<Symbol> {
    use crate::cst::TypeExpr;
    match te {
        TypeExpr::Constructor { name, .. } => Some(name.name),
        TypeExpr::App { constructor, .. } => extract_head_from_type_expr(constructor, type_op_targets),
        TypeExpr::Record { .. } => Some(interner::intern("Record")),
        TypeExpr::Row { .. } => Some(interner::intern("Record")),
        TypeExpr::Function { .. } => Some(interner::intern("Function")),
        TypeExpr::Forall { ty, .. } => extract_head_from_type_expr(ty, type_op_targets),
        TypeExpr::Constrained { ty, .. } => extract_head_from_type_expr(ty, type_op_targets),
        TypeExpr::Parens { ty, .. } => extract_head_from_type_expr(ty, type_op_targets),
        TypeExpr::TypeOp { op, .. } => type_op_targets.get(&op.value.name).copied(),
        _ => None,
    }
}

/// Extract head type constructor from typechecker Type values.
pub(crate) fn extract_head_type_con_from_types(types: &[crate::typechecker::types::Type]) -> Option<Symbol> {
    // Try all type args for multi-parameter type classes (e.g., MonadState s (State s))
    types.iter().find_map(|t| extract_head_from_type(t))
}

pub(crate) fn extract_head_from_type(ty: &crate::typechecker::types::Type) -> Option<Symbol> {
    use crate::typechecker::types::Type;
    match ty {
        Type::Con(qi) => Some(qi.name),
        Type::App(f, _) => extract_head_from_type(f),
        Type::Record(_, _) => Some(interner::intern("Record")),
        Type::Fun(_, _) => Some(interner::intern("Function")),
        _ => None,
    }
}

/// Extract type arguments from the CST instance types for a given head type constructor.
pub(crate) fn extract_cst_type_args_for_head<'a>(
    types: &'a [crate::cst::TypeExpr],
    head: Symbol,
    type_op_targets: &HashMap<Symbol, Symbol>,
) -> Vec<&'a crate::cst::TypeExpr> {
    
    for te in types {
        if extract_head_from_type_expr(te, type_op_targets) == Some(head) {
            return collect_cst_app_args(te);
        }
    }
    vec![]
}

/// Collect type arguments from a CST type application.
pub(crate) fn collect_cst_app_args(te: &crate::cst::TypeExpr) -> Vec<&crate::cst::TypeExpr> {
    use crate::cst::TypeExpr;
    match te {
        TypeExpr::App { constructor, arg, .. } => {
            let mut result = collect_cst_app_args(constructor);
            result.push(arg.as_ref());
            result
        }
        TypeExpr::Parens { ty, .. } => collect_cst_app_args(ty),
        _ => vec![],
    }
}

/// Collect type arguments from a typechecker Type after the head constructor.
pub(crate) fn collect_type_args_from_type(ty: &crate::typechecker::types::Type) -> Vec<&crate::typechecker::types::Type> {
    use crate::typechecker::types::Type;
    fn collect_inner<'a>(ty: &'a Type, args: &mut Vec<&'a Type>) {
        match ty {
            Type::App(f, arg) => {
                collect_inner(f, args);
                args.push(arg);
            }
            _ => {}
        }
    }
    let mut args = vec![];
    collect_inner(ty, &mut args);
    args
}

/// Extract binder name from a simple Var binder pattern (CST).
pub(crate) fn extract_simple_binder_name(binder: &Binder) -> Option<Symbol> {
    match binder {
        Binder::Var { name, .. } => Some(name.value),
        _ => None,
    }
}

/// Walk a type signature and find parameter positions with constrained higher-rank types.
/// Returns Vec<(param_index, dict_param_name)> where dict_param_name is e.g. "dictIsSymbol".
pub(crate) fn extract_constrained_param_indices(ty: &TypeExpr) -> Vec<(usize, String)> {
    // Strip outer Forall
    let ty = strip_outer_forall(ty);
    // Strip outer Constrained (function's own constraints)
    let ty = match ty {
        TypeExpr::Constrained { ty, .. } => ty.as_ref(),
        other => other,
    };
    // Walk the Function chain to get parameter types
    let mut result = Vec::new();
    let mut current = ty;
    let mut index = 0;
    loop {
        match current {
            TypeExpr::Function { from, to, .. } => {
                if let Some(class_name) = find_nested_constraint_class(from) {
                    let dict_name = format!("dict{class_name}");
                    result.push((index, dict_name));
                }
                current = to.as_ref();
                index += 1;
            }
            _ => break,
        }
    }
    result
}

pub(crate) fn strip_outer_forall(ty: &TypeExpr) -> &TypeExpr {
    match ty {
        TypeExpr::Forall { ty, .. } => strip_outer_forall(ty),
        TypeExpr::Parens { ty, .. } => strip_outer_forall(ty),
        other => other,
    }
}

/// Check if a type expression has a nested constraint (after stripping Forall/Parens).
/// Returns the first constraint class name if found.
pub(crate) fn find_nested_constraint_class(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Constrained { constraints, .. } => {
            constraints.first().map(|c| {
                interner::resolve(c.class.name).unwrap_or_default().to_string()
            })
        }
        TypeExpr::Forall { ty, .. } => find_nested_constraint_class(ty),
        TypeExpr::Parens { ty, .. } => find_nested_constraint_class(ty),
        _ => None,
    }
}

/// Check if an expression is a call to `unsafePartial` (from Partial.Unsafe).
/// Used to wrap the argument in a zero-arg thunk at the call site.
pub(crate) fn is_unsafe_partial_call(expr: &Expr) -> bool {
    match expr {
        Expr::Var { name, .. } => {
            let name_str = interner::resolve(name.name).unwrap_or_default();
            name_str == "unsafePartial"
        }
        _ => false,
    }
}

/// Check if a JsExpr is a reference to `unsafePartial` (already generated).
/// Used in the shunting-yard apply_op to detect `unsafePartial $ expr`.
pub(crate) fn is_js_unsafe_partial(expr: &JsExpr) -> bool {
    match expr {
        JsExpr::ModuleAccessor(_, method) if method == "unsafePartial" => true,
        JsExpr::Var(name) if name == "unsafePartial" => true,
        _ => false,
    }
}

pub(crate) fn has_partial_constraint(ty: &crate::cst::TypeExpr) -> bool {
    use crate::cst::TypeExpr;
    match ty {
        TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                let class_str = interner::resolve(c.class.name).unwrap_or_default();
                if class_str == "Partial" {
                    return true;
                }
            }
            has_partial_constraint(ty)
        }
        TypeExpr::Forall { ty, .. } => has_partial_constraint(ty),
        _ => false,
    }
}
