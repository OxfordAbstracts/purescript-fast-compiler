use std::collections::{HashMap, HashSet};

use crate::interner::{self, Symbol};
use crate::lexer::token::Ident;
use crate::names::{ClassName, TypeName};

use super::*;
use super::super::common::{ident_to_js, any_name_to_js};

pub(crate) fn gen_multi_equation(ctx: &CodegenCtx, js_name: &str, decls: &[&Decl]) -> Vec<JsStmt> {
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

    let params: Vec<String> = (0..arity).map(|_i| ctx.fresh_name("v")).collect();

    let mut body = Vec::new();
    let mut last_unconditional = false;
    for decl in decls {
        if let Decl::Value { binders, guarded, where_clause, .. } = decl {
            let mut alt_body = Vec::new();

            let result_stmts = gen_guarded_expr_stmts(ctx, guarded);

            // Build pattern match condition
            let (cond, bindings) = gen_binders_match(ctx, binders, &params);
            alt_body.extend(bindings);
            if !where_clause.is_empty() {
                let where_start = alt_body.len();
                gen_let_bindings(ctx, where_clause, &mut alt_body);
                let where_end = alt_body.len();
                // Reorder where-clause bindings: reverse source order with dependency preservation
                if where_end > where_start {
                    reorder_where_bindings(&mut alt_body[where_start..where_end]);
                }
            }
            alt_body.extend(result_stmts);
            // Inline trivial aliases from where-bindings (e.g., `unsafeGet' = unsafeGet :: ...`)
            inline_trivial_aliases(&mut alt_body);
            inline_single_use_bindings(&mut alt_body);

            if let Some(cond) = cond {
                body.push(JsStmt::If(cond, alt_body, None));
                last_unconditional = false;
            } else {
                // Unconditional match (all wildcards/vars)
                body.extend(alt_body);
                last_unconditional = true;
            }
        }
    }

    // Only add the throw if the last equation wasn't an unconditional catch-all
    if !last_unconditional {
        body.push(JsStmt::Throw(JsExpr::New(
            Box::new(JsExpr::Var("Error".to_string())),
            vec![JsExpr::StringLit("Failed pattern match".to_string())],
        )));
    }

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

pub(crate) fn gen_data_decl(_ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Data { constructors, .. } = decl else { return vec![] };

    let mut stmts = Vec::new();
    for ctor in constructors {
        let ctor_js = ident_to_js(ctor.name.value.symbol());
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

pub(crate) fn gen_newtype_decl(_ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Newtype { constructor, .. } = decl else { return vec![] };
    let ctor_js = ident_to_js(constructor.value.symbol());

    // Newtype constructor is identity: var Name = function(x) { return x; };
    let identity = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );

    vec![JsStmt::VarDecl(ctor_js, Some(identity))]
}

// ===== Class declarations =====

pub(crate) fn gen_class_decl(_ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Class { members, .. } = decl else { return vec![] };

    let mut stmts = Vec::new();
    for member in members {
        let method_js = ident_to_js(member.name.value.symbol());
        let method_ps = member.name.value.resolve().unwrap_or_default();
        // Generate: var method = function(dict) { return dict["method"]; };
        // Use original PS name for the dict key (e.g. "genericBottom'" not "genericBottom$prime")
        let accessor = JsExpr::Function(
            None,
            vec!["dict".to_string()],
            vec![JsStmt::Return(JsExpr::Indexer(
                Box::new(JsExpr::Var("dict".to_string())),
                Box::new(JsExpr::StringLit(method_ps.to_string())),
            ))],
        );
        stmts.push(JsStmt::VarDecl(method_js, Some(accessor)));
    }
    stmts
}

// ===== Instance declarations =====

/// Extract a name string from a TypeExpr for instance naming.
/// E.g., `Boolean` → "Boolean", `Array a` → "Array", `Proxy` → "Proxy"
pub(crate) fn type_expr_to_name(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Constructor { name, .. } => {
            interner::resolve(name.name.symbol()).unwrap_or_default().to_string()
        }
        TypeExpr::Var { name, .. } => {
            interner::resolve(name.value.symbol()).unwrap_or_default().to_string()
        }
        TypeExpr::App { constructor, .. } => type_expr_to_name(constructor),
        TypeExpr::Parens { ty, .. } => type_expr_to_name(ty),
        _ => String::new(),
    }
}

/// Generate a JS name for an unnamed instance from its class name and type arguments.
pub(crate) fn gen_unnamed_instance_name(
    class_name: Symbol,
    types: &[TypeExpr],
    instance_registry: &HashMap<(ClassName, TypeName), Symbol>,
    type_op_targets: &HashMap<Symbol, Symbol>,
) -> String {
    // Try the instance registry first
    let registry_name = extract_head_type_con_from_cst(types, type_op_targets).and_then(|head| {
        instance_registry.get(&(ClassName::new(class_name), TypeName::new(head))).map(|n| ident_to_js(*n))
    });
    if let Some(name) = registry_name {
        return name;
    }
    // Fallback: Generate from class + types, e.g. "reifiableBoolean"
    let class_str = interner::resolve(class_name).unwrap_or_default();
    let mut gen_name = String::new();
    for (i, c) in class_str.chars().enumerate() {
        if i == 0 {
            gen_name.extend(c.to_lowercase());
        } else {
            gen_name.push(c);
        }
    }
    for ty in types {
        gen_name.push_str(&type_expr_to_name(ty));
    }
    ident_to_js(interner::intern(&gen_name))
}

pub(crate) fn gen_instance_decl(ctx: &CodegenCtx, decl: &Decl, override_name: Option<String>) -> Vec<JsStmt> {
    let Decl::Instance { name, members, constraints, class_name, types, .. } = decl else { return vec![] };

    // Use override name if provided (already deduplicated by caller), otherwise compute
    let instance_name = if let Some(n) = override_name {
        n
    } else {
        match name {
            Some(n) => ident_to_js(n.value.symbol()),
            None => gen_unnamed_instance_name(class_name.name.symbol(), types, &ctx.instance_registry, &ctx.type_op_targets),
        }
    };

    // Push dict scope entries for instance constraints (with unique names for same-class)
    // Only push runtime constraints — zero-cost constraints have no param.
    let prev_scope_len = ctx.dict_scope.borrow().len();
    {
        let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
        for constraint in constraints {
            if !ctx.known_runtime_classes.contains(&constraint.class.name.symbol()) {
                continue; // Zero-cost constraint — no runtime dict param
            }
            let class_name_str = interner::resolve(constraint.class.name.symbol()).unwrap_or_default();
            let count = dict_name_counts.entry(class_name_str.to_string()).or_insert(0);
            let dict_param = if *count == 0 {
                format!("dict{class_name_str}")
            } else {
                format!("dict{class_name_str}{count}")
            };
            *count += 1;
            ctx.dict_scope.borrow_mut().push((constraint.class.name.symbol(), dict_param));
        }
    }

    // Build multi-equation groups for instance methods (preserving source order)
    let mut method_order: Vec<Symbol> = Vec::new();
    let mut method_map: HashMap<Symbol, Vec<&Decl>> = HashMap::new();
    for member in members {
        if let Decl::Value { name: method_name, .. } = member {
            if !method_map.contains_key(&method_name.value.symbol()) {
                method_order.push(method_name.value.symbol());
            }
            method_map.entry(method_name.value.symbol()).or_default().push(member);
        }
    }

    let mut fields = Vec::new();
    for method_sym in &method_order {
        let decls = &method_map[method_sym];
        let method_js = ident_to_js(*method_sym);
        // Reset fresh counter for each instance method (original compiler does this)
        ctx.fresh_counter.set(0);

        // Check if this method has its own constraints (e.g., `discard :: Bind f => ...`)
        let method_vqi = unqualified_value_sym(*method_sym);
        let method_constraints: Vec<Symbol> = ctx.exports.method_own_constraints
            .get(&method_vqi)
            .map(|cs| cs.iter().map(|c| c.symbol()).collect())
            .or_else(|| {
                // Also check registry for imported class methods
                for (_, mod_exports) in ctx.registry.iter_all() {
                    if let Some(c) = mod_exports.method_own_constraints.get(&method_vqi) {
                        return Some(c.iter().map(|cn| cn.symbol()).collect());
                    }
                }
                None
            })
            .unwrap_or_default();

        // Push method-own-constraint dicts into scope
        let prev_scope_len_method = ctx.dict_scope.borrow().len();
        let mut method_dict_params: Vec<String> = Vec::new();
        if !method_constraints.is_empty() {
            let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
            for class_sym in &method_constraints {
                let class_name_str = interner::resolve(*class_sym).unwrap_or_default();
                let is_runtime = ctx.known_runtime_classes.contains(class_sym);
                if is_runtime {
                    let count = dict_name_counts.entry(class_name_str.to_string()).or_insert(0);
                    let dict_param = if *count == 0 {
                        format!("dict{class_name_str}")
                    } else {
                        format!("dict{class_name_str}{count}")
                    };
                    *count += 1;
                    ctx.dict_scope.borrow_mut().push((*class_sym, dict_param.clone()));
                    method_dict_params.push(dict_param);
                }
            }
        }

        let method_expr = if decls.len() == 1 {
            if let Decl::Value { binders, guarded, where_clause, .. } = decls[0] {
                if binders.is_empty() && where_clause.is_empty() {
                    gen_guarded_expr(ctx, guarded)
                } else if where_clause.is_empty() {
                    // Pre-allocate param names before generating body,
                    // so param names get the lowest fresh counter values (v, v1, v2...)
                    let pre_params = pre_allocate_param_names(ctx, binders);
                    let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                    gen_curried_function_with_params(ctx, binders, body_stmts, &pre_params)
                } else {
                    let mut iife_body = Vec::new();
                    gen_let_bindings(ctx, where_clause, &mut iife_body);
                    // Reorder where-clause bindings
                    if !iife_body.is_empty() {
                        reorder_where_bindings(&mut iife_body);
                    }
                    if binders.is_empty() {
                        let expr = gen_guarded_expr(ctx, guarded);
                        iife_body.push(JsStmt::Return(expr));
                        JsExpr::App(
                            Box::new(JsExpr::Function(None, vec![], iife_body)),
                            vec![],
                        )
                    } else {
                        // Pre-allocate param names before generating body
                        let pre_params = pre_allocate_param_names(ctx, binders);
                        let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                        iife_body.extend(body_stmts);
                        // Inline trivial aliases from where-bindings
                        inline_trivial_aliases(&mut iife_body);
                        gen_curried_function_with_params(ctx, binders, iife_body, &pre_params)
                    }
                }
            } else {
                JsExpr::Var("undefined".to_string())
            }
        } else {
            // Multi-equation method: compile like a multi-equation function
            let multi_stmts = gen_multi_equation(ctx, &method_js, decls);
            // Extract the expression from the generated VarDecl
            if let Some(JsStmt::VarDecl(_, Some(expr))) = multi_stmts.into_iter().next() {
                expr
            } else {
                JsExpr::Var("undefined".to_string())
            }
        };

        // Pop method-own-constraint dicts
        ctx.dict_scope.borrow_mut().truncate(prev_scope_len_method);

        // Wrap method expression with lambdas for method-own constraints
        let method_expr = if !method_dict_params.is_empty() {
            let mut wrapped = method_expr;
            // Wrap inside-out (last constraint is innermost)
            for param in method_dict_params.iter().rev() {
                wrapped = JsExpr::Function(
                    None,
                    vec![param.clone()],
                    vec![JsStmt::Return(wrapped)],
                );
            }
            wrapped
        } else {
            method_expr
        };

        // Use original PS name for object key (e.g. "genericBottom'" not "genericBottom$prime")
        let method_key = interner::resolve(*method_sym).unwrap_or_default().to_string();
        fields.push((method_key, method_expr));
    }

    // Add superclass accessor fields
    // For `class (Super1 m, Super2 m) <= MyClass m`, instance dicts need:
    //   Super10: function() { return super1Instance; },
    //   Super21: function() { return super2Instance; },
    gen_superclass_accessors(ctx, class_name.name.symbol(), types, constraints, &mut fields);

    let mut obj: JsExpr = JsExpr::ObjectLit(fields);

    // If the instance has constraints, wrap in curried functions taking dict params
    // and hoist dict method applications into the function body.
    // Type-level constraints (RowToList, Cons, Nub, etc.) get function() with no param.
    if !constraints.is_empty() {
        let dict_params = constraint_dict_params(constraints);

        // Step 1: Build constraint wrapping WITHOUT hoisting (inside-out).
        for ci in (0..constraints.len()).rev() {
            let is_runtime = ctx.known_runtime_classes.contains(&constraints[ci].class.name.symbol());
            if is_runtime {
                let dict_param = &dict_params[ci];
                obj = JsExpr::Function(
                    None,
                    vec![dict_param.clone()],
                    vec![JsStmt::Return(obj)],
                );
            } else {
                obj = JsExpr::Function(None, vec![], vec![JsStmt::Return(obj)]);
            }
        }

        // Step 2: Top-down hoisting pass — walk outer-to-inner so outer scopes
        // get lower numbered names (e.g., bare → 1 → 2).
        let mut shared_counter: HashMap<String, usize> = HashMap::new();
        let mut base_names: HashMap<String, String> = HashMap::new();
        let mut bare_names: HashSet<String> = HashSet::new();
        let empty_reserved: HashSet<String> = HashSet::new();
        hoist_dict_apps_top_down(&mut obj, &mut shared_counter, &mut base_names, &mut bare_names, Some(&instance_name), &empty_reserved);
    }

    // Pop dict scope
    ctx.dict_scope.borrow_mut().truncate(prev_scope_len);

    // Wrap non-function instances in IIFE if they reference constructors
    if !matches!(obj, JsExpr::Function(_, _, _)) && references_constructor(&obj) {
        let iife = JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], vec![JsStmt::Return(obj)])),
            vec![],
        );
        vec![JsStmt::VarDecl(instance_name, Some(iife))]
    } else {
        vec![JsStmt::VarDecl(instance_name, Some(obj))]
    }
}


pub(crate) fn contains_wildcard(expr: &Expr) -> bool {
    match expr {
        Expr::Wildcard { .. } => true,
        Expr::If { cond, then_expr, else_expr, .. } => {
            contains_wildcard(cond) || contains_wildcard(then_expr) || contains_wildcard(else_expr)
        }
        Expr::Case { exprs, .. } => exprs.iter().any(|e| contains_wildcard(e)),
        Expr::App { func, arg, .. } => contains_wildcard(func) || contains_wildcard(arg),
        Expr::Op { left, right, .. } => contains_wildcard(left) || contains_wildcard(right),
        Expr::Record { fields, .. } => fields.iter().any(|f| f.value.as_ref().map_or(false, |v| contains_wildcard(v))),
        Expr::Parens { expr, .. } => contains_wildcard(expr),
        Expr::TypeAnnotation { expr, .. } => contains_wildcard(expr),
        Expr::RecordAccess { expr, .. } => contains_wildcard(expr),
        Expr::Negate { expr, .. } => contains_wildcard(expr),
        Expr::Array { elements, .. } => elements.iter().any(|e| contains_wildcard(e)),
        Expr::RecordUpdate { expr, updates, .. } => {
            contains_wildcard(expr) || updates.iter().any(|u| contains_wildcard(&u.value))
        }
        Expr::BacktickApp { func, left, right, .. } => {
            contains_wildcard(func) || contains_wildcard(left) || contains_wildcard(right)
        }
        _ => false,
    }
}

/// Extract the head variable name and span from an expression, counting application depth.
/// For `App(App(Var(f, span_f), a), b)`, returns (Some(f), Some(span_f), 2).
/// For `Var(f, span_f)`, returns (Some(f), Some(span_f), 0).
/// For anything that isn't a chain of Apps ending in a Var, returns (None, None, 0).
pub(crate) fn extract_app_head_and_depth(expr: &Expr) -> (Option<Symbol>, Option<crate::span::Span>, usize) {
    match expr {
        Expr::Var { name, span, .. } => (Some(name.name.symbol()), Some(*span), 0),
        Expr::App { func, .. } => {
            let (head, head_span, depth) = extract_app_head_and_depth(func);
            (head, head_span, depth + 1)
        }
        Expr::VisibleTypeApp { func, .. } => {
            // Type apps are erased; don't count them but pass through
            extract_app_head_and_depth(func)
        }
        _ => (None, None, 0),
    }
}

pub(crate) fn gen_expr(ctx: &CodegenCtx, expr: &Expr) -> JsExpr {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || gen_expr_impl(ctx, expr))
}

fn gen_expr_impl(ctx: &CodegenCtx, expr: &Expr) -> JsExpr {
    // Handle wildcard sections: expressions containing Expr::Wildcard are
    // "anonymous function sections" — each wildcard becomes a parameter.
    if contains_wildcard(expr) && !matches!(expr, Expr::Wildcard { .. }) {
        // Save and clear wildcard params
        let saved = ctx.wildcard_params.replace(Vec::new());
        let body = gen_expr_inner(ctx, expr);
        let params = ctx.wildcard_params.replace(saved);
        // Wrap in curried lambdas
        let mut result = body;
        for param in params.into_iter().rev() {
            result = JsExpr::Function(None, vec![param], vec![JsStmt::Return(result)]);
        }
        return result;
    }
    gen_expr_inner(ctx, expr)
}

pub(crate) fn gen_expr_inner(ctx: &CodegenCtx, expr: &Expr) -> JsExpr {
    match expr {
        Expr::Var { span, name, .. } => {
            // Debug: log dict miss for class methods and constrained functions at module level
            let result = gen_qualified_ref_with_span(ctx, name.module.map(|m| m.symbol()), name.name.symbol(), Some(*span));
            // Check if this is a constrained higher-rank parameter that needs eta-expansion
            if name.module.is_none() {
                if let Some(dict_name) = ctx.constrained_hr_params.borrow().get(&name.name.symbol()) {
                    // Only wrap if the variable is NOT in call position (handled by caller)
                    // Wrap: `f` → `function(dictClass) { return f(dictClass); }`
                    return JsExpr::Function(
                        None,
                        vec![dict_name.clone()],
                        vec![JsStmt::Return(JsExpr::App(
                            Box::new(result),
                            vec![JsExpr::Var(dict_name.clone())],
                        ))],
                    );
                }
            }
            // When discharging Partial (inside unsafePartial arg), auto-call
            // Partial-wrapped LOCAL functions with () to strip the dictPartial layer.
            // Cross-module Partial functions are handled in gen_qualified_ref_with_span.
            if ctx.discharging_partial.get() && ctx.partial_fns.contains(&name.name.symbol())
                && ctx.local_names.contains(&name.name.symbol())
            {
                return JsExpr::App(Box::new(result), vec![]);
            }
            result
        }

        Expr::Constructor { name, .. } => {
            let ctor_name = name.name.symbol();
            let ctor_module = name.module.map(|m| m.symbol());
            // Check newtype first — newtype constructors are identity functions
            if ctx.newtype_names.contains(&TypeName::new(ctor_name)) {
                gen_qualified_ref_raw(ctx, ctor_module, ctor_name)
            } else if let Some((_, _, fields)) = ctx.ctor_details.get(&unqualified_ctor_sym(ctor_name)) {
                if fields.is_empty() {
                    // Nullary: Ctor.value
                    let base = gen_qualified_ref_raw(ctx, ctor_module, ctor_name);
                    JsExpr::Indexer(
                        Box::new(base),
                        Box::new(JsExpr::StringLit("value".to_string())),
                    )
                } else {
                    // N-ary: Ctor.create
                    let base = gen_qualified_ref_raw(ctx, ctor_module, ctor_name);
                    JsExpr::Indexer(
                        Box::new(base),
                        Box::new(JsExpr::StringLit("create".to_string())),
                    )
                }
            } else {
                // Try looking up in imported modules' ctor_details
                let imported_ctor = ctx.name_source.get(&ctor_name).and_then(|parts| {
                    ctx.registry.lookup(parts).and_then(|mod_exports| {
                        mod_exports.ctor_details.get(&unqualified_ctor_sym(ctor_name))
                    })
                });
                if let Some((_, _, fields)) = imported_ctor {
                    let base = gen_qualified_ref_raw(ctx, ctor_module, ctor_name);
                    if fields.is_empty() {
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
                } else {
                    // Unknown constructor — default to .create as safe fallback
                    let base = gen_qualified_ref_raw(ctx, ctor_module, ctor_name);
                    JsExpr::Indexer(
                        Box::new(base),
                        Box::new(JsExpr::StringLit("create".to_string())),
                    )
                }
            }
        }

        Expr::Literal { lit, .. } => gen_literal(ctx, lit),

        Expr::App { func, arg, span, .. } => {
            // Detect record update syntax: expr { field = value, ... }
            // The parser produces App(expr, Record { is_update=true }) for record updates.
            if let Expr::Record { fields, .. } = arg.as_ref() {
                if !fields.is_empty() && fields.iter().all(|f| f.is_update && f.value.is_some()) {
                    let updates: Vec<RecordUpdate> = fields
                        .iter()
                        .filter_map(|f| {
                            Some(RecordUpdate {
                                span: f.span,
                                label: f.label.clone(),
                                value: f.value.clone()?,
                            })
                        })
                        .collect();
                    if !updates.is_empty() {
                        // If func is App, peel it: record update binds to rightmost atom.
                        // `f x { a = 1 }` means `f (x { a = 1 })`
                        if let Expr::App { func: outer_func, arg: inner_arg, .. } = func.as_ref() {
                            let updated = gen_record_update(ctx, *span, inner_arg, &updates);
                            let f = gen_expr(ctx, outer_func);
                            return JsExpr::App(Box::new(f), vec![updated]);
                        }
                        return gen_record_update(ctx, *span, func, &updates);
                    }
                }
            }
            // Newtype constructor application is identity — just emit the argument
            if let Expr::Constructor { name, .. } = func.as_ref() {
                if ctx.newtype_names.contains(&TypeName::new(name.name.symbol())) {
                    return gen_expr(ctx, arg);
                }
            }
            // Detect unsafePartial calls: enable Partial discharge mode for the argument.
            // In the original compiler, unsafePartial(expr) strips the dictPartial layer
            // from Partial-constrained values within expr by calling them with ().
            if is_unsafe_partial_call(func) {
                let prev = ctx.discharging_partial.get();
                ctx.discharging_partial.set(true);
                let a = gen_expr(ctx, arg);
                ctx.discharging_partial.set(prev);
                // unsafePartial is identity at runtime — just return the arg
                return a;
            }
            let f = gen_expr(ctx, func);
            let a = gen_expr(ctx, arg);
            let mut result = JsExpr::App(Box::new(f), vec![a]);
            // Check if this application completes the arrow depth for a return-type-constrained function.
            // After applying enough explicit args, insert the return-type dict application.
            // app_depth counts how many Apps are in `func` already; +1 for this App.
            let (head_name, head_span, app_depth) = extract_app_head_and_depth(func);
            if let Some(head_sym) = head_name {
                let depth_key = unqualified_value_sym(head_sym);
                if let Some(&arrow_depth) = ctx.exports.return_type_arrow_depth.get(&depth_key) {
                    if app_depth + 1 == arrow_depth {
                        // Insert return-type dicts at this point
                        if let Some(dicts) = head_span.and_then(|s| ctx.resolved_dict_map.get(&s)) {
                            let rt_class_names: Vec<Symbol> = ctx.exports.return_type_constraints
                                .get(&depth_key)
                                .map(|cs| cs.iter().map(|(c, _)| c.name_symbol()).collect())
                                .unwrap_or_default();
                            for class_name in &rt_class_names {
                                if let Some((_, dict_expr)) = dicts.iter().find(|(cn, _)| cn == class_name) {
                                    if !matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                                        let js_dict = dict_expr_to_js(ctx, dict_expr);
                                        result = JsExpr::App(Box::new(result), vec![js_dict]);
                                    }
                                } else {
                                    // Try scope-based dict resolution for parametric cases
                                    let scope = ctx.dict_scope.borrow();
                                    if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, *class_name) {
                                        result = JsExpr::App(Box::new(result), vec![dict_expr]);
                                    }
                                }
                            }
                        } else {
                            // No resolved dicts at head span — try scope-based resolution
                            let rt_class_names: Vec<Symbol> = ctx.exports.return_type_constraints
                                .get(&depth_key)
                                .map(|cs| cs.iter().map(|(c, _)| c.name_symbol()).collect())
                                .unwrap_or_default();
                            let scope = ctx.dict_scope.borrow();
                            for class_name in &rt_class_names {
                                if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, *class_name) {
                                    result = JsExpr::App(Box::new(result), vec![dict_expr]);
                                }
                            }
                        }
                    }
                }
            }
            result
        }

        Expr::VisibleTypeApp { span, func, .. } => {
            // Type applications are erased at runtime, but constraints deferred
            // at the VTA span may need dict application (e.g. `reflect @"asdf"`
            // needs the Reflectable dict applied).
            let base = gen_expr(ctx, func);
            if let Some(dicts) = ctx.resolved_dict_map.get(span) {
                let mut result = base;
                for (_class_name, dict_expr) in dicts {
                    if matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                        result = JsExpr::App(Box::new(result), vec![]);
                    } else {
                        let js_dict = dict_expr_to_js(ctx, dict_expr);
                        result = JsExpr::App(Box::new(result), vec![js_dict]);
                    }
                }
                result
            } else {
                base
            }
        }

        Expr::Lambda { binders, body, .. } => {
            // Register binder names as local bindings before generating body
            let prev_bindings = ctx.local_bindings.borrow().clone();
            for b in binders.iter() {
                collect_binder_names(b, &mut ctx.local_bindings.borrow_mut());
            }
            let body_stmts = gen_return_stmts(ctx, body);
            *ctx.local_bindings.borrow_mut() = prev_bindings;
            gen_curried_function(ctx, binders, body_stmts)
        }

        Expr::Op { span, left, op, right } => {
            gen_op_chain(ctx, left, op, right, *span)
        }

        Expr::OpParens { span, op } => {
            // Inline $ and # operators: ($) → function(f) { return function(x) { return f(x); }; }
            let op_str = interner::resolve(op.value.name.symbol()).unwrap_or_default();
            if op_str == "$" {
                return JsExpr::Function(
                    None,
                    vec!["f".to_string()],
                    vec![JsStmt::Return(JsExpr::Function(
                        None,
                        vec!["x".to_string()],
                        vec![JsStmt::Return(JsExpr::App(
                            Box::new(JsExpr::Var("f".to_string())),
                            vec![JsExpr::Var("x".to_string())],
                        ))],
                    ))],
                );
            }
            if op_str == "#" {
                return JsExpr::Function(
                    None,
                    vec!["x".to_string()],
                    vec![JsStmt::Return(JsExpr::Function(
                        None,
                        vec!["f".to_string()],
                        vec![JsStmt::Return(JsExpr::App(
                            Box::new(JsExpr::Var("f".to_string())),
                            vec![JsExpr::Var("x".to_string())],
                        ))],
                    ))],
                );
            }
            // Other operators: resolve to target function
            resolve_op_ref(ctx, op, Some(*span))
        }

        Expr::If { cond, then_expr, else_expr, .. } => {
            let c = gen_expr(ctx, cond);
            let t = gen_expr(ctx, then_expr);
            let e = gen_expr(ctx, else_expr);
            JsExpr::Ternary(Box::new(c), Box::new(t), Box::new(e))
        }

        Expr::Case { exprs, alts, .. } => gen_case_expr(ctx, exprs, alts),

        Expr::Let { bindings, body, .. } => {
            // Register let binding names as local before generating
            let prev_bindings = ctx.local_bindings.borrow().clone();
            for lb in bindings.iter() {
                match lb {
                    LetBinding::Value { binder, .. } => {
                        collect_binder_names(binder, &mut ctx.local_bindings.borrow_mut());
                    }
                    _ => {}
                }
            }
            let mut iife_body = Vec::new();
            gen_let_bindings(ctx, bindings, &mut iife_body);
            if !iife_body.is_empty() {
                reorder_where_bindings(&mut iife_body);
            }
            let body_expr = gen_expr(ctx, body);
            *ctx.local_bindings.borrow_mut() = prev_bindings;
            iife_body.push(JsStmt::Return(body_expr));
            JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            )
        }

        Expr::Do { span, statements, module: qual_mod } => {
            let qual_sym = qual_mod.map(|m| m.symbol());
            gen_do_expr(ctx, *span, statements, qual_sym.as_ref())
        }

        Expr::Ado { span, statements, result, module: qual_mod } => {
            let qual_sym = qual_mod.map(|m| m.symbol());
            gen_ado_expr(ctx, *span, statements, result, qual_sym.as_ref())
        }

        Expr::Record { fields, .. } => {
            let js_fields: Vec<(String, JsExpr)> = fields
                .iter()
                .map(|f| {
                    let label = interner::resolve(f.label.value.symbol()).unwrap_or_default();
                    let value = match &f.value {
                        Some(v) => gen_expr(ctx, v),
                        None => {
                            // Punned field: { x } means { x: x }
                            JsExpr::Var(ident_to_js(f.label.value.symbol()))
                        }
                    };
                    (label, value)
                })
                .collect();
            JsExpr::ObjectLit(js_fields)
        }

        Expr::RecordAccess { expr, field, .. } => {
            let obj = gen_expr_inner(ctx, expr);
            let label = interner::resolve(field.value.symbol()).unwrap_or_default();
            JsExpr::Indexer(Box::new(obj), Box::new(JsExpr::StringLit(label)))
        }

        Expr::RecordUpdate { span, expr, updates } => {
            gen_record_update(ctx, *span, expr, updates)
        }

        Expr::Parens { expr, .. } => gen_expr(ctx, expr),

        Expr::TypeAnnotation { expr, .. } => gen_expr(ctx, expr),

        Expr::Hole { name, .. } => {
            // Holes should have been caught by the typechecker, but emit an error at runtime
            let hole_name = interner::resolve(name.symbol()).unwrap_or_default();
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
            // For integer literal negation, use `-n | 0` to match the original compiler's
            // Int32 coercion convention
            if matches!(&e, JsExpr::IntLit(_)) {
                JsExpr::Binary(
                    JsBinaryOp::BitwiseOr,
                    Box::new(JsExpr::Unary(JsUnaryOp::Negate, Box::new(e))),
                    Box::new(JsExpr::IntLit(0)),
                )
            } else {
                JsExpr::Unary(JsUnaryOp::Negate, Box::new(e))
            }
        }

        Expr::AsPattern { name, .. } => {
            // This shouldn't appear in expression position normally
            gen_expr(ctx, name)
        }

        Expr::Wildcard { .. } => {
            let name = ctx.fresh_name("__");
            ctx.wildcard_params.borrow_mut().push(name.clone());
            JsExpr::Var(name)
        }

        Expr::BacktickApp { func, left, right, .. } => {
            let f = gen_expr(ctx, func);
            let l = gen_expr(ctx, left);
            let r = gen_expr(ctx, right);
            JsExpr::App(Box::new(JsExpr::App(Box::new(f), vec![l])), vec![r])
        }
    }
}

pub(crate) fn gen_literal(ctx: &CodegenCtx, lit: &Literal) -> JsExpr {
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

pub(crate) fn gen_qualified_ref_with_span(ctx: &CodegenCtx, module: Option<Symbol>, name: Symbol, span: Option<crate::span::Span>) -> JsExpr {
    // Check if it's a foreign import in the current module
    if module.is_none() && ctx.foreign_imports.contains(&name) {
        let original_name = interner::resolve(name).unwrap_or_default();
        return JsExpr::ModuleAccessor("$foreign".to_string(), original_name);
    }

    let base = gen_qualified_ref_raw(ctx, module, name);

    // Local bindings (lambda params, let/where bindings, case binders) are never class methods
    // or constrained functions — skip all dict application for them. This prevents a local
    // binding like `append = \o -> ...` from getting the Prelude `append`'s Semigroup dict.
    if module.is_none() && ctx.local_bindings.borrow().contains(&name) {
        if !ctx.local_constrained_bindings.borrow().contains(&name) {
            return base;
        }
    }

    // Module-level names that shadow imported class methods/constrained functions
    // should not get dict application unless they have their own constraints.
    // E.g., local `append = \o -> ...` (in Objects test) shadows Prelude's `append`.
    if module.is_none() && ctx.local_names.contains(&name) {
        let has_own_constraints = ctx.exports.signature_constraints.contains_key(&unqualified_value_sym(name))
            || ctx.exports.return_type_constraints.contains_key(&unqualified_value_sym(name));
        let is_own_class_method = ctx.exports.class_methods.contains_key(&unqualified_value_sym(name));
        if !has_own_constraints && !is_own_class_method {
            return base;
        }
    }

    // If this is a class method and we have a matching dict in scope, apply it
    if let Some(dict_app) = try_apply_dict(ctx, name, base.clone(), span) {
        return dict_app;
    }

    // Fallback: if the function has constraints that are ALL zero-cost (e.g. Coercible),
    // strip each phantom wrapper with an empty `()` call. This handles both:
    // 1. Module-level concrete calls where resolved_dict_map has ZeroCost entries
    // 2. Polymorphic calls inside constrained functions where scope has no entry
    //    (because zero-cost constraints are not pushed to dict_scope)
    {
        let fn_constraints = ctx.all_fn_constraints.borrow().get(&name).cloned().unwrap_or_default();
        if !fn_constraints.is_empty() && fn_constraints.iter().all(|c| !ctx.known_runtime_classes.contains(c)) {
            let mut result = base;
            for _ in &fn_constraints {
                result = JsExpr::App(Box::new(result), vec![]);
            }
            return result;
        }
    }

    // Partial-constrained functions have a $dictPartial wrapper that needs ()
    // at call sites. This is tracked separately from signature_constraints
    // because Partial is auto-satisfied and excluded from constraint resolution.
    if ctx.partial_fns.contains(&name) {
        return JsExpr::App(Box::new(base), vec![]);
    }

    base
}

/// If `name` is a class method or constrained function and we have matching dicts in scope,
/// return the expression with dict args applied.

// ===== Guarded expressions =====

pub(crate) fn gen_guarded_expr(ctx: &CodegenCtx, guarded: &GuardedExpr) -> JsExpr {
    match guarded {
        GuardedExpr::Unconditional(expr) => gen_expr(ctx, expr),
        GuardedExpr::Guarded(guards) => {
            // Convert guards into nested ternaries
            gen_guards_expr(ctx, guards)
        }
    }
}

pub(crate) fn gen_guarded_expr_stmts(ctx: &CodegenCtx, guarded: &GuardedExpr) -> Vec<JsStmt> {
    match guarded {
        GuardedExpr::Unconditional(expr) => gen_return_stmts(ctx, expr),
        GuardedExpr::Guarded(guards) => gen_guards_stmts(ctx, guards),
    }
}

/// Generate return statements for an expression. For case expressions, this
/// inlines the if/instanceof chains directly instead of wrapping in an IIFE.
pub(crate) fn gen_return_stmts(ctx: &CodegenCtx, expr: &Expr) -> Vec<JsStmt> {
    match expr {
        Expr::Case { exprs, alts, .. } => {
            // If case scrutinees contain wildcards (section syntax like `case _, x, _ of`),
            // don't inline as statements — fall through to gen_expr which handles wrapping
            if exprs.iter().any(|e| contains_wildcard(e)) {
                vec![JsStmt::Return(gen_expr(ctx, expr))]
            } else {
                gen_case_stmts(ctx, exprs, alts)
            }
        }
        Expr::Let { bindings, body, .. } => {
            // Inline let bindings in tail position instead of wrapping in IIFE
            let prev_bindings = ctx.local_bindings.borrow().clone();
            for lb in bindings.iter() {
                if let LetBinding::Value { binder, .. } = lb {
                    collect_binder_names(binder, &mut ctx.local_bindings.borrow_mut());
                }
            }
            let mut stmts = Vec::new();
            gen_let_bindings(ctx, bindings, &mut stmts);
            if !stmts.is_empty() {
                reorder_where_bindings(&mut stmts);
            }
            stmts.extend(gen_return_stmts(ctx, body));
            // Inline trivial aliases (e.g., where-bindings that are just type annotations
            // on imported names: `unsafeGet' = unsafeGet :: ...` → use unsafeGet directly)
            inline_trivial_aliases(&mut stmts);
            *ctx.local_bindings.borrow_mut() = prev_bindings;
            stmts
        }
        Expr::Parens { expr, .. } => gen_return_stmts(ctx, expr),
        Expr::If { cond, then_expr, else_expr, .. } => {
            // if-then-else in return position: if (cond) { return then; }; return else;
            let cond_js = gen_expr(ctx, cond);
            let then_stmts = gen_return_stmts(ctx, then_expr);
            let else_stmts = gen_return_stmts(ctx, else_expr);
            let mut stmts = Vec::new();
            stmts.push(JsStmt::If(cond_js, then_stmts, None));
            stmts.extend(else_stmts);
            stmts
        }
        _ => vec![JsStmt::Return(gen_expr(ctx, expr))],
    }
}

/// Generate case expression as a series of if-statements (not an IIFE).
/// Used when the case is in tail position (returned from a function).
pub(crate) fn gen_case_stmts(ctx: &CodegenCtx, scrutinees: &[Expr], alts: &[CaseAlternative]) -> Vec<JsStmt> {
    let scrut_exprs: Vec<JsExpr> = scrutinees.iter().map(|e| gen_expr(ctx, e)).collect();

    // If scrutinees are simple variables, use them directly; otherwise bind to temps
    let mut stmts = Vec::new();
    // Check if all alternatives use wildcard binders for a given scrutinee position —
    // if so, that scrutinee is never actually inspected and we can skip binding it.
    let scrut_names: Vec<String> = scrut_exprs.iter().enumerate().map(|(i, e)| {
        if let JsExpr::Var(name) = e {
            name.clone()
        } else {
            // Check if this scrutinee is actually used by any binder
            let all_wildcard = alts.iter().all(|alt| {
                alt.binders.get(i).map_or(true, |b| matches!(b, Binder::Wildcard { .. }))
            });
            if all_wildcard {
                // Never used — skip binding, use a dummy name
                format!("__unused_{i}")
            } else {
                let name = ctx.fresh_name("v");
                stmts.push(JsStmt::VarDecl(name.clone(), Some(e.clone())));
                name
            }
        }
    }).collect();

    let mut has_unconditional = false;
    for alt in alts {
        let (cond, bindings) = gen_binders_match(ctx, &alt.binders, &scrut_names);
        let mut alt_body = Vec::new();
        alt_body.extend(bindings);

        // Check if this alt is truly unconditional (no binder condition AND no guards)
        let is_guarded = matches!(&alt.result, GuardedExpr::Guarded(_));

        let result_stmts = gen_guarded_expr_stmts(ctx, &alt.result);
        alt_body.extend(result_stmts);
        // Inline binding-then-return: var x = <expr>; return x; → return <expr>;
        inline_single_use_bindings(&mut alt_body);

        if let Some(cond) = cond {
            stmts.push(JsStmt::If(cond, alt_body, None));
        } else if is_guarded {
            // Wildcard binder but guarded result — guards may not match,
            // so emit guard stmts (without trailing throw) and continue to next alt
            // Remove the trailing throw since we'll fall through to the next alternative
            if let Some(JsStmt::Throw(_)) = alt_body.last() {
                alt_body.pop();
            }
            stmts.extend(alt_body);
        } else {
            stmts.extend(alt_body);
            has_unconditional = true;
            break;
        }
    }

    if !has_unconditional {
        stmts.push(JsStmt::Throw(JsExpr::New(
            Box::new(JsExpr::Var("Error".to_string())),
            vec![JsExpr::StringLit("Failed pattern match".to_string())],
        )));
    }

    stmts
}

pub(crate) fn gen_guards_expr(ctx: &CodegenCtx, guards: &[Guard]) -> JsExpr {
    // Build nested ternary: cond1 ? e1 : cond2 ? e2 : error
    let mut result = JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    );

    for guard in guards.iter().rev() {
        let (cond, pre_stmts, guard_bindings) = gen_guard_condition(ctx, &guard.patterns);
        let body = gen_expr(ctx, &guard.expr);
        if !pre_stmts.is_empty() || !guard_bindings.is_empty() {
            // Pattern guard with bindings: use IIFE to scope the bindings
            let mut iife_body = pre_stmts;
            let mut if_body = guard_bindings;
            if_body.push(JsStmt::Return(body));
            iife_body.push(JsStmt::If(
                cond,
                if_body,
                None,
            ));
            iife_body.push(JsStmt::Return(result.clone()));
            result = JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            );
        } else {
            result = JsExpr::Ternary(Box::new(cond), Box::new(body), Box::new(result));
        }
    }

    result
}

pub(crate) fn gen_guards_stmts(ctx: &CodegenCtx, guards: &[Guard]) -> Vec<JsStmt> {
    let mut stmts = Vec::new();
    for guard in guards {
        let (cond, pre_stmts, guard_bindings) = gen_guard_condition(ctx, &guard.patterns);
        // Use gen_return_stmts to inline let-expressions in guard bodies
        let body_stmts = gen_return_stmts(ctx, &guard.expr);
        // Emit pre-statements (pattern guard temp vars) before the condition check
        stmts.extend(pre_stmts);
        // If guard condition is `true` (i.e. `| otherwise`), emit body directly
        if matches!(&cond, JsExpr::BoolLit(true)) {
            stmts.extend(guard_bindings);
            stmts.extend(body_stmts);
            return stmts;
        }
        let mut if_body = guard_bindings;
        if_body.extend(body_stmts);
        stmts.push(JsStmt::If(
            cond,
            if_body,
            None,
        ));
    }
    stmts.push(JsStmt::Throw(JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )));
    stmts
}

/// Returns (condition, pre_statements, bindings) where:
/// - pre_statements: emitted BEFORE the if (e.g., `var $guard = expr`)
/// - bindings: emitted INSIDE the if-body (e.g., `var y = $guard.value0`)
pub(crate) fn gen_guard_condition(ctx: &CodegenCtx, patterns: &[GuardPattern]) -> (JsExpr, Vec<JsStmt>, Vec<JsStmt>) {
    let mut conditions: Vec<JsExpr> = Vec::new();
    let mut pre_stmts: Vec<JsStmt> = Vec::new();
    let mut bindings: Vec<JsStmt> = Vec::new();
    for pattern in patterns {
        match pattern {
            GuardPattern::Boolean(expr) => {
                conditions.push(gen_expr(ctx, expr));
            }
            GuardPattern::Pattern(binder, expr) => {
                // Pattern guard: `pat <- expr`
                // 1. Evaluate expr into a temp var (pre-statement)
                // 2. Generate pattern match condition
                // 3. Generate bindings (go into if-body)
                let temp = ctx.fresh_name("$guard");
                let expr_js = gen_expr(ctx, expr);
                pre_stmts.push(JsStmt::VarDecl(temp.clone(), Some(expr_js)));

                let scrutinee = JsExpr::Var(temp);
                let (cond, binder_bindings) = gen_binder_match(ctx, binder, &scrutinee);

                if let Some(c) = cond {
                    conditions.push(c);
                }
                bindings.extend(binder_bindings);
            }
        }
    }

    let cond = if conditions.len() == 1 {
        conditions.into_iter().next().unwrap()
    } else if conditions.is_empty() {
        JsExpr::BoolLit(true)
    } else {
        conditions
            .into_iter()
            .reduce(|a, b| JsExpr::Binary(JsBinaryOp::And, Box::new(a), Box::new(b)))
            .unwrap_or(JsExpr::BoolLit(true))
    };
    (cond, pre_stmts, bindings)
}

// ===== Curried functions =====

/// Pre-allocate parameter names for binders before generating the function body.
/// This ensures params get the lowest fresh counter values (v, v1, v2...).
pub(crate) fn pre_allocate_param_names(ctx: &CodegenCtx, binders: &[Binder]) -> Vec<Option<String>> {
    binders.iter().map(|b| {
        match b {
            Binder::Var { .. } => None,
            Binder::Wildcard { .. } => Some(ctx.fresh_name("v")),
            _ => Some(ctx.fresh_name("v")),
        }
    }).collect()
}

/// Like gen_curried_function but uses pre-allocated param names.
pub(crate) fn gen_curried_function_with_params(ctx: &CodegenCtx, binders: &[Binder], body: Vec<JsStmt>, param_names: &[Option<String>]) -> JsExpr {
    if binders.is_empty() {
        return JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], body)),
            vec![],
        );
    }
    build_curried_function_body(ctx, binders, body, param_names)
}

pub(crate) fn gen_curried_function(ctx: &CodegenCtx, binders: &[Binder], body: Vec<JsStmt>) -> JsExpr {
    if binders.is_empty() {
        // No binders: return IIFE
        return JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], body)),
            vec![],
        );
    }

    // Pre-generate param names in forward order so wildcards get v, v1, v2...
    let param_names = pre_allocate_param_names(ctx, binders);
    build_curried_function_body(ctx, binders, body, &param_names)
}

pub(crate) fn build_curried_function_body(ctx: &CodegenCtx, binders: &[Binder], body: Vec<JsStmt>, param_names: &[Option<String>]) -> JsExpr {

    // Build from inside out
    let mut current_body = body;

    for (i, binder) in binders.iter().enumerate().rev() {
        match binder {
            Binder::Var { name, .. } => {
                let param = ident_to_js(name.value.symbol());
                current_body = vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![param],
                    current_body,
                ))];
            }
            Binder::Wildcard { .. } => {
                let param = param_names[i].clone().unwrap();
                current_body = vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![param],
                    current_body,
                ))];
            }
            _ => {
                // Complex binder: introduce a parameter and pattern match
                let param = param_names[i].clone().unwrap();
                let mut match_body = Vec::new();
                let (cond, bindings) = gen_binder_match(ctx, binder, &JsExpr::Var(param.clone()));
                match_body.extend(bindings);

                if let Some(cond) = cond {
                    let then_body = current_body.clone();
                    match_body.push(JsStmt::If(cond, then_body, None));
                    match_body.push(JsStmt::Throw(JsExpr::New(
                        Box::new(JsExpr::Var("Error".to_string())),
                        vec![JsExpr::StringLit("Failed pattern match".to_string())],
                    )));
                } else {
                    match_body.extend(current_body.clone());
                }

                inline_single_use_bindings(&mut match_body);

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

pub(crate) fn gen_curried_function_from_stmts(
    ctx: &CodegenCtx,
    binders: &[Binder],
    body: Vec<JsStmt>,
) -> JsExpr {
    gen_curried_function(ctx, binders, body)
}

// ===== Let bindings =====

pub(crate) fn gen_let_bindings(ctx: &CodegenCtx, bindings: &[LetBinding], stmts: &mut Vec<JsStmt>) {
    // Group consecutive same-name Var bindings for multi-equation functions
    let mut i = 0;
    while i < bindings.len() {
        match &bindings[i] {
            LetBinding::Value { binder: Binder::Var { name, .. }, .. } => {
                let binding_name = name.value.symbol();
                // Collect all consecutive bindings with same name
                let start = i;
                i += 1;
                while i < bindings.len() {
                    if let LetBinding::Value { binder: Binder::Var { name: n2, .. }, .. } = &bindings[i] {
                        if n2.value.symbol() == binding_name {
                            i += 1;
                            continue;
                        }
                    }
                    // Also skip type signatures for the same name
                    if let LetBinding::Signature { name: n2, .. } = &bindings[i] {
                        if n2.value.symbol() == binding_name {
                            i += 1;
                            continue;
                        }
                    }
                    break;
                }

                // Check if this let-bound function has constraints (needs dict params)
                // Use span-keyed lookup to avoid name collisions between different let blocks
                let binding_span = if let LetBinding::Value { span, .. } = &bindings[start] {
                    Some(*span)
                } else {
                    None
                };
                let constraints = binding_span
                    .and_then(|span| ctx.exports.let_binding_constraints.get(&span))
                    .cloned();

                // Register local constrained function in all_fn_constraints so call sites
                // in the let body will pass dicts via try_apply_dict
                if let Some(ref constraints) = constraints {
                    if !constraints.is_empty() {
                        let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name_symbol()).collect();
                        ctx.all_fn_constraints.borrow_mut().insert(binding_name, class_names);
                        ctx.local_constrained_bindings.borrow_mut().insert(binding_name);
                    }
                }

                // Push dict scope entries for constraints (unique names for duplicate classes)
                let prev_scope_len = ctx.dict_scope.borrow().len();
                if let Some(ref constraints) = constraints {
                    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
                    for (class_qi, _) in constraints {
                        if !ctx.known_runtime_classes.contains(&class_qi.name_symbol()) {
                            continue; // Zero-cost constraint — no runtime dict param
                        }
                        let class_name_str = class_qi.name.resolve().unwrap_or_default();
                        let count = dict_name_counts.entry(class_name_str.to_string()).or_insert(0);
                        let dict_param = if *count == 0 {
                            format!("dict{class_name_str}")
                        } else {
                            format!("dict{class_name_str}{count}")
                        };
                        *count += 1;
                        ctx.dict_scope.borrow_mut().push((class_qi.name_symbol(), dict_param));
                    }
                }

                let group = &bindings[start..i];
                let js_name = ident_to_js(binding_name);


                if group.len() == 1 {
                    // Single equation — generate normally
                    if let LetBinding::Value { expr, .. } = &group[0] {
                        let mut val = gen_expr(ctx, expr);
                        val = wrap_with_dict_params_named(val, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name));
                        stmts.push(JsStmt::VarDecl(js_name, Some(val)));
                    }
                } else {
                    // Multi-equation: collect the lambda bodies and compile as case alternatives
                    let mut result = gen_multi_equation_let(ctx, &js_name, group);
                    if let Some(ref constraints) = constraints {
                        if !constraints.is_empty() {
                            if let Some(JsStmt::VarDecl(_, Some(expr))) = result.first_mut() {
                                *expr = wrap_with_dict_params_named(expr.clone(), Some(constraints), &ctx.known_runtime_classes, Some(&js_name));
                            }
                        }
                    }
                    stmts.extend(result);
                }

                // Pop dict scope
                ctx.dict_scope.borrow_mut().truncate(prev_scope_len);
            }
            LetBinding::Value { binder, expr, .. } => {
                // Non-var binder (pattern binding): destructure
                let val = gen_expr(ctx, expr);
                let tmp = ctx.fresh_name("v");
                stmts.push(JsStmt::VarDecl(tmp.clone(), Some(val)));
                let (_, pat_bindings) = gen_binder_match(ctx, binder, &JsExpr::Var(tmp));
                stmts.extend(pat_bindings);
                i += 1;
            }
            LetBinding::Signature { .. } => {
                // Type signatures produce no JS
                i += 1;
            }
        }
    }
    // Apply TCO to any tail-recursive let-bound functions
    apply_tco_if_applicable(stmts);

    // Apply $runtime_lazy wrapping for self-referential/mutually-recursive value bindings
    apply_runtime_lazy(ctx, stmts);
}

/// Detect and wrap self-referential or mutually-recursive non-function bindings
/// with `$runtime_lazy`. This handles cases like:
/// - `let selfOwn = { a: 1, b: force \_ -> selfOwn.a }` (self-referential)
/// - `let f = ... g ...; g = ... f ...` (mutually recursive non-functions)
pub(crate) fn apply_runtime_lazy(ctx: &CodegenCtx, stmts: &mut Vec<JsStmt>) {
    // Collect binding names and their init expressions
    let binding_names: Vec<Option<String>> = stmts.iter().map(|s| {
        if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
    }).collect();

    let name_set: HashSet<&str> = binding_names.iter()
        .filter_map(|n| n.as_deref())
        .collect();

    if name_set.is_empty() { return; }

    // For each binding, collect which other bindings it references
    let mut refs_map: Vec<HashSet<String>> = Vec::with_capacity(stmts.len());
    for stmt in stmts.iter() {
        let mut var_refs = HashSet::new();
        if let JsStmt::VarDecl(_, Some(init)) = stmt {
            collect_var_refs_in_expr(init, &mut var_refs);
        }
        // Only keep refs to other bindings in this block
        var_refs.retain(|r| name_set.contains(r.as_str()));
        refs_map.push(var_refs);
    }

    // Build name->index map for efficient lookup
    let name_to_idx: HashMap<&str, usize> = binding_names.iter().enumerate()
        .filter_map(|(i, n)| n.as_deref().map(|name| (name, i)))
        .collect();

    // Compute transitive reachability using Floyd-Warshall style transitive closure
    let n = stmts.len();
    let mut reachable = vec![vec![false; n]; n];
    for (i, refs) in refs_map.iter().enumerate() {
        for r in refs {
            if let Some(&j) = name_to_idx.get(r.as_str()) {
                reachable[i][j] = true;
            }
        }
    }
    // Transitive closure
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                if reachable[i][k] && reachable[k][j] {
                    reachable[i][j] = true;
                }
            }
        }
    }

    // A binding needs $runtime_lazy if:
    // 1. It's not a function (lambda) -- functions defer evaluation
    // 2. It references itself (directly or transitively through other bindings)
    let mut needs_lazy: Vec<bool> = vec![false; stmts.len()];

    for (i, stmt) in stmts.iter().enumerate() {
        if binding_names[i].is_none() { continue; }
        let init = match stmt {
            JsStmt::VarDecl(_, Some(init)) => init,
            _ => continue,
        };

        // Skip function bindings -- they don't evaluate eagerly
        if matches!(init, JsExpr::Function(..)) { continue; }

        // Skip constructor IIFEs
        if is_constructor_iife(stmt) { continue; }

        // Check if this binding can transitively reach itself (cycle)
        if reachable[i][i] {
            needs_lazy[i] = true;
        }
    }

    if !needs_lazy.iter().any(|&b| b) { return; }

    // Mark that we need the $runtime_lazy helper
    ctx.needs_runtime_lazy.set(true);

    // Build the lazy var names and replacement expressions
    let module_name = ctx.module_name;
    let mut lazy_names: HashMap<String, String> = HashMap::new();

    // First pass: collect which bindings need lazy and create their $lazy_ names
    for (i, &is_lazy) in needs_lazy.iter().enumerate() {
        if is_lazy {
            if let Some(ref name) = binding_names[i] {
                lazy_names.insert(name.clone(), format!("$lazy_{}", name));
            }
        }
    }

    // Second pass: build replacement stmts
    let mut non_lazy_stmts: Vec<JsStmt> = Vec::new();
    let mut lazy_decls: Vec<JsStmt> = Vec::new();
    let mut lazy_inits: Vec<JsStmt> = Vec::new();

    for (i, stmt) in stmts.drain(..).enumerate() {
        if needs_lazy[i] {
            if let JsStmt::VarDecl(name, Some(mut init)) = stmt {
                let lazy_name = lazy_names.get(&name).unwrap().clone();
                // Replace references to ALL lazy bindings within this init expression.
                for (orig, lazy) in &lazy_names {
                    let lazy_call = JsExpr::App(
                        Box::new(JsExpr::Var(lazy.clone())),
                        vec![],
                    );
                    substitute_var_with_expr_in_expr(&mut init, orig, &lazy_call);
                }

                // var $lazy_X = $runtime_lazy("X", "ModuleName", function() { return <init>; })
                lazy_decls.push(JsStmt::VarDecl(lazy_name.clone(), Some(JsExpr::App(
                    Box::new(JsExpr::Var("$runtime_lazy".to_string())),
                    vec![
                        JsExpr::StringLit(name.clone()),
                        JsExpr::StringLit(module_name.to_string()),
                        JsExpr::Function(None, vec![], vec![JsStmt::Return(init)]),
                    ],
                ))));

                // var X = $lazy_X(def_line)
                lazy_inits.push(JsStmt::VarDecl(name.clone(), Some(JsExpr::App(
                    Box::new(JsExpr::Var(lazy_name)),
                    vec![],
                ))));
            } else {
                non_lazy_stmts.push(stmt);
            }
        } else {
            // For non-lazy bindings, replace references to lazy bindings
            let mut stmt = stmt;
            if let JsStmt::VarDecl(ref binding_name, Some(ref mut init)) = stmt {
                for (orig, lazy) in &lazy_names {
                    if orig == binding_name { continue; }
                    let lazy_call = JsExpr::App(
                        Box::new(JsExpr::Var(lazy.clone())),
                        vec![],
                    );
                    substitute_var_with_expr_in_expr(init, orig, &lazy_call);
                }
            }
            non_lazy_stmts.push(stmt);
        }
    }

    // Assemble: non-lazy functions first, then lazy declarations, then lazy initializations
    let mut new_stmts: Vec<JsStmt> = Vec::with_capacity(
        non_lazy_stmts.len() + lazy_decls.len() + lazy_inits.len()
    );
    new_stmts.extend(non_lazy_stmts);
    new_stmts.extend(lazy_decls);
    new_stmts.extend(lazy_inits);

    *stmts = new_stmts;
}

/// Compile multi-equation let bindings into a single function.
/// Each binding has form `LetBinding::Value { binder: Var(name), expr: Lambda(...) | body }`.
/// The lambda bodies become case alternatives in a merged function.
pub(crate) fn gen_multi_equation_let(ctx: &CodegenCtx, js_name: &str, group: &[LetBinding]) -> Vec<JsStmt> {
    // Extract equations: unwrap lambda layers to get binders + body expr
    let mut equations: Vec<(Vec<Binder>, &Expr)> = Vec::new();

    for binding in group {
        if let LetBinding::Value { expr, .. } = binding {
            let mut binders = Vec::new();
            let mut current = expr;
            loop {
                match current {
                    Expr::Lambda { binders: lambda_binders, body, .. } => {
                        binders.extend(lambda_binders.iter().cloned());
                        current = body.as_ref();
                    }
                    _ => break,
                }
            }
            equations.push((binders, current));
        }
    }

    if equations.is_empty() {
        return vec![];
    }

    let arity = equations[0].0.len();
    if arity == 0 {
        // Zero-arity: just use first equation
        if let LetBinding::Value { expr, .. } = &group[0] {
            let val = gen_expr(ctx, expr);
            return vec![JsStmt::VarDecl(js_name.to_string(), Some(val))];
        }
        return vec![];
    }

    let params: Vec<String> = (0..arity).map(|_i| ctx.fresh_name("v")).collect();

    let mut body = Vec::new();
    for (binders, body_expr) in &equations {
        let (cond, bindings) = gen_binders_match(ctx, binders, &params);
        let mut alt_body = Vec::new();
        alt_body.extend(bindings);

        // Check if body is the guarded desugaring: Case(true, alts)
        // from the parser rule `f binders | guard = expr`
        if let Expr::Case { exprs, alts, .. } = body_expr {
            if exprs.len() == 1 {
                if let Expr::Literal { lit: Literal::Boolean(true), .. } = &exprs[0] {
                    // Guarded desugaring — emit each guard's alternatives inline
                    // WITHOUT a trailing throw (fallthrough to next equation)
                    for alt in alts {
                        match &alt.result {
                            GuardedExpr::Unconditional(expr) => {
                                alt_body.push(JsStmt::Return(gen_expr(ctx, expr)));
                            }
                            GuardedExpr::Guarded(guards) => {
                                // Emit guard conditions as if-return WITHOUT trailing throw
                                for guard in guards {
                                    let (guard_cond, pre_stmts, guard_bindings) = gen_guard_condition(ctx, &guard.patterns);
                                    let guard_body = gen_expr(ctx, &guard.expr);
                                    alt_body.extend(pre_stmts);
                                    let mut if_body = guard_bindings;
                                    if_body.push(JsStmt::Return(guard_body));
                                    alt_body.push(JsStmt::If(
                                        guard_cond,
                                        if_body,
                                        None,
                                    ));
                                }
                            }
                        }
                    }

                    if let Some(cond) = cond {
                        body.push(JsStmt::If(cond, alt_body, None));
                    } else {
                        body.extend(alt_body);
                    }
                    continue;
                }
            }
        }

        // Non-guarded: just return the body expression
        alt_body.push(JsStmt::Return(gen_expr(ctx, body_expr)));

        if let Some(cond) = cond {
            body.push(JsStmt::If(cond, alt_body, None));
        } else {
            body.extend(alt_body);
        }
    }

    body.push(JsStmt::Throw(JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
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

    if let Some(JsStmt::Return(func)) = result.into_iter().next() {
        vec![JsStmt::VarDecl(js_name.to_string(), Some(func))]
    } else {
        vec![]
    }
}

// ===== Case expressions =====

pub(crate) fn gen_case_expr(ctx: &CodegenCtx, scrutinees: &[Expr], alts: &[CaseAlternative]) -> JsExpr {
    // Introduce temp vars for scrutinees
    let scrut_names: Vec<String> = (0..scrutinees.len())
        .map(|_i| ctx.fresh_name("v"))
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

    iife_body.push(JsStmt::Throw(JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )));

    JsExpr::App(
        Box::new(JsExpr::Function(None, vec![], iife_body)),
        vec![],
    )
}

/// Collect all variable names bound by a binder pattern.
pub(crate) fn collect_binder_names(binder: &Binder, names: &mut HashSet<Symbol>) {
    match binder {
        Binder::Var { name, .. } => { names.insert(name.value.symbol()); }
        Binder::As { name, binder, .. } => {
            names.insert(name.value.symbol());
            collect_binder_names(binder, names);
        }
        Binder::Constructor { args, .. } => {
            for arg in args { collect_binder_names(arg, names); }
        }
        Binder::Array { elements, .. } => {
            for elem in elements { collect_binder_names(elem, names); }
        }
        Binder::Record { fields, .. } => {
            for field in fields {
                if let Some(ref b) = field.binder {
                    collect_binder_names(b, names);
                } else {
                    // Pun: { x } binds x
                    names.insert(field.label.value.symbol());
                }
            }
        }
        Binder::Typed { binder, .. } | Binder::Parens { binder, .. } => collect_binder_names(binder, names),
        Binder::Op { left, right, .. } => {
            collect_binder_names(left, names);
            collect_binder_names(right, names);
        }
        Binder::Literal { .. } | Binder::Wildcard { .. } => {}
    }
}

// ===== Pattern matching =====

/// Generate match conditions and variable bindings for a list of binders
/// against a list of scrutinee variable names.
pub(crate) fn gen_binders_match(
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
pub(crate) fn gen_binder_match(
    ctx: &CodegenCtx,
    binder: &Binder,
    scrutinee: &JsExpr,
) -> (Option<JsExpr>, Vec<JsStmt>) {
    match binder {
        Binder::Wildcard { .. } => (None, vec![]),

        Binder::Var { name, .. } => {
            let js_name = ident_to_js(name.value.symbol());
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
                Literal::Boolean(b) => if *b {
                    scrutinee.clone()
                } else {
                    JsExpr::Unary(JsUnaryOp::Not, Box::new(scrutinee.clone()))
                },
                Literal::Array(_) => {
                    // Array literal in binder — Binder::Array handles proper array patterns
                    JsExpr::BoolLit(true)
                }
            };
            (Some(cond), vec![])
        }

        Binder::Constructor { name, args, .. } => {
            let ctor_name = name.name.symbol();

            // Check if this is a newtype constructor (erased)
            if ctx.newtype_names.contains(&TypeName::new(ctor_name)) {
                if args.len() == 1 {
                    return gen_binder_match(ctx, &args[0], scrutinee);
                }
                return (None, vec![]);
            }

            let mut conditions = Vec::new();
            let mut bindings = Vec::new();

            // Determine if we need an instanceof check (sum types)
            let is_sum = if let Some((parent, _, _)) = ctx.ctor_details.get(&unqualified_ctor_sym(ctor_name)) {
                ctx.data_constructors
                    .get(parent)
                    .map_or(false, |ctors| ctors.len() > 1)
            } else {
                false
            };

            if is_sum {
                let ctor_ref = gen_qualified_ref_raw(ctx, name.module.map(|m| m.symbol()), name.name.symbol());
                conditions.push(JsExpr::InstanceOf(
                    Box::new(scrutinee.clone()),
                    Box::new(ctor_ref),
                ));
            }

            // Bind constructor fields — cast scrutinee to `any` so tsc allows .valueN access
            // on union types where not all variants have the field.
            for (i, arg) in args.iter().enumerate() {
                let cast_scrutinee = if is_sum {
                    scrutinee.clone()
                } else {
                    scrutinee.clone()
                };
                let field_access = JsExpr::Indexer(
                    Box::new(cast_scrutinee),
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
                let label = interner::resolve(field.label.value.symbol()).unwrap_or_default();
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
                        let js_name = ident_to_js(field.label.value.symbol());
                        bindings.push(JsStmt::VarDecl(js_name, Some(field_access)));
                    }
                }
            }

            let combined = combine_conditions(conditions);
            (combined, bindings)
        }

        Binder::As { name, binder, .. } => {
            let js_name = ident_to_js(name.value.symbol());
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
            let is_function_op = ctx.function_op_aliases.contains(&unqualified_op_sym(op_name.name.symbol()));

            if !is_function_op {
                // Constructor operator — treat as constructor binder with 2 args.
                // Resolve the operator to its target constructor name (e.g., `!` → `Cons`).
                let resolved_name = if let Some((_, target_name)) = ctx.operator_targets.get(&op_name.name.symbol()) {
                    Qualified { module: op_name.module, name: ConstructorName::new(*target_name) }
                } else {
                    op_name.map(|n| ConstructorName::new(n.symbol()))
                };
                let ctor_binder = Binder::Constructor {
                    span: binder.span(),
                    name: resolved_name,
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

pub(crate) fn combine_conditions(conditions: Vec<JsExpr>) -> Option<JsExpr> {
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

pub(crate) fn gen_record_update(ctx: &CodegenCtx, span: crate::span::Span, base: &Expr, updates: &[RecordUpdate]) -> JsExpr {
    let base_expr = gen_expr(ctx, base);

    // Build set of updated field names
    let update_label_set: HashSet<String> = updates.iter().map(|u| {
        interner::resolve(u.label.value.symbol()).unwrap_or_default()
    }).collect();

    // If we know all the record fields from typechecking, generate an object literal
    if let Some(all_fields) = ctx.record_update_fields.get(&span) {
        let mut fields = Vec::new();
        // Non-updated fields first (preserve from base), then updated fields
        for field_sym in all_fields {
            let label = field_sym.resolve().unwrap_or_default();
            if !update_label_set.contains(&label) {
                fields.push((label.clone(), JsExpr::Indexer(
                    Box::new(base_expr.clone()),
                    Box::new(JsExpr::StringLit(label)),
                )));
            }
        }
        for update in updates {
            let label = interner::resolve(update.label.value.symbol()).unwrap_or_default();
            // Use gen_expr_inner to avoid re-wrapping wildcards in nested record updates.
            // Wildcards inside update values should flow to the outer wildcard_params collection.
            let value = gen_expr_inner(ctx, &update.value);
            fields.push((label, value));
        }
        return JsExpr::ObjectLit(fields);
    }

    // Fallback: shallow copy + overwrite via for-in loop
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
        let label = interner::resolve(update.label.value.symbol()).unwrap_or_default();
        let value = gen_expr_inner(ctx, &update.value);
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

pub(crate) fn gen_do_expr(ctx: &CodegenCtx, span: crate::span::Span, statements: &[DoStatement], qual_mod: Option<&Ident>) -> JsExpr {
    // Do notation desugars to bind chains:
    // do { x <- a; b } → bind(a)(function(x) { return b; })
    // do { a; b } → discard(a)(b) or bind(a)(function(_) { return b; })

    let bind_ref = make_qualified_ref_with_span(ctx, qual_mod, "bind", Some(span));

    if statements.is_empty() {
        return JsExpr::Var("undefined".to_string());
    }

    gen_do_stmts(ctx, statements, &bind_ref, qual_mod)
}

pub(crate) fn gen_do_stmts(
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
        DoStatement::Discard { expr, span, .. } => {
            let action = gen_expr(ctx, expr);
            let rest_expr = gen_do_stmts(ctx, rest, bind_ref, qual_mod);
            // If `discard` is defined locally in this module, use it (matches original compiler).
            // Otherwise, use `bind` directly since Control.Bind.discard is a class accessor
            // that requires Discard + Bind dictionaries we can't resolve from the CST.
            // Semantically equivalent: discard(discardUnit)(dictBind) = bind(dictBind) for Unit.
            let discard_sym = interner::intern("discard");
            let call_ref = if ctx.local_names.contains(&discard_sym)
                || ctx.local_bindings.borrow().contains(&discard_sym)
            {
                gen_qualified_ref_with_span(ctx, qual_mod.copied(), discard_sym, Some(*span))
            } else {
                bind_ref.clone()
            };
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(call_ref),
                    vec![action],
                )),
                vec![JsExpr::Function(
                    None,
                    vec![],
                    vec![JsStmt::Return(rest_expr)],
                )],
            )
        }
        DoStatement::Bind { binder, expr, .. } => {
            let action = gen_expr(ctx, expr);
            let rest_expr = gen_do_stmts(ctx, rest, bind_ref, qual_mod);

            let param = match binder {
                Binder::Var { name, .. } => ident_to_js(name.value.symbol()),
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
            // Register let binding names so they shadow operators in rest
            let prev_bindings = ctx.local_bindings.borrow().clone();
            for lb in bindings.iter() {
                if let LetBinding::Value { binder: Binder::Var { name, .. }, .. } = lb {
                    ctx.local_bindings.borrow_mut().insert(name.value.symbol());
                }
            }
            let mut iife_body = Vec::new();
            gen_let_bindings(ctx, bindings, &mut iife_body);
            let rest_expr = gen_do_stmts(ctx, rest, bind_ref, qual_mod);
            *ctx.local_bindings.borrow_mut() = prev_bindings;
            iife_body.push(JsStmt::Return(rest_expr));
            JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            )
        }
    }
}

// ===== Ado notation =====

pub(crate) fn gen_ado_expr(
    ctx: &CodegenCtx,
    span: crate::span::Span,
    statements: &[DoStatement],
    result: &Expr,
    qual_mod: Option<&Ident>,
) -> JsExpr {
    // Ado desugars to apply/map chains
    let map_ref = make_qualified_ref_with_span(ctx, qual_mod, "map", Some(span));
    let apply_ref = make_qualified_ref_with_span(ctx, qual_mod, "apply", Some(span));

    if statements.is_empty() {
        // ado in expr → pure(expr)
        let pure_ref = make_qualified_ref_with_span(ctx, qual_mod, "pure", Some(span));
        let result_expr = gen_expr(ctx, result);
        return JsExpr::App(Box::new(pure_ref), vec![result_expr]);
    }

    let result_expr = gen_expr(ctx, result);

    // Build the curried lambda inside-out to properly handle Let bindings.
    // Let bindings get injected into the function body at the right position.
    let mut body = result_expr;
    let mut pending_lets: Vec<JsStmt> = Vec::new();

    for stmt in statements.iter().rev() {
        match stmt {
            DoStatement::Bind { binder, .. } => {
                let param = match binder {
                    Binder::Var { name, .. } => ident_to_js(name.value.symbol()),
                    _ => ctx.fresh_name("v"),
                };
                let mut fn_body = Vec::new();
                fn_body.extend(pending_lets.drain(..));
                fn_body.push(JsStmt::Return(body));
                body = JsExpr::Function(None, vec![param], fn_body);
            }
            DoStatement::Let { bindings, .. } => {
                let mut let_stmts = Vec::new();
                gen_let_bindings(ctx, bindings, &mut let_stmts);
                // Prepend to pending_lets (since we're iterating in reverse)
                let_stmts.extend(pending_lets.drain(..));
                pending_lets = let_stmts;
            }
            DoStatement::Discard { .. } => {
                let param = ctx.fresh_name("v");
                let mut fn_body = Vec::new();
                fn_body.extend(pending_lets.drain(..));
                fn_body.push(JsStmt::Return(body));
                body = JsExpr::Function(None, vec![param], fn_body);
            }
        }
    }

    // If there are remaining pending_lets (let before first bind), wrap in IIFE
    if !pending_lets.is_empty() {
        pending_lets.push(JsStmt::Return(body));
        body = JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], pending_lets)),
            vec![],
        );
    }

    // Now build the apply chain: map(func)(first_action) then apply(current)(action)
    // Collect bind/discard actions (not lets)
    let actions: Vec<&Expr> = statements.iter().filter_map(|stmt| {
        match stmt {
            DoStatement::Bind { expr, .. } | DoStatement::Discard { expr, .. } => Some(expr),
            _ => None,
        }
    }).collect();

    if actions.is_empty() {
        return body;
    }

    let first_action = gen_expr(ctx, actions[0]);
    let mut current = JsExpr::App(
        Box::new(JsExpr::App(Box::new(map_ref), vec![body])),
        vec![first_action],
    );

    for action_expr in actions.iter().skip(1) {
        let action = gen_expr(ctx, action_expr);
        current = JsExpr::App(
            Box::new(JsExpr::App(Box::new(apply_ref.clone()), vec![current])),
            vec![action],
        );
    }

    current
}

pub(crate) fn make_qualified_ref_with_span(ctx: &CodegenCtx, qual_mod: Option<&Ident>, name: &str, span: Option<crate::span::Span>) -> JsExpr {
    let name_sym = interner::intern(name);
    let ext_name = export_name(name_sym);
    let base = if let Some(mod_sym) = qual_mod {
        let mod_str = interner::resolve(*mod_sym).unwrap_or_default();
        let mut resolved = None;
        for imp in &ctx.module.imports {
            if let Some(ref qual) = imp.qualified {
                let qual_str = qual.parts
                    .iter()
                    .map(|s| interner::resolve(*s).unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(".");
                if qual_str == mod_str {
                    if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                        resolved = Some(JsExpr::ModuleAccessor(js_mod.clone(), ext_name.clone()));
                        break;
                    }
                }
            }
            let imp_name = imp.module.parts
                .iter()
                .map(|s| interner::resolve(*s).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".");
            if imp_name == mod_str {
                if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                    resolved = Some(JsExpr::ModuleAccessor(js_mod.clone(), ext_name.clone()));
                    break;
                }
            }
        }
        resolved.unwrap_or_else(|| {
            let js_mod = any_name_to_js(&mod_str.replace('.', "_"));
            JsExpr::ModuleAccessor(js_mod, ext_name.clone())
        })
    } else {
        if let Some(source_parts) = ctx.name_source.get(&name_sym) {
            if let Some(js_mod) = ctx.import_map.get(source_parts) {
                JsExpr::ModuleAccessor(js_mod.clone(), ext_name.clone())
            } else {
                JsExpr::Var(any_name_to_js(name))
            }
        } else {
            // Search imported modules for class methods (e.g., bind from do-notation)
            let mut found_mod = None;
            if ctx.all_class_methods.contains_key(&name_sym) {
                let mut sorted_imports: Vec<_> = ctx.import_map.iter().collect();
                sorted_imports.sort_by_key(|(_, js_mod)| (*js_mod).clone());
                for (mod_parts, js_mod) in sorted_imports {
                    if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
                        if mod_exports.class_methods.contains_key(&unqualified_value_sym(name_sym))
                            || mod_exports.values.contains_key(&unqualified_value_sym(name_sym)) {
                            found_mod = Some(JsExpr::ModuleAccessor(js_mod.clone(), ext_name.clone()));
                            break;
                        }
                    }
                }
            }
            found_mod.unwrap_or_else(|| JsExpr::Var(any_name_to_js(name)))
        }
    };

    // Apply dict if available (for class methods like bind, pure, map, apply)
    let name_sym = interner::intern(name);
    if let Some(dict_app) = try_apply_dict(ctx, name_sym, base.clone(), span) {
        return dict_app;
    }

    base
}

// ===== Topological sort =====

/// Collect all `Var` references from a JsExpr.

/// Generate code for an operator expression, handling operator precedence via shunting-yard.
/// The CST parses operator chains as right-associative trees, but we need to respect
/// declared fixities (e.g., `*` binds tighter than `+`).
pub(crate) fn gen_op_chain(ctx: &CodegenCtx, left: &Expr, op: &Spanned<Qualified<OpName>>, right: &Expr, expr_span: crate::span::Span) -> JsExpr {
    // Flatten the right-recursive Op chain
    let mut operands: Vec<&Expr> = vec![left];
    let mut operators: Vec<&Spanned<Qualified<OpName>>> = vec![op];
    let mut current: &Expr = right;
    loop {
        match current {
            Expr::Op { left: rl, op: rop, right: rr, .. } => {
                operands.push(rl.as_ref());
                operators.push(rop);
                current = rr.as_ref();
            }
            _ => break,
        }
    }
    operands.push(current);

    // Single operator: no rebalancing needed
    if operators.len() == 1 {
        return gen_single_op(ctx, &operands[0], operators[0], &operands[1], expr_span);
    }

    // Shunting-yard algorithm for multiple operators
    let mut output: Vec<JsExpr> = Vec::new();
    let mut op_stack: Vec<usize> = Vec::new(); // indices into operators

    output.push(gen_expr(ctx, operands[0]));

    // Resolve operator symbol to string for fixity lookup (avoids interner inconsistency)
    let op_name = |sym: Symbol| -> String {
        crate::interner::resolve(sym).unwrap_or_default()
    };

    for i in 0..operators.len() {
        let name_i = op_name(operators[i].value.name.symbol());
        let (assoc_i, prec_i) = ctx.op_fixities.get(&name_i)
            .copied()
            .unwrap_or((Associativity::Left, 9));
        while let Some(&top_idx) = op_stack.last() {
            let (_assoc_top, prec_top) = ctx.op_fixities.get(&op_name(operators[top_idx].value.name.symbol()))
                .copied()
                .unwrap_or((Associativity::Left, 9));

            let should_pop = if prec_top > prec_i {
                true
            } else if prec_top == prec_i && assoc_i == Associativity::Left {
                true
            } else {
                false
            };

            if should_pop {
                op_stack.pop();
                let rhs = output.pop().unwrap();
                let lhs = output.pop().unwrap();
                output.push(apply_op(ctx, operators[top_idx], lhs, rhs));
            } else {
                break;
            }
        }

        op_stack.push(i);
        output.push(gen_expr(ctx, operands[i + 1]));
    }

    // Pop remaining operators
    while let Some(top_idx) = op_stack.pop() {
        let rhs = output.pop().unwrap();
        let lhs = output.pop().unwrap();
        output.push(apply_op(ctx, operators[top_idx], lhs, rhs));
    }

    output.pop().unwrap()
}

/// Generate code for a single operator application.
pub(crate) fn gen_single_op(ctx: &CodegenCtx, left: &Expr, op: &Spanned<Qualified<OpName>>, right: &Expr, _expr_span: crate::span::Span) -> JsExpr {
    // Optimize `f $ x` (apply) to `f(x)` and `x # f` (applyFlipped) to `f(x)`
    if is_apply_operator(ctx, op) {
        let flipped = is_apply_flipped_operator(ctx, op);
        if !flipped {
            // Detect `unsafePartial $ expr` — enable Partial discharge mode for the argument
            if is_unsafe_partial_call(left) {
                let prev = ctx.discharging_partial.get();
                ctx.discharging_partial.set(true);
                let x = gen_expr(ctx, right);
                ctx.discharging_partial.set(prev);
                return x;
            }
        }
        let (func_expr, arg_expr) = if flipped {
            // `a # f` = `f(a)` — right is the function, left is the argument
            (right, left)
        } else {
            // `f $ x` = `f(x)` — left is the function, right is the argument
            (left, right)
        };
        let f = gen_expr(ctx, func_expr);
        let x = gen_expr(ctx, arg_expr);
        return JsExpr::App(Box::new(f), vec![x]);
    }
    // Use the operator's own span for dict lookup, because the typechecker stores
    // resolved dicts keyed by the AST Expr::Var span, which is op.span (the operator
    // token's span), NOT the full Expr::Op span.
    let op_ref = resolve_op_ref(ctx, op, Some(op.span));
    let l = gen_expr(ctx, left);
    let r = gen_expr(ctx, right);
    // When the operator resolved to a bare module accessor (no dict applied),
    // try to inline it as a native JS binary operation. This handles the case where
    // the operator is inside a local let-binding whose typeclass constraint was
    // generalized and not resolved to a concrete instance.
    if let JsExpr::ModuleAccessor(ref module, ref method) = op_ref {
        if let Some(inlined) = try_inline_bare_op(module, method, &l, &r) {
            return inlined;
        }
    }
    JsExpr::App(
        Box::new(JsExpr::App(Box::new(op_ref), vec![l])),
        vec![r],
    )
}

/// Apply an operator to two JS expressions.
pub(crate) fn apply_op(ctx: &CodegenCtx, op: &Spanned<Qualified<OpName>>, lhs: JsExpr, rhs: JsExpr) -> JsExpr {
    // Optimize `f $ x` (apply) to `f(x)` and `x # f` (applyFlipped) to `f(x)`
    if is_apply_operator(ctx, op) {
        if is_apply_flipped_operator(ctx, op) {
            return JsExpr::App(Box::new(rhs), vec![lhs]);
        }
        // Detect `unsafePartial $ expr` — unsafePartial is identity when Partial
        // functions are already pre-stripped via partial_fns/gen_qualified_ref_with_span.
        if is_js_unsafe_partial(&lhs) {
            return rhs;
        }
        return JsExpr::App(Box::new(lhs), vec![rhs]);
    }
    let op_ref = resolve_op_ref(ctx, op, Some(op.span));
    // When the operator resolved to a bare module accessor (no dict applied),
    // try to inline it as a native JS binary operation.
    if let JsExpr::ModuleAccessor(ref module, ref method) = op_ref {
        if let Some(inlined) = try_inline_bare_op(module, method, &lhs, &rhs) {
            return inlined;
        }
    }
    JsExpr::App(
        Box::new(JsExpr::App(Box::new(op_ref), vec![lhs])),
        vec![rhs],
    )
}

/// Try to inline a bare (no dict) class method as a native JS binary operation.
/// This handles the case where an operator is inside a generalized local binding
/// whose typeclass constraint was not resolved to a concrete instance.
/// Since the most common case is Number types, we default to Number semantics.
pub(crate) fn try_inline_bare_op(module: &str, method: &str, a: &JsExpr, b: &JsExpr) -> Option<JsExpr> {
    // Number ops from their respective modules
    let op = match (module, method) {
        (m, "add") if m.ends_with("Semiring") => Some(JsBinaryOp::Add),
        (m, "mul") if m.ends_with("Semiring") => Some(JsBinaryOp::Mul),
        (m, "sub") if m.ends_with("Ring") => Some(JsBinaryOp::Sub),
        (m, "div") if m.ends_with("EuclideanRing") => Some(JsBinaryOp::Div),
        (m, "eq") if m.ends_with("Eq") => Some(JsBinaryOp::StrictEq),
        (m, "notEq") if m.ends_with("Eq") => Some(JsBinaryOp::StrictNeq),
        (m, "lessThan") if m.ends_with("Ord") => Some(JsBinaryOp::Lt),
        (m, "lessThanOrEq") if m.ends_with("Ord") => Some(JsBinaryOp::Lte),
        (m, "greaterThan") if m.ends_with("Ord") => Some(JsBinaryOp::Gt),
        (m, "greaterThanOrEq") if m.ends_with("Ord") => Some(JsBinaryOp::Gte),
        (m, "append") if m.ends_with("Semigroup") => Some(JsBinaryOp::Add),
        _ => None,
    };
    op.map(|o| JsExpr::Binary(o, Box::new(a.clone()), Box::new(b.clone())))
}

/// Check if an operator is `$` or `#` (apply/applyFlipped from Data.Function), which should be inlined
pub(crate) fn is_apply_operator(ctx: &CodegenCtx, op: &Spanned<Qualified<OpName>>) -> bool {
    if let Some((_, target_name)) = ctx.operator_targets.get(&op.value.name.symbol()) {
        let name = interner::resolve(*target_name).unwrap_or_default();
        if name != "apply" && name != "applyFlipped" {
            return false;
        }
        // Exclude class method operators like <*> (Control.Apply.apply)
        // by checking the operator symbol name — $ and # are the only
        // function-application operators
        let op_name = interner::resolve(op.value.name.symbol()).unwrap_or_default();
        op_name == "$" || op_name == "#"
    } else {
        false
    }
}

/// Check if an operator is `#` (applyFlipped), meaning arguments should be swapped: `a # f` = `f(a)`
pub(crate) fn is_apply_flipped_operator(ctx: &CodegenCtx, op: &Spanned<Qualified<OpName>>) -> bool {
    if let Some((_, target_name)) = ctx.operator_targets.get(&op.value.name.symbol()) {
        let name = interner::resolve(*target_name).unwrap_or_default();
        if name != "applyFlipped" {
            return false;
        }
        let op_name = interner::resolve(op.value.name.symbol()).unwrap_or_default();
        op_name == "#"
    } else {
        false
    }
}

/// Resolve an operator to its JS reference (target function + dict application).
pub(crate) fn resolve_op_ref(ctx: &CodegenCtx, op: &Spanned<Qualified<OpName>>, expr_span: Option<crate::span::Span>) -> JsExpr {
    let op_sym = op.value.name.symbol();
    // Use expr_span for dict lookup (matches typechecker's span for OpParens vs Op)
    let lookup_span = expr_span.or(Some(op.span));

    // If the operator name itself is a local let-binding (e.g., backtick `div` where
    // `div` is locally defined), use the local variable instead of the imported operator.
    // But if the local binding is constrained, fall through to apply dicts.
    if op.value.module.is_none() && ctx.local_bindings.borrow().contains(&op_sym) {
        if !ctx.local_constrained_bindings.borrow().contains(&op_sym) {
            return JsExpr::Var(ident_to_js(op_sym));
        }
        // Constrained local binding: use gen_qualified_ref_with_span to apply dicts
        return gen_qualified_ref_with_span(ctx, None, op_sym, lookup_span);
    }

    if let Some((source_parts, target_name)) = ctx.operator_targets.get(&op_sym) {
        // Check if the target is a data constructor by looking it up in ctor_details
        let is_ctor = is_constructor_name(ctx, *target_name);
        if is_ctor {
            // Constructor operator: emit Ctor.create (curried constructor)
            let base = gen_qualified_ref_raw(ctx, None, *target_name);
            return JsExpr::Indexer(
                Box::new(base),
                Box::new(JsExpr::StringLit("create".to_string())),
            );
        }
        if source_parts.is_none() && (ctx.local_names.contains(target_name) || ctx.name_source.contains_key(target_name)) {
            // Temporarily remove the operator target from local_bindings so that
            // a local let-shadow (e.g. `let f = (-) in a % b` where % aliases module-level f)
            // doesn't intercept the operator resolution.
            let was_bound = ctx.local_bindings.borrow_mut().remove(target_name);
            if was_bound && ctx.local_names.contains(target_name) {
                // The operator target is a module-level name shadowed by a let binding.
                // JsExpr::Var("f") would capture the let-bound value, not the module-level one.
                // Instead, look at the module-level declaration for the target and generate
                // the expression directly (e.g., f = (+) → resolve (+) instead).
                ctx.local_bindings.borrow_mut().insert(*target_name); // restore
                if let Some(stored) = ctx.module_level_exprs.borrow().get(target_name).cloned() {
                    stored
                } else {
                    // Fallback: try to find the module-level decl and resolve its body
                    let mut resolved = None;
                    for decl in &ctx.module.decls {
                        if let Decl::Value { name: ref dname, binders, guarded: GuardedExpr::Unconditional(body), .. } = decl {
                            if dname.value.symbol() == *target_name && binders.is_empty() {
                                // Generate the expression for the module-level definition
                                resolved = Some(gen_expr(ctx, body));
                                break;
                            }
                        }
                    }
                    resolved.unwrap_or_else(|| {
                        gen_qualified_ref_with_span(ctx, None, *target_name, lookup_span)
                    })
                }
            } else {
                let result = gen_qualified_ref_with_span(ctx, None, *target_name, lookup_span);
                if was_bound {
                    ctx.local_bindings.borrow_mut().insert(*target_name);
                }
                result
            }
        } else if let Some(parts) = source_parts {
            // Target not in name_source — resolve via operator's source module
            if let Some(js_mod) = ctx.import_map.get(parts) {
                let target_js = export_name(*target_name);
                let base = JsExpr::ModuleAccessor(js_mod.clone(), target_js);
                // Try to apply dict
                if let Some(dict_applied) = try_apply_dict(ctx, *target_name, base.clone(), lookup_span) {
                    dict_applied
                } else {
                    base
                }
            } else {
                gen_qualified_ref_with_span(ctx, None, *target_name, lookup_span)
            }
        } else {
            gen_qualified_ref_with_span(ctx, None, *target_name, lookup_span)
        }
    } else {
        // No operator_targets entry — this is a backtick-infixed function or constructor.
        // Check if it's a constructor name and emit .create if so.
        if is_constructor_name(ctx, op_sym) {
            let base = gen_qualified_ref_raw(ctx, op.value.module.map(|m| m.symbol()), op.value.name.symbol());
            return JsExpr::Indexer(
                Box::new(base),
                Box::new(JsExpr::StringLit("create".to_string())),
            );
        }
        gen_qualified_ref_with_span(ctx, op.value.module.map(|m| m.symbol()), op.value.name.symbol(), lookup_span)
    }
}

/// Check if a name refers to a data constructor (local or imported).
pub(crate) fn is_constructor_name(ctx: &CodegenCtx, name: Symbol) -> bool {
    // Check local ctor_details
    if ctx.ctor_details.contains_key(&unqualified_ctor_sym(name)) {
        return true;
    }
    // Check imported modules' ctor_details
    if let Some(source_parts) = ctx.name_source.get(&name) {
        if let Some(mod_exports) = ctx.registry.lookup(source_parts) {
            if mod_exports.ctor_details.contains_key(&unqualified_ctor_sym(name)) {
                return true;
            }
        }
    }
    false
}

// ===== Post-processing: inline known typeclass operations =====

/// Extract method name and dict name from a 3-level nested application:
/// App(ModuleAccessor(mod, method), [ModuleAccessor(_, dict)])
pub(crate) fn extract_method_dict_from_expr(expr: &JsExpr) -> Option<(&str, &str)> {
    if let JsExpr::App(callee, args) = expr {
        if args.len() == 1 {
            if let JsExpr::ModuleAccessor(_, method) = callee.as_ref() {
                if let JsExpr::ModuleAccessor(_, dict) = &args[0] {
                    if is_eq_dict(dict) || is_ord_dict(dict)
                        || matches!(dict.as_str(), "semiringInt" | "semiringNumber"
                            | "ringInt" | "ringNumber"
                            | "euclideanRingInt" | "euclideanRingNumber"
                            | "heytingAlgebraBoolean")
                    {
                        return Some((method.as_str(), dict.as_str()));
                    }
                }
            }
        }
    }
    None
}

/// Try to inline a fully-applied binary op in post-processing: method(dict)(x)(y)
pub(crate) fn try_inline_binary_op_post(expr: &JsExpr) -> Option<JsExpr> {
    if let JsExpr::App(outer_callee, outer_args) = expr {
        if outer_args.len() != 1 { return None; }
        let y = &outer_args[0];

        if let JsExpr::App(mid_callee, mid_args) = outer_callee.as_ref() {
            if mid_args.len() != 1 { return None; }
            let x = &mid_args[0];

            if let Some((method, dict)) = extract_method_dict_from_expr(mid_callee) {
                let is_int = dict.ends_with("Int");
                // Comparison and equality ops
                let op = match method {
                    "lessThan" => Some(JsBinaryOp::Lt),
                    "lessThanOrEq" => Some(JsBinaryOp::Lte),
                    "greaterThan" => Some(JsBinaryOp::Gt),
                    "greaterThanOrEq" => Some(JsBinaryOp::Gte),
                    "eq" => Some(JsBinaryOp::StrictEq),
                    "notEq" => Some(JsBinaryOp::StrictNeq),
                    "add" if !is_int => Some(JsBinaryOp::Add),
                    "mul" if !is_int => Some(JsBinaryOp::Mul),
                    "sub" if !is_int => Some(JsBinaryOp::Sub),
                    "div" if !is_int => Some(JsBinaryOp::Div),
                    "conj" if dict == "heytingAlgebraBoolean" => Some(JsBinaryOp::And),
                    "disj" if dict == "heytingAlgebraBoolean" => Some(JsBinaryOp::Or),
                    _ => None,
                };
                if let Some(op) = op {
                    return Some(JsExpr::Binary(op, Box::new(x.clone()), Box::new(y.clone())));
                }
                // Int arithmetic with |0
                if is_int {
                    let arith_op = match method {
                        "add" => Some(JsBinaryOp::Add),
                        "mul" => Some(JsBinaryOp::Mul),
                        "sub" => Some(JsBinaryOp::Sub),
                        _ => None,
                    };
                    if let Some(op) = arith_op {
                        return Some(JsExpr::Binary(
                            JsBinaryOp::BitwiseOr,
                            Box::new(JsExpr::Binary(op, Box::new(x.clone()), Box::new(y.clone()))),
                            Box::new(JsExpr::IntLit(0)),
                        ));
                    }
                }
            }
        }
    }
    None
}

/// Try to inline a unary op in post-processing: method(dict)(x)
pub(crate) fn try_inline_unary_op_post(expr: &JsExpr) -> Option<JsExpr> {
    if let JsExpr::App(callee, args) = expr {
        if args.len() != 1 { return None; }
        let x = &args[0];

        if let Some((method, dict)) = extract_method_dict_from_expr(callee) {
            let is_int = dict.ends_with("Int");
            match method {
                "negate" if is_int => return Some(JsExpr::Binary(
                    JsBinaryOp::BitwiseOr,
                    Box::new(JsExpr::Unary(JsUnaryOp::Negate, Box::new(x.clone()))),
                    Box::new(JsExpr::IntLit(0)),
                )),
                "negate" => return Some(JsExpr::Unary(JsUnaryOp::Negate, Box::new(x.clone()))),
                "not" if dict == "heytingAlgebraBoolean" => {
                    return Some(JsExpr::Unary(JsUnaryOp::Not, Box::new(x.clone())));
                }
                _ => {}
            }
        }
    }
    None
}

/// Try to inline a constant in post-processing: method(dict) → literal
pub(crate) fn try_inline_constant_post(expr: &JsExpr) -> Option<JsExpr> {
    if let Some((method, dict)) = extract_method_dict_from_expr(expr) {
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

pub(crate) fn inline_known_ops_expr(expr: &mut JsExpr) {
    // First, recurse into sub-expressions
    match expr {
        JsExpr::App(callee, args) => {
            inline_known_ops_expr(callee);
            for arg in args.iter_mut() {
                inline_known_ops_expr(arg);
            }
        }
        JsExpr::Function(_, _, body) => {
            for s in body.iter_mut() {
                inline_known_ops_stmt(s);
            }
        }
        JsExpr::Binary(_, l, r) => {
            inline_known_ops_expr(l);
            inline_known_ops_expr(r);
        }
        JsExpr::Unary(_, e) => inline_known_ops_expr(e),
        JsExpr::Ternary(c, t, f) => {
            inline_known_ops_expr(c);
            inline_known_ops_expr(t);
            inline_known_ops_expr(f);
        }
        JsExpr::ArrayLit(elems) => {
            for e in elems.iter_mut() { inline_known_ops_expr(e); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, e) in fields.iter_mut() { inline_known_ops_expr(e); }
        }
        JsExpr::Indexer(obj, key) => {
            inline_known_ops_expr(obj);
            inline_known_ops_expr(key);
        }
        JsExpr::New(callee, args) => {
            inline_known_ops_expr(callee);
            for arg in args.iter_mut() { inline_known_ops_expr(arg); }
        }
        JsExpr::InstanceOf(l, r) => {
            inline_known_ops_expr(l);
            inline_known_ops_expr(r);
        }
        _ => {}
    }

    // Then try to inline this expression
    if let Some(inlined) = try_inline_binary_op_post(expr) {
        *expr = inlined;
        return;
    }
    if let Some(inlined) = try_inline_unary_op_post(expr) {
        *expr = inlined;
        return;
    }
    if let Some(inlined) = try_inline_constant_post(expr) {
        *expr = inlined;
    }
}

pub(crate) fn inline_known_ops_stmt(stmt: &mut JsStmt) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) => inline_known_ops_expr(expr),
        JsStmt::Return(expr) | JsStmt::Throw(expr) | JsStmt::Expr(expr) => {
            inline_known_ops_expr(expr);
        }
        JsStmt::Assign(target, expr) => {
            inline_known_ops_expr(target);
            inline_known_ops_expr(expr);
        }
        JsStmt::If(cond, then_stmts, else_stmts) => {
            inline_known_ops_expr(cond);
            for s in then_stmts.iter_mut() { inline_known_ops_stmt(s); }
            if let Some(else_s) = else_stmts {
                for s in else_s.iter_mut() { inline_known_ops_stmt(s); }
            }
        }
        JsStmt::Block(_stmts) | JsStmt::While(_, _stmts) => {
            if let JsStmt::While(cond, _) = stmt {
                inline_known_ops_expr(cond);
            }
            // Re-match to avoid borrow issues
        }
        JsStmt::For(_, init, bound, body) => {
            inline_known_ops_expr(init);
            inline_known_ops_expr(bound);
            for s in body.iter_mut() { inline_known_ops_stmt(s); }
        }
        JsStmt::ForIn(_, obj, body) => {
            inline_known_ops_expr(obj);
            for s in body.iter_mut() { inline_known_ops_stmt(s); }
        }
        JsStmt::FunctionDecl(_, _, body) => {
            for s in body.iter_mut() { inline_known_ops_stmt(s); }
        }
        _ => {}
    }
    // Handle While and Block after initial match to avoid borrow issues
    match stmt {
        JsStmt::While(cond, body) => {
            inline_known_ops_expr(cond);
            for s in body.iter_mut() { inline_known_ops_stmt(s); }
        }
        JsStmt::Block(stmts) => {
            for s in stmts.iter_mut() { inline_known_ops_stmt(s); }
        }
        _ => {}
    }
}
