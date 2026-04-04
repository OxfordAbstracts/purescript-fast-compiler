use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use crate::interner::{self, Symbol};
use crate::names::{ClassName, Qualified, TypeName, TypeVarName, ValueName};

use super::*;
use super::super::common::any_name_to_js;

/// Wrap the return value of a function expression with dict parameters.
/// Used for functions whose return type has inner forall constraints.
/// E.g., `function(v) { return v.value0; }` becomes
/// `function(v) { return function(dictMonad) { return v.value0(dictMonad); }; }`
pub(crate) fn wrap_return_value_with_dict_params(
    expr: JsExpr,
    dict_param_names: &[String],
) -> JsExpr {
    if dict_param_names.is_empty() {
        return expr;
    }
    // Walk into the function expression to find the innermost body (after all curried params)
    match expr {
        JsExpr::Function(name, params, stmts) => {
            let wrapped_stmts = wrap_stmts_return_with_dicts(stmts, dict_param_names);
            JsExpr::Function(name, params, wrapped_stmts)
        }
        other => {
            // Not a function — wrap the expression itself
            wrap_expr_with_return_dicts(other, dict_param_names)
        }
    }
}

/// Wrap the return statement(s) in a list of stmts with dict params.
pub(crate) fn wrap_stmts_return_with_dicts(stmts: Vec<JsStmt>, dict_params: &[String]) -> Vec<JsStmt> {
    stmts.into_iter().map(|stmt| match stmt {
        JsStmt::Return(expr) => {
            JsStmt::Return(wrap_expr_with_return_dicts(expr, dict_params))
        }
        other => other,
    }).collect()
}

/// Wrap an expression with `function(dict1) { return function(dict2) { return expr; }; }`
/// The expression body already has dict references resolved via scope, so we only
/// wrap with lambda parameters — we do NOT apply dicts to the expression.
pub(crate) fn wrap_expr_with_return_dicts(expr: JsExpr, dict_params: &[String]) -> JsExpr {
    // Wrap with curried dict param functions (inside-out)
    let mut result = expr;
    for param in dict_params.iter().rev() {
        result = JsExpr::Function(None, vec![param.clone()], vec![JsStmt::Return(result)]);
    }
    result
}

/// Apply dicts to expression AND wrap with dict param functions (pass-through).
/// E.g., `expr` → `function(dict1) { return expr(dict1); }`
/// Used when the body did not consume the dicts — the value already has the constraint type.
pub(crate) fn wrap_expr_with_return_dicts_apply(expr: JsExpr, dict_params: &[String]) -> JsExpr {
    let mut inner = expr;
    for param in dict_params {
        inner = JsExpr::App(Box::new(inner), vec![JsExpr::Var(param.clone())]);
    }
    let mut result = inner;
    for param in dict_params.iter().rev() {
        result = JsExpr::Function(None, vec![param.clone()], vec![JsStmt::Return(result)]);
    }
    result
}

/// Like wrap_return_value_with_dict_params but applies dicts (pass-through mode).
pub(crate) fn wrap_return_value_with_dict_params_apply(
    expr: JsExpr,
    dict_param_names: &[String],
) -> JsExpr {
    if dict_param_names.is_empty() {
        return expr;
    }
    match expr {
        JsExpr::Function(name, params, stmts) => {
            let wrapped_stmts = wrap_stmts_return_with_dicts_apply(stmts, dict_param_names);
            JsExpr::Function(name, params, wrapped_stmts)
        }
        other => {
            wrap_expr_with_return_dicts_apply(other, dict_param_names)
        }
    }
}

pub(crate) fn wrap_stmts_return_with_dicts_apply(stmts: Vec<JsStmt>, dict_params: &[String]) -> Vec<JsStmt> {
    stmts.into_iter().map(|stmt| match stmt {
        JsStmt::Return(expr) => {
            JsStmt::Return(wrap_expr_with_return_dicts_apply(expr, dict_params))
        }
        other => other,
    }).collect()
}

/// Optional runtime check context for dict parameter wrapping.
pub(crate) struct DictCheckCtx<'a> {
    pub class_expected_fields: &'a HashMap<Symbol, HashSet<String>>,
    pub needs_runtime_check: &'a Cell<bool>,
    pub location: String,
}

/// Wrap an expression with curried dict parameters from type class constraints.
/// E.g. `Show a => Eq a => ...` → `function(dictShow) { return function(dictEq) { return expr; }; }`
pub(crate) fn wrap_with_dict_params_named(
    expr: JsExpr,
    constraints: Option<&Vec<(Qualified<ClassName>, Vec<crate::typechecker::types::Type>)>>,
    known_runtime_classes: &HashSet<Symbol>,
    fn_name: Option<&str>,
    check_ctx: Option<&DictCheckCtx>,
) -> JsExpr {
    wrap_with_dict_params_named_excluding(expr, constraints, known_runtime_classes, fn_name, &HashSet::new(), check_ctx)
}

/// Like wrap_with_dict_params_named but with a set of excluded callee names for hoisting.
/// Calls to functions in `excluded_callees` will not be hoisted to prevent mutual recursion.
pub(crate) fn wrap_with_dict_params_named_excluding(
    expr: JsExpr,
    constraints: Option<&Vec<(Qualified<ClassName>, Vec<crate::typechecker::types::Type>)>>,
    known_runtime_classes: &HashSet<Symbol>,
    fn_name: Option<&str>,
    excluded_callees: &HashSet<String>,
    check_ctx: Option<&DictCheckCtx>,
) -> JsExpr {
    let Some(constraints) = constraints else { return expr };
    if constraints.is_empty() { return expr; }

    // Pre-compute unique dict param names (must match dict_scope push naming)
    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
    let mut dict_params: Vec<Option<String>> = Vec::new();
    for (class_qi, _) in constraints.iter() {
        if !known_runtime_classes.contains(&class_qi.name_symbol()) {
            dict_params.push(None); // phantom — no runtime dict
        } else {
            let class_name = class_qi.name.resolve().unwrap_or_default();
            let count = dict_name_counts.entry(class_name.to_string()).or_insert(0);
            let dict_param = if *count == 0 {
                format!("dict{class_name}")
            } else {
                format!("dict{class_name}{count}")
            };
            *count += 1;
            dict_params.push(Some(dict_param));
        }
    }

    // Step 1: Build constraint wrapping WITHOUT hoisting (inside-out)
    let mut result = expr;
    for (i, (class_qi, _)) in constraints.iter().enumerate().rev() {
        match &dict_params[i] {
            None => {
                result = JsExpr::Function(
                    None,
                    vec![],
                    vec![JsStmt::Return(result)],
                );
            }
            Some(dict_param) => {
                let mut body = Vec::new();
                // Insert runtime dict check if enabled
                if let Some(ctx) = check_ctx {
                    let class_sym = class_qi.name_symbol();
                    if let Some(expected_fields) = ctx.class_expected_fields.get(&class_sym) {
                        let class_name_str = class_qi.name.resolve().unwrap_or_default();
                        body.push(super::gen_dict_proxy_wrap(
                            dict_param,
                            &class_name_str,
                            expected_fields,
                            &ctx.location,
                        ));
                        ctx.needs_runtime_check.set(true);
                    }
                }
                body.push(JsStmt::Return(result));
                result = JsExpr::Function(
                    None,
                    vec![dict_param.clone()],
                    body,
                );
            }
        }
    }
    // Dict hoisting disabled for correctness
    result
}

/// Generate dict parameter names for constraints, numbering duplicates.
/// E.g., [Eq, Eq] → ["dictEq", "dictEq1"], [Show, Eq] → ["dictShow", "dictEq"]
pub(crate) fn constraint_dict_params(constraints: &[Constraint]) -> Vec<String> {
    let mut counts: HashMap<Symbol, usize> = HashMap::new();
    let mut result = Vec::new();
    let mut used_names: HashSet<String> = HashSet::new();
    for c in constraints {
        let count = counts.entry(c.class.name.symbol()).or_insert(0);
        let class_name = interner::resolve(c.class.name.symbol()).unwrap_or_default();
        let name = if *count == 0 {
            format!("dict{class_name}")
        } else {
            format!("dict{class_name}{count}")
        };
        *count += 1;
        // If name collides with a previously used name, bump the suffix
        if used_names.contains(&name) {
            let mut suffix = *count;
            loop {
                let candidate = format!("dict{class_name}{suffix}");
                if !used_names.contains(&candidate) {
                    used_names.insert(candidate.clone());
                    result.push(candidate);
                    break;
                }
                suffix += 1;
            }
        } else {
            used_names.insert(name.clone());
            result.push(name);
        }
    }
    result
}

/// Generate a dict parameter name from a constraint, e.g. `Show a` → `dictShow`
pub(crate) fn constraint_to_dict_param(constraint: &Constraint) -> String {
    let class_name = interner::resolve(constraint.class.name.symbol()).unwrap_or_default();
    format!("dict{class_name}")
}

/// Generate superclass accessor fields for an instance dict.
///
/// For `class (Applicative m, Bind m) <= Monad m`, an instance like `monadEffect`
/// needs fields:
///   Applicative0: function() { return applicativeEffect; },
///   Bind1: function() { return bindEffect; },
pub(crate) fn gen_superclass_accessors(
    ctx: &CodegenCtx,
    class_name: Symbol,
    instance_types: &[crate::cst::TypeExpr],
    instance_constraints: &[Constraint],
    fields: &mut Vec<(String, JsExpr)>,
) {
    // Look up class superclasses
    let superclasses = find_class_superclasses(ctx, class_name);
    if superclasses.is_empty() {
        return;
    }

    // Get the class's type variable names (for matching superclass args to instance types)
    let class_tvs = find_class_type_vars(ctx, class_name);

    // Extract head type constructor from instance types (for registry lookup)
    let head_type = extract_head_type_con_from_cst(instance_types, &ctx.type_op_targets);

    for (idx, (super_class_qi, super_args)) in superclasses.iter().enumerate() {
        let super_name = super_class_qi.name.resolve().unwrap_or_default();
        let accessor_name = format!("{super_name}{idx}");

        // Type-level classes (Coercible, etc.) have no runtime dict — return undefined
        if !ctx.known_runtime_classes.contains(&super_class_qi.name_symbol()) {
            let thunk = JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(JsExpr::Var("undefined".to_string()))],
            );
            fields.push((accessor_name, thunk));
            continue;
        }

        // Try to resolve the superclass instance:
        // 1. If the instance has constraints AND the relevant instance type is a bare type variable,
        //    the superclass dict comes directly from the constraint param.
        //    BUT if the instance type has a concrete head (e.g., StateT s m), the constraint dict
        //    is for the wrong type — we need the instance for that concrete type instead.
        //    E.g., `Monad m => MonadState s (StateT s m)` with superclass `Monad m`:
        //    `m` maps to `StateT s m` → need `monadStateT(dictMonad)`, not just `dictMonad`.
        // 2. Otherwise, look up in instance registry

        // Check if the constraint dict would be exact (instance type is a bare variable)
        let constraint_dict_is_exact = if !class_tvs.is_empty() && !super_args.is_empty() {
            let mut all_bare_vars = true;
            for super_arg in super_args {
                if let crate::typechecker::types::Type::Var(tv) = super_arg {
                    if let Some(pos) = class_tvs.iter().position(|v| *tv == *v) {
                        if let Some(inst_type) = instance_types.get(pos) {
                            if extract_head_from_type_expr(inst_type, &ctx.type_op_targets).is_some() {
                                all_bare_vars = false;
                                break;
                            }
                        }
                    }
                }
            }
            all_bare_vars
        } else {
            true
        };

        // Try constraint match only when the instance type is a bare variable
        let from_constraint = if constraint_dict_is_exact {
            find_superclass_from_constraints(instance_constraints, super_class_qi.name_symbol())
        } else {
            None
        };

        let dict_expr = if let Some(dict) = from_constraint {
            dict
        } else {
            // Registry lookup: find the superclass instance for the concrete head type
            let effective_head = if !class_tvs.is_empty() && !super_args.is_empty() {
                let mut found_head = None;
                for super_arg in super_args {
                    if let crate::typechecker::types::Type::Var(tv) = super_arg {
                        if let Some(pos) = class_tvs.iter().position(|v| *tv == *v) {
                            if let Some(h) = instance_types.get(pos).and_then(|t| extract_head_from_type_expr(t, &ctx.type_op_targets)) {
                                found_head = Some(h);
                                break;
                            }
                        }
                    }
                }
                found_head.or(head_type)
            } else {
                head_type
            };

            let Some(head) = effective_head else { continue };
            let base_ref = resolve_instance_ref(ctx, super_class_qi.name_symbol(), head);

            // If the resolved instance is a local constrained instance,
            // apply the matching constraint dicts from the parent instance.
            let inst_sym = ctx.instance_registry.get(&(ClassName::new(super_class_qi.name_symbol()), TypeName::new(head))).cloned();
            if let Some(inst_name) = inst_sym {
                if let Some(constraint_classes) = ctx.instance_constraint_classes.get(&inst_name) {
                    if !constraint_classes.is_empty() {
                        let parent_dict_params = constraint_dict_params(instance_constraints);
                        let mut applied = base_ref;
                        for sc_class in constraint_classes {
                            if !ctx.known_runtime_classes.contains(sc_class) {
                                applied = JsExpr::App(Box::new(applied), vec![]);
                                continue;
                            }
                            if let Some(pos) = instance_constraints.iter().position(|c| c.class.name.symbol() == *sc_class) {
                                applied = JsExpr::App(
                                    Box::new(applied),
                                    vec![JsExpr::Var(parent_dict_params[pos].clone())],
                                );
                            } else {
                                let class_str = interner::resolve(*sc_class).unwrap_or_default();
                                let mut found_dict = false;
                                for (i, parent_c) in instance_constraints.iter().enumerate() {
                                    let mut chain = Vec::new();
                                    if find_superclass_chain(ctx, parent_c.class.name.symbol(), *sc_class, &mut chain) {
                                        let mut dict_access = JsExpr::Var(parent_dict_params[i].clone());
                                        for accessor in &chain {
                                            dict_access = JsExpr::App(
                                                Box::new(JsExpr::Indexer(
                                                    Box::new(dict_access),
                                                    Box::new(JsExpr::StringLit(accessor.clone())),
                                                )),
                                                vec![],
                                            );
                                        }
                                        applied = JsExpr::App(Box::new(applied), vec![dict_access]);
                                        found_dict = true;
                                        break;
                                    }
                                }
                                if !found_dict {
                                    applied = JsExpr::App(
                                        Box::new(applied),
                                        vec![JsExpr::Var(format!("dict{class_str}"))],
                                    );
                                }
                            }
                        }
                        applied
                    } else {
                        base_ref
                    }
                } else {
                    base_ref
                }
            } else {
                base_ref
            }
        };

        // Generate thunk: function() { return dictExpr; }
        let thunk = JsExpr::Function(
            None,
            vec![],
            vec![JsStmt::Return(dict_expr)],
        );
        fields.push((accessor_name, thunk));
    }
}

/// Find class superclasses from pre-built lookup table.
/// Checks the current module's exports first, so locally-defined classes
/// take precedence over imported ones with the same unqualified name.
pub(crate) fn find_class_superclasses(
    ctx: &CodegenCtx,
    class_name: Symbol,
) -> Vec<(Qualified<ClassName>, Vec<crate::typechecker::types::Type>)> {
    // Check local module's class_superclasses first (keyed by Qualified<ClassName>)
    let local_key = unqualified_class_sym(class_name);
    if let Some((_, supers)) = ctx.exports.class_superclasses.get(&local_key) {
        return supers.clone();
    }
    ctx.all_class_superclasses.get(&class_name).map(|(_, supers)| supers.clone()).unwrap_or_default()
}

pub(crate) fn find_class_type_vars(
    ctx: &CodegenCtx,
    class_name: Symbol,
) -> Vec<crate::names::TypeVarName> {
    // Check local module's class_superclasses first (keyed by Qualified<ClassName>)
    let local_key = unqualified_class_sym(class_name);
    if let Some((tvs, _)) = ctx.exports.class_superclasses.get(&local_key) {
        return tvs.clone();
    }
    ctx.all_class_superclasses.get(&class_name).map(|(tvs, _)| tvs.clone()).unwrap_or_default()
}

/// Check if a superclass dict can be obtained from the instance's own constraint parameters.
/// E.g., for `instance (Semigroup a) => Semigroup (Maybe a)`, the `Semigroup` constraint
/// on `a` comes from the instance constraint parameter.
pub(crate) fn find_superclass_from_constraints(
    instance_constraints: &[Constraint],
    super_class: Symbol,
) -> Option<JsExpr> {
    for constraint in instance_constraints {
        if constraint.class.name.symbol() == super_class {
            let class_name_str = interner::resolve(super_class).unwrap_or_default();
            let dict_param = format!("dict{class_name_str}");
            return Some(JsExpr::Var(dict_param));
        }
    }
    None
}

/// Try to reach a needed superclass via a superclass chain from one of the instance constraints.
/// E.g., if the instance has `Monad m` as a constraint and needs `Functor`, this builds:
/// `dictMonad.Bind1().Apply0().Functor0()`
fn find_superclass_via_chain_from_constraints(
    ctx: &CodegenCtx,
    instance_constraints: &[Constraint],
    super_class: Symbol,
) -> Option<JsExpr> {
    for constraint in instance_constraints {
        let constraint_class = constraint.class.name.symbol();
        let mut chain = Vec::new();
        if find_superclass_chain(ctx, constraint_class, super_class, &mut chain) {
            let class_name_str = interner::resolve(constraint_class).unwrap_or_default();
            let mut expr = JsExpr::Var(format!("dict{class_name_str}"));
            for accessor in &chain {
                expr = JsExpr::App(
                    Box::new(JsExpr::Indexer(
                        Box::new(expr),
                        Box::new(JsExpr::StringLit(accessor.clone())),
                    )),
                    vec![],
                );
            }
            return Some(expr);
        }
    }
    None
}

/// Try to resolve a type class dict for a Record type using the typechecker's
/// full instance resolution (handles RowToList, OrdRecord/EqRecord chains, etc.).
/// Returns None if resolution fails (falls back to simple instance ref).
pub(crate) fn try_resolve_record_dict(
    ctx: &CodegenCtx,
    class_name: Symbol,
    underlying_ty: Option<&crate::typechecker::types::Type>,
) -> Option<JsExpr> {
    use crate::typechecker::types::Type;

    let record_ty = underlying_ty?;
    // Only handle Record types
    if !matches!(record_ty, Type::Record(_, _)) {
        return None;
    }

    // Build combined_registry from ctx.instance_registry + imported modules
    let mut combined_registry: HashMap<(Symbol, Symbol), Vec<(Symbol, Option<Vec<Symbol>>)>> = HashMap::new();
    for (&(class_name, head_name), &inst_name) in &ctx.instance_registry {
        let module_parts = ctx.instance_sources.get(&inst_name)
            .and_then(|s| s.clone());
        combined_registry.entry((class_name.symbol(), head_name.symbol()))
            .or_default()
            .push((inst_name, module_parts));
    }

    // Build all_instances from registry
    let mut all_instances: HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>> = HashMap::new();
    // Local module instances from exports
    for (class_qi, inst_list) in &ctx.exports.instances {
        all_instances.entry(*class_qi).or_default().extend(inst_list.iter().cloned());
    }
    // Imported module instances
    for imp in &ctx.module.imports {
        if let Some(mod_exports) = ctx.registry.lookup(&imp.module.parts) {
            for (class_qi, inst_list) in &mod_exports.instances {
                all_instances.entry(*class_qi).or_default().extend(inst_list.iter().cloned());
            }
        }
    }

    // Build type_aliases
    let mut type_aliases: HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)> = HashMap::new();
    for (qi, (params, body)) in &ctx.exports.type_aliases {
        type_aliases.insert(*qi, (params.clone(), body.clone()));
    }
    for imp in &ctx.module.imports {
        if let Some(mod_exports) = ctx.registry.lookup(&imp.module.parts) {
            for (qi, (params, body)) in &mod_exports.type_aliases {
                type_aliases.entry(*qi).or_insert((params.clone(), body.clone()));
            }
        }
    }

    // Build instance_var_kinds
    let mut instance_var_kinds: HashMap<Symbol, HashMap<TypeVarName, Symbol>> = HashMap::new();
    for (name, kinds) in &ctx.exports.instance_var_kinds {
        instance_var_kinds.insert(*name, kinds.clone());
    }
    for imp in &ctx.module.imports {
        if let Some(mod_exports) = ctx.registry.lookup(&imp.module.parts) {
            for (name, kinds) in &mod_exports.instance_var_kinds {
                instance_var_kinds.entry(*name).or_insert_with(|| kinds.clone());
            }
        }
    }

    let concrete_args = vec![record_ty.clone()];
    let class_name_typed = Qualified::<ClassName>::unqualified(ClassName::new(class_name));
    let inst_name_all_modules = HashMap::new(); // No name collisions expected for record constraints
    let dict_expr = crate::typechecker::check::resolve_dict_expr_from_registry(
        &combined_registry,
        &all_instances,
        &type_aliases,
        &class_name_typed,
        &concrete_args,
        None,
        &instance_var_kinds,
        &inst_name_all_modules,
    )?;

    // Only use the result if it's more than a bare Var (i.e., has constraint applications)
    match &dict_expr {
        crate::typechecker::registry::DictExpr::Var(_, _) => None, // Fall back to simple resolution
        _ => Some(dict_expr_to_js(ctx, &dict_expr)),
    }
}

/// Resolve an instance reference: given a class and head type constructor,
/// find the instance name and generate a JS reference to it.
pub(crate) fn resolve_instance_ref(ctx: &CodegenCtx, class_name: Symbol, head: Symbol) -> JsExpr {
    let key = (ClassName::new(class_name), TypeName::new(head));
    // Check local instance registry first
    if let Some(inst_name) = ctx.instance_registry.get(&key) {
        let inst_js = ident_to_js(*inst_name);
        if ctx.local_names.contains(inst_name) {
            return JsExpr::Var(inst_js.clone());
        }
        // Find the source module by checking which imported module has this (class, head) entry.
        // This avoids collisions from instance_sources when different modules export instances
        // with the same name but for different types (e.g., eqDateTime in Data.DateTime vs
        // Data.DateTime.Instant).
        for imp in &ctx.module.imports {
            if let Some(mod_exports) = ctx.registry.lookup(&imp.module.parts) {
                if mod_exports.instance_registry.get(&key).map(|n| *n == *inst_name).unwrap_or(false) {
                    if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                        return JsExpr::ModuleAccessor(js_mod.clone(), inst_js);
                    }
                }
            }
        }
        // Fallback to instance_sources if no module match found
        if let Some(source) = ctx.instance_sources.get(inst_name) {
            match source {
                None => {
                    return JsExpr::Var(inst_js.clone());
                },
                Some(parts) => {
                    if let Some(js_mod) = ctx.import_map.get(parts) {
                        return JsExpr::ModuleAccessor(js_mod.clone(), inst_js);
                    }
                }
            }
        }
        // Try name_source
        if let Some(source_parts) = ctx.name_source.get(inst_name) {
            if let Some(js_mod) = ctx.import_map.get(source_parts) {
                return JsExpr::ModuleAccessor(js_mod.clone(), inst_js);
            }
        }
        return JsExpr::Var(inst_js);
    }

    // Fallback: look up in all imported module registries
    for imp in &ctx.module.imports {
        if let Some(mod_exports) = ctx.registry.lookup(&imp.module.parts) {
            if let Some(inst_name) = mod_exports.instance_registry.get(&key) {
                let inst_js = ident_to_js(*inst_name);
                if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), inst_js);
                }
                return JsExpr::Var(inst_js);
            }
        }
    }

    // Last resort: synthesize a likely name and try to qualify it
    let class_str = interner::resolve(class_name).unwrap_or_default();
    let head_str = interner::resolve(head).unwrap_or_default();
    let likely_name = format!(
        "{}{}",
        class_str[..1].to_lowercase(),
        &class_str[1..]
    );
    let synthesized = format!("{likely_name}{head_str}");
    let synthesized_sym = interner::intern(&synthesized);
    // Try to find module for the synthesized instance name
    if let Some(Some(parts)) = ctx.instance_sources.get(&synthesized_sym) {
        if let Some(js_mod) = ctx.import_map.get(parts) {
            return JsExpr::ModuleAccessor(js_mod.clone(), synthesized);
        }
    }
    // Also search imported modules
    for (mod_parts, js_mod) in &ctx.import_map {
        if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
            for (_, inst_name) in &mod_exports.instance_registry {
                if interner::resolve(*inst_name).as_deref() == Some(synthesized.as_str()) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), synthesized);
                }
            }
        }
    }
    JsExpr::Var(synthesized)
}

/// Find the local Eq instance name for a given type constructor.
/// Used by constrained Ord derives to reference the corresponding Eq instance.
pub(crate) fn find_local_eq_instance_for_type(ctx: &CodegenCtx, head_type: Option<Symbol>, eq_sym: Symbol) -> Option<String> {
    let head = head_type?;
    // Check instance registry for (Eq, head_type)
    if let Some(inst_name) = ctx.instance_registry.get(&(ClassName::new(eq_sym), TypeName::new(head))) {
        return Some(ident_to_js(*inst_name));
    }
    // Synthesize the name: eqTypeName
    let head_str = interner::resolve(head).unwrap_or_default();
    Some(format!("eq{head_str}"))
}

// ===== Expression translation =====

/// Check if an expression contains any Expr::Wildcard nodes (for section syntax).

pub(crate) fn try_apply_dict(ctx: &CodegenCtx, name: Symbol, base: JsExpr, span: Option<crate::span::Span>) -> Option<JsExpr> {
    try_apply_dict_with_module(ctx, name, base, span, None)
}

pub(crate) fn try_apply_dict_with_module(ctx: &CodegenCtx, name: Symbol, base: JsExpr, span: Option<crate::span::Span>, module_qualifier: Option<Symbol>) -> Option<JsExpr> {
    let scope = ctx.dict_scope.borrow();

    if !scope.is_empty() {
        // First, check if this is a class method — try all classes that define this method
        if let Some(class_entries) = find_class_method_all(ctx, name) {
            for (class_qi, _) in &class_entries {
                // Before using scope-based lookup, check if the resolved_dict_map has a
                // concrete zero-arg instance for this call site. This handles cases like
                // `show(showString)` inside a function with `Show a` in scope, where
                // scope-based lookup would incorrectly return `dictShow`.
                if let Some(mut resolved) = try_apply_resolved_dict_for_class(ctx, &base, span, class_qi.name_symbol()) {
                    // Also apply method-own constraints from scope or resolved_dicts
                    let method_own = find_method_own_constraints(ctx, name, class_qi.name_symbol());
                    for own_class in &method_own {
                        // Try resolved_dicts first (concrete instances like monoidString)
                        let mut found = false;
                        if let Some(dicts) = span.and_then(|s| ctx.resolved_dict_map.get(&s)) {
                            if let Some((_, own_dict_expr)) = dicts.iter().find(|(cn, _)| cn == own_class) {
                                if !matches!(own_dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                                    let own_js = dict_expr_to_js(ctx, own_dict_expr);
                                    resolved = JsExpr::App(Box::new(resolved), vec![own_js]);
                                }
                                found = true;
                            }
                        }
                        // Fallback to scope — try direct match first, then superclass chains.
                        // Direct match avoids resolving e.g. Applicative m when we need
                        // Applicative (ParserT s m), but for method-own constraints like
                        // Monad on `lift`, the dict is only reachable via superclass chain
                        // (e.g., MonadTell -> Monad1()).
                        if !found {
                            if let Some(own_dict) = find_dict_in_scope_direct(ctx, &scope, *own_class) {
                                resolved = JsExpr::App(Box::new(resolved), vec![own_dict]);
                            } else if let Some(own_dict) = find_dict_in_scope(ctx, &scope, *own_class) {
                                resolved = JsExpr::App(Box::new(resolved), vec![own_dict]);
                            }
                        }
                    }
                    return Some(resolved);
                }
                if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, class_qi.name_symbol()) {
                    let mut result = JsExpr::App(Box::new(base), vec![dict_expr]);
                    // Also apply method-own constraints (e.g., eq1 :: forall a. Eq a => ...)
                    // These are constraints on the method's signature beyond the class constraint.
                    let method_own = find_method_own_constraints(ctx, name, class_qi.name_symbol());
                    for own_class in &method_own {
                        // Try resolved_dicts first (concrete instances like monoidString)
                        let mut found = false;
                        if let Some(dicts) = span.and_then(|s| ctx.resolved_dict_map.get(&s)) {
                            if let Some((_, own_dict_expr)) = dicts.iter().find(|(cn, _)| cn == own_class) {
                                if !matches!(own_dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                                    let own_js = dict_expr_to_js(ctx, own_dict_expr);
                                    result = JsExpr::App(Box::new(result), vec![own_js]);
                                }
                                found = true;
                            }
                        }
                        // Fallback to scope — try direct match first, then superclass chains
                        if !found {
                            if let Some(own_dict) = find_dict_in_scope_direct(ctx, &scope, *own_class) {
                                result = JsExpr::App(Box::new(result), vec![own_dict]);
                            } else if let Some(own_dict) = find_dict_in_scope(ctx, &scope, *own_class) {
                                result = JsExpr::App(Box::new(result), vec![own_dict]);
                            }
                        }
                    }
                    return Some(result);
                }
            }
        }

        // Second, check if this is a constrained function (not a class method but has constraints)
        let fn_constraints = find_fn_constraints_with_module(ctx, name, module_qualifier).unwrap_or_default();
        if !fn_constraints.is_empty() {
            let resolved_dicts = span.and_then(|s| ctx.resolved_dict_map.get(&s));

            // First try: resolve ALL from resolved_dict_map
            // Accept concrete zero-arg dicts, App dicts (parameterized instances like
            // monadStateT(dictMonad)), and ConstraintArg dicts (direct constraint refs).
            if let Some(dicts) = resolved_dicts {
                let mut result = base.clone();
                let mut all_resolved = true;
                let mut occ = HashMap::new();
                for class_name in &fn_constraints {
                    // Zero-cost constraints (Row.Cons, Row.Lacks, etc.) — apply empty ()
                    if !ctx.known_runtime_classes.contains(class_name) {
                        result = JsExpr::App(Box::new(result), vec![]);
                        continue;
                    }
                    let nth = occ.entry(*class_name).or_insert(0usize);
                    if let Some(dict_expr) = find_nth_dict(dicts, *class_name, *nth) {
                        *nth += 1;
                        use crate::typechecker::registry::DictExpr;
                        if is_concrete_zero_arg_dict(dict_expr, ctx)
                            || matches!(dict_expr, DictExpr::App(_, _, _))
                            || matches!(dict_expr, DictExpr::ConstraintArg(_))
                        {
                            let js_dict = dict_expr_to_js(ctx, dict_expr);
                            result = JsExpr::App(Box::new(result), vec![js_dict]);
                        } else if let DictExpr::Var(inst_name, _) = dict_expr {
                            // Parameterized instance (e.g., monadStateT) that needs
                            // its own constraint args applied. Try to resolve them.
                            if let Some(constraint_classes) = ctx.instance_constraint_classes.get(inst_name) {
                                let mut inst_result = dict_expr_to_js(ctx, dict_expr);
                                let mut inst_ok = true;
                                for cc in constraint_classes {
                                    if !ctx.known_runtime_classes.contains(cc) {
                                        inst_result = JsExpr::App(Box::new(inst_result), vec![]);
                                    } else if let Some(scope_dict) = find_dict_in_scope(ctx, &scope, *cc) {
                                        inst_result = JsExpr::App(Box::new(inst_result), vec![scope_dict]);
                                    } else {
                                        inst_ok = false;
                                        break;
                                    }
                                }
                                if inst_ok {
                                    result = JsExpr::App(Box::new(result), vec![inst_result]);
                                } else {
                                    all_resolved = false;
                                    break;
                                }
                            } else {
                                all_resolved = false;
                                break;
                            }
                        } else {
                            all_resolved = false;
                            break;
                        }
                    } else {
                        all_resolved = false;
                        break;
                    }
                }
                if all_resolved {
                    return Some(result);
                }
            }

            // Second try: resolve ALL from scope
            {
                let mut result = base.clone();
                let mut all_found = true;
                let mut occ = HashMap::new();
                for class_name in &fn_constraints {
                    // Zero-cost constraints — apply empty ()
                    if !ctx.known_runtime_classes.contains(class_name) {
                        result = JsExpr::App(Box::new(result), vec![]);
                        continue;
                    }
                    let nth = occ.entry(*class_name).or_insert(0usize);
                    if let Some(dict_expr) = find_dict_in_scope_nth(ctx, &scope, *class_name, *nth) {
                        *nth += 1;
                        result = JsExpr::App(Box::new(result), vec![dict_expr]);
                    } else {
                        all_found = false;
                        break;
                    }
                }
                if all_found {
                    return Some(result);
                }
            }

            // Third try: hybrid — for each constraint, try resolved_dict_map first,
            // then scope, then zero-cost. This handles cases where some constraints
            // are concrete (from resolved_dict_map) and others are parametric (from scope).
            {
                let mut result = base.clone();
                let mut all_found = true;
                let mut resolved_occ: HashMap<Symbol, usize> = HashMap::new();
                let mut scope_occ: HashMap<Symbol, usize> = HashMap::new();
                for class_name in &fn_constraints {
                    // Try resolved_dict_map first (concrete instances)
                    let r_nth = resolved_occ.entry(*class_name).or_insert(0usize);
                    let from_resolved = resolved_dicts.and_then(|dicts| {
                        find_nth_dict(dicts, *class_name, *r_nth).and_then(|dict_expr| {
                            if is_concrete_zero_arg_dict(dict_expr, ctx) {
                                Some(dict_expr_to_js(ctx, dict_expr))
                            } else {
                                None
                            }
                        })
                    });
                    if let Some(js_dict) = from_resolved {
                        *r_nth += 1;
                        result = JsExpr::App(Box::new(result), vec![js_dict]);
                    } else {
                        let s_nth = scope_occ.entry(*class_name).or_insert(0usize);
                        if let Some(dict_expr) = find_dict_in_scope_nth(ctx, &scope, *class_name, *s_nth) {
                            *s_nth += 1;
                            // From scope (parametric dict parameter)
                            result = JsExpr::App(Box::new(result), vec![dict_expr]);
                        } else if !ctx.known_runtime_classes.contains(class_name) {
                            // Zero-cost constraint (no runtime dict needed)
                            result = JsExpr::App(Box::new(result), vec![]);
                        } else {
                            all_found = false;
                            break;
                        }
                    }
                }
                if all_found {
                    return Some(result);
                }
            }
        }

        // Third, check if this is an instance with constraints (e.g., monadStateT referenced
        // from applyStateT — both have Monad constraint). Instances are not in all_fn_constraints,
        // they're in instance_constraint_classes.
        // Skip this check if the name resolves to an imported regular function that happens to
        // share its name with a local instance. E.g., instance `decodeForeignObject` in Class.purs
        // vs function `decodeForeignObject` imported from Decoders.purs.
        // Only skip if: (1) name resolves to an imported function, AND (2) the current
        // module has an instance with this same name.
        let has_local_instance_with_name = ctx.exports.instance_registry.values().any(|&inst_sym| inst_sym == name);
        let skip_instance_check = has_local_instance_with_name
            && ctx.name_source.get(&name).map(|parts| *parts != ctx.module_parts).unwrap_or(false);
        if !skip_instance_check {
        if let Some(inst_constraints) = ctx.instance_constraint_classes.get(&name) {
            if !inst_constraints.is_empty() {
                let mut result = base.clone();
                let mut all_found = true;
                let mut occ = HashMap::new();
                for class_name in inst_constraints {
                    let nth = occ.entry(*class_name).or_insert(0usize);
                    if let Some(dict_expr) = find_dict_in_scope_nth(ctx, &scope, *class_name, *nth) {
                        *nth += 1;
                        result = JsExpr::App(Box::new(result), vec![dict_expr]);
                    } else if !ctx.known_runtime_classes.contains(class_name) {
                        // Zero-cost constraint
                        result = JsExpr::App(Box::new(result), vec![]);
                    } else {
                        all_found = false;
                        break;
                    }
                }
                if all_found {
                    return Some(result);
                }
            }
        }
        } // end !is_imported_function
    }

    // Drop the scope borrow before trying resolved_dict_map
    drop(scope);

    // At module level (scope is empty), try to resolve instance constraints
    // using resolved_dict_map. This handles cases like `gsep(gsepStringRoute)`
    // where `gsepStringRoute` has instance constraints that need dict application.
    if let Some(inst_constraints) = ctx.instance_constraint_classes.get(&name) {
        if !inst_constraints.is_empty() {
            if let Some(s) = span {
                if let Some(dicts) = ctx.resolved_dict_map.get(&s) {
                    let mut result = base.clone();
                    let mut all_found = true;
                    for class_name in inst_constraints {
                        if let Some((_, dict_expr)) = dicts.iter().find(|(cn, _)| *cn == *class_name) {
                            if !matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                                let dict_js = dict_expr_to_js(ctx, dict_expr);
                                result = JsExpr::App(Box::new(result), vec![dict_js]);
                            }
                        } else if !ctx.known_runtime_classes.contains(class_name) {
                            // Zero-cost constraint — skip
                        } else {
                            all_found = false;
                            break;
                        }
                    }
                    if all_found {
                        return Some(result);
                    }
                }
            }
        }
    }

    // Fallback: try resolved_dict_map for module-level dict resolution
    try_apply_resolved_dict(ctx, name, base.clone(), span, module_qualifier)
}

/// Try to resolve a class method call using the resolved_dict_map for a specific class.
/// Returns Some if the resolved dict is:
/// - A concrete zero-arg instance (showString, eqInt), OR
/// - A ConstraintArg (reference to a specific constraint parameter)
pub(crate) fn try_apply_resolved_dict_for_class(ctx: &CodegenCtx, base: &JsExpr, span: Option<crate::span::Span>, class_name: Symbol) -> Option<JsExpr> {
    let span = span?;
    let dicts = ctx.resolved_dict_map.get(&span)?;
    if let Some((_, dict_expr)) = dicts.iter().find(|(cn, _)| *cn == class_name) {
        // Handle ConstraintArg — this is a resolved constraint parameter reference
        if matches!(dict_expr, crate::typechecker::registry::DictExpr::ConstraintArg(_)) {
            let js_dict = dict_expr_to_js(ctx, dict_expr);
            return Some(JsExpr::App(Box::new(base.clone()), vec![js_dict]));
        }
        // Handle App instances (like eqArray(dictEq)): the resolved dict is more
        // specific than what scope-based lookup would return. For example, in
        // `eq1Array`'s method `eq1 = eq`, the resolved dict for `eq` is
        // `App(eqArray, [ConstraintArg(0)])` → `eqArray(dictEq)`, while
        // scope-based lookup would incorrectly return just `dictEq`.
        if matches!(dict_expr, crate::typechecker::registry::DictExpr::App(_, _, _)) {
            let js_dict = dict_expr_to_js(ctx, dict_expr);
            return Some(JsExpr::App(Box::new(base.clone()), vec![js_dict]));
        }
        // Only use the resolved dict if it's a concrete zero-arg instance
        // (like showString, eqInt).
        if !is_concrete_zero_arg_dict(dict_expr, ctx) {
            // The resolved dict is a parameterized instance (e.g., monadTellWriterT)
            // that the typechecker couldn't fully resolve sub-constraints for.
            // Try to resolve the constraint args from scope and resolved_dicts.
            if let crate::typechecker::registry::DictExpr::Var(inst_name, _) = dict_expr {
                if let Some(constraint_classes) = ctx.instance_constraint_classes.get(inst_name) {
                    let scope = ctx.dict_scope.borrow();
                    let mut result = dict_expr_to_js(ctx, dict_expr);
                    let mut all_applied = true;
                    for constraint_class in constraint_classes {
                        if !ctx.known_runtime_classes.contains(constraint_class) {
                            // Phantom constraint — apply ()
                            result = JsExpr::App(Box::new(result), vec![]);
                            continue;
                        }
                        // Try resolved_dicts first for concrete instances
                        let mut found = false;
                        if let Some(all_dicts) = ctx.resolved_dict_map.get(&span) {
                            if let Some((_, sub_dict_expr)) = all_dicts.iter().find(|(cn, _)| cn == constraint_class) {
                                if is_concrete_zero_arg_dict(sub_dict_expr, ctx)
                                    || matches!(sub_dict_expr, crate::typechecker::registry::DictExpr::App(_, _, _))
                                {
                                    let sub_js = dict_expr_to_js(ctx, sub_dict_expr);
                                    result = JsExpr::App(Box::new(result), vec![sub_js]);
                                    found = true;
                                }
                            }
                        }
                        if !found {
                            // Try scope for constraint parameters (e.g., dictMonad)
                            if let Some(scope_dict) = find_dict_in_scope(ctx, &scope, *constraint_class) {
                                result = JsExpr::App(Box::new(result), vec![scope_dict]);
                                found = true;
                            }
                        }
                        if !found {
                            all_applied = false;
                            break;
                        }
                    }
                    if all_applied {
                        return Some(JsExpr::App(Box::new(base.clone()), vec![result]));
                    }
                }
            }
            return None;
        }
        let js_dict = dict_expr_to_js(ctx, dict_expr);
        return Some(JsExpr::App(Box::new(base.clone()), vec![js_dict]));
    }
    None
}

/// Check if a DictExpr is a fully concrete zero-argument instance.
/// Returns true only for simple DictExpr::Var instances that don't need dict arguments,
/// like `showString`, `eqInt`, etc. Returns false for parameterized instances like
/// `eqArray` (which needs `dictEq`) or applied instances like `App(eqArray, [dictEq])`.
pub(crate) fn is_concrete_zero_arg_dict(dict: &crate::typechecker::registry::DictExpr, ctx: &CodegenCtx) -> bool {
    use crate::typechecker::registry::DictExpr;
    match dict {
        DictExpr::Var(name, _) => {
            // Check if this is an instance with NO constraints (zero-arg)
            if let Some(constraints) = ctx.instance_constraint_classes.get(name) {
                return constraints.is_empty();
            }
            // Not in instance_constraint_classes — check if it looks like a dict parameter
            let name_str = interner::resolve(*name).unwrap_or_default();
            !name_str.starts_with("dict")
        }
        DictExpr::App(_, _, _) => false, // Applied instances are not zero-arg
        DictExpr::ConstraintArg(_) => false, // Constraint param, not a concrete instance
        DictExpr::InlineIsSymbol(_) => true, // Inline IsSymbol is fully concrete
        DictExpr::InlineReflectable(_) => true, // Inline Reflectable is fully concrete
        DictExpr::ZeroCost => true, // Zero-cost constraint, no actual dict needed
    }
}

/// Try to resolve a class method or constrained function call using the pre-resolved dict map.
/// This handles module-level calls where dict_scope is empty but the typechecker resolved
/// the concrete instance dict. Uses expression span for unambiguous lookup.
pub(crate) fn try_apply_resolved_dict(ctx: &CodegenCtx, name: Symbol, base: JsExpr, span: Option<crate::span::Span>, module_qualifier: Option<Symbol>) -> Option<JsExpr> {
    let span = span?;

    // Look up pre-resolved dicts at this expression span.
    // The typechecker stores resolved dicts keyed by expression span,
    // so this is unambiguous regardless of name collisions.
    let dicts = ctx.resolved_dict_map.get(&span)?;

    if dicts.is_empty() {
        return None;
    }

    // Check if this is a class method — if so, apply only the matching class dict
    // and any method-own constraints that have resolved dicts available.
    if let Some(class_entries) = ctx.all_class_methods.get(&name) {
        for (class_qi, _) in class_entries {
            let class_name = class_qi.name_symbol();
            if let Some((_, dict_expr)) = dicts.iter().find(|(cn, _)| *cn == class_name) {
                if matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                    return Some(JsExpr::App(Box::new(base), vec![]));
                }
                let js_dict = dict_expr_to_js(ctx, dict_expr);
                let mut result = JsExpr::App(Box::new(base), vec![js_dict]);

                // Also apply method-own constraints if their dicts are in resolved_dict_map
                let method_own = find_method_own_constraints(ctx, name, class_name);
                for own_class in &method_own {
                    if let Some((_, own_dict_expr)) = dicts.iter().find(|(cn, _)| cn == own_class) {
                        if matches!(own_dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                            result = JsExpr::App(Box::new(result), vec![]);
                        } else {
                            let own_js = dict_expr_to_js(ctx, own_dict_expr);
                            result = JsExpr::App(Box::new(result), vec![own_js]);
                        }
                    }
                }
                return Some(result);
            }
        }
    }

    // For constrained functions, apply dicts in the order of their signature constraints.
    // This ensures the right dict is applied for each constraint parameter.
    let fn_constraints = find_fn_constraints_with_module(ctx, name, module_qualifier);
    if let Some(ref fn_constraints) = fn_constraints {
    if !fn_constraints.is_empty() {
        let mut result = base;
        // Extract head type from existing resolved dicts for resolving missing ones.
        // For a function like abs :: Ord a => Ring a => a -> a, if Ord Int is resolved,
        // we know the head type is Int and can resolve Ring Int from the instance registry.
        let head_type: Option<Symbol> = dicts.iter().find_map(|(_, dict_expr)| {
            extract_head_from_dict_expr(dict_expr, ctx)
        });
        // Track occurrence counts per class for duplicate constraints
        // (e.g., MyClass a => MyClass (Box a) => should use 0th and 1st MyClass dicts)
        let mut occ: HashMap<Symbol, usize> = HashMap::new();
        for class_name in fn_constraints {
            let nth = occ.entry(*class_name).or_insert(0);
            if let Some(dict_expr) = find_nth_dict(dicts, *class_name, *nth) {
                *nth += 1;
                if matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost)
                    || !ctx.known_runtime_classes.contains(class_name)
                {
                    // Zero-cost constraint: either explicitly marked ZeroCost or the class
                    // has no methods/superclasses (e.g., AddNat, Prim.Row.Cons).
                    result = JsExpr::App(Box::new(result), vec![]);
                    continue;
                }
                let js_dict = dict_expr_to_js(ctx, dict_expr);
                result = JsExpr::App(Box::new(result), vec![js_dict]);
            } else if let Some(head) = head_type {
                // Check if this constraint is a superclass of another constraint
                // that IS resolved in dicts. If so, it's satisfied through the parent
                // dict's superclass accessor, not as a separate dict parameter.
                let class_name_str = crate::interner::resolve(*class_name).unwrap_or_default();
                let is_superclass_of_resolved = dicts.iter().any(|(resolved_class, _)| {
                    let ri_class = crate::interner::resolve(*resolved_class)
                        .map(|s| crate::interner::intern(&s))
                        .unwrap_or(*resolved_class);
                    if let Some((_, supers)) = ctx.all_class_superclasses.get(&ri_class) {
                        supers.iter().any(|(sc, _)| {
                            sc.name.resolve().map_or(false, |s| s == class_name_str)
                        })
                    } else {
                        false
                    }
                });
                if is_superclass_of_resolved {
                    continue;
                }
                // Try to resolve from instance registry — but only if the instance
                // is a zero-arg instance (no sub-dicts needed). Parameterized instances
                // like ordArray(dictOrd) would be applied without arguments, crashing.
                // This guards against head_type from one type variable being used for
                // a different constraint's type variable (e.g., Foldable f => Ord a =>).
                if let Some(inst_name) = ctx.instance_registry.get(&(ClassName::new(*class_name), TypeName::new(head))).filter(|inst| {
                    ctx.instance_constraint_classes.get(inst).map_or(true, |cs| cs.is_empty())
                }) {
                    let js_name = ident_to_js(*inst_name);
                    let ext_name = export_name(*inst_name);
                    let js_dict = if ctx.local_names.contains(inst_name) {
                        JsExpr::Var(js_name)
                    } else if let Some(source_parts) = ctx.instance_sources.get(inst_name) {
                        match source_parts {
                            None => JsExpr::Var(js_name),
                            Some(parts) => {
                                if let Some(js_mod) = ctx.import_map.get(parts) {
                                    JsExpr::ModuleAccessor(js_mod.clone(), ext_name)
                                } else {
                                    JsExpr::Var(js_name)
                                }
                            }
                        }
                    } else {
                        JsExpr::Var(js_name)
                    };
                    result = JsExpr::App(Box::new(result), vec![js_dict]);
                } else if !ctx.known_runtime_classes.contains(class_name) {
                    // Zero-cost constraint (e.g. Coercible) — strip dict wrapper with empty call
                    result = JsExpr::App(Box::new(result), vec![]);
                }
            } else if !ctx.known_runtime_classes.contains(class_name) {
                // Zero-cost constraint with no head type info — strip dict wrapper
                result = JsExpr::App(Box::new(result), vec![]);
            }
        }
        return Some(result);
    }
    // fn_constraints is Some(empty) — confirmed no constraints, skip fallback
    return None;
    }

    // Apply all resolved dicts at this span in order.
    // This handles: constrained functions, let-bound constrained functions,
    // and class methods where the class name didn't match all_class_methods
    // (e.g. methods from support modules with different symbol interning).
    // Skip dicts that belong to return-type constraints — those are handled
    // by the RT_DICT mechanism in the App handler after enough args are applied.
    let rt_class_names: HashSet<Symbol> = ctx.exports.return_type_constraints
        .get(&unqualified_value_sym(name))
        .map(|cs| cs.iter().map(|(c, _)| c.name_symbol()).collect())
        .unwrap_or_default();
    let mut result = base;
    for (class_name, dict_expr) in dicts {
        if rt_class_names.contains(class_name) {
            continue; // handled by RT_DICT in App
        }
        if matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
            result = JsExpr::App(Box::new(result), vec![]);
        } else {
            let js_dict = dict_expr_to_js(ctx, dict_expr);
            result = JsExpr::App(Box::new(result), vec![js_dict]);
        }
    }
    Some(result)
}

/// Extract the head type constructor from a DictExpr by looking up the instance
/// in the instance registry. E.g., ordInt → Int, eqArray → Array.
pub(crate) fn extract_head_from_dict_expr(dict: &crate::typechecker::registry::DictExpr, ctx: &CodegenCtx) -> Option<Symbol> {
    use crate::typechecker::registry::DictExpr;
    match dict {
        DictExpr::Var(name, _) => {
            // Look through instance_registry for any entry whose value matches this name
            for ((_, head), inst) in &ctx.instance_registry {
                if inst == name {
                    return Some(head.symbol());
                }
            }
            None
        }
        DictExpr::App(name, _, _) => {
            for ((_, head), inst) in &ctx.instance_registry {
                if inst == name {
                    return Some(head.symbol());
                }
            }
            None
        }
        _ => None,
    }
}

/// Convert a DictExpr from the typechecker into a JS expression.
pub(crate) fn dict_expr_to_js(ctx: &CodegenCtx, dict: &crate::typechecker::registry::DictExpr) -> JsExpr {
    use crate::typechecker::registry::DictExpr;
    match dict {
        DictExpr::Var(name, module_hint) => {
            // Check if this instance name was deduplicated (collision avoidance)
            let js_name = if let Some(deduped) = ctx.deduped_instance_names.borrow().get(name) {
                deduped.clone()
            } else {
                ident_to_js(*name)
            };
            let ext_name = export_name(*name);
            // Check if local or imported.
            // Priority order:
            // 1. Local names (defined in this module)
            // 2. Module hint from typechecker (disambiguates colliding instance names
            //    like bindProxy in both Control.Bind and Pipes.Internal)
            // 3. instance_sources / name_source lookups
            // 4. Fallback: search imported modules
            if ctx.local_names.contains(name) {
                JsExpr::Var(js_name)
            } else if let Some(hint_parts) = module_hint {
                // Use the module hint from the typechecker's instance resolution.
                // This MUST come before instance_sources because instance_sources
                // uses unqualified symbol keys and or_insert, so when two modules
                // export instances with the same name, instance_sources has whichever
                // was registered first — not necessarily the correct one.
                // Re-intern hint parts to match import_map Symbol IDs.
                let hint_reinterned: Vec<crate::interner::Symbol> = hint_parts.iter()
                    .map(|s| crate::interner::resolve(*s)
                        .map(|r| crate::interner::intern(&r))
                        .unwrap_or(*s))
                    .collect();
                if let Some(js_mod) = ctx.import_map.get(&hint_reinterned).or_else(|| ctx.import_map.get(hint_parts)) {
                    JsExpr::ModuleAccessor(js_mod.clone(), ext_name)
                } else if let Some(source) = ctx.instance_sources.get(name) {
                    match source {
                        None => JsExpr::Var(js_name),
                        Some(parts) => {
                            if let Some(js_mod) = ctx.import_map.get(parts) {
                                JsExpr::ModuleAccessor(js_mod.clone(), ext_name)
                            } else {
                                JsExpr::Var(js_name)
                            }
                        }
                    }
                } else {
                    JsExpr::Var(js_name)
                }
            } else if let Some(source) = ctx.instance_sources.get(name) {
                match source {
                    None => {
                        JsExpr::Var(js_name)
                    },
                    Some(parts) => {
                        if let Some(js_mod) = ctx.import_map.get(parts) {
                            JsExpr::ModuleAccessor(js_mod.clone(), ext_name)
                        } else {
                            JsExpr::Var(js_name)
                        }
                    }
                }
            } else if let Some(source_parts) = ctx.name_source.get(name) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    JsExpr::ModuleAccessor(js_mod.clone(), ext_name)
                } else {
                    JsExpr::Var(js_name)
                }
            } else {
                // Fallback: search imported modules for this instance name
                let mut found = None;
                for (mod_parts, js_mod) in &ctx.import_map {
                    if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
                        for (_, inst_name) in &mod_exports.instance_registry {
                            if *inst_name == *name {
                                found = Some(JsExpr::ModuleAccessor(js_mod.clone(), ext_name.clone()));
                                break;
                            }
                        }
                        if found.is_some() { break; }
                        if mod_exports.values.contains_key(&unqualified_value_sym(*name)) {
                            found = Some(JsExpr::ModuleAccessor(js_mod.clone(), ext_name.clone()));
                            break;
                        }
                    }
                }
                found.unwrap_or(JsExpr::Var(js_name))
            }
        }
        DictExpr::App(name, sub_dicts, module_hint) => {
            let base = dict_expr_to_js(ctx, &DictExpr::Var(*name, module_hint.clone()));
            let mut result = base;

            // Look up the instance's constraint list to interleave phantom () calls.
            // sub_dicts only contains runtime dict args, but the instance function
            // also has function() wrappers for phantom (type-level) constraints.
            if let Some(constraint_classes) = ctx.instance_constraint_classes.get(name) {
                let mut sub_idx = 0;
                for class_sym in constraint_classes {
                    if ctx.known_runtime_classes.contains(class_sym) {
                        // Runtime constraint — apply next sub_dict
                        if sub_idx < sub_dicts.len() {
                            let mut sub_js = dict_expr_to_js(ctx, &sub_dicts[sub_idx]);
                            // Runtime check: verify sub-dict is an object before passing
                            if ctx.runtime_checks {
                                let inst_name = crate::interner::resolve(*name).unwrap_or_default();
                                let class_str = crate::interner::resolve(*class_sym).unwrap_or_default();
                                let location = format!("{}.sub_dict {}({})", ctx.module_name, inst_name, class_str);
                                sub_js = JsExpr::App(
                                    Box::new(JsExpr::Var("$check".to_string())),
                                    vec![
                                        sub_js,
                                        JsExpr::StringLit("object".to_string()),
                                        JsExpr::StringLit(location),
                                    ],
                                );
                                ctx.needs_runtime_check.set(true);
                            }
                            result = JsExpr::App(Box::new(result), vec![sub_js]);
                            sub_idx += 1;
                        }
                    } else {
                        // Phantom constraint — apply ()
                        result = JsExpr::App(Box::new(result), vec![]);
                    }
                }
                // Apply any remaining sub_dicts (shouldn't happen normally)
                while sub_idx < sub_dicts.len() {
                    let sub_js = dict_expr_to_js(ctx, &sub_dicts[sub_idx]);
                    result = JsExpr::App(Box::new(result), vec![sub_js]);
                    sub_idx += 1;
                }
            } else {
                // No constraint info — fall back to applying all sub_dicts directly
                for sub in sub_dicts {
                    let sub_js = dict_expr_to_js(ctx, sub);
                    result = JsExpr::App(Box::new(result), vec![sub_js]);
                }
            }
            // Runtime check: verify the fully-applied instance produces a valid dict object
            if ctx.runtime_checks {
                let inst_name = crate::interner::resolve(*name).unwrap_or_default();
                let location = format!("{}.dict_app {}", ctx.module_name, inst_name);
                result = JsExpr::App(
                    Box::new(JsExpr::Var("$check".to_string())),
                    vec![
                        result,
                        JsExpr::StringLit("object".to_string()),
                        JsExpr::StringLit(location),
                    ],
                );
                ctx.needs_runtime_check.set(true);
            }
            result
        }
        DictExpr::ConstraintArg(idx) => {
            // Look up the i-th constraint parameter in the current dict scope
            let scope = ctx.dict_scope.borrow();
            if let Some((_, param_name)) = scope.get(*idx) {
                JsExpr::Var(param_name.clone())
            } else {
                // Fallback: shouldn't happen in practice
                JsExpr::Var(format!("__constraint_{idx}"))
            }
        }
        DictExpr::InlineIsSymbol(label) => {
            // Generate inline IsSymbol dictionary: { reflectSymbol: function() { return "label"; } }
            JsExpr::ObjectLit(vec![
                ("reflectSymbol".to_string(), JsExpr::Function(
                    None,
                    vec![],
                    vec![JsStmt::Return(JsExpr::StringLit(label.clone()))],
                )),
            ])
        }
        DictExpr::InlineReflectable(val) => {
            use crate::typechecker::registry::ReflectableValue;
            let return_expr = match val {
                ReflectableValue::String(s) => JsExpr::StringLit(s.clone()),
                ReflectableValue::Int(n) => JsExpr::IntLit(*n),
                ReflectableValue::Boolean(b) => JsExpr::BoolLit(*b),
                ReflectableValue::Ordering(name) => {
                    // Data_Ordering.LT.value, Data_Ordering.GT.value, Data_Ordering.EQ.value
                    JsExpr::Indexer(
                        Box::new(JsExpr::Indexer(
                            Box::new(JsExpr::Var("Data_Ordering".to_string())),
                            Box::new(JsExpr::StringLit(name.clone())),
                        )),
                        Box::new(JsExpr::StringLit("value".to_string())),
                    )
                }
            };
            JsExpr::ObjectLit(vec![
                ("reflectType".to_string(), JsExpr::Function(
                    None,
                    vec!["v".to_string()],
                    vec![JsStmt::Return(return_expr)],
                )),
            ])
        }
        DictExpr::ZeroCost => {
            // Should not be reached — ZeroCost dicts are handled specially at call sites
            JsExpr::Var("undefined".to_string())
        }
    }
}

/// Find all class entries for a method name (a method may exist in multiple classes).
pub(crate) fn find_class_method_all(ctx: &CodegenCtx, method_name: Symbol) -> Option<Vec<(Qualified<ClassName>, Vec<crate::names::TypeVarName>)>> {
    ctx.all_class_methods.get(&method_name).cloned()
}

/// Find class method info for a name (returns first matching class).
/// Find a class method's own constraints — constraints on the method's signature
/// that are NOT the class constraint itself. For example, `eq1 :: forall a. Eq a => ...`
/// has own constraint `Eq` (while the class constraint is `Eq1`).
pub(crate) fn find_method_own_constraints(ctx: &CodegenCtx, method_name: Symbol, _class_name: Symbol) -> Vec<Symbol> {
    let method_qi = unqualified_value_sym(method_name);
    // Check local exports first
    if let Some(constraints) = ctx.exports.method_own_constraints.get(&method_qi) {
        return constraints.iter().map(|c| c.symbol()).collect();
    }
    // Check registry modules
    for (_, mod_exports) in ctx.registry.iter_all() {
        if let Some(constraints) = mod_exports.method_own_constraints.get(&method_qi) {
            return constraints.iter().map(|c| c.symbol()).collect();
        }
    }
    vec![]
}

/// Find constraint class names for a function (non-class-method).
/// When `module_qualifier` is provided, look up constraints from that specific module's
/// exports to avoid collisions between same-named functions from different modules
/// (e.g., Data.Set.union :: Ord a => vs Data.HashMap.union :: Hashable k =>).
pub(crate) fn find_fn_constraints_with_module(ctx: &CodegenCtx, name: Symbol, module_qualifier: Option<Symbol>) -> Option<Vec<Symbol>> {
    // Don't apply to class methods (handled separately) — but only if not locally defined
    // as a regular function (e.g., local `discard` shadows imported class method `discard`)
    if ctx.all_class_methods.contains_key(&name) && !ctx.all_fn_constraints.borrow().contains_key(&name) {
        return Some(vec![]);
    }
    // When a module qualifier is provided, look up constraints from that specific module.
    // This avoids incorrect constraint resolution when multiple modules export the same
    // function name with different constraints (e.g., Data.Set.union :: Ord vs Data.HashMap.union :: Hashable).
    if let Some(mod_sym) = module_qualifier {
        let mod_str = crate::interner::resolve(mod_sym).unwrap_or_default();
        // Resolve module alias through CST imports: `import X.Y.Z as Alias` → "Alias" → X.Y.Z parts
        let full_mod_parts: Option<Vec<crate::interner::Symbol>> = ctx.module.imports.iter().find_map(|imp| {
            if let Some(ref qualified) = imp.qualified {
                // `import X.Y.Z as Alias` — qualified is "Alias"
                let alias_name = qualified.parts.iter()
                    .map(|s| crate::interner::resolve(*s).unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(".");
                if alias_name == mod_str {
                    return Some(imp.module.parts.clone());
                }
            }
            // Direct import (no alias): module name matches
            let imp_name = imp.module.parts.iter()
                .map(|s| crate::interner::resolve(*s).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".");
            if imp_name == mod_str {
                return Some(imp.module.parts.clone());
            }
            None
        });
        if let Some(parts) = full_mod_parts {
            if let Some(mod_exports) = ctx.registry.lookup(&parts) {
                let val_qi = unqualified_value_sym(name);
                if let Some(constraints) = mod_exports.signature_constraints.get(&val_qi) {
                    let ri = |s: crate::interner::Symbol| -> crate::interner::Symbol {
                        crate::interner::resolve(s)
                            .map(|r| crate::interner::intern(&r))
                            .unwrap_or(s)
                    };
                    return Some(constraints.iter().map(|(c, _)| ri(c.name_symbol())).collect());
                }
                // Module resolved but function not in signature_constraints.
                // Check if the module actually exports this value — if so, it truly has
                // no constraints and we should return empty to avoid name collisions.
                // If not exported, fall through to global map (might be re-exported).
                let has_value = mod_exports.values.contains_key(&val_qi)
                    || mod_exports.class_methods.contains_key(&val_qi);
                if has_value {
                    return Some(vec![]);
                }
            }
        }
    }
    // For unqualified names: check if this is a local let/where binding first.
    // Local let bindings always shadow imported functions with the same name.
    // Without this check, a local `clamp :: Number -> Number` could pick up
    // `Data.Ord.clamp :: Ord a => ...` constraints via name_source.
    if module_qualifier.is_none() && ctx.local_bindings.borrow().contains(&name) {
        let fn_constraints = ctx.all_fn_constraints.borrow();
        if let Some(constraints) = fn_constraints.get(&name) {
            return Some(constraints.clone());
        }
        // Local binding with no constraint entry → no constraints
        return Some(vec![]);
    }

    // When no module qualifier is provided, try to determine the source module
    // from name_source (for unqualified imports like `import Data.Array (fold)`).
    // This prevents using constraints from a different module that exports the same name
    // (e.g., Data.Foldable.fold has [Foldable, Monoid] but Data.Array.fold has just [Monoid]).
    if module_qualifier.is_none() {
        if let Some(source_parts) = ctx.name_source.get(&name) {
            if let Some(mod_exports) = ctx.registry.lookup(source_parts) {
                let val_qi = unqualified_value_sym(name);
                if let Some(constraints) = mod_exports.signature_constraints.get(&val_qi) {
                    let ri = |s: crate::interner::Symbol| -> crate::interner::Symbol {
                        crate::interner::resolve(s)
                            .map(|r| crate::interner::intern(&r))
                            .unwrap_or(s)
                    };
                    return Some(constraints.iter().map(|(c, _)| ri(c.name_symbol())).collect());
                }
                // Module resolved via name_source but function not in signature_constraints.
                // Check if the module actually exports this value — if so, it truly has
                // no constraints. Only return empty if the value is confirmed exported.
                let has_value = mod_exports.values.contains_key(&val_qi)
                    || mod_exports.class_methods.contains_key(&val_qi);
                if has_value {
                    return Some(vec![]);
                }
            }
        }
    }
    ctx.all_fn_constraints.borrow().get(&name).cloned()
}

/// Find a dict expression for a given class name in the current scope.
/// When `direct_only` is true, only return direct matches (no superclass chains).
/// This is used for method-own constraints where superclass chains can resolve
/// to the wrong type's instance (e.g., Applicative m instead of Applicative (ParserT s m)).
pub(crate) fn find_dict_in_scope(ctx: &CodegenCtx, scope: &[(Symbol, String)], class_name: Symbol) -> Option<JsExpr> {
    find_dict_in_scope_inner(ctx, scope, class_name, false)
}

pub(crate) fn find_dict_in_scope_direct(ctx: &CodegenCtx, scope: &[(Symbol, String)], class_name: Symbol) -> Option<JsExpr> {
    find_dict_in_scope_inner(ctx, scope, class_name, true)
}

fn find_dict_in_scope_inner(ctx: &CodegenCtx, scope: &[(Symbol, String)], class_name: Symbol, direct_only: bool) -> Option<JsExpr> {
    // Direct match (skip empty-name placeholders for zero-cost constraints)
    for (scope_class, dict_param) in scope.iter().rev() {
        if *scope_class == class_name && !dict_param.is_empty() {
            // Mark return-type dicts as used
            if ctx.return_type_dict_params.borrow().contains(dict_param) {
                ctx.used_return_type_dicts.borrow_mut().insert(dict_param.clone());
            }
            return Some(JsExpr::Var(dict_param.clone()));
        }
    }

    if direct_only {
        return None;
    }

    // Superclass chain: e.g., dictApplicative["Apply0"]()["Functor0"]()
    // Prefer the most recent scope entry (iterating .rev()), with a fallback
    // to shorter chains only when the depth difference is significant (>=2).
    // This handles the common case where method-level dict params (more recent)
    // should be preferred over instance-level constraints (older), even when
    // the instance constraint has a shorter superclass chain.
    // E.g., in `traverse` of `Traversable (NonEmpty f)`:
    //   - dictTraversable → Functor0 (depth 1, instance-level)
    //   - dictApplicative → Apply0 → Functor0 (depth 2, method-level)
    //   The method-level path (depth 2) is correct because it's the Functor for `m`,
    //   not `f`. Taking the most recent scope entry first ensures this.
    let mut best: Option<(JsExpr, usize, String)> = None;
    for (scope_class, dict_param) in scope.iter().rev() {
        if dict_param.is_empty() { continue; } // Skip zero-cost placeholders
        let mut accessors = Vec::new();
        if find_superclass_chain(ctx, *scope_class, class_name, &mut accessors) {
            let depth = accessors.len();
            let should_use = match &best {
                None => true,
                // Only replace the current best if the new chain is significantly shorter
                // (depth diff >= 2). This prevents instance constraints with shorter chains
                // from overriding method-level params with slightly longer chains.
                Some((_, best_depth, _)) => *best_depth >= depth + 2,
            };
            if should_use {
                let mut expr = JsExpr::Var(dict_param.clone());
                for accessor in &accessors {
                    // Runtime check: verify accessor function exists on dict before calling
                    if ctx.runtime_checks {
                        // $check(dict["Accessor0"], "function", "location") before calling it
                        let accessor_field = JsExpr::Indexer(
                            Box::new(expr.clone()),
                            Box::new(JsExpr::StringLit(accessor.clone())),
                        );
                        let class_name_str = crate::interner::resolve(class_name).unwrap_or_default();
                        let location = format!("{}.superclass {}.{}", ctx.module_name, dict_param, accessor);
                        // Wrap: (function() { $check(dict["A0"], "function", loc); return dict["A0"](); })()
                        expr = JsExpr::App(
                            Box::new(JsExpr::Function(
                                None,
                                vec![],
                                vec![
                                    JsStmt::Expr(JsExpr::App(
                                        Box::new(JsExpr::Var("$check".to_string())),
                                        vec![
                                            accessor_field,
                                            JsExpr::StringLit("function".to_string()),
                                            JsExpr::StringLit(location.clone()),
                                        ],
                                    )),
                                    JsStmt::VarDecl(
                                        "$_r".to_string(),
                                        Some(JsExpr::App(
                                            Box::new(JsExpr::Indexer(
                                                Box::new(expr),
                                                Box::new(JsExpr::StringLit(accessor.clone())),
                                            )),
                                            vec![],
                                        )),
                                    ),
                                    JsStmt::Expr(JsExpr::App(
                                        Box::new(JsExpr::Var("$check".to_string())),
                                        vec![
                                            JsExpr::Var("$_r".to_string()),
                                            JsExpr::StringLit("object".to_string()),
                                            JsExpr::StringLit(format!("{} result of {}", class_name_str, location)),
                                        ],
                                    )),
                                    JsStmt::Return(JsExpr::Var("$_r".to_string())),
                                ],
                            )),
                            vec![],
                        );
                        ctx.needs_runtime_check.set(true);
                    } else {
                        expr = JsExpr::App(
                            Box::new(JsExpr::Indexer(
                                Box::new(expr),
                                Box::new(JsExpr::StringLit(accessor.clone())),
                            )),
                            vec![],
                        );
                    }
                }
                best = Some((expr, depth, dict_param.clone()));
            }
        }
    }
    if let Some((expr, _, dict_param)) = best {
        // Mark return-type dicts as used (via superclass chain)
        if ctx.return_type_dict_params.borrow().contains(&dict_param) {
            ctx.used_return_type_dicts.borrow_mut().insert(dict_param);
        }
        return Some(expr);
    }

    None
}

/// Find the nth occurrence of class_name in a dicts list (for duplicate constraints like Newtype t a => Newtype s b =>).
pub(crate) fn find_nth_dict<'a>(dicts: &'a [(Symbol, crate::typechecker::registry::DictExpr)], class_name: Symbol, nth: usize) -> Option<&'a crate::typechecker::registry::DictExpr> {
    let mut count = 0;
    for (cn, de) in dicts {
        if *cn == class_name {
            if count == nth {
                return Some(de);
            }
            count += 1;
        }
    }
    None
}

/// Like `find_dict_in_scope` but finds the nth occurrence of the class (for duplicate constraints).
pub(crate) fn find_dict_in_scope_nth(ctx: &CodegenCtx, scope: &[(Symbol, String)], class_name: Symbol, nth: usize) -> Option<JsExpr> {
    // Direct matches
    let mut count = 0;
    for (scope_class, dict_param) in scope.iter().rev() {
        if *scope_class == class_name && !dict_param.is_empty() {
            if count == nth {
                if ctx.return_type_dict_params.borrow().contains(dict_param) {
                    ctx.used_return_type_dicts.borrow_mut().insert(dict_param.clone());
                }
                return Some(JsExpr::Var(dict_param.clone()));
            }
            count += 1;
        }
    }
    // For nth == 0, also try superclass chains (same as find_dict_in_scope)
    if nth == 0 {
        return find_dict_in_scope(ctx, scope, class_name);
    }
    None
}

/// Find superclass accessor name: if `to_class` is a superclass of `from_class`,
/// return the accessor name (e.g., "Applicative0") to get the sub-dict.
/// Returns None if not a direct superclass.
/// Find the full chain of superclass accessors from `from_class` to `to_class`.
/// E.g., Applicative → Functor produces ["Apply0", "Functor0"].
/// Returns true if a chain was found, with accessors appended to `chain`.
pub(crate) fn find_superclass_chain(ctx: &CodegenCtx, from_class: Symbol, to_class: Symbol, chain: &mut Vec<String>) -> bool {
    if from_class == to_class {
        return true;
    }
    // Check local module's class_superclasses first, then fall back to global
    let local_key = unqualified_class_sym(from_class);
    let supers = if let Some((_, supers)) = ctx.exports.class_superclasses.get(&local_key) {
        supers.clone()
    } else if let Some((_, supers)) = ctx.all_class_superclasses.get(&from_class) {
        supers.clone()
    } else {
        return false;
    };
    for (idx, (super_qi, _)) in supers.iter().enumerate() {
        let super_name = super_qi.name.resolve().unwrap_or_default();
        let accessor = format!("{super_name}{idx}");
        chain.push(accessor);
        if find_superclass_chain(ctx, super_qi.name_symbol(), to_class, chain) {
            return true;
        }
        chain.pop();
    }
    false
}

pub(crate) fn gen_qualified_ref_raw(ctx: &CodegenCtx, module: Option<Symbol>, name: Symbol) -> JsExpr {
    let js_name = ident_to_js(name);
    // The name used in ModuleAccessor must match what the exporting module exposes.
    // For reserved words (new → $$new internally, exported `as new`) the export name is `new`.
    // For special chars (assert' → assert$prime) the export name is `assert$prime`.
    let ext_name = export_name(name);

    match module {
        None => {
            // Check if this is a locally-defined name (module-level declaration)
            if ctx.local_names.contains(&name) {
                return JsExpr::Var(js_name);
            }
            // Check if this is a locally-bound name (lambda param, let/where binding, case binder)
            if ctx.local_bindings.borrow().contains(&name) {
                return JsExpr::Var(js_name);
            }
            // Check if this is an imported name.
            // First try name_source (respects explicit import lists) to find the source module,
            // then try to refine to the defining module via the source module's value_origins.
            if let Some(source_parts) = ctx.name_source.get(&name) {
                // Try to resolve to the defining module (not the re-exporting module).
                // E.g., `show` imported from Prelude should resolve to Data_Show, not Prelude.
                // Use the SOURCE MODULE's value_origins (not our own, which may be polluted
                // by other imports that export the same name from a different module).
                if let Some(source_exports) = ctx.registry.lookup(source_parts) {
                    if let Some(origin_sym) = source_exports.value_origins.get(&ValueName::new(name)) {
                        let origin_str = interner::resolve(*origin_sym).unwrap_or_default();
                        let origin_parts: Vec<Symbol> = origin_str.split('.').map(|s| interner::intern(s)).collect();
                        if let Some(js_mod) = ctx.import_map.get(&origin_parts) {
                            return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                        }
                    }
                }
                // Fallback: use the import source directly
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                }
            }
            // Fallback: use this module's value_origins for names not in name_source
            if let Some(origin_sym) = ctx.exports.value_origins.get(&ValueName::new(name)) {
                let origin_str = interner::resolve(*origin_sym).unwrap_or_default();
                let origin_parts: Vec<Symbol> = origin_str.split('.').map(|s| interner::intern(s)).collect();
                if let Some(js_mod) = ctx.import_map.get(&origin_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                }
            }
            // Check if this is an imported instance (globally visible).
            // Search the current module's direct imports to find the correct source,
            // avoiding ambiguity when multiple modules define instances with the same name
            // for different types (e.g., functorNonEmptyList in both Data.List.Types
            // and Data.List.Lazy.Types).
            {
                let mut found_via_import = false;
                for imp in &ctx.module.imports {
                    if let Some(mod_exports) = ctx.registry.lookup(&imp.module.parts) {
                        // Check if this imported module's registry has an instance with this name
                        let has_instance = mod_exports.instance_registry.values().any(|&inst| inst == name);
                        if has_instance {
                            // Resolve to the defining module if possible
                            if let Some(defining_parts) = mod_exports.instance_modules.get(&name) {
                                if let Some(js_mod) = ctx.import_map.get(defining_parts) {
                                    found_via_import = true;
                                    return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                                }
                            }
                            // Fallback: use the importing module directly
                            if let Some(js_mod) = ctx.import_map.get(&imp.module.parts) {
                                found_via_import = true;
                                return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                            }
                        }
                    }
                }
                // Global fallback if not found via direct imports
                if !found_via_import {
                    if let Some(Some(source_parts)) = ctx.instance_sources.get(&name) {
                        if let Some(js_mod) = ctx.import_map.get(source_parts) {
                            return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                        }
                    }
                }
            }
            // Check if this is a class method — search imported modules for the method
            if ctx.all_class_methods.contains_key(&name) {
                // Sort for deterministic output
                let mut sorted_imports: Vec<_> = ctx.import_map.iter().collect();
                sorted_imports.sort_by_key(|(_, js_mod)| (*js_mod).clone());
                for (mod_parts, js_mod) in &sorted_imports {
                    if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
                        if mod_exports.class_methods.contains_key(&unqualified_value_sym(name))
                            || mod_exports.values.contains_key(&unqualified_value_sym(name)) {
                            return JsExpr::ModuleAccessor((*js_mod).clone(), ext_name);
                        }
                    }
                }
            }
            // Fallback: bare variable (could be a local binding like lambda param)
            JsExpr::Var(js_name)
        }
        Some(mod_sym) => {
            // Look up the module in import map
            // The module qualifier is a single symbol containing the alias
            let mod_str = interner::resolve(mod_sym).unwrap_or_default();

            // Count how many imports match this qualifier to detect shared aliases
            // (e.g., `import X as Regex` and `import Y as Regex`).
            let matching_imports: usize = ctx.module.imports.iter().filter(|imp| {
                if let Some(ref qual) = imp.qualified {
                    let qual_str = qual.parts.iter()
                        .map(|s| interner::resolve(*s).unwrap_or_default())
                        .collect::<Vec<_>>().join(".");
                    qual_str == mod_str
                } else {
                    let imp_name = imp.module.parts.iter()
                        .map(|s| interner::resolve(*s).unwrap_or_default())
                        .collect::<Vec<_>>().join(".");
                    imp_name == mod_str
                }
            }).count();

            // If multiple imports share this qualifier, use name_source first for disambiguation
            if matching_imports > 1 {
                if let Some(origin_parts) = ctx.name_source.get(&name) {
                    if let Some(js_mod) = ctx.import_map.get(origin_parts) {
                        return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                    }
                }
            }

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
                            return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
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
                        return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                    }
                }
            }
            // Fallback: use name_source for shared-alias disambiguation.
            // E.g., `import Data.String.Regex (replace') as Regex` and
            //  `import Data.String.Regex.Unsafe (unsafeRegex) as Regex` — both share
            //  the `Regex` qualifier, so name_source picks the correct module.
            if let Some(origin_parts) = ctx.name_source.get(&name) {
                if let Some(js_mod) = ctx.import_map.get(origin_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                }
            }
            // Final fallback: use the module name directly
            let js_mod = any_name_to_js(&mod_str.replace('.', "_"));
            JsExpr::ModuleAccessor(js_mod, ext_name)
        }
    }
}
