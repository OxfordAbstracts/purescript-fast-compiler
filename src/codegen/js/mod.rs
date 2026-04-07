/// CST-to-JavaScript code generation.
///
/// Translates the PureScript CST directly to a JS AST, which is then
/// pretty-printed to ES module JavaScript. Mirrors the original PureScript
/// compiler's Language.PureScript.CodeGen.JS module.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use crate::cst::*;
use crate::interner::{self, Symbol};
use crate::names::{
    self, ClassName, ConstructorName, LabelName, OpName, Qualified, TypeName, TypeVarName,
    ValueName,
};
use crate::typechecker::{ModuleExports, ModuleRegistry};
use crate::typechecker::types::Type;

use super::common::{any_name_to_js, ident_to_js, is_js_builtin, is_js_reserved, is_valid_js_identifier, module_name_to_js};
use super::js_ast::*;

mod derive;
pub(crate) use derive::*;
mod optimize;
pub(crate) use optimize::*;
mod tco;
pub(crate) use tco::*;
mod dict;
pub(crate) use dict::*;
mod expr;
pub(crate) use expr::*;
mod module_org;
pub(crate) use module_org::*;

/// Shared runtime checks ES module.
/// Written to `$runtime_checks.mjs` in the output directory root.
/// All modules import helpers from this file instead of inlining them.
pub const RUNTIME_CHECKS_JS: &str = r#"// $runtime_checks.mjs — shared runtime validation helpers

function tagOf(value) {
    return Object.prototype.toString.call(value).slice(8, -1);
}

// Rich type description for error messages — includes constructor name and fields for PS types
function describeValue(value, depth) {
    if (depth === undefined) depth = 0;
    if (value === null) return "null";
    if (value === undefined) return "undefined";
    var tag = tagOf(value);
    if (tag === "String") return depth === 0 ? "String(" + JSON.stringify(value).substring(0, 40) + ")" : "String";
    if (tag === "Number") return depth === 0 ? "Number(" + value + ")" : "Number";
    if (tag === "Boolean") return "Boolean(" + value + ")";
    if (tag === "Array") return "Array(" + value.length + ")";
    if (tag === "Function") return "Function";
    if (tag === "Object" && value.constructor && value.constructor.name !== "Object") {
        var name = value.constructor.name;
        if (depth < 3) {
            var parts = [];
            if ("value0" in value) parts.push(describeValue(value.value0, depth + 1));
            if ("value1" in value) parts.push(describeValue(value.value1, depth + 1));
            if (parts.length > 0) return "(" + name + " " + parts.join(" ") + ")";
        }
        return name;
    }
    if (tag === "Object") {
        var keys = Object.keys(value);
        if (keys.length <= 5) return "{" + keys.join(", ") + "}";
        return "{" + keys.slice(0, 5).join(", ") + ", ...(" + keys.length + ")}";
    }
    return tag;
}

export { tagOf as $tagOf };

// === Value type checking ===
export function $check(val, expected, location) {
    if (expected === "integer") {
        if (typeof val !== "number" || !Number.isInteger(val)) {
            throw new TypeError("Runtime check: expected Int but got " + tagOf(val) +
                " (" + String(val).substring(0, 80) + ") at " + location);
        }
    } else if (expected === "array") {
        if (!Array.isArray(val)) {
            throw new TypeError("Runtime check: expected Array but got " + tagOf(val) +
                " (" + String(val).substring(0, 80) + ") at " + location);
        }
    } else if (expected === "object") {
        if (typeof val !== "object" || val === null) {
            throw new TypeError("Runtime check: expected object but got " + tagOf(val) +
                " (" + String(val).substring(0, 80) + ") at " + location);
        }
    } else {
        if (typeof val !== expected) {
            throw new TypeError("Runtime check: expected " + expected + " but got " + tagOf(val) +
                " (" + String(val).substring(0, 80) + ") at " + location);
        }
    }
    return val;
}

// === Proxy-based dict wrapping ===
// Wraps a dict in a Proxy that validates ALL field access at point of use.
export function $proxy_dict(dict, className, expectedKeys, location) {
    if (typeof dict !== "object" || dict === null) {
        throw new TypeError("Dict check: expected " + className + " dict (object) but got " +
            tagOf(dict) + " (" + String(dict).substring(0, 80) + ") at " + location);
    }
    for (var i = 0; i < expectedKeys.length; i++) {
        if (!(expectedKeys[i] in dict)) {
            throw new TypeError("Dict check: " + className + " dict missing '" + expectedKeys[i] +
                "', has: [" + Object.keys(dict).join(", ") + "] at " + location);
        }
    }
    return new Proxy(dict, {
        get: function(target, prop, receiver) {
            if (typeof prop === "symbol") return Reflect.get(target, prop, receiver);
            var val = target[prop];
            if (val === undefined && prop !== "constructor" && prop !== "toString" &&
                prop !== "valueOf" && prop !== "toJSON" && prop !== "then") {
                throw new TypeError("Dict access: " + className + " dict has no field '" + String(prop) +
                    "' at " + location + ", has: [" + Object.keys(target).join(", ") + "]");
            }
            return val;
        }
    });
}

// === Proxy-based dict wrapping (no expected keys — just access validation) ===
export function $proxy_dict_lite(dict, className, location) {
    if (typeof dict !== "object" || dict === null) {
        throw new TypeError("Dict check: expected " + className + " dict (object) but got " +
            tagOf(dict) + " (" + String(dict).substring(0, 80) + ") at " + location);
    }
    return new Proxy(dict, {
        get: function(target, prop, receiver) {
            if (typeof prop === "symbol") return Reflect.get(target, prop, receiver);
            var val = target[prop];
            if (val === undefined && prop !== "constructor" && prop !== "toString" &&
                prop !== "valueOf" && prop !== "toJSON" && prop !== "then") {
                throw new TypeError("Dict access: " + className + " dict has no field '" + String(prop) +
                    "' at " + location + ", has: [" + Object.keys(target).join(", ") + "]");
            }
            return val;
        }
    });
}

// === Method access validation ===
export function $method_check(dict, method, className, location) {
    if (typeof dict !== "object" || dict === null) {
        throw new TypeError("Method check: " + className + "." + method + " called on " +
            tagOf(dict) + " (" + String(dict).substring(0, 80) + ") (not a dict) at " + location);
    }
    var val = dict[method];
    if (val === undefined) {
        throw new TypeError("Method check: " + className + "." + method + " is undefined at " +
            location + ", dict has: [" + Object.keys(dict).join(", ") + "]" +
            ", dict tag: " + tagOf(dict));
    }
    return val;
}

// === Checked function application ===
// Wraps every function call: validates callee is a function.
// No try/catch to preserve V8 JIT optimization on hot paths.
export function $app(f, a, loc) {
    if (typeof f !== "function") {
        throw new TypeError("Not a function: " + describeValue(f) +
            " at " + loc + ", applied to: " + describeValue(a));
    }
    return f(a);
}

// === Wrap a method function to validate its result type after N curried applications ===
// arity=1: f(x) → check result; arity=2: f(x)(y) → check result
// Catches errors INSIDE the method and rethrows with location context.
export function $wrap_method(fn, arity, expectedType, location) {
    if (arity === 1) {
        return function(a) {
            var result;
            try {
                result = fn(a);
            } catch (e) {
                throw new TypeError("Method call failed at " + location +
                    " with arg: " + describeValue(a) +
                    "\n  Caused by: " + e.message);
            }
            if (typeof result !== expectedType) {
                throw new TypeError("Method result: expected " + expectedType + " but got " + describeValue(result) +
                    " at " + location + " (arg was: " + describeValue(a) + ")");
            }
            return result;
        };
    }
    if (arity === 2) {
        return function(a) {
            return function(b) {
                var result;
                try {
                    result = fn(a)(b);
                } catch (e) {
                    throw new TypeError("Method call failed at " + location +
                        " with args: " + describeValue(a) + ", " + describeValue(b) +
                        "\n  Caused by: " + e.message);
                }
                if (typeof result !== expectedType) {
                    throw new TypeError("Method result: expected " + expectedType + " but got " + describeValue(result) +
                        " at " + location);
                }
                return result;
            };
        };
    }
    return fn;
}
"#;

/// Pre-computed global codegen data derived from the full module registry.
/// Computed once before codegen and shared across all modules to avoid
/// redundant `registry.iter_all()` calls per module.
pub struct GlobalCodegenData {
    /// All operator fixities from all modules: op_symbol → (associativity, precedence)
    pub op_fixities: HashMap<String, (Associativity, u8)>,
    /// All class methods: method_name → [(class_qi, type_vars)]
    pub all_class_methods: HashMap<Symbol, Vec<(Qualified<ClassName>, Vec<TypeVarName>)>>,
    /// All signature constraints: fn_name → [class_names]
    pub all_fn_constraints: HashMap<Symbol, Vec<Symbol>>,
    /// All class superclasses: class_name → (type_vars, superclass list)
    pub all_class_superclasses: HashMap<Symbol, (Vec<TypeVarName>, Vec<(Qualified<ClassName>, Vec<Type>)>)>,
    /// Classes with methods or superclasses (have runtime dicts)
    pub known_runtime_classes: HashSet<Symbol>,
    /// Global instance registry: (class, head_type_con) → instance_name
    pub instance_registry: HashMap<(ClassName, TypeName), Symbol>,
    /// Instance sources: instance_name → defining_module_parts
    pub instance_sources: HashMap<Symbol, Option<Vec<Symbol>>>,
    /// Instance constraint classes: instance_name → [class_names]
    pub instance_constraint_classes: HashMap<Symbol, Vec<Symbol>>,
    /// Instance constraint info: instance_name → (head_type_args, [(constraint_class, constraint_type_args)])
    /// head_type_args: args from the instance head pattern (e.g. [Var(s), Var(m)] for StateT s m)
    /// constraint_type_args: for each constraint, the types it's applied to (e.g. [Var(m)] for Functor m)
    pub instance_constraint_info: HashMap<Symbol, (Vec<Type>, Vec<(Symbol, Vec<Type>)>)>,
    /// Defining modules for instances: instance_name → module_parts
    pub defining_modules: HashMap<Symbol, Vec<Symbol>>,
    /// Whether to emit runtime type checks in generated JS.
    pub runtime_checks: bool,
    /// Expected fields for each class dict: class_name → {method/superclass accessor names}
    pub class_expected_fields: HashMap<Symbol, HashSet<String>>,
}

impl GlobalCodegenData {
    /// Build global codegen data from the registry in a single pass.
    pub fn from_registry(registry: &ModuleRegistry) -> Self {
        let all_modules = registry.iter_all();

        let mut op_fixities: HashMap<String, (Associativity, u8)> = HashMap::new();
        let mut all_class_methods: HashMap<Symbol, Vec<(Qualified<ClassName>, Vec<TypeVarName>)>> = HashMap::new();
        let mut all_fn_constraints: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
        let mut all_class_superclasses: HashMap<Symbol, (Vec<TypeVarName>, Vec<(Qualified<ClassName>, Vec<Type>)>)> = HashMap::new();
        let mut instance_registry: HashMap<(ClassName, TypeName), Symbol> = HashMap::new();
        let mut instance_sources: HashMap<Symbol, Option<Vec<Symbol>>> = HashMap::new();
        let mut instance_constraint_classes: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
        let mut instance_constraint_info: HashMap<Symbol, (Vec<Type>, Vec<(Symbol, Vec<Type>)>)> = HashMap::new();
        let mut defining_modules: HashMap<Symbol, Vec<Symbol>> = HashMap::new();

        // First pass: collect defining_modules (needed for instance_sources)
        for (_mod_parts, mod_exports) in &all_modules {
            for (inst_sym, def_parts) in &mod_exports.instance_modules {
                defining_modules.entry(*inst_sym).or_insert_with(|| def_parts.clone());
            }
        }


        // Re-intern a symbol to ensure consistency across compilation levels.
        // Registry exports may contain symbols interned at different times.
        let ri = |sym: Symbol| -> Symbol {
            crate::interner::resolve(sym)
                .map(|s| crate::interner::intern(&s))
                .unwrap_or(sym)
        };

        // Main pass: collect everything else
        for (mod_parts, mod_exports) in &all_modules {
            // Operator fixities
            for (op_qi, (assoc, prec)) in &mod_exports.value_fixities {
                let name = op_qi.name.resolve().unwrap_or_default();
                op_fixities.entry(name).or_insert((*assoc, *prec));
            }

            // Class methods
            for (method, (class, tvs)) in &mod_exports.class_methods {
                all_class_methods.entry(ri(method.name_symbol())).or_insert_with(Vec::new).push((class.clone(), tvs.clone()));
            }

            // Signature constraints
            for (name, constraints) in &mod_exports.signature_constraints {
                let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| ri(c.name_symbol())).collect();
                all_fn_constraints.entry(ri(name.name_symbol())).or_insert(class_names);
            }

            // Class superclasses
            for (name, (tvs, supers)) in &mod_exports.class_superclasses {
                let ri_supers: Vec<(Qualified<ClassName>, Vec<Type>)> = supers.iter().map(|(sc, args)| {
                    let ri_name = ClassName::new(ri(sc.name_symbol()));
                    let module = sc.module;
                    (Qualified { module, name: ri_name }, args.clone())
                }).collect();
                all_class_superclasses.entry(ri(name.name_symbol())).or_insert_with(|| (tvs.clone(), ri_supers));
            }

            // Instance registry
            for (&(class_name, head_name), inst_sym) in &mod_exports.instance_registry {
                instance_registry.entry((ClassName::new(ri(class_name.symbol())), TypeName::new(ri(head_name.symbol())))).or_insert(ri(*inst_sym));
                let ri_inst = ri(*inst_sym);
                // Use this module's own instance_modules to find the defining module.
                // This avoids name collisions when different modules define instances
                // with the same name (e.g., bindProxy in Control.Bind vs Pipes.Internal).
                let has_real_source = mod_exports.instance_modules.contains_key(inst_sym)
                    || mod_exports.instance_modules.contains_key(&ri_inst);
                let source = mod_exports.instance_modules.get(inst_sym).cloned()
                    .or_else(|| mod_exports.instance_modules.get(&ri_inst).cloned())
                    .unwrap_or_else(|| mod_parts.to_vec());
                if has_real_source {
                    // This module actually defines the instance — prefer its source
                    instance_sources.insert(ri_inst, Some(source));
                } else {
                    // This is an imported instance — only register if no other source exists
                    instance_sources.entry(ri_inst).or_insert(Some(source));
                }
            }

            // Instance constraint classes and sources from instances map
            for (class_qi, inst_list) in &mod_exports.instances {
                for (inst_types, inst_constraints, inst_name_opt) in inst_list {
                    let inst_name_resolved = inst_name_opt.or_else(|| {
                        extract_head_type_con_from_types(inst_types)
                            .and_then(|head| mod_exports.instance_registry.get(&(ClassName::new(class_qi.name_symbol()), TypeName::new(head))).copied())
                    });
                    if let Some(inst_name) = inst_name_resolved {
                        let ri_inst = ri(inst_name);
                        let constraint_classes: Vec<Symbol> = inst_constraints.iter().map(|(c, _)| ri(c.name_symbol())).collect();
                        instance_constraint_classes.entry(ri_inst).or_insert(constraint_classes);
                        // Collect instance constraint info: head type args + constraint type args
                        // This allows derive newtype to properly resolve constraint dicts.
                        instance_constraint_info.entry(ri_inst).or_insert_with(|| {
                            // Extract type args from the instance head (e.g. [Var(s), Var(m)] for StateT s m).
                            // For multi-param classes (e.g., MonadState s (StateT s m)), use the LAST
                            // type that has a constructor head, not the first (which may be a bare type var).
                            let head_type_args: Vec<Type> = inst_types.iter().rev()
                                .find(|ty| extract_head_from_type(ty).is_some())
                                .map(|head_ty| collect_type_args_from_type_owned(head_ty))
                                .unwrap_or_default();
                            // Extract constraint type args (e.g. [[Var(m)]] for Functor m)
                            let constraint_info: Vec<(Symbol, Vec<Type>)> = inst_constraints.iter().map(|(c, args)| {
                                (ri(c.name_symbol()), args.clone())
                            }).collect();
                            (head_type_args, constraint_info)
                        });
                        let source = defining_modules.get(&inst_name).cloned()
                            .or_else(|| defining_modules.get(&ri_inst).cloned())
                            .unwrap_or_else(|| mod_parts.to_vec());
                        instance_sources.entry(ri_inst).or_insert(Some(source));
                    }
                }
            }
        }

        // Derive known_runtime_classes from the collected data
        let mut known_runtime_classes: HashSet<Symbol> = HashSet::new();
        for (_, entries) in &all_class_methods {
            for (class_qi, _) in entries {
                known_runtime_classes.insert(ri(class_qi.name_symbol()));
            }
        }
        for (class_sym, (_, supers)) in &all_class_superclasses {
            if !supers.is_empty() {
                known_runtime_classes.insert(ri(*class_sym));
            }
        }

        // Remove classes whose methods are all just `coerce` at runtime (no dict actually used).
        // Newtype: wrap/unwrap are both `coerce`, so Newtype dicts are never accessed.
        // Type.Equality.TypeEquals: proof is just identity via Coercible, dict never accessed.
        // The reference compiler generates `()` for these constraint params.
        // IMPORTANT: Only exclude TypeEquals if its sole method is `proof` (the Type.Equality
        // method). A locally-defined TypeEquals with methods like coerce/coerceBack IS a
        // runtime class and must NOT be excluded. We detect the Type.Equality variant by
        // checking that NO method named `coerce` or `coerceBack` is associated with TypeEquals.
        let type_equals_is_zero_cost = {
            let type_equals_sym = crate::interner::intern("TypeEquals");
            // Check if any method of TypeEquals is coerce or coerceBack
            let has_local_methods = all_class_methods.iter().any(|(method_sym, entries)| {
                let method_name = crate::interner::resolve(*method_sym).unwrap_or_default();
                matches!(method_name.as_ref(), "coerce" | "coerceBack")
                    && entries.iter().any(|(class_qi, _)| {
                        class_qi.name_symbol() == type_equals_sym
                    })
            });
            !has_local_methods // zero-cost only if no coerce/coerceBack methods
        };
        known_runtime_classes.retain(|s| {
            let name = crate::interner::resolve(*s).unwrap_or_default();
            match name.as_ref() {
                "Newtype" => false,
                "TypeEquals" => !type_equals_is_zero_cost,
                _ => true,
            }
        });

        // Build class_expected_fields: class → {method names + superclass accessor names}
        let mut class_expected_fields: HashMap<Symbol, HashSet<String>> = HashMap::new();
        for (method_sym, entries) in &all_class_methods {
            for (class_qi, _) in entries {
                let class_sym = ri(class_qi.name_symbol());
                if let Some(method_name) = crate::interner::resolve(*method_sym) {
                    class_expected_fields.entry(class_sym).or_default().insert(method_name.to_string());
                }
            }
        }
        // Add superclass accessor names (e.g., "Functor0", "Applicative0")
        for (class_sym, (_, supers)) in &all_class_superclasses {
            for (idx, (super_qi, _)) in supers.iter().enumerate() {
                if let Some(super_name) = crate::interner::resolve(super_qi.name_symbol()) {
                    class_expected_fields.entry(ri(*class_sym)).or_default().insert(format!("{super_name}{idx}"));
                }
            }
        }

        GlobalCodegenData {
            op_fixities,
            all_class_methods,
            all_fn_constraints,
            all_class_superclasses,
            known_runtime_classes,
            instance_registry,
            instance_sources,
            instance_constraint_classes,
            instance_constraint_info,
            defining_modules,
            runtime_checks: false, // Set by caller
            class_expected_fields,
        }
    }
}

/// Collect all type arguments from a type application (owned version).
/// E.g., App(App(Con(StateT), Var(s)), Var(m)) → [Var(s), Var(m)]
fn collect_type_args_from_type_owned(ty: &Type) -> Vec<Type> {
    fn collect_inner(ty: &Type, args: &mut Vec<Type>) {
        match ty {
            Type::App(f, arg) => {
                collect_inner(f, args);
                args.push((**arg).clone());
            }
            _ => {}
        }
    }
    let mut args = vec![];
    collect_inner(ty, &mut args);
    args
}

/// Create an unqualified Qualified<ConstructorName> for map lookups.
pub(crate) fn unqualified_ctor_sym(name: Symbol) -> Qualified<ConstructorName> {
    Qualified::unqualified(ConstructorName::new(name))
}

/// Check if a constructor name belongs to a newtype.
/// First checks if the constructor name itself is in newtype_names (common case where
/// the type and constructor share the same name, e.g. `newtype Identity a = Identity a`).
/// Then looks up the constructor's parent type from ctor_details and checks that.
/// This handles cases like `newtype Summary = Count { ... }` where the constructor
/// name differs from the type name.
pub(crate) fn is_newtype_ctor(ctx: &CodegenCtx, ctor_name: Symbol) -> bool {
    // Look up parent type from ctor_details (includes imported constructors)
    // and check if the parent type is a newtype AND the constructor has exactly 1 field.
    // The field count check prevents false positives: e.g., `Nil` (0 fields) in Step type
    // could have parent "List" in ctor_details when "List" is also a newtype name
    // (from Data.List.Lazy.Types), but Nil is not a newtype constructor.
    let ctor_qi = unqualified_ctor_sym(ctor_name);
    if let Some((parent_type, _, fields)) = ctx.ctor_details.get(&ctor_qi) {
        if fields.len() == 1 && ctx.newtype_names.contains(&parent_type.name) {
            return true;
        }
    }
    // Fast path: type and constructor share the same name.
    // Only use this fallback when ctor_details lookup fails (no imported info).
    if ctx.ctor_details.get(&ctor_qi).is_none() {
        if ctx.newtype_names.contains(&TypeName::new(ctor_name)) {
            return true;
        }
    }
    false
}

/// Generate statements for a failed pattern match: console.error logs + throw.
/// If `scrutinees` is non-empty, logs the values and their types before throwing.
pub(crate) fn gen_failed_pattern_match_stmts(scrutinees: &[String]) -> Vec<JsStmt> {
    let mut stmts = Vec::new();
    if !scrutinees.is_empty() {
        let console_error = JsExpr::Indexer(
            Box::new(JsExpr::Var("console".to_string())),
            Box::new(JsExpr::StringLit("error".to_string())),
        );
        // console.error("Value:", v1, v2, ...)
        let mut value_args = vec![JsExpr::StringLit("Failed pattern match at value:".to_string())];
        for name in scrutinees {
            value_args.push(JsExpr::Var(name.clone()));
        }
        stmts.push(JsStmt::Expr(JsExpr::App(
            Box::new(console_error.clone()),
            value_args,
        )));
        // console.error("Type:", typeof v1, typeof v2, ...)
        let mut type_args = vec![JsExpr::StringLit("Type:".to_string())];
        for name in scrutinees {
            type_args.push(JsExpr::Unary(
                JsUnaryOp::Typeof,
                Box::new(JsExpr::Var(name.clone())),
            ));
        }
        stmts.push(JsStmt::Expr(JsExpr::App(
            Box::new(console_error.clone()),
            type_args,
        )));
        // console.error("Constructor:", v1.constructor, v2.constructor, ...)
        let mut ctor_args = vec![JsExpr::StringLit("Constructor:".to_string())];
        for name in scrutinees {
            ctor_args.push(JsExpr::Indexer(
                Box::new(JsExpr::Var(name.clone())),
                Box::new(JsExpr::StringLit("constructor".to_string())),
            ));
        }
        stmts.push(JsStmt::Expr(JsExpr::App(
            Box::new(console_error),
            ctor_args,
        )));
    }
    stmts.push(JsStmt::Throw(JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )));
    stmts
}

/// Create an unqualified Qualified<TypeName> for map lookups.
pub(crate) fn unqualified_type_sym(name: Symbol) -> Qualified<TypeName> {
    Qualified::unqualified(TypeName::new(name))
}

/// Create an unqualified Qualified<ClassName> for map lookups.
pub(crate) fn unqualified_class_sym(name: Symbol) -> Qualified<ClassName> {
    Qualified::unqualified(ClassName::new(name))
}

/// Create an unqualified Qualified<ValueName> for map lookups.
pub(crate) fn unqualified_value_sym(name: Symbol) -> Qualified<ValueName> {
    Qualified::unqualified(ValueName::new(name))
}

/// Create an unqualified Qualified<OpName> for map lookups.
pub(crate) fn unqualified_op_sym(name: Symbol) -> Qualified<OpName> {
    Qualified::unqualified(OpName::new(name))
}

/// Context threaded through code generation for a single module.
pub(crate) struct CodegenCtx<'a> {
    /// The module being compiled
    pub(crate) module: &'a Module,
    /// This module's exports (from typechecking)
    pub(crate) exports: &'a ModuleExports,
    /// Registry of all typechecked modules
    #[allow(dead_code)]
    pub(crate) registry: &'a ModuleRegistry,
    /// Module name as dot-separated string (e.g. "Data.Maybe")
    #[allow(dead_code)]
    pub(crate) module_name: &'a str,
    /// Module name parts as symbols
    pub(crate) module_parts: &'a [Symbol],
    /// Set of names that are newtypes (newtype constructor erasure)
    pub(crate) newtype_names: HashSet<TypeName>,
    /// Mapping from constructor name → (parent_type, type_vars, field_types)
    pub(crate) ctor_details: HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<crate::typechecker::types::Type>)>,
    /// Data type → constructor names (to determine sum vs product)
    pub(crate) data_constructors: HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>>,
    /// Operators that alias functions (not constructors)
    pub(crate) function_op_aliases: &'a HashSet<Qualified<OpName>>,
    /// Names of foreign imports in this module
    pub(crate) foreign_imports: HashSet<Symbol>,
    /// Import map: module_parts → JS variable name
    pub(crate) import_map: HashMap<Vec<Symbol>, String>,
    /// Names defined locally in this module (values, ctors, foreign, instances)
    pub(crate) local_names: HashSet<Symbol>,
    /// Imported name → source module parts (for resolving unqualified references)
    pub(crate) name_source: HashMap<Symbol, Vec<Symbol>>,
    /// Operator → target name resolution: op_symbol → (source_module_parts_or_none, target_name)
    pub(crate) operator_targets: HashMap<Symbol, (Option<Vec<Symbol>>, Symbol)>,
    /// Counter for generating fresh variable names
    pub(crate) fresh_counter: Cell<usize>,
    /// Current dict scope: class_name → dict_param_name
    /// Populated when inside a constrained function body.
    pub(crate) dict_scope: std::cell::RefCell<Vec<(Symbol, String)>>,
    /// Instance registry: (class_name, head_type_con) → instance_name
    pub(crate) instance_registry: HashMap<(ClassName, TypeName), Symbol>,
    /// Instance name → source module parts (None = local)
    pub(crate) instance_sources: HashMap<Symbol, Option<Vec<Symbol>>>,
    /// Instance name → constraint class names (for determining if instance needs dict application)
    pub(crate) instance_constraint_classes: HashMap<Symbol, Vec<Symbol>>,
    /// Instance constraint info: instance_name → (head_type_args, [(constraint_class, constraint_type_args)])
    /// Used for derive newtype constraint dict resolution.
    pub(crate) instance_constraint_info: HashMap<Symbol, (Vec<Type>, Vec<(Symbol, Vec<Type>)>)>,
    /// Pre-built: class method → list of (class_name, type_vars) — borrowed from GlobalCodegenData
    pub(crate) all_class_methods: &'a HashMap<Symbol, Vec<(Qualified<ClassName>, Vec<TypeVarName>)>>,
    /// Pre-built: fn_name → constraint class names (from signature_constraints)
    /// Uses RefCell because local let-bound constrained functions are added during codegen.
    pub(crate) all_fn_constraints: std::cell::RefCell<HashMap<Symbol, Vec<Symbol>>>,
    /// Pre-built: class_name → (type_vars, superclass list) — borrowed from GlobalCodegenData
    pub(crate) all_class_superclasses: &'a HashMap<Symbol, (Vec<TypeVarName>, Vec<(Qualified<ClassName>, Vec<Type>)>)>,
    /// Resolved dicts from typechecker: expression_span → [(class_name, dict_expr)].
    /// Used to resolve class method dicts at module level (outside dict scope).
    /// Each span uniquely identifies a call site, so lookups are unambiguous.
    pub(crate) resolved_dict_map: HashMap<crate::span::Span, Vec<(Symbol, crate::typechecker::registry::DictExpr)>>,
    /// Resolved constructor origins from typechecker: constructor expression span → defining module parts.
    /// Used to disambiguate same-named constructors from different types.
    pub(crate) resolved_constructors: HashMap<crate::span::Span, Vec<Symbol>>,
    /// Functions with Partial => constraint (need dict wrapper but not in signature_constraints)
    pub(crate) partial_fns: HashSet<Symbol>,
    /// When true, references to partial_fns are auto-called with () to strip the dictPartial layer.
    /// Set when inside unsafePartial argument expressions.
    pub(crate) discharging_partial: std::cell::Cell<bool>,
    /// Operator fixities — borrowed from GlobalCodegenData
    pub(crate) op_fixities: &'a HashMap<String, (Associativity, u8)>,
    /// Wildcard section parameter names (collected during gen_expr for Expr::Wildcard)
    pub(crate) wildcard_params: std::cell::RefCell<Vec<String>>,
    /// Classes that have methods (and thus runtime dictionaries) — borrowed from GlobalCodegenData
    pub(crate) known_runtime_classes: &'a HashSet<Symbol>,
    /// Locally-bound names (lambda params, let/where bindings, case binders).
    /// Used to distinguish local bindings from imported names with the same name.
    pub(crate) local_bindings: std::cell::RefCell<HashSet<Symbol>>,
    /// Subset of local_bindings that have their own type class constraints (let/where bindings).
    /// These need dict application at call sites unlike regular local bindings.
    pub(crate) local_constrained_bindings: std::cell::RefCell<HashSet<Symbol>>,
    /// Record update field info from typechecker: span → all field names.
    pub(crate) record_update_fields: &'a HashMap<crate::span::Span, Vec<LabelName>>,
    /// Parameters with constrained higher-rank types: param_name → dict_param_name.
    /// When such a parameter is used as a value (not called), it needs eta-expansion:
    /// `f` → `function(dictClass) { return f(dictClass); }`
    /// This replicates the original compiler's CoreFn representation.
    /// Scoped per-function (set before processing each function body).
    pub(crate) constrained_hr_params: std::cell::RefCell<HashMap<Symbol, String>>,
    /// Type operator → target type constructor: `/\` → `Tuple`.
    /// Built from `infixr N type Foo as op` declarations.
    pub(crate) type_op_targets: HashMap<Symbol, Symbol>,
    /// Let binding names that have been inlined at module level.
    /// Used to detect name collisions: if a name is already used, IIFE wrapping is required.
    pub(crate) module_level_let_names: std::cell::RefCell<HashSet<String>>,
    /// All JS variable names declared at module level.
    /// Used to deduplicate generated instance names that collide with value declarations.
    pub(crate) used_js_names: std::cell::RefCell<HashSet<String>>,
    /// Mapping from original instance Symbol to deduplicated JS name.
    /// Only populated when an instance name was changed due to collision.
    pub(crate) deduped_instance_names: std::cell::RefCell<HashMap<Symbol, String>>,
    /// Module-level generated expressions: name → JsExpr.
    /// Used to inline operator targets when the target is let-shadowed in an inner scope.
    pub(crate) module_level_exprs: std::cell::RefCell<HashMap<Symbol, JsExpr>>,
    /// Return-type dict param names for the current function being generated.
    /// These are added AFTER regular params in the generated function.
    pub(crate) return_type_dict_params: std::cell::RefCell<Vec<String>>,
    /// Tracks which return-type dict params were actually consumed by try_apply_dict.
    /// If a dict was consumed in the body, wrap_expr_with_return_dicts should only wrap.
    /// If no dicts were consumed, the body already has the constraint baked in — skip wrapping.
    pub(crate) used_return_type_dicts: std::cell::RefCell<HashSet<String>>,
    /// Whether the module needs the $runtime_lazy helper function.
    /// Set to true when any binding requires lazy initialization.
    pub(crate) needs_runtime_lazy: Cell<bool>,
    /// Whether to emit runtime type checks in generated JS.
    pub(crate) runtime_checks: bool,
    /// Set to true when any runtime check is emitted (triggers $check/$dict_check helper emission).
    pub(crate) needs_runtime_check: Cell<bool>,
    /// Expected fields for each class dict: class_name → {field names}
    pub(crate) class_expected_fields: &'a HashMap<Symbol, HashSet<String>>,
    /// Top-level value types from typechecker: ValueName → Type
    pub(crate) value_types: &'a HashMap<ValueName, Type>,
    /// Span→Type map from typechecker for local bindings/expressions
    pub(crate) span_types: &'a HashMap<crate::span::Span, Type>,
}

impl<'a> CodegenCtx<'a> {
    pub(crate) fn fresh_name(&self, prefix: &str) -> String {
        let n = self.fresh_counter.get();
        self.fresh_counter.set(n + 1);
        if n == 0 {
            prefix.to_string()
        } else {
            format!("{prefix}{n}")
        }
    }
    /// Deduplicate a JS variable name by appending a numeric suffix if the name
    /// is already in use. Registers the resulting name in `used_js_names`.
    pub(crate) fn deduplicate_js_name(&self, name: String) -> String {
        let mut used = self.used_js_names.borrow_mut();
        if !used.contains(&name) {
            used.insert(name.clone());
            return name;
        }
        // Find next available suffix
        let mut i = 1;
        loop {
            let candidate = format!("{name}{i}");
            if !used.contains(&candidate) {
                used.insert(candidate.clone());
                return candidate;
            }
            i += 1;
        }
    }

    /// Create a DictCheckCtx for runtime dict validation, or None if checks are disabled.
    pub(crate) fn dict_check_ctx(&self, location: &str) -> Option<dict::DictCheckCtx<'_>> {
        if self.runtime_checks {
            Some(dict::DictCheckCtx {
                class_expected_fields: self.class_expected_fields,
                needs_runtime_check: &self.needs_runtime_check,
                location: format!("{}.{}", self.module_name, location),
            })
        } else {
            None
        }
    }
}

/// Create an export entry: (js_name, Some(ps_name)) if the PS name differs and is
/// a valid JS identifier (e.g. JS reserved words like `const` → `$$const as const`).
/// For non-identifier PS names (e.g. `class'` → `class$prime`), no "as" clause is used.
pub(crate) fn export_entry(sym: Symbol) -> (String, Option<String>) {
    let js_name = ident_to_js(sym);
    let ps_name = interner::resolve(sym).unwrap_or_default();
    if js_name != ps_name && is_valid_js_identifier(&ps_name) {
        (js_name, Some(ps_name))
    } else {
        (js_name, None)
    }
}

/// Create an export entry from a JS name string (no PS name tracking).
/// Get the externally-visible export name for a symbol.
/// For reserved words like `new`, the export uses `as new` so external name is the PS name.
/// For non-identifier PS names like `assert'`, the export is just the JS-escaped name.
pub(crate) fn export_name(sym: Symbol) -> String {
    let js_name = ident_to_js(sym);
    let ps_name = interner::resolve(sym).unwrap_or_default();
    if js_name != ps_name && is_valid_js_identifier(&ps_name) {
        // Exported with alias: `$$new as new` → external name is `new`
        ps_name
    } else {
        // Exported without alias: `assert$prime` → external name is `assert$prime`
        js_name
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
    global: &GlobalCodegenData,
    all_ctor_details: &HashMap<Qualified<ConstructorName>, (Qualified<TypeName>, Vec<TypeVarName>, Vec<crate::typechecker::types::Type>)>,
    all_data_constructors: &HashMap<Qualified<TypeName>, Vec<Qualified<ConstructorName>>>,
    value_types: &HashMap<ValueName, Type>,
    span_types: &HashMap<crate::span::Span, Type>,
) -> JsModule {
    // Collect local names (names defined in this module) and Partial-constrained functions
    let mut local_names = HashSet::new();
    let mut foreign_imports_set = HashSet::new();
    let mut partial_fns = HashSet::new();
    for decl in &module.decls {
        match decl {
            Decl::Value { name, .. } => { local_names.insert(name.value.symbol()); }
            Decl::Foreign { name, .. } => {
                local_names.insert(name.value.symbol());
                foreign_imports_set.insert(name.value.symbol());
            }
            Decl::Data { constructors, .. } => {
                for ctor in constructors {
                    local_names.insert(ctor.name.value.symbol());
                }
            }
            Decl::Newtype { constructor, .. } => {
                local_names.insert(constructor.value.symbol());
            }
            Decl::Instance { .. } => {
                // Instance names are NOT added to local_names — they can't be
                // referenced in PureScript code and adding them can shadow imported
                // functions with the same name, causing false self-references in
                // method bodies (e.g., instance decodeVoid :: ... where myDecode = decodeVoid
                // would incorrectly reference itself instead of the imported decodeVoid).
                // Dict references use instance_sources instead.
            }
            Decl::Class { members, .. } => {
                for member in members {
                    local_names.insert(member.name.value.symbol());
                }
            }
            Decl::TypeSignature { name, ty, .. } => {
                // Check if type has Partial constraint — these need dict wrappers in codegen
                if has_partial_constraint(ty) {
                    partial_fns.insert(name.value.symbol());
                }
            }
            _ => {}
        }
    }

    // Build name_source: for each import, map imported names → source module parts.
    let mut name_source: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
    let mut operator_targets: HashMap<Symbol, (Option<Vec<Symbol>>, Symbol)> = HashMap::new();

    // Helper: resolve a name to its origin module parts using value_origins.
    // Used only for operator target resolution where name collisions are common
    // (e.g., Data.Function.apply vs Control.Apply.apply through Prelude).
    let resolve_origin = |name: Symbol, mod_exports: &ModuleExports, default_parts: &[Symbol]| -> Vec<Symbol> {
        if let Some(origin_mod_sym) = mod_exports.value_origins.get(&ValueName::new(name)) {
            let origin_str = interner::resolve(*origin_mod_sym).unwrap_or_default();
            if !origin_str.is_empty() {
                let origin_parts: Vec<Symbol> = origin_str.split('.').map(|s| interner::intern(s)).collect();
                if registry.lookup(&origin_parts).is_some() {
                    return origin_parts;
                }
            }
        }
        default_parts.to_vec()
    };

    // Collect operator targets from this module's exports
    for (op_qi, target_qi) in &exports.value_operator_targets {
        operator_targets.insert(op_qi.name_symbol(), (None, target_qi.name_symbol()));
    }

    for imp in &module.imports {
        let parts = &imp.module.parts;
        // Skip Prim and self-imports
        if !parts.is_empty() {
            let first = interner::resolve(parts[0]).unwrap_or_default();
            if first == "Prim" { continue; }
        }
        if *parts == module_parts { continue; }

        // Look up imported module in registry
        if let Some(mod_exports) = registry.lookup(parts) {
            // Import partial_value_names from this module
            for name in &mod_exports.partial_value_names {
                partial_fns.insert(name.symbol());
            }
            // Collect all value names exported by this module
            let all_names: Vec<Symbol> = mod_exports.values.keys().map(|qi| qi.name_symbol()).collect();

            // Collect constructor names — only from types defined in this module
            let all_ctor_names: Vec<Symbol> = mod_exports.ctor_details.iter()
                .filter(|(_, (parent_qi, _, _))| mod_exports.data_constructors.contains_key(parent_qi))
                .map(|(qi, _)| qi.name_symbol())
                .collect();

            // Determine which names to import based on import list
            let is_qualified_only = imp.qualified.is_some() && imp.imports.is_none();

            if !is_qualified_only {
                match &imp.imports {
                    None => {
                        // import M — import all names, tracing to origin module
                        for name in all_names.iter().chain(all_ctor_names.iter()) {
                            if !local_names.contains(name) {
                                let origin = resolve_origin(*name, mod_exports, parts);
                                name_source.entry(*name).or_insert_with(|| origin);
                            }
                        }
                    }
                    Some(ImportList::Explicit(items)) => {
                        // Explicit imports should OVERWRITE previous entries from import-all,
                        // since the user explicitly requested this name from this module.
                        // E.g., `import ExitCodes (Success(..))` should take priority over
                        // `import Options.Applicative.Types` which also exports Success.
                        for item in items {
                            match item {
                                Import::Value(n) => {
                                    if !local_names.contains(&n.value.symbol()) {
                                        let origin = resolve_origin(n.value.symbol(), mod_exports, parts);
                                        name_source.insert(n.value.symbol(), origin);
                                    }
                                }
                                Import::Type(type_name, Some(DataMembers::All)) => {
                                    // Only import constructors that belong to this specific type,
                                    // not all constructors from the module. This prevents
                                    // `import M (TypeA(..))` from stealing constructors that belong
                                    // to TypeB when both types share constructor names.
                                    let type_sym = type_name.value.symbol();
                                    let type_qi = Qualified::unqualified(TypeName::new(type_sym));
                                    if let Some(type_ctors) = mod_exports.data_constructors.get(&type_qi) {
                                        for ctor_qi in type_ctors {
                                            let ctor_sym = ctor_qi.name_symbol();
                                            if !local_names.contains(&ctor_sym) {
                                                let origin = resolve_origin(ctor_sym, mod_exports, parts);
                                                name_source.insert(ctor_sym, origin);
                                            }
                                        }
                                    }
                                }
                                Import::Type(_, Some(DataMembers::Explicit(ctors))) => {
                                    for ctor in ctors {
                                        if !local_names.contains(&ctor.value.symbol()) {
                                            let origin = resolve_origin(ctor.value.symbol(), mod_exports, parts);
                                            name_source.insert(ctor.value.symbol(), origin);
                                        }
                                    }
                                }
                                Import::Class(n) => {
                                    for (method_qi, (class_qi, _)) in &mod_exports.class_methods {
                                        if class_qi.name_symbol() == n.value.symbol() {
                                            let method_sym = method_qi.name_symbol();
                                            if !local_names.contains(&method_sym) {
                                                let origin = resolve_origin(method_sym, mod_exports, parts);
                                                name_source.insert(method_sym, origin);
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    Some(ImportList::Hiding(items)) => {
                        let hidden: HashSet<Symbol> = items.iter().map(|i| i.name()).collect();
                        for name in all_names.iter().chain(all_ctor_names.iter()) {
                            if !hidden.contains(name) && !local_names.contains(name) {
                                let origin = resolve_origin(*name, mod_exports, parts);
                                name_source.entry(*name).or_insert_with(|| origin);
                            }
                        }
                    }
                }
            }

            // Collect operator targets from imported module, respecting import list filtering
            // (e.g., `import Prelude hiding ((/))` should exclude the `/` operator)
            for (op_qi, target_qi) in &mod_exports.value_operator_targets {
                let op_sym = op_qi.name_symbol();
                let is_explicit_import = matches!(&imp.imports, Some(ImportList::Explicit(_)));
                let should_import = if is_qualified_only {
                    false // Qualified-only imports don't bring operators into the unqualified namespace
                } else {
                    match &imp.imports {
                        None => true, // import all
                        Some(ImportList::Explicit(items)) => {
                            // Import operator if it's explicitly listed OR its target is imported
                            // (PureScript imports operators when their target function is imported)
                            let explicit_names: HashSet<Symbol> = items.iter().map(|i| i.name()).collect();
                            explicit_names.contains(&op_sym) || explicit_names.contains(&target_qi.name_symbol())
                        }
                        Some(ImportList::Hiding(items)) => {
                            // Import all except hidden
                            let hidden: HashSet<Symbol> = items.iter().map(|i| i.name()).collect();
                            !hidden.contains(&op_sym)
                        }
                    }
                };
                if !should_import { continue; }
                let target_sym = target_qi.name_symbol();
                let resolve_target = || {
                    // Resolve operator target to its origin module
                    let target_origin = resolve_origin(target_sym, mod_exports, parts);
                    if registry.lookup(&target_origin).is_some() {
                        (Some(target_origin), target_sym)
                    } else if mod_exports.values.contains_key(target_qi) || mod_exports.ctor_details.contains_key(&target_qi.map(names::value_as_constructor)) {
                        (Some(parts.clone()), target_sym)
                    } else {
                        (None, target_sym)
                    }
                };
                if is_explicit_import {
                    // Explicit imports overwrite previous entries, since the user
                    // explicitly requested this operator from this module.
                    operator_targets.insert(op_sym, resolve_target());
                } else {
                    operator_targets.entry(op_sym).or_insert_with(resolve_target);
                }
                // Also register the operator's target (e.g., Cons for (:)) in name_source
                // so that uses of the constructor are resolved to the correct module
                if !local_names.contains(&target_sym) {
                    let target_origin = resolve_origin(target_sym, mod_exports, parts);
                    if is_explicit_import {
                        name_source.insert(target_sym, target_origin);
                    } else {
                        name_source.entry(target_sym).or_insert_with(|| target_origin);
                    }
                }
            }
        }
    }

    // Build all_fn_constraints: module's own take priority, then global (filtering local_names)
    let mut fn_constraints = HashMap::new();
    for (name, constraints) in &exports.signature_constraints {
        let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name_symbol()).collect();
        fn_constraints.entry(name.name_symbol()).or_insert(class_names);
    }
    for (name, class_names) in &global.all_fn_constraints {
        if !local_names.contains(name) {
            fn_constraints.entry(*name).or_insert_with(|| class_names.clone());
        }
    }

    // Augment global data with current module's exports (needed when codegen runs
    // before the module is registered in the registry, e.g. fused typecheck+codegen).
    let mut known_runtime_classes = global.known_runtime_classes.clone();
    let mut all_class_methods = global.all_class_methods.clone();
    let mut all_class_superclasses = global.all_class_superclasses.clone();
    let mut instance_registry = global.instance_registry.clone();
    let mut instance_sources = global.instance_sources.clone();
    let mut instance_constraint_classes = global.instance_constraint_classes.clone();
    let mut instance_constraint_info = global.instance_constraint_info.clone();

    // Add module's own class methods
    for (method, (class, tvs)) in &exports.class_methods {
        all_class_methods.entry(method.name_symbol()).or_insert_with(Vec::new).push((class.clone(), tvs.clone()));
    }
    // Add module's own class superclasses
    for (name, (tvs, supers)) in &exports.class_superclasses {
        all_class_superclasses.entry(name.name_symbol()).or_insert_with(|| (tvs.clone(), supers.clone()));
    }
    // Add module's own instance registry
    // Use `insert` (not `or_insert`) for instance_sources here: exports.instance_registry
    // only contains locally-defined instances, and local definitions must take priority over
    // imported ones. Using `or_insert` would keep the imported source (e.g. Data_Show.showString)
    // even when the current module also defines an instance with the same name (e.g. a local
    // `showString :: Show String` in a module that redefines `Show`).
    for (&(class_name, head_name), &inst_sym) in &exports.instance_registry {
        instance_registry.entry((class_name, head_name)).or_insert(inst_sym);
        instance_sources.insert(inst_sym, None); // None = local (current module)
    }
    // Add module's own instance constraint classes and info
    for (_class_qi, inst_list) in &exports.instances {
        for (inst_types, inst_constraints, inst_name_opt) in inst_list {
            if let Some(inst_name) = inst_name_opt {
                let constraint_classes: Vec<Symbol> = inst_constraints.iter().map(|(c, _)| c.name_symbol()).collect();
                instance_constraint_classes.entry(*inst_name).or_insert(constraint_classes);
                // Also store constraint info for derive newtype resolution.
                // Use the LAST type with a constructor head for multi-param classes.
                instance_constraint_info.entry(*inst_name).or_insert_with(|| {
                    let head_type_args: Vec<Type> = inst_types.iter().rev()
                        .find(|ty| extract_head_from_type(ty).is_some())
                        .map(|head_ty| collect_type_args_from_type_owned(head_ty))
                        .unwrap_or_default();
                    let constraint_info: Vec<(Symbol, Vec<Type>)> = inst_constraints.iter().map(|(c, args)| {
                        (c.name_symbol(), args.clone())
                    }).collect();
                    (head_type_args, constraint_info)
                });
            }
        }
    }
    // Derive known_runtime_classes from augmented data
    for (_, entries) in &all_class_methods {
        for (class_qi, _) in entries {
            known_runtime_classes.insert(class_qi.name_symbol());
        }
    }
    // Classes with superclasses are also runtime
    for (class_sym, (_, supers)) in &all_class_superclasses {
        if !supers.is_empty() {
            known_runtime_classes.insert(*class_sym);
        }
    }
    // Re-apply zero-cost class exclusions after per-module re-adds.
    // Newtype/Type.Equality.TypeEquals are zero-cost: their methods are all `coerce`/identity,
    // so the dict is never accessed at runtime. The reference compiler uses unit
    // wrappers `function()` for all Newtype-constrained functions.
    // Without this retain, Newtype gets re-added above because it has a superclass
    // (Coercible), causing named dict params instead of unit wrappers.
    // IMPORTANT: Only exclude TypeEquals if it's the Type.Equality variant (sole method: proof).
    // A locally-defined TypeEquals with coerce/coerceBack methods IS a runtime class.
    let type_equals_is_zero_cost = {
        let type_equals_sym = crate::interner::intern("TypeEquals");
        let has_local_methods = all_class_methods.iter().any(|(method_sym, entries)| {
            let method_name = crate::interner::resolve(*method_sym).unwrap_or_default();
            matches!(method_name.as_ref(), "coerce" | "coerceBack")
                && entries.iter().any(|(class_qi, _)| {
                    class_qi.name_symbol() == type_equals_sym
                })
        });
        !has_local_methods
    };
    known_runtime_classes.retain(|s| {
        let name = crate::interner::resolve(*s).unwrap_or_default();
        match name.as_ref() {
            "Newtype" => false,
            "TypeEquals" => !type_equals_is_zero_cost,
            _ => true,
        }
    });

    // Build module-specific op_fixities from the module's imports.
    // Each module may import different operators with the same symbol (e.g., "/" is
    // `infixr 1 gsep as /` in Routing.Duplex.Generic.Syntax but `infixl 7 div as /`
    // in Data.EuclideanRing). Start from global fixities, then override with fixities
    // from specifically imported modules (which reflect what's actually in scope).
    let mut merged_op_fixities = global.op_fixities.clone();
    // Override with fixities from imported modules
    for imp in &module.imports {
        if let Some(mod_exports) = registry.lookup(&imp.module.parts) {
            for (op_qi, (assoc, prec)) in &mod_exports.value_fixities {
                let name = op_qi.name.resolve().unwrap_or_default();
                merged_op_fixities.insert(name, (*assoc, *prec));
            }
        }
    }
    // Module's own fixities take highest priority
    for (op_qi, fixity) in &exports.value_fixities {
        let name = op_qi.name.resolve().unwrap_or_default();
        merged_op_fixities.insert(name, *fixity);
    }

    let mut ctx = CodegenCtx {
        module,
        exports,
        registry,
        module_name,
        module_parts,
        newtype_names: exports.newtype_names.clone(),
        ctor_details: all_ctor_details.clone(),
        data_constructors: all_data_constructors.clone(),
        function_op_aliases: &exports.function_op_aliases,
        foreign_imports: foreign_imports_set,
        import_map: HashMap::new(),
        local_names,
        name_source,
        operator_targets,
        fresh_counter: Cell::new(0),
        dict_scope: std::cell::RefCell::new(Vec::new()),
        instance_registry,
        instance_sources,
        instance_constraint_classes,
        instance_constraint_info,
        all_class_methods: &all_class_methods,
        all_fn_constraints: std::cell::RefCell::new(fn_constraints),
        all_class_superclasses: &all_class_superclasses,
        resolved_dict_map: exports.resolved_dicts.clone(),
        resolved_constructors: exports.resolved_constructors.clone(),
        partial_fns,
        discharging_partial: std::cell::Cell::new(false),
        op_fixities: &merged_op_fixities,
        wildcard_params: std::cell::RefCell::new(Vec::new()),
        known_runtime_classes: &known_runtime_classes,
        local_bindings: std::cell::RefCell::new(HashSet::new()),
        local_constrained_bindings: std::cell::RefCell::new(HashSet::new()),
        record_update_fields: &exports.record_update_fields,
        constrained_hr_params: std::cell::RefCell::new(HashMap::new()),
        type_op_targets: HashMap::new(),
        module_level_let_names: std::cell::RefCell::new(HashSet::new()),
        module_level_exprs: std::cell::RefCell::new(HashMap::new()),
        return_type_dict_params: std::cell::RefCell::new(Vec::new()),
        used_return_type_dicts: std::cell::RefCell::new(HashSet::new()),
        used_js_names: std::cell::RefCell::new(HashSet::new()),
        deduped_instance_names: std::cell::RefCell::new(HashMap::new()),
        needs_runtime_lazy: Cell::new(false),
        runtime_checks: global.runtime_checks,
        needs_runtime_check: Cell::new(false),
        class_expected_fields: &global.class_expected_fields,
        value_types,
        span_types,
    };

    // Pre-populate used_js_names with all value, constructor, and foreign names
    for decl in &module.decls {
        match decl {
            Decl::Value { name, .. } => {
                ctx.used_js_names.borrow_mut().insert(ident_to_js(name.value.symbol()));
            }
            Decl::Data { constructors, .. } => {
                for ctor in constructors {
                    ctx.used_js_names.borrow_mut().insert(ident_to_js(ctor.name.value.symbol()));
                }
            }
            Decl::Newtype { constructor, .. } => {
                ctx.used_js_names.borrow_mut().insert(ident_to_js(constructor.value.symbol()));
            }
            Decl::Foreign { name, .. } => {
                ctx.used_js_names.borrow_mut().insert(ident_to_js(name.value.symbol()));
            }
            Decl::Class { members, .. } => {
                for member in members {
                    ctx.used_js_names.borrow_mut().insert(ident_to_js(member.name.value.symbol()));
                }
            }
            _ => {}
        }
    }

    // Build type operator → target map from fixity declarations
    for decl in &module.decls {
        if let Decl::Fixity { is_type: true, target, operator, .. } = decl {
            ctx.type_op_targets.insert(operator.value.symbol(), target.name);
        }
    }
    // Also collect from imported modules' CST fixity declarations
    // (these are in the module's imports, not the registry)
    // For now, we rely on the typechecker's instance_registry which already resolved names.

    // Merge imported constructor details (ctor_details, data_constructors, newtype_names)
    // so pattern matching on imported constructors generates proper instanceof checks.
    for imp in &module.imports {
        let parts = &imp.module.parts;
        if !parts.is_empty() {
            let first = interner::resolve(parts[0]).unwrap_or_default();
            if first == "Prim" { continue; }
        }
        if *parts == module_parts { continue; }
        if let Some(mod_exports) = registry.lookup(parts) {
            for (qi, details) in &mod_exports.ctor_details {
                ctx.ctor_details.entry(qi.clone()).or_insert_with(|| details.clone());
            }
            for (qi, ctors) in &mod_exports.data_constructors {
                ctx.data_constructors.entry(qi.clone()).or_insert_with(|| ctors.clone());
            }
            for name in &mod_exports.newtype_names {
                ctx.newtype_names.insert(*name);
            }
        }
    }

    // op_fixities, all_class_methods, all_class_superclasses, known_runtime_classes
    // are borrowed from GlobalCodegenData (pre-computed once).
    // all_fn_constraints was initialized in the CodegenCtx constructor with local_names filtering.

    let mut exported_names: Vec<(String, Option<String>)> = Vec::new();
    let mut foreign_re_exports: Vec<String> = Vec::new();

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

        let mut js_name = module_name_to_js(parts);
        // Avoid clashes with local names (e.g., import Test + data constructor Test)
        let js_name_sym = interner::intern(&js_name);
        if ctx.local_names.contains(&js_name_sym) {
            js_name = format!("{js_name}$module");
        }
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

    // Ensure origin modules referenced by name_source and operator_targets have JS imports.
    // When we trace through value_origins, we may reference modules not
    // directly in module.imports (e.g., Data.Show via Prelude).
    {
        let mut origin_modules: Vec<Vec<Symbol>> = Vec::new();
        // From operator_targets
        for (source_parts, _) in ctx.operator_targets.values() {
            if let Some(parts) = source_parts {
                if !ctx.import_map.contains_key(parts) {
                    origin_modules.push(parts.clone());
                }
            }
        }
        // From name_source (value origin modules)
        for parts in ctx.name_source.values() {
            if !ctx.import_map.contains_key(parts) {
                origin_modules.push(parts.clone());
            }
        }
        origin_modules.sort();
        origin_modules.dedup();
        for parts in origin_modules {
            let mut js_name = module_name_to_js(&parts);
            let js_name_sym = interner::intern(&js_name);
            if ctx.local_names.contains(&js_name_sym) {
                js_name = format!("{js_name}$module");
            }
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
            ctx.import_map.insert(parts, js_name);
        }
    }

    // Instance tables are initialized from GlobalCodegenData (cloned).
    // Overlay local module instances (these take priority via insert, overwriting global data).
    // 1. From this module's own exports (populated by the typechecker)
    for (&(class_name, head_name), &inst_sym) in &exports.instance_registry {
        ctx.instance_registry.insert((class_name, head_name), inst_sym);
        ctx.instance_sources.insert(inst_sym, None);
    }
    // 2. Also scan CST for local instances (in case typechecker didn't populate all)
    for decl in &module.decls {
        if let Decl::Instance { name: Some(n), class_name, types, constraints, .. } = decl {
            if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                ctx.instance_registry.insert((ClassName::new(class_name.name.symbol()), TypeName::new(head)), n.value.symbol());
            }
            // Always mark local instances as local in instance_sources,
            // even when the head type is a type variable (e.g., TypeEquals a a).
            // Without this, an imported instance with the same name takes priority.
            ctx.instance_sources.insert(n.value.symbol(), None);
            // Track constraint classes for this instance
            let constraint_classes: Vec<Symbol> = constraints.iter().map(|c| c.class.name.symbol()).collect();
            ctx.instance_constraint_classes.insert(n.value.symbol(), constraint_classes);
        }
        if let Decl::Derive { name: Some(n), constraints, .. } = decl {
            let constraint_classes: Vec<Symbol> = constraints.iter().map(|c| c.class.name.symbol()).collect();
            ctx.instance_constraint_classes.insert(n.value.symbol(), constraint_classes);
        }
    }

    // Add JS imports for instance source modules referenced by resolved_dicts
    // (instances from transitive dependencies need to be importable)
    {
        use crate::typechecker::registry::DictExpr;
        fn collect_dict_names(dict: &DictExpr, names: &mut HashSet<Symbol>) {
            match dict {
                DictExpr::Var(name, _) => { names.insert(*name); }
                DictExpr::App(name, subs, _) => {
                    names.insert(*name);
                    for sub in subs { collect_dict_names(sub, names); }
                }
                DictExpr::ConstraintArg(_) => {} // Local constraint param, no import needed
                DictExpr::InlineIsSymbol(_) => {} // Inline dict, no import needed
                DictExpr::InlineReflectable(_) => {} // Inline dict, no import needed
                DictExpr::ZeroCost => {} // Zero-cost constraint, no import needed
                DictExpr::SuperClassAccess(_, _) => {} // Derived from constraint param, no import needed
            }
        }
        let mut needed_names = HashSet::new();
        for dicts in exports.resolved_dicts.values() {
            for (_, dict_expr) in dicts {
                collect_dict_names(dict_expr, &mut needed_names);
            }
        }
        let mut needed_modules: HashSet<Vec<Symbol>> = HashSet::new();
        for name in &needed_names {
            if ctx.local_names.contains(name) { continue; }
            if ctx.name_source.contains_key(name) { continue; }
            if let Some(Some(parts)) = ctx.instance_sources.get(name) {
                if !ctx.import_map.contains_key(parts) {
                    needed_modules.insert(parts.clone());
                }
            }
        }
        let mut sorted_needed_modules: Vec<_> = needed_modules.into_iter().collect();
        sorted_needed_modules.sort();
        for parts in sorted_needed_modules {
            if !parts.is_empty() {
                let first = interner::resolve(parts[0]).unwrap_or_default();
                if first == "Prim" { continue; }
            }
            if parts == ctx.module_parts { continue; }

            let js_name = module_name_to_js(&parts);
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
            ctx.import_map.insert(parts, js_name);
        }
    }

    // Add JS imports for instance source modules referenced by derive newtype instances.
    // When `derive newtype instance Foo Bar`, the codegen needs to reference the underlying
    // type's instance, which may live in a module not yet imported.
    {
        let mut needed_modules: HashSet<Vec<Symbol>> = HashSet::new();
        for decl in &module.decls {
            if let Decl::Derive { newtype: true, class_name, types, .. } = decl {
                // Find the underlying type's instance
                if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                    let qi = unqualified_type_sym(head);
                    if let Some(ctor_names) = ctx.data_constructors.get(&qi) {
                        if let Some(ctor_qi) = ctor_names.first() {
                            if let Some((_, _, field_types)) = ctx.ctor_details.get(ctor_qi) {
                                if let Some(underlying_ty) = field_types.first() {
                                    if let Some(underlying_head) = extract_head_from_type(underlying_ty) {
                                        // Look up the instance for (class, underlying_head) in the registry
                                        if let Some(inst_name) = ctx.instance_registry.get(&(ClassName::new(class_name.name.symbol()), TypeName::new(underlying_head))) {
                                            if !ctx.local_names.contains(inst_name) {
                                                if let Some(Some(parts)) = ctx.instance_sources.get(inst_name) {
                                                    if !ctx.import_map.contains_key(parts) {
                                                        needed_modules.insert(parts.clone());
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        let mut sorted_derive_modules: Vec<_> = needed_modules.into_iter().collect();
        sorted_derive_modules.sort();
        for parts in sorted_derive_modules {
            if !parts.is_empty() {
                let first = interner::resolve(parts[0]).unwrap_or_default();
                if first == "Prim" { continue; }
            }
            if parts == ctx.module_parts { continue; }
            let js_name = module_name_to_js(&parts);
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
            ctx.import_map.insert(parts, js_name);
        }
    }

    // Add JS imports for all instance source modules that aren't yet imported.
    // This ensures that resolve_instance_ref can always qualify instance references
    // (e.g., derived Eq/Ord instances referencing field type instances from other modules).
    {
        let mut needed_modules: HashSet<Vec<Symbol>> = HashSet::new();
        for (_, source) in &ctx.instance_sources {
            if let Some(parts) = source {
                if !ctx.import_map.contains_key(parts) {
                    needed_modules.insert(parts.clone());
                }
            }
        }
        let mut sorted_modules: Vec<_> = needed_modules.into_iter().collect();
        sorted_modules.sort();
        for parts in sorted_modules {
            if !parts.is_empty() {
                let first = interner::resolve(parts[0]).unwrap_or_default();
                if first == "Prim" { continue; }
            }
            if parts == ctx.module_parts { continue; }
            let js_name = module_name_to_js(&parts);
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
            ctx.import_map.insert(parts, js_name);
        }
    }

    // Add Data.Ordering import if any derive Ord instances exist
    {
        let ord_sym = interner::intern("Ord");
        let has_derive_ord = module.decls.iter().any(|decl| {
            matches!(decl, Decl::Derive { class_name, .. } if class_name.name.symbol() == ord_sym)
        });
        if has_derive_ord {
            let ordering_parts: Vec<Symbol> = vec![interner::intern("Data"), interner::intern("Ordering")];
            if !ctx.import_map.contains_key(&ordering_parts) {
                let js_name = module_name_to_js(&ordering_parts);
                let path = "../Data.Ordering/index.js".to_string();
                imports.push(JsStmt::Import {
                    name: js_name.clone(),
                    path,
                });
                ctx.import_map.insert(ordering_parts, js_name);
            }
        }
    }

    // Build map of type signatures for constrained higher-rank parameter detection
    let mut type_sig_map: HashMap<Symbol, &TypeExpr> = HashMap::new();
    for decl in &module.decls {
        if let Decl::TypeSignature { name, ty, .. } = decl {
            type_sig_map.insert(name.value.symbol(), ty);
        }
    }

    // Pre-compute set of all module-level constrained function JS names.
    // Used to prevent hoisting calls to sibling constrained functions, which
    // would cause mutual recursion at init time (stack overflow).
    let constrained_fn_js_names: HashSet<String> = {
        let mut names = HashSet::new();
        for decl in &module.decls {
            if let Decl::TypeSignature { name, .. } = decl {
                let sym = name.value.symbol();
                if let Some(constraints) = ctx.exports.signature_constraints.get(&unqualified_value_sym(sym)) {
                    let has_runtime = constraints.iter().any(|(class_qi, _)| {
                        ctx.known_runtime_classes.contains(&class_qi.name_symbol())
                    });
                    if has_runtime {
                        names.insert(ident_to_js(sym));
                    }
                }
            }
        }
        names
    };

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
                ctx.fresh_counter.set(0);
                // Detect constrained higher-rank parameters from type signature
                ctx.constrained_hr_params.borrow_mut().clear();
                if let Some(ty_sig) = type_sig_map.get(name_sym) {
                    // Get binder names from the first value declaration
                    let binder_names: Vec<Symbol> = decls.iter()
                        .filter_map(|d| if let Decl::Value { binders, .. } = d { Some(binders) } else { None })
                        .next()
                        .map(|binders| binders.iter().filter_map(|b| extract_simple_binder_name(b)).collect())
                        .unwrap_or_default();
                    let constrained_indices = extract_constrained_param_indices(ty_sig);
                    for (idx, dict_name) in &constrained_indices {
                        if let Some(&param_name) = binder_names.get(*idx) {
                            ctx.constrained_hr_params.borrow_mut().insert(param_name, dict_name.clone());
                        }
                    }
                }
                // Detect return-type dict params from return_type_constraints
                ctx.return_type_dict_params.borrow_mut().clear();
                ctx.used_return_type_dicts.borrow_mut().clear();
                if let Some(rt_constraints) = ctx.exports.return_type_constraints.get(&unqualified_value_sym(*name_sym)) {
                    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
                    for (class_qi, _) in rt_constraints {
                        if ctx.known_runtime_classes.contains(&class_qi.name_symbol()) {
                            let class_name = class_qi.name.resolve().unwrap_or_default();
                            let count = dict_name_counts.entry(class_name.to_string()).or_insert(0);
                            let dict_param = if *count == 0 {
                                format!("dict{class_name}")
                            } else {
                                format!("dict{class_name}{count}")
                            };
                            *count += 1;
                            ctx.return_type_dict_params.borrow_mut().push(dict_param);
                        }
                    }
                }
                let stmts = gen_value_decl(&ctx, *name_sym, decls, &constrained_fn_js_names);
                body.extend(stmts);
                if is_exported(&ctx, *name_sym) {
                    exported_names.push(export_entry(*name_sym));
                }
            }
            DeclGroup::Data(decl) => {
                if let Decl::Data { name: _data_name, type_vars: _, constructors, .. } = decl {
                    for ctor in constructors {
                        if is_exported(&ctx, ctor.name.value.symbol()) {
                            exported_names.push(export_entry(ctor.name.value.symbol()));
                        }
                    }
                }
                let stmts = gen_data_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Newtype(decl) => {
                if let Decl::Newtype { name: _nt_name, type_vars: _, constructor, .. } = decl {
                    if is_exported(&ctx, constructor.value.symbol()) {
                        exported_names.push(export_entry(constructor.value.symbol()));
                    }
                }
                let stmts = gen_newtype_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Foreign(name_sym) => {
                let original_name = interner::resolve(*name_sym).unwrap_or_default();
                if is_exported(&ctx, *name_sym) {
                    // Foreign exports are re-exported directly from the foreign module
                    foreign_re_exports.push(original_name);
                }
                // No var declaration needed — references use $foreign.name directly
            }
            DeclGroup::Instance(decl) => {
                let override_name = if let Decl::Instance { name: Some(n), .. } = decl {
                    // Named instances use their explicit name (no deduplication needed)
                    exported_names.push(export_entry(n.value.symbol()));
                    None
                } else if let Decl::Instance { name: None, class_name, types, .. } = decl {
                    // Unnamed instances — generate and deduplicate name to avoid collisions
                    let raw_name = gen_unnamed_instance_name(class_name.name.symbol(), types, &ctx.instance_registry, &ctx.type_op_targets);
                    let deduped = ctx.deduplicate_js_name(raw_name.clone());
                    // If the name was deduplicated, record the mapping so that
                    // dict_expr_to_js can translate references to this instance.
                    if deduped != raw_name {
                        if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                            if let Some(&orig_sym) = ctx.instance_registry.get(&(ClassName::new(class_name.name.symbol()), TypeName::new(head))) {
                                ctx.deduped_instance_names.borrow_mut().insert(orig_sym, deduped.clone());
                            }
                        }
                    }
                    exported_names.push((deduped.clone(), None));
                    Some(deduped)
                } else {
                    None
                };
                let stmts = gen_instance_decl(&ctx, decl, override_name);
                body.extend(stmts);
            }
            DeclGroup::Class(decl) => {
                // Export class method names using original PS symbols (not JS-encoded names)
                if let Decl::Class { members, .. } = decl {
                    for member in members {
                        if is_exported(&ctx, member.name.value.symbol()) {
                            exported_names.push(export_entry(member.name.value.symbol()));
                        }
                    }
                }
                let stmts = gen_class_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Fixity(decl) => {
                // Operator aliases produce no JS output for type-level operators or
                // constructor aliases. For function aliases (e.g. `infix 5 tie as -#-`),
                // we generate a `var $op = target;` binding so the operator can be
                // accessed as a named export (e.g. `Foo.$minus$hash$minus`).
                if let Decl::Fixity { is_type, operator, target, .. } = decl {
                    if !is_type && ctx.function_op_aliases.contains(&unqualified_op_sym(operator.value.symbol())) {
                        let op_js = any_name_to_js(&interner::resolve(operator.value.symbol()).unwrap_or_default());
                        let target_expr = crate::codegen::js::expr::gen_qualified_ref_with_span(
                            &ctx,
                            target.module.map(|m| m),
                            target.name,
                            None,
                        );
                        body.push(JsStmt::VarDecl(op_js.clone(), Some(target_expr)));
                        exported_names.push((op_js, None));
                    }
                }
            }
            DeclGroup::Derive(decl) => {
                let override_name = if let Decl::Derive { name: Some(name), .. } = decl {
                    // Named derive instances use their explicit name
                    exported_names.push(export_entry(name.value.symbol()));
                    None
                } else if let Decl::Derive { name: None, class_name, types, .. } = decl {
                    // Unnamed derive instances — generate and deduplicate name
                    let raw_name = gen_unnamed_instance_name(class_name.name.symbol(), types, &ctx.instance_registry, &ctx.type_op_targets);
                    let deduped = ctx.deduplicate_js_name(raw_name.clone());
                    if deduped != raw_name {
                        if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                            if let Some(&orig_sym) = ctx.instance_registry.get(&(ClassName::new(class_name.name.symbol()), TypeName::new(head))) {
                                ctx.deduped_instance_names.borrow_mut().insert(orig_sym, deduped.clone());
                            }
                        }
                    }
                    exported_names.push((deduped.clone(), None));
                    Some(deduped)
                } else {
                    None
                };
                let stmts = gen_derive_decl(&ctx, decl, override_name);
                body.extend(stmts);
            }
            DeclGroup::TypeAlias
            | DeclGroup::TypeSig | DeclGroup::ForeignData
            | DeclGroup::KindSig => {
                // These produce no JS output
            }
        }
    }

    // Topological sort: reorder body declarations so that dependencies come before uses
    body = topo_sort_body(body);

    // Generate re-exports: for names exported by this module but defined elsewhere,
    // use `export { name } from "module"` syntax instead of local var bindings.
    // Collect names that are already in the main export block.
    // These should NOT also appear in re-export blocks (would cause duplicate export errors).
    // Note: we use exported_names (not all defined_names) because a name can be locally defined
    // (e.g., as an instance method variable) without being exported — in that case, it should
    // still be re-exported from the source module if `module M` re-exports it.
    let exported_name_set: HashSet<String> = exported_names
        .iter()
        .map(|(name, _)| name.clone())
        .collect();

    // Build a map of module_name → set of value names imported from that module.
    // This is used to filter re-exports: `module M` in the export list should only
    // re-export names that were explicitly imported from M.
    let mut imported_names_by_module: HashMap<String, HashSet<Symbol>> = HashMap::new();
    // For re-exports, track the import source module for each name.
    // Explicit imports use the import source; import-all uses name_source (origin).
    let mut reexport_source: HashMap<Symbol, String> = HashMap::new();
    for imp in &module.imports {
        let mod_name = imp.module.parts.iter()
            .map(|s| interner::resolve(*s).unwrap_or_default())
            .collect::<Vec<_>>()
            .join(".");
        if let Some(ImportList::Explicit(items)) = &imp.imports {
            let entry = imported_names_by_module.entry(mod_name.clone()).or_default();
            for item in items {
                match item {
                    Import::Value(ident) => {
                        entry.insert(ident.value.symbol());
                        reexport_source.entry(ident.value.symbol()).or_insert_with(|| mod_name.clone());
                    }
                    Import::Type(ident, members) => {
                        // Type name itself — NOT inserted, types don't have runtime values.
                        // Only data constructors are runtime values that can be re-exported.
                        // Constructors
                        match members {
                            Some(DataMembers::All) => {
                                // All constructors — look them up from the specific imported
                                // module's exports to avoid name collisions (e.g., Step exists
                                // in both Data.List.Lazy.Types and Control.Monad.Rec.Class).
                                let qi = unqualified_type_sym(ident.value.symbol());
                                let ctor_names = ctx.registry.lookup(&imp.module.parts)
                                    .and_then(|mod_exp| mod_exp.data_constructors.get(&qi))
                                    .or_else(|| ctx.data_constructors.get(&qi));
                                if let Some(ctor_names) = ctor_names {
                                    for ctor in ctor_names {
                                        entry.insert(ctor.name_symbol());
                                        reexport_source.entry(ctor.name_symbol()).or_insert_with(|| mod_name.clone());
                                    }
                                }
                            }
                            Some(DataMembers::Explicit(ctors)) => {
                                for c in ctors {
                                    entry.insert(c.value.symbol());
                                    reexport_source.entry(c.value.symbol()).or_insert_with(|| mod_name.clone());
                                }
                            }
                            None => {}
                        }
                    }
                    Import::Class(_ident) => {
                        // Don't add class methods to the imported names set.
                        // Only explicitly listed Import::Value items should count
                        // for re-export filtering. The original compiler re-exports
                        // only values explicitly named in the import list.
                    }
                    Import::TypeOp(_) => {} // operators don't produce re-exports
                }
            }
        } else if imp.imports.is_none() || matches!(imp.imports, Some(ImportList::Hiding(_))) {
            // `import M` or `import M hiding (...)` — imports everything (or almost everything).
            // Populate with names from that module that are also in the current module's
            // exports, so that `module M` in the export list re-exports them correctly.
            // We intersect with the current module's exports to avoid re-exporting names
            // that the import source's JS output doesn't actually provide.
            let entry = imported_names_by_module.entry(mod_name).or_default();
            if let Some(mod_exports) = ctx.registry.lookup(&imp.module.parts) {
                for qi in mod_exports.values.keys() {
                    // Only include if the current module also exports this name
                    let as_ctor = qi.map(names::value_as_constructor);
                    if exports.values.contains_key(qi) || exports.ctor_details.contains_key(&as_ctor) {
                        entry.insert(qi.name_symbol());
                    }
                }
                for qi in mod_exports.ctor_details.keys() {
                    let as_val = qi.map(names::constructor_as_value);
                    if exports.values.contains_key(&as_val) || exports.ctor_details.contains_key(qi) {
                        entry.insert(qi.name_symbol());
                    }
                }
            }
        }
    }

    // Build alias → full module name map from imports
    let mut import_alias_to_full: HashMap<String, Vec<String>> = HashMap::new();
    for imp in &module.imports {
        let full_name = imp.module.parts.iter()
            .map(|s| interner::resolve(*s).unwrap_or_default())
            .collect::<Vec<_>>()
            .join(".");
        if let Some(ref alias) = imp.qualified {
            let alias_name = alias.parts.iter()
                .map(|s| interner::resolve(*s).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".");
            import_alias_to_full.entry(alias_name).or_default().push(full_name.clone());
        }
        // Also map full name to itself (for unaliased re-exports)
        import_alias_to_full.entry(full_name.clone()).or_default().push(full_name);
    }

    // Collect re-exported module names from the export list
    let mut reexported_modules: HashSet<String> = HashSet::new();
    if let Some(export_list) = &module.exports {
        for export in &export_list.value.exports {
            if let Export::Module(mod_name) = export {
                let name = mod_name.parts.iter()
                    .map(|s| interner::resolve(*s).unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(".");
                // Resolve alias to full module name(s)
                if let Some(full_names) = import_alias_to_full.get(&name) {
                    for full_name in full_names {
                        reexported_modules.insert(full_name.clone());
                    }
                } else {
                    reexported_modules.insert(name);
                }
            }
        }
    }

    let mut reexport_map: HashMap<String, Vec<(String, Option<String>)>> = HashMap::new();
    // Generate re-exports directly from the export list's `module M` entries.
    // For each re-exported module, include only the names explicitly imported from that module.
    // Use name_source to find the ORIGINAL defining module for each name, so that
    // re-exports from re-export modules (e.g., Prelude) point to the actual source.
    for reexported_mod in &reexported_modules {
        if let Some(imported) = imported_names_by_module.get(reexported_mod) {
            for name_sym in imported {
                let original_name = interner::resolve(*name_sym).unwrap_or_default();
                // Skip operator symbols
                if original_name.chars().next().map_or(false, |c| !c.is_alphabetic() && c != '_') {
                    continue;
                }
                // Skip names that are already in the main export block (would cause duplicate exports)
                let js_name = ident_to_js(*name_sym);
                if exported_name_set.contains(&js_name) {
                    continue;
                }
                // Skip type-only names — only include names that have a runtime value
                let val_qi = unqualified_value_sym(*name_sym);
                let ctor_qi = unqualified_ctor_sym(*name_sym);
                let has_value = exports.values.contains_key(&val_qi)
                    || ctx.ctor_details.contains_key(&ctor_qi);
                if !has_value {
                    let mut found_in_any = false;
                    for (_, mod_exports) in ctx.registry.iter_all() {
                        if mod_exports.values.contains_key(&val_qi)
                            || mod_exports.ctor_details.contains_key(&ctor_qi)
                        {
                            found_in_any = true;
                            break;
                        }
                    }
                    if !found_in_any {
                        continue;
                    }
                }
                // For explicit imports, use the import source module (matching the original
                // compiler). For import-all, use name_source to find the defining module
                // (since the import source may be a re-export module without the name in
                // its own JS output).
                let js_path = if let Some(source_mod) = reexport_source.get(name_sym) {
                    format!("../{}/index.js", source_mod)
                } else if let Some(origin_parts) = ctx.name_source.get(name_sym) {
                    let origin_mod = origin_parts.iter()
                        .map(|s| interner::resolve(*s).unwrap_or_default())
                        .collect::<Vec<_>>()
                        .join(".");
                    format!("../{}/index.js", origin_mod)
                } else {
                    format!("../{}/index.js", reexported_mod)
                };
                // Use the export_name (what the source module actually exports)
                let ext_name = export_name(*name_sym);
                reexport_map
                    .entry(js_path.clone())
                    .or_default()
                    .push((ext_name, None));
            }
        }
    }
    // Convert to sorted vec
    let mut reexports: Vec<(String, Vec<(String, Option<String>)>)> = reexport_map.into_iter().collect();
    reexports.sort_by(|a, b| a.0.cmp(&b.0));

    let foreign_module_path = if has_ffi {
        Some("./foreign.js".to_string())
    } else {
        None
    };

    // Topologically sort body declarations so that dependencies come before dependents
    let mut body = topo_sort_body(body);

    // Build constructor arity map for uncurrying
    let ctor_arities: HashMap<String, usize> = ctx.ctor_details.iter()
        .map(|(qi, (_, _, fields))| {
            let name = export_name(qi.name.symbol());
            (name, fields.len())
        })
        .collect();

    // Convert Ctor.create(a)(b) to new Ctor(a, b) — matches reference compiler
    body = body.into_iter().map(|s| uncurry_create_to_new_stmt(s, &ctor_arities)).collect();

    // Inline mutual recursion in where-bound functions to make them self-recursive,
    // enabling TCO in the subsequent pass.
    inline_mutual_recursion_for_tco(&mut body);

    // Apply TCO to any tail-recursive top-level functions
    apply_tco_if_applicable(&mut body);

    // inline_field_access_in_stmt disabled for correctness debugging

    // Module-level dict hoisting disabled for correctness

    // Apply $runtime_lazy wrapping for self-referential/mutually-recursive module-level bindings
    // (e.g., typeclass instance dictionaries that form cycles)
    apply_runtime_lazy(&ctx, &mut body);

    // Move import-only constants (non-functions) to the front of the module body.
    // These are CSE-hoisted dict applications like `var bind = M.bind(M.bindEffect)`.
    // They have no local dependencies and must be available before any function
    // whose body references them is called.
    {
        let local_names: HashSet<String> = body.iter().filter_map(|s| {
            if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
        }).collect();
        let (import_only, rest): (Vec<_>, Vec<_>) = body.into_iter().partition(|stmt| {
            if let JsStmt::VarDecl(_, Some(init)) = stmt {
                if matches!(init, JsExpr::Function(..)) {
                    return false;
                }
                let mut refs = HashSet::new();
                collect_eager_refs_expr(init, &mut refs);
                !refs.iter().any(|r| local_names.contains(r))
            } else {
                false
            }
        });
        body = import_only;
        body.extend(rest);
    }

    // Move constructor declarations (self-contained IIFEs) to the front.
    // Constructors have no external deps and are needed before any code
    // that uses `instanceof` or `new Ctor()`.
    {
        let (ctors, rest): (Vec<_>, Vec<_>) = body.into_iter().partition(|stmt| {
            is_constructor_iife(stmt)
        });
        body = ctors;
        body.extend(rest);
    }

    // Move `main` to the end of the module body.
    // `main` is the entry point and its eager expressions may transitively depend
    // on any module-level var. Placing it last ensures everything is initialized.
    {
        let main_idx = body.iter().position(|s| {
            matches!(s, JsStmt::VarDecl(name, _) if name == "main")
        });
        if let Some(idx) = main_idx {
            let main_stmt = body.remove(idx);
            body.push(main_stmt);
        }
    }

    // Inline known typeclass operations (e.g., ordInt compare → native operators)
    // This is kept because native JS operators handle NaN correctly per IEEE 754
    for stmt in body.iter_mut() {
        inline_known_ops_stmt(stmt);
    }

    // Eliminate unused imports: only keep imports whose module name is actually
    // referenced in the generated body via ModuleAccessor expressions,
    // or whose module path is a re-export source.
    let used_modules = collect_used_modules(&body);
    // Build set of import paths that are re-export sources
    let mut reexport_paths: HashSet<String> = reexports.iter().map(|(path, _)| path.clone()).collect();
    // Also keep imports for modules that appear in `module M` export entries,
    // even if they only re-export types (no runtime values). The original compiler does this.
    for mod_name in &reexported_modules {
        reexport_paths.insert(format!("../{mod_name}/index.js"));
    }
    let mut imports: Vec<JsStmt> = imports.into_iter().filter(|stmt| {
        if let JsStmt::Import { name, path, .. } = stmt {
            used_modules.contains(name.as_str()) || reexport_paths.contains(path)
        } else {
            true
        }
    }).collect();

    // Sort imports by name for deterministic output
    imports.sort_by(|a, b| {
        let name_a = match a { JsStmt::Import { name, .. } => name.as_str(), _ => "" };
        let name_b = match b { JsStmt::Import { name, .. } => name.as_str(), _ => "" };
        name_a.cmp(name_b)
    });
    // Deduplicate exports (same JS name can appear from value + instance)
    {
        let mut seen = HashSet::new();
        exported_names.retain(|(js_name, _)| seen.insert(js_name.clone()));
    }
    // If any binding needed $runtime_lazy, prepend the helper function
    if ctx.needs_runtime_lazy.get() {
        body.insert(0, gen_runtime_lazy_decl());
    }
    // If any runtime checks were emitted, prepend the import for the shared helpers module
    if ctx.needs_runtime_check.get() {
        imports.insert(0, gen_runtime_check_import());
    }

    JsModule {
        imports,
        body,
        exports: exported_names,
        foreign_exports: foreign_re_exports,
        foreign_module_path,
        reexports,
    }
}

/// Generate the $runtime_lazy helper function declaration.
pub(crate) fn gen_runtime_lazy_decl() -> JsStmt {
    // Use RawJs for the helper since it's a fixed template
    JsStmt::VarDecl("$runtime_lazy".to_string(), Some(JsExpr::RawJs(
        "function (name, moduleName, init) {\n\
         \x20   var state = 0;\n\
         \x20   var val;\n\
         \x20   return function () {\n\
         \x20       if (state === 2) return val;\n\
         \x20       if (state === 1) throw new ReferenceError(name + \" was needed before it finished initializing (module \" + moduleName + \")\", moduleName);\n\
         \x20       state = 1;\n\
         \x20       val = init();\n\
         \x20       state = 2;\n\
         \x20       return val;\n\
         \x20   };\n\
         }".to_string()
    )))
}

/// Generate a $proxy_dict call that wraps a dict param in a Proxy for access validation.
/// The dict variable is reassigned to the Proxy-wrapped version.
pub(crate) fn gen_dict_proxy_wrap(dict_param: &str, class_name: &str, expected_fields: impl IntoIterator<Item = impl AsRef<str>>, location: &str) -> JsStmt {
    let check_fn = JsExpr::Var("$proxy_dict".to_string());
    JsStmt::Assign(
        JsExpr::Var(dict_param.to_string()),
        JsExpr::App(
            Box::new(check_fn),
            vec![
                JsExpr::Var(dict_param.to_string()),
                JsExpr::StringLit(class_name.to_string()),
                JsExpr::ArrayLit(expected_fields.into_iter().map(|f| JsExpr::StringLit(f.as_ref().to_string())).collect()),
                JsExpr::StringLit(location.to_string()),
            ],
        ),
    )
}

/// Generate a $check call statement for a value.
pub(crate) fn gen_value_check_call(js_var: &str, expected: &str, location: &str) -> JsStmt {
    let check_fn = JsExpr::Var("$check".to_string());
    JsStmt::Expr(JsExpr::App(
        Box::new(check_fn),
        vec![
            JsExpr::Var(js_var.to_string()),
            JsExpr::StringLit(expected.to_string()),
            JsExpr::StringLit(location.to_string()),
        ],
    ))
}

/// For well-known class methods, returns (arity, result_js_type) where arity is
/// the number of curried arguments before the result, and result_js_type is the
/// expected JS typeof of the final return value.
/// E.g. Show.show :: a -> String → (1, "string")
/// E.g. Eq.eq :: a -> a -> Boolean → (2, "boolean")
pub(crate) fn known_method_result_type(class_name: &str, method_name: &str) -> Option<(usize, &'static str)> {
    match (class_name, method_name) {
        ("Show", "show") => Some((1, "string")),
        ("Eq", "eq") => Some((2, "boolean")),
        ("HeytingAlgebra", "not") => Some((1, "boolean")),
        ("HeytingAlgebra", "disj") => Some((2, "boolean")),
        ("HeytingAlgebra", "conj") => Some((2, "boolean")),
        ("HeytingAlgebra", "implies") => Some((2, "boolean")),
        ("BooleanAlgebra", _) => None, // inherits from HeytingAlgebra
        _ => None,
    }
}

/// Map a Type to the expected JS typeof string for runtime checking.
/// Returns None for polymorphic or uncheckable types.
pub(crate) fn type_to_js_check(ty: &Type) -> Option<&'static str> {
    match ty {
        Type::Con(qi) => {
            let name = qi.name.resolve().unwrap_or_default();
            match name.as_ref() {
                "Int" => Some("integer"),
                "Number" => Some("number"),
                "String" | "Char" => Some("string"),
                "Boolean" => Some("boolean"),
                // Don't check user-defined Con types — they could be newtypes
                // over primitives (e.g., Milliseconds wrapping Number)
                _ => None,
            }
        }
        Type::Fun(_, _) => Some("function"),
        Type::Record(_, _) => Some("object"),
        Type::App(head, _) => {
            // Only check Array — other applied types could be newtypes,
            // Effect/Aff (functions), or polymorphic
            let mut h = head.as_ref();
            loop {
                match h {
                    Type::App(hh, _) => h = hh.as_ref(),
                    Type::Con(qi) => {
                        let name = qi.name.resolve().unwrap_or_default();
                        return match name.as_ref() {
                            "Array" => Some("array"),
                            _ => None,
                        };
                    }
                    _ => return None,
                }
            }
        }
        Type::Forall(_, inner) => type_to_js_check(inner),
        Type::Var(_) | Type::Unif(_) => None, // polymorphic, can't check
        Type::TypeString(_) | Type::TypeInt(_) => None, // type-level, not runtime values
    }
}

/// Generate runtime check statements for a value given its Type.
/// Returns empty vec for uncheckable types.
pub(crate) fn type_to_check_stmts(ty: &Type, js_var: &str, location: &str) -> Vec<JsStmt> {
    if let Some(expected) = type_to_js_check(ty) {
        vec![gen_value_check_call(js_var, expected, location)]
    } else {
        vec![]
    }
}

/// Decompose a function type into (param_types, return_type).
/// Strips Forall wrappers but stops at non-Fun types.
fn decompose_fun_type(ty: &Type) -> Vec<&Type> {
    let mut params = Vec::new();
    let mut current = ty;
    loop {
        match current {
            Type::Forall(_, inner) => { current = inner; }
            Type::Fun(arg, ret) => {
                params.push(arg.as_ref());
                current = ret;
            }
            _ => break,
        }
    }
    params
}

/// Insert runtime type checks into a curried function expression.
/// Walks into nested Function nodes and inserts $check calls for each parameter
/// whose type is known and checkable.
pub(crate) fn insert_arg_type_checks(
    expr: &mut JsExpr,
    ty: &Type,
    fn_name: &str,
    needs_runtime_check: &Cell<bool>,
) {
    let param_types = decompose_fun_type(ty);
    if param_types.is_empty() {
        return;
    }
    insert_arg_checks_recursive(expr, &param_types, 0, fn_name, needs_runtime_check);
}

fn insert_arg_checks_recursive(
    expr: &mut JsExpr,
    param_types: &[&Type],
    depth: usize,
    fn_name: &str,
    needs_runtime_check: &Cell<bool>,
) {
    if depth >= param_types.len() {
        return;
    }
    // Match Function(None, [param_name], body)
    if let JsExpr::Function(_, ref params, ref mut body) = expr {
        if params.len() == 1 {
            let param_name = &params[0];
            let ty = param_types[depth];
            let check_stmts = type_to_check_stmts(ty, param_name, &format!("{fn_name}({param_name})"));
            if !check_stmts.is_empty() {
                needs_runtime_check.set(true);
                // Insert checks at the beginning of the function body
                for (i, stmt) in check_stmts.into_iter().enumerate() {
                    body.insert(i, stmt);
                }
            }
            // Recurse into the next level: body should contain Return(Function(...))
            for stmt in body.iter_mut() {
                if let JsStmt::Return(ref mut inner_expr) = stmt {
                    insert_arg_checks_recursive(inner_expr, param_types, depth + 1, fn_name, needs_runtime_check);
                    break;
                }
            }
        }
    }
}

/// Generate the runtime check import statement.
/// Imports helpers from the shared `$runtime_checks.mjs` module in the output root.
pub(crate) fn gen_runtime_check_import() -> JsStmt {
    JsStmt::RawJs(
        "import { $check, $proxy_dict, $proxy_dict_lite, $method_check, $wrap_method, $app } from \"../$runtime_checks.mjs\";".to_string()
    )
}

// ===== Declaration groups =====

#[allow(dead_code)]
pub(crate) enum DeclGroup<'a> {
    Value(Symbol, Vec<&'a Decl>),
    Data(&'a Decl),
    Newtype(&'a Decl),
    Foreign(Symbol),
    Instance(&'a Decl),
    Class(&'a Decl),
    TypeAlias,
    Fixity(&'a Decl),
    TypeSig,
    ForeignData,
    Derive(&'a Decl),
    KindSig,
}

pub(crate) fn collect_decl_groups(decls: &[Decl]) -> Vec<DeclGroup<'_>> {
    // Collect all declarations interleaved in source order.
    // Values with the same name are merged into a single group.
    let mut result: Vec<DeclGroup<'_>> = Vec::new();
    let mut value_map: HashMap<Symbol, Vec<&Decl>> = HashMap::new();
    let mut value_seen: HashSet<Symbol> = HashSet::new();

    // Pre-collect value equations for merging
    for decl in decls {
        if let Decl::Value { name, .. } = decl {
            value_map.entry(name.value.symbol()).or_default().push(decl);
        }
    }

    // Process all declarations in source order (interleaved)
    for decl in decls {
        match decl {
            Decl::Value { name, .. } => {
                let sym = name.value.symbol();
                if value_seen.contains(&sym) {
                    continue;
                }
                value_seen.insert(sym);
                if let Some(equations) = value_map.remove(&sym) {
                    result.push(DeclGroup::Value(sym, equations));
                }
            }
            Decl::Data { kind_sig, is_role_decl, .. } => {
                if *kind_sig != KindSigSource::None {
                    result.push(DeclGroup::KindSig);
                } else if *is_role_decl {
                    // role declarations produce no JS
                } else {
                    result.push(DeclGroup::Data(decl));
                }
            }
            Decl::Newtype { .. } => result.push(DeclGroup::Newtype(decl)),
            Decl::Foreign { name, .. } => result.push(DeclGroup::Foreign(name.value.symbol())),
            Decl::Instance { .. } => result.push(DeclGroup::Instance(decl)),
            Decl::Class { is_kind_sig, .. } => {
                if *is_kind_sig {
                    result.push(DeclGroup::KindSig);
                } else {
                    result.push(DeclGroup::Class(decl));
                }
            }
            Decl::TypeAlias { .. } => result.push(DeclGroup::TypeAlias),
            Decl::Fixity { .. } => result.push(DeclGroup::Fixity(decl)),
            Decl::TypeSignature { .. } => result.push(DeclGroup::TypeSig),
            Decl::ForeignData { .. } => result.push(DeclGroup::ForeignData),
            Decl::Derive { .. } => result.push(DeclGroup::Derive(decl)),
        }
    }
    result
}

// ===== Export checking =====

pub(crate) fn is_exported(ctx: &CodegenCtx, name: Symbol) -> bool {
    match &ctx.module.exports {
        None => true, // No export list means export everything
        Some(export_list) => {
            for export in &export_list.value.exports {
                match export {
                    Export::Value(ident) => {
                        if ident.symbol() == name {
                            return true;
                        }
                    }
                    Export::Type(_, Some(DataMembers::All)) => {
                        // Check if name is a constructor of this type
                        if ctx.ctor_details.contains_key(&unqualified_ctor_sym(name)) {
                            return true;
                        }
                    }
                    Export::Type(_, Some(DataMembers::Explicit(ctors))) => {
                        if ctors.iter().any(|c| c.value.symbol() == name) {
                            return true;
                        }
                    }
                    Export::Class(_) => {
                        // Class methods are exported as values
                        if ctx.exports.class_methods.contains_key(&unqualified_value_sym(name)) {
                            return true;
                        }
                    }
                    Export::Module(_) => {
                        // Module re-exports are handled in the re-export generation code.
                        // Don't return true here — individual names are filtered there.
                    }
                    _ => {}
                }
            }
            false
        }
    }
}

// ===== Value declarations =====

pub(crate) fn gen_value_decl(ctx: &CodegenCtx, name: Symbol, decls: &[&Decl], constrained_siblings: &HashSet<String>) -> Vec<JsStmt> {
    let js_name = ident_to_js(name);

    // Excluded callees = sibling constrained functions minus self.
    // Prevents hoisting calls to these siblings (mutual recursion at init time).
    let excluded_callees: HashSet<String> = constrained_siblings.iter()
        .filter(|n| n.as_str() != js_name)
        .cloned()
        .collect();

    // Check if this value has type class constraints (needs dict params)
    let constraints = ctx.exports.signature_constraints.get(&unqualified_value_sym(name)).cloned();

    // Push dict scope entries for constraints (with unique names for duplicate classes)
    // Only push runtime constraints — zero-cost constraints (Coercible, etc.) have no param.
    let prev_scope_len = ctx.dict_scope.borrow().len();
    if let Some(ref constraints) = constraints {
        let name_str = crate::interner::resolve(name).unwrap_or_default();
        let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
        for (class_qi, _) in constraints {
            if !ctx.known_runtime_classes.contains(&class_qi.name_symbol()) {
                // Push placeholder for zero-cost constraint so ConstraintArg indices stay aligned
                ctx.dict_scope.borrow_mut().push((class_qi.name_symbol(), String::new()));
                continue;
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

    // Also push return-type constraint dicts into scope so that class method
    // resolution (try_apply_dict) can find dicts from inner forall constraints
    // (rank-2 types). E.g., `foo :: a -> Foo a` where `Foo a = forall f. Monad f => f a`
    // needs Applicative available from Monad via superclass chain for `pure`.
    if let Some(rt_constraints) = ctx.exports.return_type_constraints.get(&unqualified_value_sym(name)) {
        let rt_dict_params = ctx.return_type_dict_params.borrow().clone();
        let mut idx = 0;
        for (class_qi, _) in rt_constraints {
            if ctx.known_runtime_classes.contains(&class_qi.name_symbol()) {
                if idx < rt_dict_params.len() {
                    ctx.dict_scope.borrow_mut().push((class_qi.name_symbol(), rt_dict_params[idx].clone()));
                    idx += 1;
                }
            }
        }
    }

    let mut result = if decls.len() == 1 {
        if let Decl::Value { binders, guarded, where_clause, .. } = decls[0] {
            if binders.is_empty() && where_clause.is_empty() {
                // For unconditional let expressions at the top level, inline
                // the bindings + final value instead of wrapping in an IIFE
                if let GuardedExpr::Unconditional(body) = guarded {
                    if let Some(stmts) = try_inline_let_value(ctx, &js_name, body, constraints.as_ref()) {
                        return stmts;
                    }
                }
                let mut expr = gen_guarded_expr(ctx, guarded);
                // Wrap return value with return-type dict params
                let rt_dict_params = ctx.return_type_dict_params.borrow().clone();
                if !rt_dict_params.is_empty() {
                    let used = ctx.used_return_type_dicts.borrow();
                    let any_used = rt_dict_params.iter().any(|p| used.contains(p));
                    if any_used {
                        // Body consumed dicts via try_apply_dict — wrap only (no apply)
                        expr = wrap_expr_with_return_dicts(expr, &rt_dict_params);
                    } else {
                        // Body did not consume dicts — pass-through: apply + wrap
                        expr = wrap_expr_with_return_dicts_apply(expr, &rt_dict_params);
                    }
                }
                let check_ctx = ctx.dict_check_ctx(&js_name);
                expr = wrap_with_dict_params_named_excluding(expr, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name), &excluded_callees, check_ctx.as_ref());
                // Wrap constructor applications/references in IIFE for proper init order
                if references_constructor(&expr) {
                    let ctor_arities: HashMap<String, usize> = ctx.ctor_details.iter()
                        .map(|(qi, (_, _, fields))| (export_name(qi.name.symbol()), fields.len()))
                        .collect();
                    let expr = uncurry_create_to_new(expr, &ctor_arities);
                    let iife = JsExpr::App(
                        Box::new(JsExpr::Function(None, vec![], vec![JsStmt::Return(expr)])),
                        vec![],
                    );
                    vec![JsStmt::VarDecl(js_name, Some(iife))]
                } else {
                    vec![JsStmt::VarDecl(js_name, Some(expr))]
                }
            } else if where_clause.is_empty() {
                // Register binder names as local bindings so body references
                // resolve to locals (not imports with same name)
                let prev_bindings = ctx.local_bindings.borrow().clone();
                for b in binders.iter() {
                    collect_binder_names(b, &mut ctx.local_bindings.borrow_mut());
                }
                let body_expr = gen_guarded_expr_stmts(ctx, guarded);
                *ctx.local_bindings.borrow_mut() = prev_bindings;
                let mut func = gen_curried_function(ctx, binders, body_expr);
                // Insert argument type checks if runtime_checks is enabled
                if ctx.runtime_checks {
                    let vn = ValueName::new(name);
                    if let Some(ty) = ctx.value_types.get(&vn) {
                        insert_arg_type_checks(&mut func, ty, &format!("{}.{}", ctx.module_name, js_name), &ctx.needs_runtime_check);
                    }
                }
                // Wrap return value with return-type dict params
                let rt_dict_params = ctx.return_type_dict_params.borrow().clone();
                if !rt_dict_params.is_empty() {
                    let used = ctx.used_return_type_dicts.borrow();
                    let any_used = rt_dict_params.iter().any(|p| used.contains(p));
                    if any_used {
                        // Body consumed dicts — wrap only
                        func = wrap_return_value_with_dict_params(func, &rt_dict_params);
                    } else {
                        // Body did not consume dicts — apply + wrap (pass-through)
                        func = wrap_return_value_with_dict_params_apply(func, &rt_dict_params);
                    }
                }
                let check_ctx2 = ctx.dict_check_ctx(&js_name);
                func = wrap_with_dict_params_named_excluding(func, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name), &excluded_callees, check_ctx2.as_ref());
                vec![JsStmt::VarDecl(js_name, Some(func))]
            } else {
                let mut iife_body = Vec::new();
                // Register binder + where-clause binding names in local_bindings so that
                // body references resolve to locals (not imports with same name).
                let prev_bindings = ctx.local_bindings.borrow().clone();
                for b in binders.iter() {
                    collect_binder_names(b, &mut ctx.local_bindings.borrow_mut());
                }
                for lb in where_clause.iter() {
                    if let LetBinding::Value { binder, .. } = lb {
                        collect_binder_names(binder, &mut ctx.local_bindings.borrow_mut());
                    }
                }
                gen_let_bindings(ctx, where_clause, &mut iife_body);
                if !iife_body.is_empty() {
                    reorder_where_bindings(&mut iife_body);
                }

                if binders.is_empty() {
                    // Try to inline where bindings at top level (no IIFE)
                    if let GuardedExpr::Unconditional(body) = guarded {
                        let no_constraints = constraints.as_ref().map_or(true, |c| c.is_empty());
                        // Check for module-level name conflicts before inlining
                        let where_names: Vec<String> = iife_body.iter().filter_map(|s| {
                            if let JsStmt::VarDecl(n, _) = s { Some(n.clone()) } else { None }
                        }).collect();
                        let has_conflict = {
                            let existing = ctx.module_level_let_names.borrow();
                            where_names.iter().any(|n| existing.contains(n))
                        };
                        // Check for circular dependencies among where bindings
                        let has_circular_deps = {
                            let name_set: HashSet<&str> = where_names.iter().map(|n| n.as_str()).collect();
                            iife_body.iter().any(|s| {
                                if let JsStmt::VarDecl(_, Some(init)) = s {
                                    let mut var_refs = HashSet::new();
                                    collect_var_refs_in_expr(init, &mut var_refs);
                                    var_refs.iter().any(|r| name_set.contains(r.as_str()))
                                } else {
                                    false
                                }
                            })
                        };
                        if no_constraints && !has_conflict && !has_circular_deps {
                            // Register names as used at module level
                            {
                                let mut existing = ctx.module_level_let_names.borrow_mut();
                                for n in &where_names {
                                    existing.insert(n.clone());
                                }
                            }
                            let body_expr = gen_expr(ctx, body);
                            *ctx.local_bindings.borrow_mut() = prev_bindings;
                            // If body references one of the where bindings, inline
                            if let JsExpr::Var(ref var_name) = body_expr {
                                for i in (0..iife_body.len()).rev() {
                                    if let JsStmt::VarDecl(ref binding_name, ref init) = iife_body[i] {
                                        if binding_name == var_name {
                                            let init = init.clone();
                                            iife_body[i] = JsStmt::VarDecl(js_name.clone(), init);
                                            iife_body.truncate(i + 1);
                                            return iife_body;
                                        }
                                    }
                                }
                            }
                            iife_body.push(JsStmt::VarDecl(js_name.clone(), Some(body_expr)));
                            return iife_body;
                        }
                    }
                    let expr = gen_guarded_expr(ctx, guarded);
                    *ctx.local_bindings.borrow_mut() = prev_bindings;
                    iife_body.push(JsStmt::Return(expr));
                    let iife = JsExpr::App(
                        Box::new(JsExpr::Function(None, vec![], iife_body)),
                        vec![],
                    );
                    let check_ctx3 = ctx.dict_check_ctx(&js_name);
                    let wrapped = wrap_with_dict_params_named_excluding(iife, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name), &excluded_callees, check_ctx3.as_ref());
                    vec![JsStmt::VarDecl(js_name, Some(wrapped))]
                } else {
                    let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                    *ctx.local_bindings.borrow_mut() = prev_bindings;
                    iife_body.extend(body_stmts);
                    // inline_trivial_aliases disabled for correctness debugging
                    let mut func = gen_curried_function_from_stmts(ctx, binders, iife_body);
                    // Insert argument type checks if runtime_checks is enabled
                    if ctx.runtime_checks {
                        let vn = ValueName::new(name);
                        if let Some(ty) = ctx.value_types.get(&vn) {
                            insert_arg_type_checks(&mut func, ty, &format!("{}.{}", ctx.module_name, js_name), &ctx.needs_runtime_check);
                        }
                    }
                    let check_ctx4 = ctx.dict_check_ctx(&js_name);
                    func = wrap_with_dict_params_named_excluding(func, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name), &excluded_callees, check_ctx4.as_ref());
                    vec![JsStmt::VarDecl(js_name, Some(func))]
                }
            }
        } else {
            vec![]
        }
    } else {
        let mut stmts = gen_multi_equation(ctx, &js_name, decls);
        if let Some(ref constraints) = constraints {
            if !constraints.is_empty() {
                if let Some(JsStmt::VarDecl(_, Some(expr))) = stmts.first_mut() {
                    let check_ctx5 = ctx.dict_check_ctx(&js_name);
                    let wrapped = wrap_with_dict_params_named_excluding(expr.clone(), Some(constraints), &ctx.known_runtime_classes, Some(&js_name), &excluded_callees, check_ctx5.as_ref());
                    *expr = wrapped;
                }
            }
        }
        stmts
    };

    // Pop dict scope
    ctx.dict_scope.borrow_mut().truncate(prev_scope_len);

    // If this function has a Partial constraint, wrap with an empty-parameter function.
    // The Partial constraint is zero-cost — no dict is actually passed.
    // unsafePartial strips this layer by calling f() with no args.
    // Reference compiler: function() { return <body>; }
    if ctx.partial_fns.contains(&name) {
        if let Some(JsStmt::VarDecl(_, Some(expr))) = result.first_mut() {
            *expr = JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(expr.clone())],
            );
        }
    }

    // NOTE: Top-level value type checks (non-function) are NOT emitted as separate
    // statements because lazy initialization ($runtime_lazy) and declaration reordering
    // can cause the check to execute before the variable is defined.

    result
}

/// Register VarDecl names from inlined stmts into module_level_let_names,
/// excluding the target declaration name itself (that's the module-level value).
pub(crate) fn register_module_level_names(ctx: &CodegenCtx, stmts: &[JsStmt], target_name: &str) {
    let mut existing = ctx.module_level_let_names.borrow_mut();
    for stmt in stmts {
        if let JsStmt::VarDecl(n, _) = stmt {
            if n != target_name {
                existing.insert(n.clone());
            }
        }
    }
}

