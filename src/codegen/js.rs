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
use crate::typechecker::{ModuleExports, ModuleRegistry};
use crate::typechecker::types::Type;

use super::common::{any_name_to_js, ident_to_js, is_js_builtin, is_js_reserved, is_valid_js_identifier, module_name_to_js};
use super::js_ast::*;

/// Pre-computed global codegen data derived from the full module registry.
/// Computed once before codegen and shared across all modules to avoid
/// redundant `registry.iter_all()` calls per module.
pub struct GlobalCodegenData {
    /// All operator fixities from all modules: op_symbol → (associativity, precedence)
    pub op_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// All class methods: method_name → [(class_qi, type_vars)]
    pub all_class_methods: HashMap<Symbol, Vec<(QualifiedIdent, Vec<QualifiedIdent>)>>,
    /// All signature constraints: fn_name → [class_names]
    pub all_fn_constraints: HashMap<Symbol, Vec<Symbol>>,
    /// All class superclasses: class_name → (type_vars, superclass list)
    pub all_class_superclasses: HashMap<Symbol, (Vec<Symbol>, Vec<(QualifiedIdent, Vec<Type>)>)>,
    /// Classes with methods or superclasses (have runtime dicts)
    pub known_runtime_classes: HashSet<Symbol>,
    /// Class method declaration order: class_name → [method_names]
    pub class_method_order: HashMap<Symbol, Vec<Symbol>>,
    /// Global instance registry: (class, head_type_con) → instance_name
    pub instance_registry: HashMap<(Symbol, Symbol), Symbol>,
    /// Instance sources: instance_name → defining_module_parts
    pub instance_sources: HashMap<Symbol, Option<Vec<Symbol>>>,
    /// Instance constraint classes: instance_name → [class_names]
    pub instance_constraint_classes: HashMap<Symbol, Vec<Symbol>>,
    /// Defining modules for instances: instance_name → module_parts
    pub defining_modules: HashMap<Symbol, Vec<Symbol>>,
}

impl GlobalCodegenData {
    /// Build global codegen data from the registry in a single pass.
    pub fn from_registry(registry: &ModuleRegistry) -> Self {
        let all_modules = registry.iter_all();

        let mut op_fixities: HashMap<Symbol, (Associativity, u8)> = HashMap::new();
        let mut all_class_methods: HashMap<Symbol, Vec<(QualifiedIdent, Vec<QualifiedIdent>)>> = HashMap::new();
        let mut all_fn_constraints: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
        let mut all_class_superclasses: HashMap<Symbol, (Vec<Symbol>, Vec<(QualifiedIdent, Vec<Type>)>)> = HashMap::new();
        let mut class_method_order: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
        let mut instance_registry: HashMap<(Symbol, Symbol), Symbol> = HashMap::new();
        let mut instance_sources: HashMap<Symbol, Option<Vec<Symbol>>> = HashMap::new();
        let mut instance_constraint_classes: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
        let mut defining_modules: HashMap<Symbol, Vec<Symbol>> = HashMap::new();

        // First pass: collect defining_modules (needed for instance_sources)
        for (_mod_parts, mod_exports) in &all_modules {
            for (inst_sym, def_parts) in &mod_exports.instance_modules {
                defining_modules.entry(*inst_sym).or_insert_with(|| def_parts.clone());
            }
        }

        // Main pass: collect everything else
        for (mod_parts, mod_exports) in &all_modules {
            // Operator fixities
            for (op_qi, (assoc, prec)) in &mod_exports.value_fixities {
                op_fixities.entry(op_qi.name).or_insert((*assoc, *prec));
            }

            // Class methods
            for (method, (class, tvs)) in &mod_exports.class_methods {
                all_class_methods.entry(method.name).or_insert_with(Vec::new).push((class.clone(), tvs.clone()));
            }

            // Signature constraints
            for (name, constraints) in &mod_exports.signature_constraints {
                let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name).collect();
                all_fn_constraints.entry(name.name).or_insert(class_names);
            }

            // Class superclasses
            for (name, (tvs, supers)) in &mod_exports.class_superclasses {
                all_class_superclasses.entry(name.name).or_insert_with(|| (tvs.clone(), supers.clone()));
            }

            // Class method order
            for (class_name, methods) in &mod_exports.class_method_order {
                class_method_order.entry(*class_name).or_insert_with(|| methods.clone());
            }

            // Instance registry
            for ((class_sym, head_sym), inst_sym) in &mod_exports.instance_registry {
                instance_registry.entry((*class_sym, *head_sym)).or_insert(*inst_sym);
                let source = defining_modules.get(inst_sym).cloned()
                    .unwrap_or_else(|| mod_parts.to_vec());
                instance_sources.entry(*inst_sym).or_insert(Some(source));
            }

            // Instance constraint classes and sources from instances map
            for (class_qi, inst_list) in &mod_exports.instances {
                for (inst_types, inst_constraints, inst_name_opt) in inst_list {
                    let inst_name_resolved = inst_name_opt.or_else(|| {
                        extract_head_type_con_from_types(inst_types)
                            .and_then(|head| mod_exports.instance_registry.get(&(class_qi.name, head)).copied())
                    });
                    if let Some(inst_name) = inst_name_resolved {
                        let constraint_classes: Vec<Symbol> = inst_constraints.iter().map(|(c, _)| c.name).collect();
                        instance_constraint_classes.entry(inst_name).or_insert(constraint_classes);
                        let source = defining_modules.get(&inst_name).cloned()
                            .unwrap_or_else(|| mod_parts.to_vec());
                        instance_sources.entry(inst_name).or_insert(Some(source));
                    }
                }
            }
        }

        // Derive known_runtime_classes from the collected data
        let mut known_runtime_classes: HashSet<Symbol> = HashSet::new();
        for (_, entries) in &all_class_methods {
            for (class_qi, _) in entries {
                known_runtime_classes.insert(class_qi.name);
            }
        }
        for (class_sym, (_, supers)) in &all_class_superclasses {
            if !supers.is_empty() {
                known_runtime_classes.insert(*class_sym);
            }
        }

        GlobalCodegenData {
            op_fixities,
            all_class_methods,
            all_fn_constraints,
            all_class_superclasses,
            known_runtime_classes,
            class_method_order,
            instance_registry,
            instance_sources,
            instance_constraint_classes,
            defining_modules,
        }
    }
}

/// Create an unqualified QualifiedIdent from a Symbol (for map lookups).
fn unqualified(name: Symbol) -> QualifiedIdent {
    QualifiedIdent { module: None, name }
}

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
    newtype_names: HashSet<Symbol>,
    /// Mapping from constructor name → (parent_type, type_vars, field_types)
    ctor_details: HashMap<QualifiedIdent, (QualifiedIdent, Vec<QualifiedIdent>, Vec<crate::typechecker::types::Type>)>,
    /// Data type → constructor names (to determine sum vs product)
    data_constructors: HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
    /// Operators that alias functions (not constructors)
    function_op_aliases: &'a HashSet<QualifiedIdent>,
    /// Names of foreign imports in this module
    foreign_imports: HashSet<Symbol>,
    /// Import map: module_parts → JS variable name
    import_map: HashMap<Vec<Symbol>, String>,
    /// Names defined locally in this module (values, ctors, foreign, instances)
    local_names: HashSet<Symbol>,
    /// Imported name → source module parts (for resolving unqualified references)
    name_source: HashMap<Symbol, Vec<Symbol>>,
    /// Operator → target name resolution: op_symbol → (source_module_parts_or_none, target_name)
    operator_targets: HashMap<Symbol, (Option<Vec<Symbol>>, Symbol)>,
    /// Counter for generating fresh variable names
    fresh_counter: Cell<usize>,
    /// Current dict scope: class_name → dict_param_name
    /// Populated when inside a constrained function body.
    dict_scope: std::cell::RefCell<Vec<(Symbol, String)>>,
    /// Instance registry: (class_name, head_type_con) → instance_name
    instance_registry: HashMap<(Symbol, Symbol), Symbol>,
    /// Instance name → source module parts (None = local)
    instance_sources: HashMap<Symbol, Option<Vec<Symbol>>>,
    /// Instance name → constraint class names (for determining if instance needs dict application)
    instance_constraint_classes: HashMap<Symbol, Vec<Symbol>>,
    /// Pre-built: class method → list of (class_name, type_vars) — borrowed from GlobalCodegenData
    all_class_methods: &'a HashMap<Symbol, Vec<(QualifiedIdent, Vec<QualifiedIdent>)>>,
    /// Pre-built: fn_name → constraint class names (from signature_constraints)
    /// Uses RefCell because local let-bound constrained functions are added during codegen.
    all_fn_constraints: std::cell::RefCell<HashMap<Symbol, Vec<Symbol>>>,
    /// Pre-built: class_name → (type_vars, superclass list) — borrowed from GlobalCodegenData
    all_class_superclasses: &'a HashMap<Symbol, (Vec<Symbol>, Vec<(QualifiedIdent, Vec<Type>)>)>,
    /// Resolved dicts from typechecker: expression_span → [(class_name, dict_expr)].
    /// Used to resolve class method dicts at module level (outside dict scope).
    /// Each span uniquely identifies a call site, so lookups are unambiguous.
    resolved_dict_map: HashMap<crate::span::Span, Vec<(Symbol, crate::typechecker::registry::DictExpr)>>,
    /// Functions with Partial => constraint (need dict wrapper but not in signature_constraints)
    partial_fns: HashSet<Symbol>,
    /// When true, references to partial_fns are auto-called with () to strip the dictPartial layer.
    /// Set when inside unsafePartial argument expressions.
    discharging_partial: std::cell::Cell<bool>,
    /// Operator fixities — borrowed from GlobalCodegenData
    op_fixities: &'a HashMap<Symbol, (Associativity, u8)>,
    /// Wildcard section parameter names (collected during gen_expr for Expr::Wildcard)
    wildcard_params: std::cell::RefCell<Vec<String>>,
    /// Classes that have methods (and thus runtime dictionaries) — borrowed from GlobalCodegenData
    known_runtime_classes: &'a HashSet<Symbol>,
    /// Locally-bound names (lambda params, let/where bindings, case binders).
    /// Used to distinguish local bindings from imported names with the same name.
    local_bindings: std::cell::RefCell<HashSet<Symbol>>,
    /// Subset of local_bindings that have their own type class constraints (let/where bindings).
    /// These need dict application at call sites unlike regular local bindings.
    local_constrained_bindings: std::cell::RefCell<HashSet<Symbol>>,
    /// Record update field info from typechecker: span → all field names.
    record_update_fields: &'a HashMap<crate::span::Span, Vec<Symbol>>,
    /// Class method declaration order — borrowed from GlobalCodegenData
    class_method_order: &'a HashMap<Symbol, Vec<Symbol>>,
    /// Parameters with constrained higher-rank types: param_name → dict_param_name.
    /// When such a parameter is used as a value (not called), it needs eta-expansion:
    /// `f` → `function(dictClass) { return f(dictClass); }`
    /// This replicates the original compiler's CoreFn representation.
    /// Scoped per-function (set before processing each function body).
    constrained_hr_params: std::cell::RefCell<HashMap<Symbol, String>>,
    /// Type operator → target type constructor: `/\` → `Tuple`.
    /// Built from `infixr N type Foo as op` declarations.
    type_op_targets: HashMap<Symbol, Symbol>,
    /// Let binding names that have been inlined at module level.
    /// Used to detect name collisions: if a name is already used, IIFE wrapping is required.
    module_level_let_names: std::cell::RefCell<HashSet<String>>,
    /// All JS variable names declared at module level.
    /// Used to deduplicate generated instance names that collide with value declarations.
    used_js_names: std::cell::RefCell<HashSet<String>>,
    /// Mapping from original instance Symbol to deduplicated JS name.
    /// Only populated when an instance name was changed due to collision.
    deduped_instance_names: std::cell::RefCell<HashMap<Symbol, String>>,
    /// Module-level generated expressions: name → JsExpr.
    /// Used to inline operator targets when the target is let-shadowed in an inner scope.
    module_level_exprs: std::cell::RefCell<HashMap<Symbol, JsExpr>>,
    /// Return-type dict param names for the current function being generated.
    /// These are added AFTER regular params in the generated function.
    return_type_dict_params: std::cell::RefCell<Vec<String>>,
}

impl<'a> CodegenCtx<'a> {
    fn fresh_name(&self, prefix: &str) -> String {
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
    fn deduplicate_js_name(&self, name: String) -> String {
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
}

/// Create an export entry: (js_name, Some(ps_name)) if the PS name differs and is
/// a valid JS identifier (e.g. JS reserved words like `const` → `$$const as const`).
/// For non-identifier PS names (e.g. `class'` → `class$prime`), no "as" clause is used.
fn export_entry(sym: Symbol) -> (String, Option<String>) {
    let js_name = ident_to_js(sym);
    let ps_name = interner::resolve(sym).unwrap_or_default();
    if js_name != ps_name && is_valid_js_identifier(&ps_name) {
        (js_name, Some(ps_name))
    } else {
        (js_name, None)
    }
}

/// Create an export entry from a JS name string (no PS name tracking).
fn export_entry_js(js_name: String) -> (String, Option<String>) {
    (js_name, None)
}

/// Get the externally-visible export name for a symbol.
/// For reserved words like `new`, the export uses `as new` so external name is the PS name.
/// For non-identifier PS names like `assert'`, the export is just the JS-escaped name.
fn export_name(sym: Symbol) -> String {
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
) -> JsModule {


    // Collect local names (names defined in this module) and Partial-constrained functions
    let mut local_names = HashSet::new();
    let mut foreign_imports_set = HashSet::new();
    let mut partial_fns = HashSet::new();
    for decl in &module.decls {
        match decl {
            Decl::Value { name, .. } => { local_names.insert(name.value); }
            Decl::Foreign { name, .. } => {
                local_names.insert(name.value);
                foreign_imports_set.insert(name.value);
            }
            Decl::Data { constructors, .. } => {
                for ctor in constructors {
                    local_names.insert(ctor.name.value);
                }
            }
            Decl::Newtype { constructor, .. } => {
                local_names.insert(constructor.value);
            }
            Decl::Instance { name: Some(n), .. } => {
                local_names.insert(n.value);
            }
            Decl::Class { members, .. } => {
                for member in members {
                    local_names.insert(member.name.value);
                }
            }
            Decl::TypeSignature { name, ty, .. } => {
                // Check if type has Partial constraint — these need dict wrappers in codegen
                if has_partial_constraint(ty) {
                    partial_fns.insert(name.value);
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
        if let Some(origin_mod_sym) = mod_exports.value_origins.get(&name) {
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
        operator_targets.insert(op_qi.name, (None, target_qi.name));
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
                partial_fns.insert(*name);
            }
            // Collect all value names exported by this module
            let all_names: Vec<Symbol> = mod_exports.values.keys().map(|qi| qi.name).collect();

            // Collect constructor names — only from types defined in this module
            let all_ctor_names: Vec<Symbol> = mod_exports.ctor_details.iter()
                .filter(|(_, (parent_qi, _, _))| mod_exports.data_constructors.contains_key(parent_qi))
                .map(|(qi, _)| qi.name)
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
                        for item in items {
                            match item {
                                Import::Value(n) => {
                                    if !local_names.contains(&n.value) {
                                        let origin = resolve_origin(n.value, mod_exports, parts);
                                        name_source.entry(n.value).or_insert_with(|| origin);
                                    }
                                }
                                Import::Type(_, Some(DataMembers::All)) => {
                                    // Import all constructors of this type, tracing to origin module
                                    for ctor_name in &all_ctor_names {
                                        if !local_names.contains(ctor_name) {
                                            let origin = resolve_origin(*ctor_name, mod_exports, parts);
                                            name_source.entry(*ctor_name).or_insert_with(|| origin);
                                        }
                                    }
                                }
                                Import::Type(_, Some(DataMembers::Explicit(ctors))) => {
                                    for ctor in ctors {
                                        if !local_names.contains(&ctor.value) {
                                            let origin = resolve_origin(ctor.value, mod_exports, parts);
                                            name_source.entry(ctor.value).or_insert_with(|| origin);
                                        }
                                    }
                                }
                                Import::Class(n) => {
                                    // Import class method names, tracing to origin module
                                    for (method_qi, (class_qi, _)) in &mod_exports.class_methods {
                                        if class_qi.name == n.value {
                                            if !local_names.contains(&method_qi.name) {
                                                let origin = resolve_origin(method_qi.name, mod_exports, parts);
                                                name_source.entry(method_qi.name).or_insert_with(|| origin);
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

            // Collect operator targets from imported module
            for (op_qi, target_qi) in &mod_exports.value_operator_targets {
                operator_targets.entry(op_qi.name).or_insert_with(|| {
                    // Resolve operator target to its origin module
                    let target_origin = resolve_origin(target_qi.name, mod_exports, parts);
                    if registry.lookup(&target_origin).is_some() {
                        (Some(target_origin), target_qi.name)
                    } else if mod_exports.values.contains_key(target_qi) || mod_exports.ctor_details.contains_key(target_qi) {
                        (Some(parts.clone()), target_qi.name)
                    } else {
                        (None, target_qi.name)
                    }
                });
            }
        }
    }

    // Build all_fn_constraints: module's own take priority, then global (filtering local_names)
    let mut fn_constraints = HashMap::new();
    for (name, constraints) in &exports.signature_constraints {
        let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name).collect();
        fn_constraints.entry(name.name).or_insert(class_names);
    }
    for (name, class_names) in &global.all_fn_constraints {
        if !local_names.contains(name) {
            fn_constraints.entry(*name).or_insert_with(|| class_names.clone());
        }
    }

    let mut ctx = CodegenCtx {
        module,
        exports,
        registry,
        module_name,
        module_parts,
        newtype_names: exports.newtype_names.clone(),
        ctor_details: exports.ctor_details.clone(),
        data_constructors: exports.data_constructors.clone(),
        function_op_aliases: &exports.function_op_aliases,
        foreign_imports: foreign_imports_set,
        import_map: HashMap::new(),
        local_names,
        name_source,
        operator_targets,
        fresh_counter: Cell::new(0),
        dict_scope: std::cell::RefCell::new(Vec::new()),
        instance_registry: global.instance_registry.clone(),
        instance_sources: global.instance_sources.clone(),
        instance_constraint_classes: global.instance_constraint_classes.clone(),
        all_class_methods: &global.all_class_methods,
        all_fn_constraints: std::cell::RefCell::new(fn_constraints),
        all_class_superclasses: &global.all_class_superclasses,
        resolved_dict_map: exports.resolved_dicts.clone(),
        partial_fns,
        discharging_partial: std::cell::Cell::new(false),
        op_fixities: &global.op_fixities,
        wildcard_params: std::cell::RefCell::new(Vec::new()),
        known_runtime_classes: &global.known_runtime_classes,
        local_bindings: std::cell::RefCell::new(HashSet::new()),
        local_constrained_bindings: std::cell::RefCell::new(HashSet::new()),
        record_update_fields: &exports.record_update_fields,
        class_method_order: &global.class_method_order,
        constrained_hr_params: std::cell::RefCell::new(HashMap::new()),
        type_op_targets: HashMap::new(),
        module_level_let_names: std::cell::RefCell::new(HashSet::new()),
        module_level_exprs: std::cell::RefCell::new(HashMap::new()),
        return_type_dict_params: std::cell::RefCell::new(Vec::new()),
        used_js_names: std::cell::RefCell::new(HashSet::new()),
        deduped_instance_names: std::cell::RefCell::new(HashMap::new()),
    };

    // Pre-populate used_js_names with all value, constructor, and foreign names
    for decl in &module.decls {
        match decl {
            Decl::Value { name, .. } => {
                ctx.used_js_names.borrow_mut().insert(ident_to_js(name.value));
            }
            Decl::Data { constructors, .. } => {
                for ctor in constructors {
                    ctx.used_js_names.borrow_mut().insert(ident_to_js(ctor.name.value));
                }
            }
            Decl::Newtype { constructor, .. } => {
                ctx.used_js_names.borrow_mut().insert(ident_to_js(constructor.value));
            }
            Decl::Foreign { name, .. } => {
                ctx.used_js_names.borrow_mut().insert(ident_to_js(name.value));
            }
            Decl::Class { members, .. } => {
                for member in members {
                    ctx.used_js_names.borrow_mut().insert(ident_to_js(member.name.value));
                }
            }
            _ => {}
        }
    }

    // Build type operator → target map from fixity declarations
    for decl in &module.decls {
        if let Decl::Fixity { is_type: true, target, operator, .. } = decl {
            ctx.type_op_targets.insert(operator.value, target.name);
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

    // op_fixities, all_class_methods, all_class_superclasses, known_runtime_classes,
    // class_method_order are borrowed from GlobalCodegenData (pre-computed once).
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
    for ((class_sym, head_sym), inst_sym) in &exports.instance_registry {
        ctx.instance_registry.insert((*class_sym, *head_sym), *inst_sym);
        ctx.instance_sources.insert(*inst_sym, None);
    }
    // 2. Also scan CST for local instances and derive instances (in case typechecker didn't populate all)
    for decl in &module.decls {
        if let Decl::Instance { name: Some(n), class_name, types, constraints, .. } = decl {
            if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                ctx.instance_registry.insert((class_name.name, head), n.value);
                ctx.instance_sources.insert(n.value, None);
            }
            // Track constraint classes for this instance
            let constraint_classes: Vec<Symbol> = constraints.iter().map(|c| c.class.name).collect();
            ctx.instance_constraint_classes.insert(n.value, constraint_classes);
        }
        if let Decl::Derive { name, class_name, types, constraints, .. } = decl {
            if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                // For unnamed derives, generate a standard instance name
                let inst_sym = if let Some(n) = name {
                    n.value
                } else {
                    // Try registry first, else generate from class+head
                    ctx.instance_registry.get(&(class_name.name, head)).copied().unwrap_or_else(|| {
                        let class_str = interner::resolve(class_name.name).unwrap_or_default();
                        let head_str = interner::resolve(head).unwrap_or_default();
                        let short_class = class_str.rsplit('.').next().unwrap_or(&class_str);
                        let short_head = head_str.rsplit('.').next().unwrap_or(&head_str);
                        let first_lower = short_class.chars().next().map(|c| c.to_lowercase().to_string()).unwrap_or_default();
                        let inst_name = format!("{}{}{}", first_lower, &short_class[1..], short_head);
                        interner::intern(&inst_name)
                    })
                };
                ctx.instance_registry.entry((class_name.name, head)).or_insert(inst_sym);
                ctx.instance_sources.insert(inst_sym, None);
            }
            if let Some(n) = name {
                let constraint_classes: Vec<Symbol> = constraints.iter().map(|c| c.class.name).collect();
                ctx.instance_constraint_classes.insert(n.value, constraint_classes);
            }
        }
    }

    // Add JS imports for instance source modules referenced by resolved_dicts
    // (instances from transitive dependencies need to be importable)
    {
        use crate::typechecker::registry::DictExpr;
        fn collect_dict_names(dict: &DictExpr, names: &mut HashSet<Symbol>) {
            match dict {
                DictExpr::Var(name) => { names.insert(*name); }
                DictExpr::App(name, subs) => {
                    names.insert(*name);
                    for sub in subs { collect_dict_names(sub, names); }
                }
                DictExpr::ConstraintArg(_) => {} // Local constraint param, no import needed
                DictExpr::InlineIsSymbol(_) => {} // Inline dict, no import needed
                DictExpr::InlineReflectable(_) => {} // Inline dict, no import needed
                DictExpr::ZeroCost => {} // Zero-cost constraint, no import needed
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
                    let qi = unqualified(head);
                    if let Some(ctor_names) = ctx.data_constructors.get(&qi) {
                        if let Some(ctor_qi) = ctor_names.first() {
                            if let Some((_, _, field_types)) = ctx.ctor_details.get(ctor_qi) {
                                if let Some(underlying_ty) = field_types.first() {
                                    if let Some(underlying_head) = extract_head_from_type(underlying_ty) {
                                        // Look up the instance for (class, underlying_head) in the registry
                                        if let Some(inst_name) = ctx.instance_registry.get(&(class_name.name, underlying_head)) {
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

    // Add Data.Ordering import if any derive Ord instances exist
    {
        let ord_sym = interner::intern("Ord");
        let has_derive_ord = module.decls.iter().any(|decl| {
            matches!(decl, Decl::Derive { class_name, .. } if class_name.name == ord_sym)
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

    // Add Data.Bifunctor / Data.Profunctor imports if derive Functor needs rmap
    // (when deriving Functor for a type whose inner type only has Bifunctor/Profunctor)
    {
        let functor_sym = interner::intern("Functor");
        let bifunctor_sym = interner::intern("Bifunctor");
        let profunctor_sym = interner::intern("Profunctor");
        let has_derive_functor = module.decls.iter().any(|decl| {
            matches!(decl, Decl::Derive { newtype: false, class_name, .. } if class_name.name == functor_sym)
        });
        if has_derive_functor {
            // Check if any inner types need Bifunctor's rmap
            let mut needs_bifunctor = false;
            let mut needs_profunctor = false;
            for decl in &module.decls {
                if let Decl::Derive { newtype: false, class_name, types, .. } = decl {
                    if class_name.name != functor_sym { continue; }
                    if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                        let qi = unqualified(head);
                        if let Some(ctor_names) = ctx.data_constructors.get(&qi) {
                            for ctor_qi in ctor_names {
                                if let Some((_, _, field_types)) = ctx.ctor_details.get(ctor_qi) {
                                    for ft in field_types {
                                        if let Some(inner_head) = extract_head_from_type(ft) {
                                            if !ctx.instance_registry.contains_key(&(functor_sym, inner_head)) {
                                                if ctx.instance_registry.contains_key(&(bifunctor_sym, inner_head)) {
                                                    needs_bifunctor = true;
                                                } else if ctx.instance_registry.contains_key(&(profunctor_sym, inner_head)) {
                                                    needs_profunctor = true;
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
            if needs_bifunctor {
                let parts: Vec<Symbol> = vec![interner::intern("Data"), interner::intern("Bifunctor")];
                if !ctx.import_map.contains_key(&parts) {
                    let js_name = module_name_to_js(&parts);
                    let path = "../Data.Bifunctor/index.js".to_string();
                    imports.push(JsStmt::Import { name: js_name.clone(), path });
                    ctx.import_map.insert(parts, js_name);
                }
            }
            if needs_profunctor {
                let parts: Vec<Symbol> = vec![interner::intern("Data"), interner::intern("Profunctor")];
                if !ctx.import_map.contains_key(&parts) {
                    let js_name = module_name_to_js(&parts);
                    let path = "../Data.Profunctor/index.js".to_string();
                    imports.push(JsStmt::Import { name: js_name.clone(), path });
                    ctx.import_map.insert(parts, js_name);
                }
            }
        }
    }

    // Build map of type signatures for constrained higher-rank parameter detection
    let mut type_sig_map: HashMap<Symbol, &TypeExpr> = HashMap::new();
    for decl in &module.decls {
        if let Decl::TypeSignature { name, ty, .. } = decl {
            type_sig_map.insert(name.value, ty);
        }
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
                if let Some(rt_constraints) = ctx.exports.return_type_constraints.get(&unqualified(*name_sym)) {
                    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
                    for (class_qi, _) in rt_constraints {
                        if ctx.known_runtime_classes.contains(&class_qi.name) {
                            let class_name = interner::resolve(class_qi.name).unwrap_or_default();
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
                let stmts = gen_value_decl(&ctx, *name_sym, decls);
                body.extend(stmts);
                if is_exported(&ctx, *name_sym) {
                    exported_names.push(export_entry(*name_sym));
                }
            }
            DeclGroup::Data(decl) => {
                if let Decl::Data { name: data_name, type_vars, constructors, .. } = decl {
                    for ctor in constructors {
                        if is_exported(&ctx, ctor.name.value) {
                            exported_names.push(export_entry(ctor.name.value));
                        }
                    }
                }
                let stmts = gen_data_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Newtype(decl) => {
                if let Decl::Newtype { name: nt_name, type_vars, constructor, .. } = decl {
                    if is_exported(&ctx, constructor.value) {
                        exported_names.push(export_entry(constructor.value));
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
                    exported_names.push(export_entry(n.value));
                    None
                } else if let Decl::Instance { name: None, class_name, types, .. } = decl {
                    // Unnamed instances — generate and deduplicate name to avoid collisions
                    let raw_name = gen_unnamed_instance_name(class_name, types, &ctx.instance_registry, &ctx.type_op_targets);
                    let deduped = ctx.deduplicate_js_name(raw_name.clone());
                    // If the name was deduplicated, record the mapping so that
                    // dict_expr_to_js can translate references to this instance.
                    if deduped != raw_name {
                        // Find the original instance symbol from the registry
                        if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                            if let Some(&orig_sym) = ctx.instance_registry.get(&(class_name.name, head)) {
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
                        if is_exported(&ctx, member.name.value) {
                            exported_names.push(export_entry(member.name.value));
                        }
                    }
                }
                let stmts = gen_class_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Fixity(_decl) => {
                // Operator aliases produce no JS output — operators are resolved to
                // their targets at usage sites.
            }
            DeclGroup::Derive(decl) => {
                let override_name = if let Decl::Derive { name: Some(name), .. } = decl {
                    // Named derive instances use their explicit name
                    exported_names.push(export_entry(name.value));
                    None
                } else if let Decl::Derive { name: None, class_name, types, .. } = decl {
                    // Unnamed derive instances — generate and deduplicate name
                    let raw_name = gen_unnamed_instance_name(class_name, types, &ctx.instance_registry, &ctx.type_op_targets);
                    let deduped = ctx.deduplicate_js_name(raw_name.clone());
                    if deduped != raw_name {
                        if let Some(head) = extract_head_type_con_from_cst(types, &ctx.type_op_targets) {
                            if let Some(&orig_sym) = ctx.instance_registry.get(&(class_name.name, head)) {
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
    let defined_names: HashSet<String> = body
        .iter()
        .filter_map(|s| {
            if let JsStmt::VarDecl(name, _) = s {
                Some(name.clone())
            } else {
                None
            }
        })
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
                        entry.insert(ident.value);
                        reexport_source.entry(ident.value).or_insert_with(|| mod_name.clone());
                    }
                    Import::Type(ident, members) => {
                        // Type name itself
                        entry.insert(ident.value);
                        // Constructors
                        match members {
                            Some(DataMembers::All) => {
                                // All constructors — look them up from ctor_details
                                let qi = unqualified(ident.value);
                                if let Some(ctor_names) = ctx.data_constructors.get(&qi) {
                                    for ctor in ctor_names {
                                        entry.insert(ctor.name);
                                        reexport_source.entry(ctor.name).or_insert_with(|| mod_name.clone());
                                    }
                                }
                            }
                            Some(DataMembers::Explicit(ctors)) => {
                                for c in ctors {
                                    entry.insert(c.value);
                                    reexport_source.entry(c.value).or_insert_with(|| mod_name.clone());
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
                    if exports.values.contains_key(qi) || exports.ctor_details.contains_key(qi) {
                        entry.insert(qi.name);
                    }
                }
                for qi in mod_exports.ctor_details.keys() {
                    if exports.values.contains_key(qi) || exports.ctor_details.contains_key(qi) {
                        entry.insert(qi.name);
                    }
                }
            }
        }
    }

    // Build alias → full module name map from imports
    let mut import_alias_to_full: HashMap<String, String> = HashMap::new();
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
            import_alias_to_full.insert(alias_name, full_name.clone());
        }
        // Also map full name to itself (for unaliased re-exports)
        import_alias_to_full.insert(full_name.clone(), full_name);
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
                // Resolve alias to full module name
                let resolved = import_alias_to_full.get(&name).cloned().unwrap_or(name);
                reexported_modules.insert(resolved);
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
                // Skip names that are defined locally (they're in the body, not re-exports)
                let js_name = ident_to_js(*name_sym);
                if defined_names.contains(&js_name) {
                    continue;
                }
                // Skip type-only names — only include names that have a runtime value
                let qi = unqualified(*name_sym);
                let has_value = exports.values.contains_key(&qi)
                    || ctx.ctor_details.contains_key(&qi);
                if !has_value {
                    let mut found_in_any = false;
                    for (_, mod_exports) in ctx.registry.iter_all() {
                        if mod_exports.values.contains_key(&qi)
                            || mod_exports.ctor_details.contains_key(&qi)
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
    let body = topo_sort_body(body);

    // Before optimizations, collect "phantom" module-level names: base names of dict apps
    // that would be hoisted to module level in the original compiler's CSE pass but will be
    // optimized away by our optimization passes. These affect naming of inner hoisted vars.
    let phantom_module_names = collect_phantom_module_level_names(&body);

    // Optimize string concatenation: Data_Semigroup.append(Data_Semigroup.semigroupString)(a)(b) → a + b
    // Must run BEFORE module-level hoisting to prevent hoisting expressions that will be optimized away
    let mut body: Vec<JsStmt> = body.into_iter().map(|s| optimize_string_concat_stmt(s)).collect();

    // Optimize boolean operations:
    // Data_HeytingAlgebra.conj(Data_HeytingAlgebra.heytingAlgebraBoolean)(a)(b) → a && b
    // Data_HeytingAlgebra.disj(Data_HeytingAlgebra.heytingAlgebraBoolean)(a)(b) → a || b
    body = body.into_iter().map(|s| optimize_boolean_ops_stmt(s)).collect();

    // Optimize common numeric, comparison, and constant operations:
    // Data_Semiring.add(Data_Semiring.semiringNumber)(a)(b) → a + b
    // Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingNumber)(a)(b) → a / b
    // Data_Eq.eq(Data_Eq.eqInt)(a)(b) → a === b
    // Data_Ord.lessThan(Data_Ord.ordInt)(a)(b) → a < b
    // Data_Semiring.zero(Data_Semiring.semiringInt) → 0
    // etc.
    body = body.into_iter().map(optimize_common_ops_stmt).collect();

    // Collect class method names (JS names) for hoisting heuristic
    let imported_class_methods: HashSet<String> = ctx.all_class_methods.keys()
        .map(|sym| {
            let ps_name = interner::resolve(*sym).unwrap_or_default();
            ps_name.to_string()
        })
        .collect();

    // Convert Ctor.create(a)(b) to new Ctor(a, b) throughout all declarations
    body = body.into_iter().map(uncurry_create_to_new_stmt).collect();

    // Apply TCO to any tail-recursive top-level functions
    apply_tco_if_applicable(&mut body);

    // Inline field access bindings: var x = v["value0"]; ... x ... → ... v["value0"] ...
    // Applied recursively to all function bodies in the module
    for stmt in body.iter_mut() {
        inline_field_access_in_stmt(stmt);
    }

    // Hoist constant dict applications from inside function bodies to module level
    hoist_module_level_constants(&mut body, &imported_class_methods);

    // Rename inner function-level hoisted vars that conflict with module-level names
    // or phantom module-level names (names that the original compiler's CSE would have
    // created at module level before optimization eliminated them).
    rename_inner_hoists_for_module_level(&mut body, &phantom_module_names);

    // Re-sort after hoisting (new vars may need reordering)
    let mut body = topo_sort_body(body);

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

    // Inline known typeclass operations (e.g., ordInt.lessThanOrEq → <=)
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
    JsModule {
        imports,
        body,
        exports: exported_names,
        foreign_exports: foreign_re_exports,
        foreign_module_path,
        reexports,
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
    Fixity(&'a Decl),
    TypeSig,
    ForeignData,
    Derive(&'a Decl),
    KindSig,
}

fn collect_decl_groups(decls: &[Decl]) -> Vec<DeclGroup<'_>> {
    // Collect all declarations interleaved in source order.
    // Values with the same name are merged into a single group.
    let mut result: Vec<DeclGroup<'_>> = Vec::new();
    let mut value_map: HashMap<Symbol, Vec<&Decl>> = HashMap::new();
    let mut value_seen: HashSet<Symbol> = HashSet::new();

    // Pre-collect value equations for merging
    for decl in decls {
        if let Decl::Value { name, .. } = decl {
            value_map.entry(name.value).or_default().push(decl);
        }
    }

    // Process all declarations in source order (interleaved)
    for decl in decls {
        match decl {
            Decl::Value { name, .. } => {
                let sym = name.value;
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
            Decl::Foreign { name, .. } => result.push(DeclGroup::Foreign(name.value)),
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
                        if ctx.ctor_details.contains_key(&unqualified(name)) {
                            return true;
                        }
                    }
                    Export::Type(_, Some(DataMembers::Explicit(ctors))) => {
                        if ctors.iter().any(|c| c.value == name) {
                            return true;
                        }
                    }
                    Export::Class(_) => {
                        // Class methods are exported as values
                        if ctx.exports.class_methods.contains_key(&unqualified(name)) {
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

fn gen_value_decl(ctx: &CodegenCtx, name: Symbol, decls: &[&Decl]) -> Vec<JsStmt> {
    let js_name = ident_to_js(name);

    // Check if this value has type class constraints (needs dict params)
    let constraints = ctx.exports.signature_constraints.get(&unqualified(name)).cloned();

    // Push dict scope entries for constraints (with unique names for duplicate classes)
    // Only push runtime constraints — zero-cost constraints (Coercible, etc.) have no param.
    let prev_scope_len = ctx.dict_scope.borrow().len();
    if let Some(ref constraints) = constraints {
        let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
        for (class_qi, _) in constraints {
            if !ctx.known_runtime_classes.contains(&class_qi.name) {
                continue; // Zero-cost constraint — no runtime dict param
            }
            let class_name_str = interner::resolve(class_qi.name).unwrap_or_default();
            let count = dict_name_counts.entry(class_name_str.to_string()).or_insert(0);
            let dict_param = if *count == 0 {
                format!("dict{class_name_str}")
            } else {
                format!("dict{class_name_str}{count}")
            };
            *count += 1;
            ctx.dict_scope.borrow_mut().push((class_qi.name, dict_param));
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
                    expr = wrap_expr_with_return_dicts(expr, &rt_dict_params);
                }
                expr = wrap_with_dict_params_named(expr, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name));
                // Wrap constructor applications/references in IIFE for proper init order
                if references_constructor(&expr) {
                    let expr = uncurry_create_to_new(expr);
                    let iife = JsExpr::App(
                        Box::new(JsExpr::Function(None, vec![], vec![JsStmt::Return(expr)])),
                        vec![],
                    );
                    vec![JsStmt::VarDecl(js_name, Some(iife))]
                } else {
                    vec![JsStmt::VarDecl(js_name, Some(expr))]
                }
            } else if where_clause.is_empty() {
                let body_expr = gen_guarded_expr_stmts(ctx, guarded);
                let mut func = gen_curried_function(ctx, binders, body_expr);
                // Wrap return value with return-type dict params (BEFORE regular dict wrapping)
                let rt_dict_params = ctx.return_type_dict_params.borrow().clone();
                if !rt_dict_params.is_empty() {
                    func = wrap_return_value_with_dict_params(func, &rt_dict_params);
                }
                func = wrap_with_dict_params_named(func, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name));
                vec![JsStmt::VarDecl(js_name, Some(func))]
            } else {
                let mut iife_body = Vec::new();
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
                        if no_constraints && !has_conflict {
                            // Register names as used at module level
                            {
                                let mut existing = ctx.module_level_let_names.borrow_mut();
                                for n in &where_names {
                                    existing.insert(n.clone());
                                }
                            }
                            let body_expr = gen_expr(ctx, body);
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
                    iife_body.push(JsStmt::Return(expr));
                    let iife = JsExpr::App(
                        Box::new(JsExpr::Function(None, vec![], iife_body)),
                        vec![],
                    );
                    let wrapped = wrap_with_dict_params_named(iife, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name));
                    vec![JsStmt::VarDecl(js_name, Some(wrapped))]
                } else {
                    let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                    iife_body.extend(body_stmts);
                    // Inline trivial aliases: var x = y → replace x with y
                    inline_trivial_aliases(&mut iife_body);
                    let mut func = gen_curried_function_from_stmts(ctx, binders, iife_body);
                    func = wrap_with_dict_params_named(func, constraints.as_ref(), &ctx.known_runtime_classes, Some(&js_name));
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
                    let wrapped = wrap_with_dict_params_named(expr.clone(), Some(constraints), &ctx.known_runtime_classes, Some(&js_name));
                    *expr = wrapped;
                }
            }
        }
        stmts
    };

    // Pop dict scope
    ctx.dict_scope.borrow_mut().truncate(prev_scope_len);

    // If this function has a Partial constraint, wrap with dictPartial parameter.
    // unsafePartial strips this layer by calling f() with no args.
    if ctx.partial_fns.contains(&name) {
        if let Some(JsStmt::VarDecl(_, Some(expr))) = result.first_mut() {
            *expr = JsExpr::Function(
                None,
                vec!["$dictPartial".to_string()],
                vec![JsStmt::Return(expr.clone())],
            );
        }
    }

    result
}

/// Try to inline a let expression at the top level of a value declaration.
/// Instead of `var x = (function() { var a = 1; return a; })()`,
/// generates `var x = 1` when the body is a simple variable reference.
fn try_inline_let_value(
    ctx: &CodegenCtx,
    name: &str,
    expr: &Expr,
    constraints: Option<&Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)>>,
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

/// Register VarDecl names from inlined stmts into module_level_let_names,
/// excluding the target declaration name itself (that's the module-level value).
fn register_module_level_names(ctx: &CodegenCtx, stmts: &[JsStmt], target_name: &str) {
    let mut existing = ctx.module_level_let_names.borrow_mut();
    for stmt in stmts {
        if let JsStmt::VarDecl(n, _) = stmt {
            if n != target_name {
                existing.insert(n.clone());
            }
        }
    }
}

/// Wrap the return value of a function expression with dict parameters.
/// Used for functions whose return type has inner forall constraints.
/// E.g., `function(v) { return v.value0; }` becomes
/// `function(v) { return function(dictMonad) { return v.value0(dictMonad); }; }`
fn wrap_return_value_with_dict_params(
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
fn wrap_stmts_return_with_dicts(stmts: Vec<JsStmt>, dict_params: &[String]) -> Vec<JsStmt> {
    stmts.into_iter().map(|stmt| match stmt {
        JsStmt::Return(expr) => {
            JsStmt::Return(wrap_expr_with_return_dicts(expr, dict_params))
        }
        other => other,
    }).collect()
}

/// Wrap an expression with `function(dict1) { return function(dict2) { return expr(dict1)(dict2); }; }`
fn wrap_expr_with_return_dicts(expr: JsExpr, dict_params: &[String]) -> JsExpr {
    // Build the inner expression: expr(dict1)(dict2)...
    let mut inner = expr;
    for param in dict_params {
        inner = JsExpr::App(Box::new(inner), vec![JsExpr::Var(param.clone())]);
    }
    // Wrap with curried dict param functions (inside-out)
    let mut result = inner;
    for param in dict_params.iter().rev() {
        result = JsExpr::Function(None, vec![param.clone()], vec![JsStmt::Return(result)]);
    }
    result
}

/// Wrap an expression with curried dict parameters from type class constraints.
/// E.g. `Show a => Eq a => ...` → `function(dictShow) { return function(dictEq) { return expr; }; }`
fn wrap_with_dict_params(
    expr: JsExpr,
    constraints: Option<&Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)>>,
    known_runtime_classes: &HashSet<Symbol>,
) -> JsExpr {
    wrap_with_dict_params_named(expr, constraints, known_runtime_classes, None)
}

fn wrap_with_dict_params_named(
    expr: JsExpr,
    constraints: Option<&Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)>>,
    known_runtime_classes: &HashSet<Symbol>,
    fn_name: Option<&str>,
) -> JsExpr {
    let Some(constraints) = constraints else { return expr };
    if constraints.is_empty() { return expr; }

    // Pre-compute unique dict param names (must match dict_scope push naming)
    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
    let mut dict_params: Vec<Option<String>> = Vec::new();
    for (class_qi, _) in constraints.iter() {
        if !known_runtime_classes.contains(&class_qi.name) {
            dict_params.push(None); // phantom — no runtime dict
        } else {
            let class_name = interner::resolve(class_qi.name).unwrap_or_default();
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
    for (i, _) in constraints.iter().enumerate().rev() {
        match &dict_params[i] {
            None => {
                result = JsExpr::Function(
                    None,
                    vec![],
                    vec![JsStmt::Return(result)],
                );
            }
            Some(dict_param) => {
                result = JsExpr::Function(
                    None,
                    vec![dict_param.clone()],
                    vec![JsStmt::Return(result)],
                );
            }
        }
    }
    // Step 2: Top-down hoisting so outer scopes get lower numbers
    let mut counter: HashMap<String, usize> = HashMap::new();
    let mut base_names: HashMap<String, String> = HashMap::new();
    let mut bare_names: HashSet<String> = HashSet::new();
    let empty_reserved: HashSet<String> = HashSet::new();
    hoist_dict_apps_top_down(&mut result, &mut counter, &mut base_names, &mut bare_names, fn_name, &empty_reserved);
    result
}

/// Scan a function body for `method(dictParam)` or `method(dictParam.Super0())`
/// applications that appear inside nested functions, and hoist them to
/// `var method1 = method(dictParam);` bindings at the top of the body.
/// Only hoists when the dict app is used inside an inner lambda, not when
/// it's the direct return value.
fn hoist_dict_applications(dict_param: &str, body: Vec<JsStmt>) -> Vec<JsStmt> {
    let mut counter: HashMap<String, usize> = HashMap::new();
    hoist_dict_applications_with_counter(dict_param, body, &mut counter)
}

fn hoist_dict_applications_with_counter(dict_param: &str, body: Vec<JsStmt>, counter: &mut HashMap<String, usize>) -> Vec<JsStmt> {
    // Collect dict applications that appear inside nested functions
    let mut hoisted: Vec<(JsExpr, String)> = Vec::new();

    // Only collect from inside nested functions (depth > 0)
    collect_dict_apps_nested(dict_param, &body, &mut hoisted, counter, 0);

    if hoisted.is_empty() {
        return body;
    }

    // Deduplicate: same expression should get same hoisted name
    let mut unique_hoisted: Vec<(JsExpr, String)> = Vec::new();
    for (expr, name) in &hoisted {
        if !unique_hoisted.iter().any(|(e, _)| e == expr) {
            unique_hoisted.push((expr.clone(), name.clone()));
        }
    }
    // Build replacement body
    let mut new_body = Vec::new();
    for (expr, name) in &unique_hoisted {
        new_body.push(JsStmt::VarDecl(name.clone(), Some(expr.clone())));
    }

    // Replace dict apps in the original body
    let replaced_body: Vec<JsStmt> = body.into_iter().map(|s| replace_dict_apps_stmt(s, &unique_hoisted)).collect();
    new_body.extend(replaced_body);
    new_body
}

/// Top-down hoisting pass for instance constraint wrapping.
/// Walks the nested function tree from outermost to innermost, hoisting dict apps
/// at each level using a shared counter. This ensures outer scopes get lower numbers.
/// `base_names` maps hoisted var names back to their original method names,
/// so cascading applications (e.g., method1(dict)) still use the original counter key.
fn hoist_dict_apps_top_down(
    expr: &mut JsExpr,
    counter: &mut HashMap<String, usize>,
    base_names: &mut HashMap<String, String>,
    bare_names: &mut HashSet<String>,
    enclosing_name: Option<&str>,
    reserved_names: &HashSet<String>,
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

            if hoisted.is_empty() {
                *body = old_body;
            } else {
                // Collect field names from returned object literals to avoid naming conflicts
                let return_fields = collect_return_object_fields_deep(&old_body);

                // Fix method names: resolve through base_names and use shared counter
                let mut unique: Vec<(JsExpr, String)> = Vec::new();
                for (expr, _raw_name) in hoisted {
                    if unique.iter().any(|(e, _)| *e == expr) {
                        continue;
                    }
                    // Get the method name extracted from the expression
                    let raw_method = if let Some(m) = is_dict_app(&dict_param, &expr) { m } else { continue };
                    // Resolve to base name (e.g., heytingAlgebraRecordCons1 → heytingAlgebraRecordCons)
                    let base = base_names.get(&raw_method).cloned().unwrap_or_else(|| raw_method.clone());
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
        let effective_reserved = if let Some(hoisted_names) = body.iter().filter_map(|s| {
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
            hoist_dict_apps_top_down_stmt(stmt, counter, base_names, bare_names, enclosing_name, effective_reserved);
        }
    }
}

fn hoist_dict_apps_top_down_stmt(
    stmt: &mut JsStmt,
    counter: &mut HashMap<String, usize>,
    base_names: &mut HashMap<String, String>,
    bare_names: &mut HashSet<String>,
    enclosing_name: Option<&str>,
    reserved_names: &HashSet<String>,
) {
    match stmt {
        JsStmt::Return(expr) => hoist_dict_apps_top_down(expr, counter, base_names, bare_names, enclosing_name, reserved_names),
        JsStmt::VarDecl(name, Some(expr)) => hoist_dict_apps_top_down(expr, counter, base_names, bare_names, Some(name.as_str()), reserved_names),
        _ => {}
    }
}

/// Extract shared arguments from hoisted dict applications.
/// When 2+ hoisted vars share the same complex argument (e.g., `dictRing.Semiring0()`),
/// extract it into its own variable (e.g., `var Semiring0 = dictRing.Semiring0()`)
/// and replace the argument in the hoisted exprs with a Var reference.
fn extract_shared_hoisted_args(
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
fn extract_name_hint(expr: &JsExpr) -> String {
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
fn fold_constant_dict_args_into_hoisted(dict_param: &str, stmts: &mut Vec<JsStmt>) {
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
fn find_foldable_usage(dict_param: &str, var_name: &str, stmts: &[JsStmt]) -> Option<(Vec<JsExpr>, JsExpr)> {
    // Look for the var used in the body (skip the VarDecl itself)
    let mut found: Option<(Vec<JsExpr>, JsExpr)> = None;
    let mut count = 0;
    for stmt in stmts {
        find_foldable_in_stmt(dict_param, var_name, stmt, &mut found, &mut count);
    }
    // Only fold if there's exactly one usage
    if count == 1 { found } else { None }
}

fn find_foldable_in_stmt(dict_param: &str, var_name: &str, stmt: &JsStmt, found: &mut Option<(Vec<JsExpr>, JsExpr)>, count: &mut usize) {
    match stmt {
        JsStmt::VarDecl(name, _) if name == var_name => {} // skip the hoisted VarDecl itself
        JsStmt::Return(expr) => find_foldable_in_expr(dict_param, var_name, expr, found, count),
        JsStmt::VarDecl(_, Some(expr)) => find_foldable_in_expr(dict_param, var_name, expr, found, count),
        JsStmt::Expr(expr) => find_foldable_in_expr(dict_param, var_name, expr, found, count),
        _ => {}
    }
}

fn find_foldable_in_expr(dict_param: &str, var_name: &str, expr: &JsExpr, found: &mut Option<(Vec<JsExpr>, JsExpr)>, count: &mut usize) {
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
fn extract_app_chain_args(var_name: &str, expr: &JsExpr) -> Option<Vec<JsExpr>> {
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
fn expr_contains_var(expr: &JsExpr, var_name: &str) -> bool {
    match expr {
        JsExpr::Var(name) => name == var_name,
        JsExpr::App(callee, args) => expr_contains_var(callee, var_name) || args.iter().any(|a| expr_contains_var(a, var_name)),
        JsExpr::Indexer(a, b) => expr_contains_var(a, var_name) || expr_contains_var(b, var_name),
        JsExpr::Function(_, _, body) => body.iter().any(|s| stmt_contains_var(s, var_name)),
        _ => false,
    }
}

fn stmt_contains_var(stmt: &JsStmt, var_name: &str) -> bool {
    match stmt {
        JsStmt::Return(expr) | JsStmt::VarDecl(_, Some(expr)) | JsStmt::Expr(expr) => expr_contains_var(expr, var_name),
        _ => false,
    }
}

/// Replace App chain `var_name(args...)` with just `Var(var_name)` in statements,
/// where the App chain matches the folded expression.
fn replace_app_with_var_in_stmts(stmts: &mut [JsStmt], var_name: &str, folded_expr: &JsExpr) {
    for stmt in stmts.iter_mut() {
        replace_app_with_var_in_stmt(stmt, var_name, folded_expr);
    }
}

fn replace_app_with_var_in_stmt(stmt: &mut JsStmt, var_name: &str, folded_expr: &JsExpr) {
    match stmt {
        JsStmt::VarDecl(name, _) if name == var_name => {} // skip VarDecl
        JsStmt::Return(expr) => replace_app_with_var_in_expr(expr, var_name, folded_expr),
        JsStmt::VarDecl(_, Some(expr)) => replace_app_with_var_in_expr(expr, var_name, folded_expr),
        JsStmt::Expr(expr) => replace_app_with_var_in_expr(expr, var_name, folded_expr),
        _ => {}
    }
}

fn replace_app_with_var_in_expr(expr: &mut JsExpr, var_name: &str, folded_expr: &JsExpr) {
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
/// Does NOT recurse into nested functions — only checks the immediate return
/// at the current scope. Used to detect field name conflicts when naming hoisted dict vars.
fn collect_return_object_fields_deep(stmts: &[JsStmt]) -> HashSet<String> {
    let mut fields = HashSet::new();
    for stmt in stmts {
        if let JsStmt::Return(JsExpr::ObjectLit(pairs)) = stmt {
            for (name, _) in pairs {
                fields.insert(name.clone());
            }
        }
    }
    fields
}

/// Collect field names from ObjectLit returned directly in the body (non-recursive).
/// Only checks for immediate return of object literal, not nested functions.
fn collect_return_object_fields(stmts: &[JsStmt]) -> HashSet<String> {
    let mut fields = HashSet::new();
    for stmt in stmts {
        if let JsStmt::Return(expr) = stmt {
            collect_object_fields_from_expr(expr, &mut fields);
        }
    }
    fields
}

fn collect_object_fields_from_expr(expr: &JsExpr, fields: &mut HashSet<String>) {
    match expr {
        JsExpr::ObjectLit(pairs) => {
            for (name, _) in pairs {
                fields.insert(name.clone());
            }
        }
        // Look through function wrappers to find the returned object
        JsExpr::Function(_, _, body) => {
            for stmt in body {
                if let JsStmt::Return(inner) = stmt {
                    collect_object_fields_from_expr(inner, fields);
                }
            }
        }
        _ => {}
    }
}

/// Check if an expression references dict-prefixed variables other than the given one.
/// Used to prevent hoisting expressions that depend on deeper-scope dict params.
fn expr_references_other_dicts(dict_param: &str, expr: &JsExpr) -> bool {
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
fn js_expr_contains_var(expr: &JsExpr, name: &str) -> bool {
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

fn js_stmt_contains_var(stmt: &JsStmt, name: &str) -> bool {
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

fn is_dict_app(dict_param: &str, expr: &JsExpr) -> Option<String> {
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

/// Extract the base method name from a callee expression, unwrapping any application chains.
/// E.g., Var("foo") → "foo", ModuleAccessor(_, "foo") → "foo",
/// App(Var("foo"), []) → "foo" (phantom-applied),
/// App(App(ModuleAccessor(_, "foo"), [arg1]), []) → "foo" (partially applied + phantom)
fn extract_base_method_name(expr: &JsExpr) -> Option<String> {
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
fn is_dict_ref(dict_param: &str, expr: &JsExpr) -> bool {
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
fn is_dict_app_module_accessor(expr: &JsExpr) -> bool {
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
fn find_extended_dict_app(dict_param: &str, expr: &JsExpr) -> Option<String> {
    if let JsExpr::App(callee, args) = expr {
        // Check if all args are dict-like
        let all_args_dict_like = args.iter().all(|arg| is_dict_like_arg(arg));
        if !all_args_dict_like {
            return None;
        }
        // If the callee is itself a dict app, we found an extended chain
        if let Some(name) = is_dict_app(dict_param, callee) {
            return Some(name);
        }
        // Recurse into the callee
        return find_extended_dict_app(dict_param, callee);
    }
    None
}

/// Check if an argument is "dict-like" — something that could be a dict parameter,
/// a superclass accessor result, or a phantom thunk call.
fn is_dict_like_arg(arg: &JsExpr) -> bool {
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

/// Check if the innermost callee of an App chain is a module accessor.
/// Recurses through all App layers.
fn is_dict_app_module_accessor_deep(expr: &JsExpr) -> bool {
    match expr {
        JsExpr::App(callee, _) => is_dict_app_module_accessor_deep(callee),
        JsExpr::ModuleAccessor(..) => true,
        JsExpr::Indexer(_, _) => true, // superclass accessor
        _ => false,
    }
}

/// Collect dict applications from direct ObjectLit field values.
/// Only hoists dict apps that appear as standalone values (not part of call chains).
/// E.g., `f(dictParam)` when used as a New arg → hoist. `f(dictParam)(x)(y)` → don't hoist.
fn collect_direct_obj_dict_apps(
    dict_param: &str,
    obj: &JsExpr,
    hoisted: &mut Vec<(JsExpr, String)>,
    counter: &mut HashMap<String, usize>,
) {
    let fields = match obj {
        JsExpr::ObjectLit(fields) => fields,
        _ => return,
    };
    for (_, val) in fields {
        collect_standalone_dict_apps(dict_param, val, hoisted, counter);
    }
}

/// Find dict apps in an expression that are used as standalone values
/// (not as callees for further application).
fn collect_standalone_dict_apps(
    dict_param: &str,
    expr: &JsExpr,
    hoisted: &mut Vec<(JsExpr, String)>,
    counter: &mut HashMap<String, usize>,
) {
    // Check if this expression IS a dict app — if so, hoist it
    if let Some(method_name) = is_dict_app(dict_param, expr) {
        if !hoisted.iter().any(|(e, _)| e == expr) {
            let count = counter.entry(method_name.clone()).or_insert(0);
            *count += 1;
            let is_module_accessor = matches!(expr, JsExpr::App(callee, _) if matches!(callee.as_ref(), JsExpr::ModuleAccessor(..)));
            let hoisted_name = if is_module_accessor && *count == 1 {
                method_name.clone()
            } else {
                format!("{method_name}{count}")
            };
            hoisted.push((expr.clone(), hoisted_name));
        }
        return;
    }
    // Recurse into sub-expressions, but DON'T descend into App callees
    // (we don't want to hoist partial applications from chains)
    match expr {
        JsExpr::App(callee, args) => {
            // Don't recurse into callee (it would extract partial apps from chains)
            // But do recurse into args (a dict app used as an argument is standalone)
            for arg in args {
                collect_standalone_dict_apps(dict_param, arg, hoisted, counter);
            }
            // Also check callee for non-App patterns (e.g., App(New, ...) won't happen)
        }
        JsExpr::New(_, args) => {
            for arg in args {
                collect_standalone_dict_apps(dict_param, arg, hoisted, counter);
            }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields {
                collect_standalone_dict_apps(dict_param, val, hoisted, counter);
            }
        }
        JsExpr::ArrayLit(items) => {
            for item in items {
                collect_standalone_dict_apps(dict_param, item, hoisted, counter);
            }
        }
        JsExpr::Ternary(a, b, c) => {
            collect_standalone_dict_apps(dict_param, a, hoisted, counter);
            collect_standalone_dict_apps(dict_param, b, hoisted, counter);
            collect_standalone_dict_apps(dict_param, c, hoisted, counter);
        }
        JsExpr::Binary(_, a, b) | JsExpr::Indexer(a, b) => {
            collect_standalone_dict_apps(dict_param, a, hoisted, counter);
            collect_standalone_dict_apps(dict_param, b, hoisted, counter);
        }
        // Don't recurse into function bodies (those are at a different scope)
        JsExpr::Function(_, _, _) => {}
        _ => {}
    }
}

/// Recursively collect dict applications from statements, tracking function nesting depth.
/// When `include_depth_zero` is true, hoists apps at all depths (for instance bodies).
/// When false, only hoists at depth > 0 (inside nested functions).
fn collect_dict_apps_nested(dict_param: &str, stmts: &[JsStmt], hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize) {
    collect_dict_apps_nested_ex(dict_param, stmts, hoisted, counter, depth, false);
}

fn collect_dict_apps_nested_ex(dict_param: &str, stmts: &[JsStmt], hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize, include_depth_zero: bool) {
    for stmt in stmts {
        collect_dict_apps_stmt_nested_ex(dict_param, stmt, hoisted, counter, depth, include_depth_zero);
    }
}

fn collect_dict_apps_stmt_nested(dict_param: &str, stmt: &JsStmt, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize) {
    collect_dict_apps_stmt_nested_ex(dict_param, stmt, hoisted, counter, depth, false);
}

fn collect_dict_apps_stmt_nested_ex(dict_param: &str, stmt: &JsStmt, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize, include_depth_zero: bool) {
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

fn collect_dict_apps_expr_nested(dict_param: &str, expr: &JsExpr, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize) {
    collect_dict_apps_expr_nested_ex(dict_param, expr, hoisted, counter, depth, false);
}

fn collect_dict_apps_expr_nested_ex(dict_param: &str, expr: &JsExpr, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize, include_depth_zero: bool) {
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
                let hoisted_name = if is_module_accessor && *count == 1 {
                    method_name.clone()
                } else {
                    format!("{method_name}{count}")
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

/// Ensure a hoisted name is numbered (e.g. "append" → "append1").
/// Instance bodies always use numbered names, while function-level hoisting uses bare names for the first occurrence.
fn ensure_numbered_name(name: &str, counter: &HashMap<String, usize>) -> String {
    // Check if name already ends with a digit
    if name.chars().last().map_or(false, |c| c.is_ascii_digit()) {
        return name.to_string();
    }
    // The name is bare (e.g. "append") — add the count number
    if let Some(&count) = counter.get(name) {
        if count > 0 {
            return format!("{name}{count}");
        }
    }
    format!("{name}1")
}

fn replace_dict_apps_stmt(stmt: JsStmt, hoisted: &[(JsExpr, String)]) -> JsStmt {
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

fn replace_dict_apps_expr(expr: JsExpr, hoisted: &[(JsExpr, String)]) -> JsExpr {
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
fn hoist_module_level_constants(body: &mut Vec<JsStmt>, imported_class_methods: &HashSet<String>) {
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

    // 2. Walk declarations to find hoistable expressions inside function bodies
    let mut hoistables: Vec<(JsExpr, String)> = Vec::new(); // (expr, assigned_name)
    let mut hoistable_keys: HashSet<String> = HashSet::new(); // debug-string keys for O(1) dedup
    let mut used_names: HashSet<String> = module_vars.clone();

    for stmt in body.iter() {
        if let JsStmt::VarDecl(name, Some(init)) = stmt {
            find_module_hoistable_in_expr(init, &module_vars, &class_accessors, imported_class_methods, &mut hoistables, &mut hoistable_keys, &mut used_names, 0, name);
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
fn rename_conflicting_function_hoists(expr: &mut JsExpr, conflicting_names: &HashSet<String>) {
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

fn rename_conflicting_in_stmt(stmt: &mut JsStmt, conflicting_names: &HashSet<String>) {
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

fn rename_var_in_stmt(stmt: &mut JsStmt, old: &str, new: &str) {
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

fn rename_var_in_expr(expr: &mut JsExpr, old: &str, new: &str) {
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
fn collect_phantom_module_level_names(body: &[JsStmt]) -> HashSet<String> {
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

fn collect_phantom_names_in_expr(expr: &JsExpr, module_vars: &HashSet<String>, phantoms: &mut HashSet<String>, depth: usize) {
    // At depth > 0 (inside a function), look for dict apps with constant module-level args
    // that will be optimized away by subsequent passes
    if depth > 0 {
        if let JsExpr::App(callee, args) = expr {
            if args.len() == 1 && args.iter().all(|a| is_constant_ref(a, module_vars)) {
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

fn collect_phantom_names_in_stmt(stmt: &JsStmt, module_vars: &HashSet<String>, phantoms: &mut HashSet<String>, depth: usize) {
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
fn rename_inner_hoists_for_module_level(body: &mut Vec<JsStmt>, phantom_names: &HashSet<String>) {
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

fn rename_inner_hoists_in_expr(expr: &mut JsExpr, conflict_set: &HashSet<String>) {
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

        // Recurse into nested expressions in the body
        for stmt in body.iter_mut() {
            rename_inner_hoists_in_stmt(stmt, conflict_set);
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

fn rename_inner_hoists_in_stmt(stmt: &mut JsStmt, conflict_set: &HashSet<String>) {
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
fn extract_hoisted_base_name(expr: &JsExpr) -> Option<String> {
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

fn extract_hoisted_base_name_from_callee(expr: &JsExpr) -> Option<String> {
    match expr {
        JsExpr::Var(name) => Some(name.clone()),
        JsExpr::ModuleAccessor(_, name) => Some(name.clone()),
        JsExpr::App(inner, _) => extract_hoisted_base_name_from_callee(inner),
        _ => None,
    }
}

/// Find the next available name for a base, skipping all names in the conflict set.
/// E.g., base "eq" with conflict set {eq, eq1, eq2} → "eq3"
fn find_next_name_after_conflicts(base: &str, conflict_set: &HashSet<String>) -> String {
    if !conflict_set.contains(base) {
        return base.to_string();
    }
    for i in 1.. {
        let candidate = format!("{base}{i}");
        if !conflict_set.contains(&candidate) {
            return candidate;
        }
    }
    unreachable!()
}

/// Check if an expression is a class method accessor pattern:
/// `function(dict) { return dict.X; }` or `function(dict) { return dict["X"]; }`
fn is_class_accessor_pattern(expr: &JsExpr) -> bool {
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
fn is_constant_ref(expr: &JsExpr, module_vars: &HashSet<String>) -> bool {
    match expr {
        JsExpr::ModuleAccessor(_, _) => true,
        JsExpr::Var(name) => module_vars.contains(name),
        _ => false,
    }
}

/// Extract the "method name" from an expression for naming the hoisted var.
fn extract_method_name(expr: &JsExpr) -> Option<String> {
    match expr {
        JsExpr::ModuleAccessor(_, name) => Some(name.clone()),
        JsExpr::Var(name) => Some(name.clone()),
        _ => None,
    }
}

/// Check if a (method, instance) pair is a known primop that the original PureScript
/// compiler inlines as a native JS operator. These applications should NOT be hoisted
/// because the original compiler eliminates them entirely via primop inlining.
fn is_optimizable_dict_app(method: &str, instance: &str) -> bool {
    match method {
        // String concat: append(semigroupString) → +
        "append" => instance == "semigroupString",
        _ => false,
    }
}

fn is_inlinable_primop(method: &str, instance: &str) -> bool {
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
fn is_js_reserved_word(name: &str) -> bool {
    matches!(name,
        "break" | "case" | "catch" | "class" | "const" | "continue" |
        "debugger" | "default" | "delete" | "do" | "else" | "enum" |
        "export" | "extends" | "false" | "finally" | "for" | "function" |
        "if" | "import" | "in" | "instanceof" | "let" | "new" | "null" |
        "return" | "super" | "switch" | "this" | "throw" | "true" |
        "try" | "typeof" | "var" | "void" | "while" | "with" | "yield" |
        "await" | "implements" | "interface" | "package" | "private" |
        "protected" | "public" | "static"
    )
}

/// Find the first available name for a hoisted var, avoiding conflicts.
/// Returns None if the base name is a JS reserved word.
fn find_available_name(base: &str, used_names: &HashSet<String>) -> Option<String> {
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
fn find_module_hoistable_in_expr(
    expr: &JsExpr,
    module_vars: &HashSet<String>,
    class_accessors: &HashSet<String>,
    imported_class_methods: &HashSet<String>,
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
            let args_all_constant = args.len() <= 1 && args.iter().all(|a| is_constant_ref(a, module_vars));

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
                find_module_hoistable_in_stmt(stmt, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth + 1, enclosing_decl);
            }
        }
        JsExpr::App(callee, args) => {
            find_module_hoistable_in_expr(callee, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for arg in args {
                find_module_hoistable_in_expr(arg, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        JsExpr::Ternary(a, b, c) => {
            find_module_hoistable_in_expr(a, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(b, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(c, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsExpr::ArrayLit(items) => {
            for item in items {
                find_module_hoistable_in_expr(item, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields {
                find_module_hoistable_in_expr(val, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) | JsExpr::InstanceOf(a, b) => {
            find_module_hoistable_in_expr(a, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(b, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsExpr::Unary(_, a) => {
            find_module_hoistable_in_expr(a, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsExpr::New(callee, args) => {
            find_module_hoistable_in_expr(callee, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for arg in args {
                find_module_hoistable_in_expr(arg, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            }
        }
        _ => {}
    }
}

fn find_module_hoistable_in_stmt(
    stmt: &JsStmt,
    module_vars: &HashSet<String>,
    class_accessors: &HashSet<String>,
    imported_class_methods: &HashSet<String>,
    hoistables: &mut Vec<(JsExpr, String)>,
    hoistable_keys: &mut HashSet<String>,
    used_names: &mut HashSet<String>,
    depth: usize,
    enclosing_decl: &str,
) {
    match stmt {
        JsStmt::Return(expr) | JsStmt::Expr(expr) | JsStmt::Throw(expr) => {
            find_module_hoistable_in_expr(expr, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsStmt::VarDecl(_, Some(expr)) => {
            find_module_hoistable_in_expr(expr, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsStmt::Assign(target, val) => {
            find_module_hoistable_in_expr(target, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(val, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
        }
        JsStmt::If(cond, then_body, else_body) => {
            find_module_hoistable_in_expr(cond, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in then_body { find_module_hoistable_in_stmt(s, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
            if let Some(stmts) = else_body {
                for s in stmts { find_module_hoistable_in_stmt(s, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
            }
        }
        JsStmt::Block(stmts) => {
            for s in stmts { find_module_hoistable_in_stmt(s, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        JsStmt::For(_, init, bound, body_stmts) => {
            find_module_hoistable_in_expr(init, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            find_module_hoistable_in_expr(bound, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in body_stmts { find_module_hoistable_in_stmt(s, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        JsStmt::ForIn(_, obj, body_stmts) => {
            find_module_hoistable_in_expr(obj, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in body_stmts { find_module_hoistable_in_stmt(s, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        JsStmt::While(cond, body_stmts) => {
            find_module_hoistable_in_expr(cond, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl);
            for s in body_stmts { find_module_hoistable_in_stmt(s, module_vars, class_accessors, imported_class_methods, hoistables, hoistable_keys, used_names, depth, enclosing_decl); }
        }
        _ => {}
    }
}

/// Replace hoistable expressions with var references throughout an expression tree.
/// Uses a HashMap keyed by Debug string for O(1) lookup instead of linear scan.
fn replace_module_hoistable_expr(expr: JsExpr, hoistable_map: &HashMap<String, String>) -> JsExpr {
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

fn replace_module_hoistable_stmt(stmt: JsStmt, hoistable_map: &HashMap<String, String>) -> JsStmt {
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
fn reorder_where_bindings(stmts: &mut [JsStmt]) {
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
    // Handle any remaining (circular deps)
    for i in (0..n).rev() {
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
fn collect_var_refs_in_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
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

fn collect_var_refs_in_stmt(stmt: &JsStmt, refs: &mut HashSet<String>) {
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
fn uncurry_create_to_new(expr: JsExpr) -> JsExpr {
    // First, try to uncurry at this level
    let expr = uncurry_create_to_new_shallow(expr);
    // Then recurse into sub-expressions
    match expr {
        JsExpr::Function(name, params, body) => {
            JsExpr::Function(name, params, body.into_iter().map(uncurry_create_to_new_stmt).collect())
        }
        JsExpr::App(callee, args) => {
            JsExpr::App(
                Box::new(uncurry_create_to_new(*callee)),
                args.into_iter().map(uncurry_create_to_new).collect(),
            )
        }
        JsExpr::New(callee, args) => {
            JsExpr::New(
                Box::new(uncurry_create_to_new(*callee)),
                args.into_iter().map(uncurry_create_to_new).collect(),
            )
        }
        JsExpr::ObjectLit(fields) => {
            JsExpr::ObjectLit(fields.into_iter().map(|(k, v)| (k, uncurry_create_to_new(v))).collect())
        }
        JsExpr::ArrayLit(items) => {
            JsExpr::ArrayLit(items.into_iter().map(uncurry_create_to_new).collect())
        }
        JsExpr::Ternary(a, b, c) => {
            JsExpr::Ternary(
                Box::new(uncurry_create_to_new(*a)),
                Box::new(uncurry_create_to_new(*b)),
                Box::new(uncurry_create_to_new(*c)),
            )
        }
        JsExpr::Binary(op, a, b) => {
            JsExpr::Binary(op, Box::new(uncurry_create_to_new(*a)), Box::new(uncurry_create_to_new(*b)))
        }
        JsExpr::Unary(op, a) => {
            JsExpr::Unary(op, Box::new(uncurry_create_to_new(*a)))
        }
        JsExpr::Indexer(a, b) => {
            JsExpr::Indexer(Box::new(uncurry_create_to_new(*a)), Box::new(uncurry_create_to_new(*b)))
        }
        other => other,
    }
}

fn uncurry_create_to_new_stmt(stmt: JsStmt) -> JsStmt {
    match stmt {
        JsStmt::VarDecl(name, Some(expr)) => JsStmt::VarDecl(name, Some(uncurry_create_to_new(expr))),
        JsStmt::Return(expr) => JsStmt::Return(uncurry_create_to_new(expr)),
        JsStmt::Expr(expr) => JsStmt::Expr(uncurry_create_to_new(expr)),
        JsStmt::Throw(expr) => JsStmt::Throw(uncurry_create_to_new(expr)),
        JsStmt::Assign(a, b) => JsStmt::Assign(uncurry_create_to_new(a), uncurry_create_to_new(b)),
        JsStmt::If(cond, then_b, else_b) => JsStmt::If(
            uncurry_create_to_new(cond),
            then_b.into_iter().map(uncurry_create_to_new_stmt).collect(),
            else_b.map(|stmts| stmts.into_iter().map(uncurry_create_to_new_stmt).collect()),
        ),
        JsStmt::Block(stmts) => JsStmt::Block(stmts.into_iter().map(uncurry_create_to_new_stmt).collect()),
        JsStmt::For(v, init, bound, body) => JsStmt::For(
            v, uncurry_create_to_new(init), uncurry_create_to_new(bound),
            body.into_iter().map(uncurry_create_to_new_stmt).collect(),
        ),
        JsStmt::While(cond, body) => JsStmt::While(
            uncurry_create_to_new(cond),
            body.into_iter().map(uncurry_create_to_new_stmt).collect(),
        ),
        other => other,
    }
}

/// Shallow uncurry: collects curried args at this level only.
fn uncurry_create_to_new_shallow(expr: JsExpr) -> JsExpr {
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
    // Check if base is Ctor.create (Indexer with "create")
    if let JsExpr::Indexer(ctor, key) = &current {
        if let JsExpr::StringLit(s) = key.as_ref() {
            if s == "create" {
                return JsExpr::New(ctor.clone(), args);
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
fn references_constructor(expr: &JsExpr) -> bool {
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
fn references_constructor_shallow(expr: &JsExpr) -> bool {
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
fn optimize_string_concat_stmt(stmt: JsStmt) -> JsStmt {
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

fn optimize_string_concat_expr(expr: JsExpr) -> JsExpr {
    // Pattern: App(App(App(ModuleAccessor("...", "append"), ModuleAccessor("...", "semigroupString")), a), b)
    // → Binary(Add, a, b)
    match expr {
        JsExpr::App(callee, args) if args.len() == 1 => {
            // Check for append(semigroupString)(a)(b) — 3-level nested App
            if is_string_append_call(&callee, &args) {
                // Unwrap: App(App(App(append, semigroupString), a), b)
                let b = args.into_iter().next().unwrap();
                if let JsExpr::App(inner_callee, inner_args) = *callee {
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

fn is_semigroup_append(expr: &JsExpr) -> bool {
    matches!(expr, JsExpr::ModuleAccessor(_, field) if field == "append")
}

fn is_semigroup_string(expr: &JsExpr) -> bool {
    matches!(expr, JsExpr::ModuleAccessor(_, field) if field == "semigroupString")
}

/// Check if an expression is `App(App(append, semigroupString), a)` applied to `[b]`
fn is_string_append_call(callee: &JsExpr, _args: &[JsExpr]) -> bool {
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
fn optimize_boolean_ops_stmt(stmt: JsStmt) -> JsStmt {
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

fn optimize_boolean_ops_expr(expr: JsExpr) -> JsExpr {
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
fn is_boolean_op_call(callee: &JsExpr, args: &[JsExpr]) -> Option<(JsBinaryOp, JsExpr, JsExpr)> {
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

fn is_heyting_boolean_qualified(expr: &JsExpr) -> bool {
    matches!(expr, JsExpr::ModuleAccessor(_, name) if name == "heytingAlgebraBoolean")
}

/// Inline common numeric, comparison, and constant operations.
/// Matches the original PureScript compiler's `inlineCommonOperators` and `inlineCommonValues`.
fn optimize_common_ops_stmt(stmt: JsStmt) -> JsStmt {
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

fn optimize_common_ops_expr(expr: JsExpr) -> JsExpr {
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
fn extract_method_and_dict(expr: &JsExpr) -> Option<(&str, &str, &str)> {
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
fn try_inline_binary_op(callee: &JsExpr, args: &[JsExpr]) -> Option<JsExpr> {
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
fn try_inline_unary_op(callee: &JsExpr, args: &[JsExpr]) -> Option<JsExpr> {
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
fn try_inline_constant(callee: &JsExpr) -> Option<JsExpr> {
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

fn is_eq_dict(dict: &str) -> bool {
    matches!(dict, "eqInt" | "eqNumber" | "eqString" | "eqChar" | "eqBoolean")
}

fn is_ord_dict(dict: &str) -> bool {
    matches!(dict, "ordInt" | "ordNumber" | "ordString" | "ordChar" | "ordBoolean")
}

/// Inline trivial alias bindings: if `var x = y;` where y is a simple variable
/// that's a function parameter (not another where binding), replace all
/// subsequent uses of `x` with `y` and remove the binding.
fn inline_trivial_aliases(stmts: &mut Vec<JsStmt>) {
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

/// Recursively apply `inline_trivial_aliases` to all function bodies in a statement.
fn inline_trivial_aliases_recursive(stmt: &mut JsStmt) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) => inline_trivial_aliases_in_expr(expr),
        JsStmt::Return(expr) => inline_trivial_aliases_in_expr(expr),
        JsStmt::Expr(expr) => inline_trivial_aliases_in_expr(expr),
        JsStmt::Throw(expr) => inline_trivial_aliases_in_expr(expr),
        JsStmt::Assign(a, b) => {
            inline_trivial_aliases_in_expr(a);
            inline_trivial_aliases_in_expr(b);
        }
        JsStmt::If(cond, then_body, else_body) => {
            inline_trivial_aliases_in_expr(cond);
            inline_trivial_aliases(then_body);
            for s in then_body.iter_mut() { inline_trivial_aliases_recursive(s); }
            if let Some(stmts) = else_body {
                inline_trivial_aliases(stmts);
                for s in stmts.iter_mut() { inline_trivial_aliases_recursive(s); }
            }
        }
        _ => {}
    }
}

fn inline_trivial_aliases_in_expr(expr: &mut JsExpr) {
    match expr {
        JsExpr::Function(_, _, body) => {
            inline_trivial_aliases(body);
            for s in body.iter_mut() { inline_trivial_aliases_recursive(s); }
        }
        JsExpr::App(callee, args) => {
            inline_trivial_aliases_in_expr(callee);
            for a in args { inline_trivial_aliases_in_expr(a); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { inline_trivial_aliases_in_expr(v); }
        }
        JsExpr::ArrayLit(items) => {
            for i in items { inline_trivial_aliases_in_expr(i); }
        }
        JsExpr::Ternary(a, b, c) => {
            inline_trivial_aliases_in_expr(a);
            inline_trivial_aliases_in_expr(b);
            inline_trivial_aliases_in_expr(c);
        }
        JsExpr::Binary(_, a, b) | JsExpr::Indexer(a, b) => {
            inline_trivial_aliases_in_expr(a);
            inline_trivial_aliases_in_expr(b);
        }
        JsExpr::Unary(_, a) | JsExpr::InstanceOf(a, _) | JsExpr::New(a, _) => {
            inline_trivial_aliases_in_expr(a);
        }
        _ => {}
    }
}

fn substitute_var_in_stmt(stmt: &mut JsStmt, from: &str, to: &str) {
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

fn substitute_var_in_expr(expr: &mut JsExpr, from: &str, to: &str) {
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
fn count_var_in_stmts(stmts: &[JsStmt], name: &str) -> usize {
    stmts.iter().map(|s| count_var_in_stmt(s, name)).sum()
}

fn count_var_in_stmt(stmt: &JsStmt, name: &str) -> usize {
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

fn count_var_in_expr(expr: &JsExpr, name: &str) -> usize {
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
fn substitute_var_with_expr_in_stmt(stmt: &mut JsStmt, from: &str, replacement: &JsExpr) {
    match stmt {
        JsStmt::Return(expr) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::VarDecl(_, Some(expr)) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::Expr(expr) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::If(cond, then_body, else_body) => {
            substitute_var_with_expr_in_expr(cond, from, replacement);
            for s in then_body { substitute_var_with_expr_in_stmt(s, from, replacement); }
            if let Some(stmts) = else_body {
                for s in stmts { substitute_var_with_expr_in_stmt(s, from, replacement); }
            }
        }
        JsStmt::Assign(lhs, rhs) => {
            substitute_var_with_expr_in_expr(lhs, from, replacement);
            substitute_var_with_expr_in_expr(rhs, from, replacement);
        }
        JsStmt::Throw(expr) => substitute_var_with_expr_in_expr(expr, from, replacement),
        JsStmt::Block(stmts) => {
            for s in stmts { substitute_var_with_expr_in_stmt(s, from, replacement); }
        }
        JsStmt::For(_, init, bound, body) => {
            substitute_var_with_expr_in_expr(init, from, replacement);
            substitute_var_with_expr_in_expr(bound, from, replacement);
            for s in body { substitute_var_with_expr_in_stmt(s, from, replacement); }
        }
        JsStmt::ForIn(_, obj, body) => {
            substitute_var_with_expr_in_expr(obj, from, replacement);
            for s in body { substitute_var_with_expr_in_stmt(s, from, replacement); }
        }
        JsStmt::While(cond, body) => {
            substitute_var_with_expr_in_expr(cond, from, replacement);
            for s in body { substitute_var_with_expr_in_stmt(s, from, replacement); }
        }
        _ => {}
    }
}

fn substitute_var_with_expr_in_expr(expr: &mut JsExpr, from: &str, replacement: &JsExpr) {
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
            for s in body { substitute_var_with_expr_in_stmt(s, from, replacement); }
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
fn inline_field_access_bindings(stmts: &mut Vec<JsStmt>) {
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
fn inline_field_access_in_stmt(stmt: &mut JsStmt) {
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

fn inline_field_access_in_expr(expr: &mut JsExpr) {
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

// ===== Tail Call Optimization =====

/// Check if a function is tail-recursive and apply TCO transformation.
/// Called on `VarDecl(name, Some(Function(...)))` statements.
/// Transforms tail-recursive functions into while-loop form.
fn apply_tco_if_applicable(stmts: &mut Vec<JsStmt>) {
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
                transform_tco(name.clone(), expr);
            }
        }
        i += 1;
    }
}

/// Check if a curried function has dict wrapper layers (intermediate function layers
/// with VarDecl statements before returning the next function). These indicate
/// class-constrained functions like `gcd(dictEq)(dictER)(a)(b)`.
fn has_dict_wrapper_layers(expr: &JsExpr) -> bool {
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
fn unwrap_curried_fn(expr: &JsExpr) -> (Vec<Vec<String>>, &[JsStmt]) {
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
fn is_tail_recursive(fn_name: &str, arity: usize, expr: &JsExpr) -> bool {
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

fn body_has_tail_call(fn_name: &str, arity: usize, stmts: &[JsStmt]) -> bool {
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
fn is_self_call(fn_name: &str, arity: usize, expr: &JsExpr) -> bool {
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
fn extract_self_call_args(arity: usize, expr: &JsExpr) -> Vec<JsExpr> {
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
fn transform_tco(fn_name: String, expr: &mut JsExpr) {
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
    let dict_params: Vec<String> = param_layers[..dict_layer_count].iter().flatten().cloned().collect();
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

fn get_innermost_body_mut(expr: &mut JsExpr, depth: usize) -> &mut Vec<JsStmt> {
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

fn rename_params_to_copy(expr: &mut JsExpr, depth: usize, skip_layers: usize) {
    let mut current = expr;
    for level in 0..depth {
        if let JsExpr::Function(_, params, body) = current {
            // Only rename params in non-dict layers (skip_layers controls how many to skip)
            if level >= skip_layers {
                for param in params.iter_mut() {
                    *param = format!("$copy_{param}");
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

fn body_has_non_recursive_return(fn_name: &str, arity: usize, stmts: &[JsStmt]) -> bool {
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

fn loopify_stmts(
    fn_name: &str,
    arity: usize,
    all_params: &[String],
    outer_params: &[String],
    inner_params: &[String],
    stmts: &[JsStmt],
    has_base_case: bool,
) -> Vec<JsStmt> {
    loopify_stmts_with_dicts(fn_name, arity, all_params, outer_params, inner_params, stmts, has_base_case, 0)
}

fn loopify_stmts_with_dicts(
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
fn inline_single_use_bindings(stmts: &mut Vec<JsStmt>) {
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
    // Safe because property accesses on constructor results are pure.
    let mut i = 0;
    while i < stmts.len() {
        let inline_expr = if let JsStmt::VarDecl(ref name, Some(ref init)) = stmts[i] {
            if is_pure_field_access(init) {
                let use_count = count_var_uses_in_stmts(&stmts[i+1..], name);
                if use_count == 1 {
                    Some((name.clone(), init.clone()))
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
fn is_pure_field_access(expr: &JsExpr) -> bool {
    match expr {
        JsExpr::Indexer(obj, _key) => {
            matches!(obj.as_ref(), JsExpr::Var(_)) || is_pure_field_access(obj)
        }
        _ => false,
    }
}

/// Count how many times a variable name is used in a list of statements.
fn count_var_uses_in_stmts(stmts: &[JsStmt], name: &str) -> usize {
    stmts.iter().map(|s| count_var_uses_in_stmt(s, name)).sum()
}

fn count_var_uses_in_stmt(stmt: &JsStmt, name: &str) -> usize {
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

fn count_var_uses_in_expr(expr: &JsExpr, name: &str) -> usize {
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
fn substitute_expr_in_stmt(stmt: &mut JsStmt, name: &str, replacement: &JsExpr) {
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

fn substitute_expr_in_expr(expr: JsExpr, name: &str, replacement: &JsExpr) -> JsExpr {
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

    let params: Vec<String> = (0..arity).map(|i| ctx.fresh_name("v")).collect();

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

    // Newtype constructor is identity: var Name = function(x) { return x; };
    let identity = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );

    vec![JsStmt::VarDecl(ctor_js, Some(identity))]
}

// ===== Class declarations =====

fn gen_class_decl(_ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Class { members, .. } = decl else { return vec![] };

    let mut stmts = Vec::new();
    for member in members {
        let method_js = ident_to_js(member.name.value);
        let method_ps = interner::resolve(member.name.value).unwrap_or_default();
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
fn type_expr_to_name(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Constructor { name, .. } => {
            interner::resolve(name.name).unwrap_or_default().to_string()
        }
        TypeExpr::Var { name, .. } => {
            interner::resolve(name.value).unwrap_or_default().to_string()
        }
        TypeExpr::App { constructor, .. } => type_expr_to_name(constructor),
        TypeExpr::Parens { ty, .. } => type_expr_to_name(ty),
        _ => String::new(),
    }
}

/// Generate a JS name for an unnamed instance from its class name and type arguments.
fn gen_unnamed_instance_name(
    class_name: &QualifiedIdent,
    types: &[TypeExpr],
    instance_registry: &HashMap<(Symbol, Symbol), Symbol>,
    type_op_targets: &HashMap<Symbol, Symbol>,
) -> String {
    // Try the instance registry first
    let registry_name = extract_head_type_con_from_cst(types, type_op_targets).and_then(|head| {
        instance_registry.get(&(class_name.name, head)).map(|n| ident_to_js(*n))
    });
    if let Some(name) = registry_name {
        return name;
    }
    // Fallback: Generate from class + types, e.g. "reifiableBoolean"
    let class_str = interner::resolve(class_name.name).unwrap_or_default();
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

fn gen_instance_decl(ctx: &CodegenCtx, decl: &Decl, override_name: Option<String>) -> Vec<JsStmt> {
    let Decl::Instance { name, members, constraints, class_name, types, .. } = decl else { return vec![] };

    // Use override name if provided (already deduplicated by caller), otherwise compute
    let instance_name = if let Some(n) = override_name {
        n
    } else {
        match name {
            Some(n) => ident_to_js(n.value),
            None => gen_unnamed_instance_name(class_name, types, &ctx.instance_registry, &ctx.type_op_targets),
        }
    };

    // Push dict scope entries for instance constraints (with unique names for same-class)
    // Only push runtime constraints — zero-cost constraints have no param.
    let prev_scope_len = ctx.dict_scope.borrow().len();
    {
        let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
        for constraint in constraints {
            if !ctx.known_runtime_classes.contains(&constraint.class.name) {
                continue; // Zero-cost constraint — no runtime dict param
            }
            let class_name_str = interner::resolve(constraint.class.name).unwrap_or_default();
            let count = dict_name_counts.entry(class_name_str.to_string()).or_insert(0);
            let dict_param = if *count == 0 {
                format!("dict{class_name_str}")
            } else {
                format!("dict{class_name_str}{count}")
            };
            *count += 1;
            ctx.dict_scope.borrow_mut().push((constraint.class.name, dict_param));
        }
    }

    // Build multi-equation groups for instance methods (preserving source order)
    let mut method_order: Vec<Symbol> = Vec::new();
    let mut method_map: HashMap<Symbol, Vec<&Decl>> = HashMap::new();
    for member in members {
        if let Decl::Value { name: method_name, .. } = member {
            if !method_map.contains_key(&method_name.value) {
                method_order.push(method_name.value);
            }
            method_map.entry(method_name.value).or_default().push(member);
        }
    }

    let mut fields = Vec::new();
    for method_sym in &method_order {
        let decls = &method_map[method_sym];
        let method_js = ident_to_js(*method_sym);
        // Reset fresh counter for each instance method (original compiler does this)
        ctx.fresh_counter.set(0);

        // Check if this method has its own constraints (e.g., `discard :: Bind f => ...`)
        let method_qi = unqualified(*method_sym);
        let method_constraints: Vec<Symbol> = ctx.exports.method_own_constraints
            .get(&method_qi)
            .cloned()
            .or_else(|| {
                // Also check registry for imported class methods
                for (_, mod_exports) in ctx.registry.iter_all() {
                    if let Some(c) = mod_exports.method_own_constraints.get(&method_qi) {
                        return Some(c.clone());
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
    gen_superclass_accessors(ctx, class_name, types, constraints, &mut fields);

    let mut obj: JsExpr = JsExpr::ObjectLit(fields);

    // If the instance has constraints, wrap in curried functions taking dict params
    // and hoist dict method applications into the function body.
    // Type-level constraints (RowToList, Cons, Nub, etc.) get function() with no param.
    if !constraints.is_empty() {
        let dict_params = constraint_dict_params(constraints);

        // Step 1: Build constraint wrapping WITHOUT hoisting (inside-out).
        for ci in (0..constraints.len()).rev() {
            let is_runtime = ctx.known_runtime_classes.contains(&constraints[ci].class.name);
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

/// Known derivable classes from the PureScript standard library.
/// Each variant corresponds to a class that can appear in `derive instance`.
#[derive(Debug, Clone, Copy, PartialEq)]
enum DeriveClass {
    Eq,       // Data.Eq.Eq
    Ord,      // Data.Ord.Ord
    Eq1,      // Data.Eq.Eq1
    Ord1,     // Data.Ord.Ord1
    Functor,     // Data.Functor.Functor
    Foldable,    // Data.Foldable.Foldable
    Traversable, // Data.Traversable.Traversable
    Newtype,     // Data.Newtype.Newtype
    Generic,  // Data.Generic.Rep.Generic
    Bifunctor,   // Data.Bifunctor.Bifunctor
    Profunctor,  // Data.Profunctor.Profunctor
    Unknown,  // Not a known derivable class
}

/// Resolve a class name (+ optional module qualifier) to a known derivable class.
/// Checks module qualification when available, falls back to name-only matching
/// for locally-defined classes (common in tests).
fn resolve_derive_class(class_name: &str, module: Option<&str>) -> DeriveClass {
    match (class_name, module) {
        // Module-qualified matches (canonical)
        ("Eq", Some("Data.Eq")) => DeriveClass::Eq,
        ("Ord", Some("Data.Ord")) => DeriveClass::Ord,
        ("Eq1", Some("Data.Eq")) => DeriveClass::Eq1,
        ("Ord1", Some("Data.Ord")) => DeriveClass::Ord1,
        ("Functor", Some("Data.Functor")) => DeriveClass::Functor,
        ("Foldable", Some("Data.Foldable")) => DeriveClass::Foldable,
        ("Traversable", Some("Data.Traversable")) => DeriveClass::Traversable,
        ("Newtype", Some("Data.Newtype")) => DeriveClass::Newtype,
        ("Generic", Some("Data.Generic.Rep")) => DeriveClass::Generic,
        ("Bifunctor", Some("Data.Bifunctor")) => DeriveClass::Bifunctor,
        ("Profunctor", Some("Data.Profunctor")) => DeriveClass::Profunctor,
        // Unqualified fallback (for locally-defined classes in single-module tests)
        ("Eq", None) => DeriveClass::Eq,
        ("Ord", None) => DeriveClass::Ord,
        ("Eq1", None) => DeriveClass::Eq1,
        ("Ord1", None) => DeriveClass::Ord1,
        ("Functor", None) => DeriveClass::Functor,
        ("Foldable", None) => DeriveClass::Foldable,
        ("Traversable", None) => DeriveClass::Traversable,
        ("Newtype", None) => DeriveClass::Newtype,
        ("Generic", None) => DeriveClass::Generic,
        ("Bifunctor", None) => DeriveClass::Bifunctor,
        ("Profunctor", None) => DeriveClass::Profunctor,
        _ => DeriveClass::Unknown,
    }
}

/// Generate code for a `derive instance` declaration.
/// Produces actual method implementations based on the class being derived.
fn gen_derive_decl(ctx: &CodegenCtx, decl: &Decl, override_name: Option<String>) -> Vec<JsStmt> {
    let Decl::Derive { name, newtype, constraints, class_name, types, .. } = decl else { return vec![] };

    let instance_name = if let Some(n) = override_name {
        n
    } else {
        match name {
            Some(n) => ident_to_js(n.value),
            None => gen_unnamed_instance_name(class_name, types, &ctx.instance_registry, &ctx.type_op_targets),
        }
    };

    let class_str = interner::resolve(class_name.name).unwrap_or_default();
    // Resolve import alias to actual module name for derive class resolution.
    // E.g., `import Data.Generic.Rep as G` means class_name.module = Some("G"),
    // which needs to be resolved to "Data.Generic.Rep".
    let class_module_resolved: Option<String> = class_name.module.and_then(|m| {
        let alias_str = interner::resolve(m)?;
        // Check if this matches an import alias (e.g., `import Data.Generic.Rep as G`)
        for imp in &ctx.module.imports {
            if let Some(qual) = &imp.qualified {
                // The qualified alias is a ModuleName with parts
                if qual.parts.len() == 1 {
                    let qual_name = interner::resolve(qual.parts[0])?;
                    if qual_name == alias_str {
                        let parts: Vec<String> = imp.module.parts.iter()
                            .filter_map(|p| interner::resolve(*p).map(|s| s.to_string()))
                            .collect();
                        return Some(parts.join("."));
                    }
                }
            }
        }
        Some(alias_str.to_string())
    });
    let derive_kind = resolve_derive_class(&class_str, class_module_resolved.as_deref());

    // For derive newtype: delegate to the underlying type's instance
    if *newtype {
        return gen_derive_newtype_instance(ctx, &instance_name, &class_str, class_name, types, constraints);
    }

    // Extract the target type constructor name
    let target_type = extract_head_type_con_from_cst(types, &ctx.type_op_targets);

    // Look up constructors for the target type (with field types for unconstrained derives)
    let ctors_with_types: Vec<(String, usize, Vec<crate::typechecker::types::Type>)> = target_type.and_then(|t| {
        let qi = unqualified(t);
        ctx.data_constructors.get(&qi).map(|ctor_names| {
            ctor_names.iter().filter_map(|cn| {
                ctx.ctor_details.get(cn).map(|(_, _, field_types)| {
                    let name_str = interner::resolve(cn.name).unwrap_or_default();
                    (name_str, field_types.len(), field_types.clone())
                })
            }).collect::<Vec<_>>()
        })
    }).unwrap_or_default();
    let ctors: Vec<(String, usize)> = ctors_with_types.iter().map(|(n, c, _)| (n.clone(), *c)).collect();

    // Build per-constructor, per-field comparison info for Eq/Ord derives.
    let dict_params_for_all = if !constraints.is_empty() { constraint_dict_params(constraints) } else { vec![] };
    let ctor_fields_for_eq_ord: Vec<CtorFields> = if !constraints.is_empty() {
        // Constrained: build expressions from constraint dict params
        let method_name = match derive_kind {
            DeriveClass::Eq => Some("eq"),
            DeriveClass::Ord => Some("compare"),
            _ => None,
        };
        if let Some(mname) = method_name {
            let mut inline_exprs: Vec<JsExpr> = Vec::new();
            for (i, _constraint) in constraints.iter().enumerate() {
                let method_sym = interner::intern(mname);
                let method_qi = QualifiedIdent { module: None, name: method_sym };
                let method_ref = gen_qualified_ref_raw(ctx, &method_qi);
                let dict_app = JsExpr::App(
                    Box::new(method_ref),
                    vec![JsExpr::Var(dict_params_for_all[i].clone())],
                );
                inline_exprs.push(dict_app);
            }
            build_constrained_ctor_fields(&ctors, &inline_exprs)
        } else {
            vec![]
        }
    } else {
        // Unconstrained: resolve concrete instances per field
        match derive_kind {
            DeriveClass::Eq => build_unconstrained_ctor_fields(ctx, &ctors_with_types, "Eq", "eq", true),
            DeriveClass::Ord => build_unconstrained_ctor_fields(ctx, &ctors_with_types, "Ord", "compare", false),
            _ => vec![],
        }
    };

    let mut fields: Vec<(String, JsExpr)> = match derive_kind {
        DeriveClass::Eq => gen_derive_eq_methods(&ctor_fields_for_eq_ord),
        DeriveClass::Ord => gen_derive_ord_methods(ctx, &ctor_fields_for_eq_ord),
        DeriveClass::Eq1 => gen_derive_eq1_methods(ctx, target_type),
        DeriveClass::Ord1 => gen_derive_ord1_methods(ctx, target_type),
        DeriveClass::Functor => {
            // Build the map_param_expr for parametric functor constraints (e.g. dictFunctor)
            let functor_map_param = if !constraints.is_empty() {
                let dict_params = constraint_dict_params(constraints);
                // Find the Functor constraint's dict param
                constraints.iter().zip(dict_params.iter()).find_map(|(c, dp)| {
                    let class_name = interner::resolve(c.class.name).unwrap_or_default();
                    if class_name == "Functor" {
                        Some(JsExpr::Var(dp.clone()))
                    } else {
                        None
                    }
                })
            } else {
                None
            };
            gen_derive_functor_methods(ctx, &ctors_with_types, functor_map_param)
        },
        DeriveClass::Foldable => vec![],
        DeriveClass::Traversable => gen_derive_traversable_methods(ctx, &ctors_with_types, &instance_name, &dict_params_for_all),
        DeriveClass::Newtype => gen_derive_newtype_class_methods(),
        DeriveClass::Generic => gen_derive_generic_methods(ctx, &ctors),
        DeriveClass::Bifunctor => gen_derive_bifunctor_methods(ctx, &ctors),
        DeriveClass::Profunctor => gen_derive_profunctor_methods(ctx, &ctors),
        DeriveClass::Unknown => vec![],
    };

    // Add superclass accessors (e.g., Ord needs Eq0)
    // Skip for Eq1/Ord1 — they already generate their own superclass accessors
    if constraints.is_empty() && derive_kind != DeriveClass::Eq1 && derive_kind != DeriveClass::Ord1 {
        // Unconstrained: direct reference to local superclass instance
        gen_superclass_accessors(ctx, class_name, types, constraints, &mut fields);
    } else if derive_kind == DeriveClass::Ord {
        // Constrained Ord: Eq0 references the local Eq instance applied to dictOrd.Eq0().
        // Generate inline — hoist_dict_applications will extract it.
        let dict_params = constraint_dict_params(constraints);
        let eq_sym = interner::intern("Eq");
        let eq_instance_name = find_local_eq_instance_for_type(ctx, target_type, eq_sym);
        if let Some(eq_inst_js) = eq_instance_name {
            // Eq0: function() { return eqMaybe(dictOrd.Eq0()); }
            let eq_accessor = JsExpr::App(
                Box::new(JsExpr::Indexer(
                    Box::new(JsExpr::Var(dict_params[0].clone())),
                    Box::new(JsExpr::StringLit("Eq0".to_string())),
                )),
                vec![],
            );
            let eq_applied = JsExpr::App(
                Box::new(JsExpr::Var(eq_inst_js)),
                vec![eq_accessor],
            );
            fields.push(("Eq0".to_string(), JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(eq_applied)],
            )));
        }
    } else if derive_kind == DeriveClass::Traversable {
        // Constrained Traversable: Functor0 and Foldable1 reference local instances
        // applied to the constraint dict's superclass accessors.
        // e.g., Functor0: function() { return functorM(dictTraversable.Functor0()); }
        //       Foldable1: function() { return foldableM(dictTraversable.Foldable1()); }
        let dict_params = constraint_dict_params(constraints);
        if let Some(target) = target_type {
            let type_str = interner::resolve(target).unwrap_or_default();
            // Functor0: functorM(dictTraversable.Functor0())
            let functor_inst_name = format!("functor{type_str}");
            let functor0_accessor = JsExpr::App(
                Box::new(JsExpr::Indexer(
                    Box::new(JsExpr::Var(dict_params[0].clone())),
                    Box::new(JsExpr::StringLit("Functor0".to_string())),
                )),
                vec![],
            );
            let functor_applied = JsExpr::App(
                Box::new(JsExpr::Var(functor_inst_name)),
                vec![functor0_accessor],
            );
            fields.push(("Functor0".to_string(), JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(functor_applied)],
            )));

            // Foldable1: foldableM(dictTraversable.Foldable1())
            let foldable_inst_name = format!("foldable{type_str}");
            let foldable1_accessor = JsExpr::App(
                Box::new(JsExpr::Indexer(
                    Box::new(JsExpr::Var(dict_params[0].clone())),
                    Box::new(JsExpr::StringLit("Foldable1".to_string())),
                )),
                vec![],
            );
            let foldable_applied = JsExpr::App(
                Box::new(JsExpr::Var(foldable_inst_name)),
                vec![foldable1_accessor],
            );
            fields.push(("Foldable1".to_string(), JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(foldable_applied)],
            )));
        }
    }

    let mut obj: JsExpr = JsExpr::ObjectLit(fields);

    // Wrap in constraint functions with hoisted dict method calls.
    // Use a shared counter across all constraint levels so that vars with the same
    // method name get properly numbered (e.g., eq, eq2 for two Eq constraints).
    // Process outer-to-inner for correct counter ordering, then build the nesting.
    if !constraints.is_empty() {
        let mut shared_counter: HashMap<String, usize> = HashMap::new();
        // First pass: pre-count names outer-to-inner to reserve correct numbering
        let mut hoisted_per_level: Vec<Vec<(JsExpr, String)>> = Vec::new();
        for (ci, _constraint) in constraints.iter().enumerate() {
            let dict_param = &dict_params_for_all[ci];
            let body = vec![JsStmt::Return(obj.clone())];
            let mut hoisted: Vec<(JsExpr, String)> = Vec::new();
            collect_dict_apps_nested(dict_param, &body, &mut hoisted, &mut shared_counter, 0);
            // Deduplicate
            let mut unique: Vec<(JsExpr, String)> = Vec::new();
            for (expr, name) in hoisted {
                if !unique.iter().any(|(e, _)| *e == expr) {
                    unique.push((expr, name));
                }
            }
            // Sort hoisted vars alphabetically to match original compiler ordering
            unique.sort_by(|a, b| a.1.cmp(&b.1));
            hoisted_per_level.push(unique);
        }
        // Second pass: build nested functions inside-out with collected hoisting info
        for ci in (0..constraints.len()).rev() {
            let is_runtime = ctx.known_runtime_classes.contains(&constraints[ci].class.name);
            if is_runtime {
                let dict_param = &dict_params_for_all[ci];
                let mut fn_body: Vec<JsStmt> = Vec::new();
                for (expr, name) in &hoisted_per_level[ci] {
                    fn_body.push(JsStmt::VarDecl(name.clone(), Some(expr.clone())));
                }
                let inner_body = vec![JsStmt::Return(obj)];
                // Replace dict apps in inner body with hoisted var references
                let replaced: Vec<JsStmt> = inner_body.into_iter()
                    .map(|s| replace_dict_apps_stmt(s, &hoisted_per_level[ci]))
                    .collect();
                fn_body.extend(replaced);
                obj = JsExpr::Function(None, vec![dict_param.clone()], fn_body);
            } else {
                // Type-level constraint: no runtime param
                obj = JsExpr::Function(None, vec![], vec![JsStmt::Return(obj)]);
            }
        }
    }

    // Wrap non-function derive instances in IIFE if they reference constructors
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

/// Generate derive newtype instance: delegates to the underlying type's instance.
/// `derive newtype instance showName :: Show Name` → uses the Show String instance.
///
/// There are two cases:
/// 1. Underlying type is concrete (e.g., `newtype Name = Name String`, `derive newtype instance Show Name`):
///    → Reference the concrete instance: `var showName = Data_Show.showString;`
/// 2. Underlying type is a type variable (e.g., `newtype Additive a = Additive a`, `derive newtype instance Eq a => Eq (Additive a)`):
///    → Pass constraint dict through: `var eqAdditive = function(dictEq) { return dictEq; };`
fn gen_derive_newtype_instance(
    ctx: &CodegenCtx,
    instance_name: &str,
    _class_str: &str,
    class_name: &QualifiedIdent,
    types: &[crate::cst::TypeExpr],
    constraints: &[Constraint],
) -> Vec<JsStmt> {
    let head_type = extract_head_type_con_from_cst(types, &ctx.type_op_targets);

    // Find the newtype's underlying type
    let underlying_is_type_var = head_type.and_then(|head| {
        let qi = unqualified(head);
        ctx.data_constructors.get(&qi).and_then(|ctor_names| {
            ctor_names.first().and_then(|ctor_qi| {
                ctx.ctor_details.get(ctor_qi).and_then(|(_, _, field_types)| {
                    field_types.first().map(|ty| extract_head_from_type(ty).is_none())
                })
            })
        })
    }).unwrap_or(false);

    if underlying_is_type_var && !constraints.is_empty() {
        // Type variable underlying type with constraints: just pass the dict through.
        // `derive newtype instance Eq a => Eq (Additive a)` → `function(dictEq) { return dictEq; }`
        let mut obj: JsExpr = JsExpr::Var("__placeholder__".to_string());
        for (i, constraint) in constraints.iter().enumerate().rev() {
            let dict_param = constraint_to_dict_param(constraint);
            if i == constraints.len() - 1 {
                // Innermost: return the dict param directly
                obj = JsExpr::Function(
                    None,
                    vec![dict_param.clone()],
                    vec![JsStmt::Return(JsExpr::Var(dict_param))],
                );
            } else {
                obj = JsExpr::Function(
                    None,
                    vec![dict_param.clone()],
                    vec![JsStmt::Return(obj)],
                );
            }
        }
        return vec![JsStmt::VarDecl(instance_name.to_string(), Some(obj))];
    }

    // Concrete underlying type: look up the instance
    let mut obj = if let Some(head) = head_type {
        let qi = unqualified(head);
        if let Some(ctor_names) = ctx.data_constructors.get(&qi) {
            if let Some(ctor_qi) = ctor_names.first() {
                if let Some((_, _, field_types)) = ctx.ctor_details.get(ctor_qi) {
                    if let Some(underlying_ty) = field_types.first() {
                        if let Some(underlying_head) = extract_head_from_type(underlying_ty) {
                            resolve_instance_ref(ctx, class_name.name, underlying_head)
                        } else {
                            JsExpr::ObjectLit(vec![])
                        }
                    } else {
                        JsExpr::ObjectLit(vec![])
                    }
                } else {
                    JsExpr::ObjectLit(vec![])
                }
            } else {
                JsExpr::ObjectLit(vec![])
            }
        } else {
            JsExpr::ObjectLit(vec![])
        }
    } else {
        JsExpr::ObjectLit(vec![])
    };

    // Wrap in constraint functions if needed
    if !constraints.is_empty() {
        for constraint in constraints.iter().rev() {
            let dict_param = constraint_to_dict_param(constraint);
            let inner = obj;
            obj = JsExpr::Function(
                None,
                vec![dict_param.clone()],
                vec![JsStmt::Return(JsExpr::App(Box::new(inner), vec![JsExpr::Var(dict_param)]))],
            );
        }
    }

    vec![JsStmt::VarDecl(instance_name.to_string(), Some(obj))]
}

/// Generate `eq` method for derive Eq.
/// `ctor_fields` contains per-constructor, per-field comparison info.
fn gen_derive_eq_methods(
    ctor_fields: &[CtorFields],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    let mut body = Vec::new();
    let is_sum = ctor_fields.len() > 1 || (ctor_fields.len() == 1 && ctor_fields[0].fields.is_empty());

    for cf in ctor_fields {
        if cf.fields.is_empty() {
            // Nullary constructor: instanceof check → return true
            let x_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::Var(cf.ctor_name.clone())),
            );
            let y_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(y.clone())),
                Box::new(JsExpr::Var(cf.ctor_name.clone())),
            );
            let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check), Box::new(y_check));
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(JsExpr::BoolLit(true))],
                None,
            ));
        } else {
            // Constructor with fields: compare each field
            let mut field_eq = JsExpr::BoolLit(true);
            for (i, (field_name, compare)) in cf.fields.iter().enumerate() {
                let x_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let eq_call = match compare {
                    FieldCompare::MethodExpr(expr) => {
                        JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(expr.clone()),
                                vec![x_field],
                            )),
                            vec![y_field],
                        )
                    }
                    FieldCompare::StrictEq => {
                        JsExpr::Binary(JsBinaryOp::StrictEq, Box::new(x_field), Box::new(y_field))
                    }
                };
                if i == 0 {
                    field_eq = eq_call;
                } else {
                    field_eq = JsExpr::Binary(JsBinaryOp::And, Box::new(field_eq), Box::new(eq_call));
                }
            }

            if is_sum {
                let x_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::Var(cf.ctor_name.clone())),
                );
                let y_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::Var(cf.ctor_name.clone())),
                );
                let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check), Box::new(y_check));
                body.push(JsStmt::If(
                    both_check,
                    vec![JsStmt::Return(field_eq)],
                    None,
                ));
            } else {
                // Single constructor — no instanceof needed, return directly
                body.push(JsStmt::Return(field_eq));
            }
        }
    }

    // Default: constructors don't match
    if is_sum || ctor_fields.is_empty() {
        body.push(JsStmt::Return(JsExpr::BoolLit(false)));
    }

    let eq_fn = JsExpr::Function(
        None,
        vec![x],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![y],
            body,
        ))],
    );

    vec![("eq".to_string(), eq_fn)]
}

/// Generate `eq1` method for derive Eq1.
/// For newtypes: `{ eq1: function(dictEq) { return Data_Eq.eq(eqF(dictEq)); } }`
fn gen_derive_eq1_methods(ctx: &CodegenCtx, target_type: Option<Symbol>) -> Vec<(String, JsExpr)> {
    // Find the local Eq instance for this type
    let eq_sym = interner::intern("Eq");
    let eq_instance_name = target_type.and_then(|head| {
        ctx.instance_registry.get(&(eq_sym, head)).map(|n| ident_to_js(*n))
    });

    if let Some(eq_inst_js) = eq_instance_name {
        // Resolve Data.Eq.eq
        let eq_qi = QualifiedIdent { module: None, name: interner::intern("eq") };
        let eq_ref = gen_qualified_ref_raw(ctx, &eq_qi);

        // eq1: function(dictEq) { return Data_Eq.eq(eqF(dictEq)); }
        let dict_param = "dictEq".to_string();
        let eq_body = JsExpr::App(
            Box::new(eq_ref),
            vec![JsExpr::App(
                Box::new(JsExpr::Var(eq_inst_js)),
                vec![JsExpr::Var(dict_param.clone())],
            )],
        );
        let eq1_fn = JsExpr::Function(
            None,
            vec![dict_param],
            vec![JsStmt::Return(eq_body)],
        );
        vec![("eq1".to_string(), eq1_fn)]
    } else {
        vec![]
    }
}

/// Generate `compare1` and `Eq10` methods for derive Ord1.
/// For newtypes: `{ compare1: function(dictOrd) { return Data_Ord.compare(ordF(dictOrd)); }, Eq10: function() { return eq1F; } }`
fn gen_derive_ord1_methods(ctx: &CodegenCtx, target_type: Option<Symbol>) -> Vec<(String, JsExpr)> {
    let ord_sym = interner::intern("Ord");
    let ord_instance_name = target_type.and_then(|head| {
        ctx.instance_registry.get(&(ord_sym, head)).map(|n| ident_to_js(*n))
    });

    let mut fields = Vec::new();

    if let Some(ord_inst_js) = ord_instance_name {
        // Resolve Data.Ord.compare
        let compare_qi = QualifiedIdent { module: None, name: interner::intern("compare") };
        let compare_ref = gen_qualified_ref_raw(ctx, &compare_qi);

        // compare1: function(dictOrd) { return Data_Ord.compare(ordF(dictOrd)); }
        let dict_param = "dictOrd".to_string();
        let compare_body = JsExpr::App(
            Box::new(compare_ref),
            vec![JsExpr::App(
                Box::new(JsExpr::Var(ord_inst_js)),
                vec![JsExpr::Var(dict_param.clone())],
            )],
        );
        let compare1_fn = JsExpr::Function(
            None,
            vec![dict_param],
            vec![JsStmt::Return(compare_body)],
        );
        fields.push(("compare1".to_string(), compare1_fn));
    }

    // Eq10: function() { return eq1F; }
    let eq1_sym = interner::intern("Eq1");
    let eq1_instance_name = target_type.and_then(|head| {
        ctx.instance_registry.get(&(eq1_sym, head)).map(|n| ident_to_js(*n))
    });
    if let Some(eq1_inst_js) = eq1_instance_name {
        let eq10_fn = JsExpr::Function(
            None,
            vec![],
            vec![JsStmt::Return(JsExpr::Var(eq1_inst_js))],
        );
        fields.push(("Eq10".to_string(), eq10_fn));
    }

    fields
}

/// Generate `compare` method for derive Ord.
/// Returns Data_Ordering.LT/EQ/GT based on constructor order and field comparison.
/// `ctor_fields` contains per-constructor, per-field comparison info.
fn gen_derive_ord_methods(
    ctx: &CodegenCtx,
    ctor_fields: &[CtorFields],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    // Resolve Data_Ordering.EQ/LT/GT references
    let ordering_eq = resolve_ordering_ref(ctx, "EQ");
    let ordering_lt = resolve_ordering_ref(ctx, "LT");
    let ordering_gt = resolve_ordering_ref(ctx, "GT");

    let mut body = Vec::new();

    // Void type (no constructors): return EQ (unreachable)
    if ctor_fields.is_empty() {
        body.push(JsStmt::Return(ordering_eq.clone()));

        let compare_fn = JsExpr::Function(
            None,
            vec![x],
            vec![JsStmt::Return(JsExpr::Function(
                None,
                vec![y],
                body,
            ))],
        );
        return vec![("compare".to_string(), compare_fn)];
    }

    for (_i, cf) in ctor_fields.iter().enumerate() {
        let x_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.clone())),
            Box::new(JsExpr::Var(cf.ctor_name.clone())),
        );
        let y_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(y.clone())),
            Box::new(JsExpr::Var(cf.ctor_name.clone())),
        );
        let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check.clone()), Box::new(y_check.clone()));

        if cf.fields.is_empty() {
            // Both same nullary: return EQ
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(ordering_eq.clone())],
                None,
            ));
        } else {
            // Both same with fields: compare fields
            let mut inner_body = Vec::new();
            for (field_name, compare) in &cf.fields {
                let x_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                match compare {
                    FieldCompare::MethodExpr(expr) => {
                        inner_body.push(JsStmt::Return(JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(expr.clone()),
                                vec![x_field],
                            )),
                            vec![y_field],
                        )));
                    }
                    FieldCompare::StrictEq => {
                        // For strict equality in ord, we still need to return an Ordering.
                        // This shouldn't normally happen for Ord (fields should have Ord instances),
                        // but as fallback, return EQ.
                        inner_body.push(JsStmt::Return(ordering_eq.clone()));
                    }
                }
            }
            if inner_body.is_empty() {
                inner_body.push(JsStmt::Return(ordering_eq.clone()));
            }
            body.push(JsStmt::If(both_check, inner_body, None));
        }

        // If only x matches this ctor: x comes before y → LT
        // Skip LT/GT for the last constructor — it's the catch-all before the throw
        if ctor_fields.len() > 1 && _i < ctor_fields.len() - 1 {
            body.push(JsStmt::If(
                x_check,
                vec![JsStmt::Return(ordering_lt.clone())],
                None,
            ));
            // If only y matches this ctor: y comes before x → GT
            body.push(JsStmt::If(
                y_check,
                vec![JsStmt::Return(ordering_gt.clone())],
                None,
            ));
        }
    }

    // Fallback: throw error
    body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));

    let compare_fn = JsExpr::Function(
        None,
        vec![x],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![y],
            body,
        ))],
    );

    vec![("compare".to_string(), compare_fn)]
}

/// Resolve a reference to Data.Ordering.X.value (EQ, LT, GT)
fn resolve_ordering_ref(ctx: &CodegenCtx, name: &str) -> JsExpr {
    // Always use Data.Ordering module for derive Ord — even if the module defines a local Ordering type
    let ordering_parts: Vec<Symbol> = vec![interner::intern("Data"), interner::intern("Ordering")];
    if let Some(js_mod) = ctx.import_map.get(&ordering_parts) {
        return JsExpr::Indexer(
            Box::new(JsExpr::ModuleAccessor(js_mod.clone(), name.to_string())),
            Box::new(JsExpr::StringLit("value".to_string())),
        );
    }
    // Fallback: local reference
    JsExpr::Indexer(
        Box::new(JsExpr::Var(name.to_string())),
        Box::new(JsExpr::StringLit("value".to_string())),
    )
}

/// Per-field comparison info for derive Eq/Ord.
/// Each field in a constructor maps to one of these.
enum FieldCompare {
    /// Use a method expression like `Data_Eq.eq(eqInt)` applied as `expr(x.field)(y.field)`
    MethodExpr(JsExpr),
    /// Use strict equality: `x.field === y.field`
    StrictEq,
}

/// Per-constructor field info for derive Eq/Ord.
struct CtorFields {
    ctor_name: String,
    /// Each element: (field_accessor_name, comparison)
    fields: Vec<(String, FieldCompare)>,
}

/// Build a method expression for a concrete field type.
/// E.g., for `Type::Con("Int")` and method "eq", returns `Data_Eq.eq(Data_Eq.eqInt)`.
/// For `Type::Con("Int")` and method "compare", returns `Data_Ord.compare(Data_Ord.ordInt)`.
/// Returns None if the instance can't be resolved (falls back to strict equality for eq).
fn resolve_field_method_expr(
    ctx: &CodegenCtx,
    field_type: &crate::typechecker::types::Type,
    class_name: &str,
    method_name: &str,
) -> Option<JsExpr> {
    use crate::typechecker::types::Type;
    let head = match field_type {
        Type::Con(qi) => Some(qi.name),
        Type::App(f, _) => extract_head_from_type(f),
        _ => None,
    }?;
    let class_sym = interner::intern(class_name);
    // Use resolve_instance_ref to get a properly qualified reference
    let inst_ref = resolve_instance_ref(ctx, class_sym, head);
    let method_sym = interner::intern(method_name);
    let method_qi = QualifiedIdent { module: None, name: method_sym };
    let method_ref = gen_qualified_ref_raw(ctx, &method_qi);
    Some(JsExpr::App(
        Box::new(method_ref),
        vec![inst_ref],
    ))
}

/// Check if a type is a primitive that supports strict equality (===) for Eq.
fn is_eq_primitive(ty: &crate::typechecker::types::Type) -> bool {
    use crate::typechecker::types::Type;
    match ty {
        Type::Con(qi) => {
            let name = interner::resolve(qi.name).unwrap_or_default();
            matches!(name.as_str(), "Int" | "Number" | "String" | "Char" | "Boolean")
        }
        _ => false,
    }
}

/// Build per-constructor field comparison info for unconstrained Eq/Ord derives.
fn build_unconstrained_ctor_fields(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    class_name: &str,
    method_name: &str,
    use_strict_eq_for_primitives: bool,
) -> Vec<CtorFields> {
    use crate::typechecker::types::Type;
    ctors_with_types.iter().map(|(ctor_name, _field_count, field_types)| {
        // Check if this constructor has a single record argument (newtype-like)
        if field_types.len() == 1 {
            if let Type::Record(row_fields, _) = &field_types[0] {
                // Record field comparison: compare by named fields
                let fields: Vec<(String, FieldCompare)> = row_fields.iter().map(|(label, ty)| {
                    let label_str = interner::resolve(*label).unwrap_or_default().to_string();
                    let compare = if use_strict_eq_for_primitives && is_eq_primitive(ty) {
                        FieldCompare::StrictEq
                    } else {
                        resolve_field_method_expr(ctx, ty, class_name, method_name)
                            .map(FieldCompare::MethodExpr)
                            .unwrap_or(FieldCompare::StrictEq)
                    };
                    (label_str, compare)
                }).collect();
                return CtorFields { ctor_name: ctor_name.clone(), fields };
            }
        }
        // Positional fields (value0, value1, ...)
        let fields: Vec<(String, FieldCompare)> = field_types.iter().enumerate().map(|(i, ty)| {
            let field_name = format!("value{i}");
            let compare = if use_strict_eq_for_primitives && is_eq_primitive(ty) {
                FieldCompare::StrictEq
            } else {
                resolve_field_method_expr(ctx, ty, class_name, method_name)
                    .map(FieldCompare::MethodExpr)
                    .unwrap_or(FieldCompare::StrictEq)
            };
            (field_name, compare)
        }).collect();
        CtorFields { ctor_name: ctor_name.clone(), fields }
    }).collect()
}

/// Build per-constructor field comparison info for constrained Eq/Ord derives.
/// Constrained derives map constraint params to all fields using type variables.
fn build_constrained_ctor_fields(
    ctors: &[(String, usize)],
    inline_exprs: &[JsExpr],
) -> Vec<CtorFields> {
    ctors.iter().map(|(ctor_name, field_count)| {
        let fields: Vec<(String, FieldCompare)> = (0..*field_count).map(|i| {
            let field_name = format!("value{i}");
            let compare = if i < inline_exprs.len() {
                FieldCompare::MethodExpr(inline_exprs[i].clone())
            } else {
                FieldCompare::StrictEq
            };
            (field_name, compare)
        }).collect();
        CtorFields { ctor_name: ctor_name.clone(), fields }
    }).collect()
}

/// Generate a failed pattern match error expression
fn gen_failed_pattern_match(_ctx: &CodegenCtx) -> JsExpr {
    JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )
}

/// Generate `map` method for derive Functor.
/// ```js
/// map: function(f) { return function(x) {
///   if (x instanceof Nothing) return Nothing.value;
///   if (x instanceof Just) return Just.create(f(x.value0));
///   ...
/// }}
/// ```
fn gen_derive_functor_methods(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    map_param_expr: Option<JsExpr>,
) -> Vec<(String, JsExpr)> {
    let f = "f".to_string();
    let m = "m".to_string();

    // Newtype optimization: newtypes have identity constructors at runtime, so
    // we map through the inner type directly (no constructor wrapping needed).
    // - Direct field (e.g. `newtype Identity a = Identity a`): `f(m)`
    // - KnownFunctor (e.g. `newtype Test1 a = Test1 (MonoAndBi Int a)`): `map(functorMonoAndBi)(f)(m)`
    // - Passthrough (field doesn't contain type var): `m`
    if ctors_with_types.len() == 1 && ctors_with_types[0].1 == 1 {
        let ctor_sym = interner::intern(&ctors_with_types[0].0);
        if ctx.newtype_names.contains(&ctor_sym) {
            // Categorize the single field to determine how to map it
            let ctor_qi = unqualified(ctor_sym);
            let field_kind = ctx.ctor_details.get(&ctor_qi)
                .map(|(parent, type_vars, field_types_raw)| {
                    let last_tv = type_vars.last().map(|qi| qi.name);
                    let param_tv = if type_vars.len() >= 2 {
                        type_vars.get(type_vars.len() - 2).map(|qi| qi.name)
                    } else {
                        None
                    };
                    let parent_name = parent.name;
                    field_types_raw.first()
                        .map(|ft| categorize_functor_field(ft, last_tv, param_tv, parent_name))
                        .unwrap_or(FunctorFieldKind::Direct)
                })
                .unwrap_or(FunctorFieldKind::Direct);

            let body_expr = gen_functor_map_field(ctx, &field_kind, &f, JsExpr::Var(m.clone()), map_param_expr.as_ref());
            let map_fn = JsExpr::Function(
                None,
                vec![f.clone()],
                vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![m.clone()],
                    vec![JsStmt::Return(body_expr)],
                ))],
            );
            return vec![("map".to_string(), map_fn)];
        }
    }

    let ctors: Vec<(String, usize)> = ctors_with_types.iter().map(|(n, c, _)| (n.clone(), *c)).collect();
    let mut body = Vec::new();
    let is_sum = ctors.len() > 1 || (ctors.len() == 1 && ctors[0].1 == 0);

    for (ctor_name, field_count, field_types_raw) in ctors_with_types {
        if *field_count == 0 {
            // Nullary constructor: return as-is
            let m_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(m.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
            );
            body.push(JsStmt::If(
                m_check,
                vec![JsStmt::Return(JsExpr::Indexer(
                    Box::new(JsExpr::Var(ctor_name.clone())),
                    Box::new(JsExpr::StringLit("value".to_string())),
                ))],
                None,
            ));
        } else {
            // Look up field types to determine how to map each field
            let ctor_sym = interner::intern(ctor_name);
            let ctor_qi = unqualified(ctor_sym);
            let field_kinds: Vec<FunctorFieldKind> = ctx.ctor_details.get(&ctor_qi)
                .map(|(parent, type_vars, _ftypes)| {
                    let last_tv = type_vars.last().map(|qi| qi.name);
                    let param_tv = if type_vars.len() >= 2 {
                        type_vars.get(type_vars.len() - 2).map(|qi| qi.name)
                    } else {
                        None
                    };
                    let parent_name = parent.name;
                    field_types_raw.iter().map(|ft| categorize_functor_field(ft, last_tv, param_tv, parent_name)).collect::<Vec<_>>()
                })
                .unwrap_or_else(|| vec![FunctorFieldKind::Direct; *field_count]);

            // Build args for new Ctor(arg0, arg1, ...)
            let mut args = Vec::new();
            for i in 0..*field_count {
                let field_access = JsExpr::Indexer(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::StringLit(format!("value{i}"))),
                );
                let kind = field_kinds.get(i).cloned().unwrap_or(FunctorFieldKind::Direct);
                let arg = gen_functor_map_field(ctx, &kind, &f, field_access, map_param_expr.as_ref());
                args.push(arg);
            }

            let result = JsExpr::New(
                Box::new(JsExpr::Var(ctor_name.clone())),
                args,
            );

            if is_sum {
                let m_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::Var(ctor_name.clone())),
                );
                body.push(JsStmt::If(
                    m_check,
                    vec![JsStmt::Return(result)],
                    None,
                ));
            } else {
                // Single constructor: no instanceof needed
                body.push(JsStmt::Return(result));
            }
        }
    }

    // Fallback: throw error for sum types
    if is_sum {
        body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    let map_fn = JsExpr::Function(
        None,
        vec![f],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![m],
            body,
        ))],
    );

    vec![("map".to_string(), map_fn)]
}

#[derive(Debug, Clone)]
enum FunctorFieldKind {
    /// The field is the type variable directly (a) → apply f
    Direct,
    /// The field does not involve the type var → pass through unchanged
    Passthrough,
    /// Map through a known functor: Array, Tuple, etc. Inner is how to map the arg.
    /// Symbol is the type constructor name (e.g. "Array")
    KnownFunctor(Symbol, Box<FunctorFieldKind>),
    /// Map through the parametric functor variable (f a). Inner is how to map the arg.
    ParamFunctor(Box<FunctorFieldKind>),
    /// Map through a function type (a -> b). Inner is how to map the return type.
    FunctionMap(Box<FunctorFieldKind>),
    /// Record with per-field mapping
    Record(Vec<(Symbol, FunctorFieldKind)>),
}

/// Categorize a constructor field for Functor deriving.
/// `ty` is the field type, `last_tv` is the last type variable (the one being mapped),
/// `param_tv` is the second-to-last type variable (the parametric functor, e.g. `f`),
/// `parent_type` is the type being derived for.
fn categorize_functor_field(
    ty: &crate::typechecker::types::Type,
    last_tv: Option<Symbol>,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
) -> FunctorFieldKind {
    use crate::typechecker::types::Type;

    let last_tv = match last_tv {
        Some(v) => v,
        None => return FunctorFieldKind::Passthrough,
    };

    if !type_contains_var(ty, last_tv) {
        return FunctorFieldKind::Passthrough;
    }

    match ty {
        Type::Var(v) if *v == last_tv => FunctorFieldKind::Direct,

        Type::Fun(_arg_ty, ret_ty) => {
            // a -> b: map over the return type using functorFn composition
            let inner = categorize_functor_field(ret_ty, Some(last_tv), param_tv, parent_type);
            FunctorFieldKind::FunctionMap(Box::new(inner))
        }

        Type::Forall(_, body) => {
            // forall t. constraint => body desugars to function params at runtime
            // Each forall/constraint adds a function layer
            categorize_forall_field(body, last_tv, param_tv, parent_type)
        }

        Type::Record(fields, _tail) => {
            let mut field_kinds = Vec::new();
            for (name, field_ty) in fields {
                let kind = categorize_functor_field(field_ty, Some(last_tv), param_tv, parent_type);
                field_kinds.push((*name, kind));
            }
            FunctorFieldKind::Record(field_kinds)
        }

        Type::App(head, arg) => {
            categorize_app_field(head, arg, last_tv, param_tv, parent_type)
        }

        _ => FunctorFieldKind::Direct,
    }
}

/// Handle forall types: each forall variable (and constraint dict) becomes a function parameter
fn categorize_forall_field(
    ty: &crate::typechecker::types::Type,
    last_tv: Symbol,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
) -> FunctorFieldKind {
    use crate::typechecker::types::Type;
    match ty {
        Type::Fun(_arg, ret) => {
            // constraint dict or forall var becomes a function param
            let inner = categorize_forall_field(ret, last_tv, param_tv, parent_type);
            FunctorFieldKind::FunctionMap(Box::new(inner))
        }
        Type::Forall(_, body) => {
            categorize_forall_field(body, last_tv, param_tv, parent_type)
        }
        _ => categorize_functor_field(ty, Some(last_tv), param_tv, parent_type),
    }
}

/// Handle App types: extract the head constructor and determine mapping strategy
fn categorize_app_field(
    head: &crate::typechecker::types::Type,
    arg: &crate::typechecker::types::Type,
    last_tv: Symbol,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
) -> FunctorFieldKind {
    use crate::typechecker::types::Type;

    // Get the innermost argument's kind (how to map it)
    let inner = categorize_functor_field(arg, Some(last_tv), param_tv, parent_type);

    match head {
        // Simple: Con arg (e.g. Array a, Tuple a)
        Type::Con(qi) => {
            FunctorFieldKind::KnownFunctor(qi.name, Box::new(inner))
        }
        // Parametric: Var(f) arg (e.g. f a)
        Type::Var(v) if param_tv == Some(*v) => {
            FunctorFieldKind::ParamFunctor(Box::new(inner))
        }
        // Nested App: e.g. App(App(Con(Tuple), Int), arg) — peel off to get head
        Type::App(inner_head, _inner_arg) => {
            // Extract the outermost type constructor
            if let Some(head_con) = extract_app_head(head) {
                FunctorFieldKind::KnownFunctor(head_con, Box::new(inner))
            } else {
                // Unknown nested app — try parametric
                FunctorFieldKind::Direct
            }
        }
        _ => FunctorFieldKind::Direct,
    }
}

/// Extract the head type constructor name from a (possibly nested) App chain.
fn extract_app_head(ty: &crate::typechecker::types::Type) -> Option<Symbol> {
    use crate::typechecker::types::Type;
    match ty {
        Type::Con(qi) => Some(qi.name),
        Type::App(head, _) => extract_app_head(head),
        _ => None,
    }
}

fn type_contains_var(ty: &crate::typechecker::types::Type, var: Symbol) -> bool {
    use crate::typechecker::types::Type;
    match ty {
        Type::Var(v) => *v == var,
        Type::App(h, arg) => type_contains_var(h, var) || type_contains_var(arg, var),
        Type::Fun(a, b) => type_contains_var(a, var) || type_contains_var(b, var),
        Type::Forall(_, body) => type_contains_var(body, var),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_contains_var(t, var))
                || tail.as_ref().map_or(false, |t| type_contains_var(t, var))
        }
        _ => false,
    }
}

/// Resolve Data.Functor.map reference
fn resolve_functor_map_ref(ctx: &CodegenCtx) -> JsExpr {
    let map_sym = interner::intern("map");
    let map_qi = QualifiedIdent { module: None, name: map_sym };
    gen_qualified_ref_raw(ctx, &map_qi)
}

/// Resolve the functor-like mapping for a known type constructor.
/// Returns (map_fn_expr, instance_expr) where map_fn_expr is the map/rmap function
/// and instance_expr is the dictionary to pass.
///
/// Prefers Functor instance (uses Data.Functor.map), falls back to:
/// - Bifunctor (uses Data.Bifunctor.rmap)
/// - Profunctor (uses Data.Profunctor.rmap)
enum FunctorResolution {
    /// Use Data.Functor.map(instance)
    Functor(JsExpr),
    /// Use Data.Bifunctor.rmap(instance) or Data.Profunctor.rmap(instance)
    Rmap(JsExpr),
}

fn resolve_functor_or_rmap(ctx: &CodegenCtx, type_con: Symbol) -> Option<FunctorResolution> {
    let type_str = interner::resolve(type_con).unwrap_or_default();
    let short_name = type_str.rsplit('.').next().unwrap_or(&type_str);

    // Special cases for built-in types
    let functor_instance_name = match short_name {
        "Function" | "Fn" | "->" => "functorFn".to_string(),
        other => format!("functor{other}"),
    };

    // Check if a Functor instance exists in the registry
    let functor_sym = interner::intern("Functor");
    if ctx.instance_registry.contains_key(&(functor_sym, type_con)) {
        let instance_sym = interner::intern(&functor_instance_name);
        let qi = QualifiedIdent { module: None, name: instance_sym };
        return Some(FunctorResolution::Functor(gen_qualified_ref_raw(ctx, &qi)));
    }

    // Check for Bifunctor instance → use rmap
    let bifunctor_sym = interner::intern("Bifunctor");
    if ctx.instance_registry.contains_key(&(bifunctor_sym, type_con)) {
        let instance_name = format!("bifunctor{short_name}");
        let instance_sym = interner::intern(&instance_name);
        let qi = QualifiedIdent { module: None, name: instance_sym };
        return Some(FunctorResolution::Rmap(gen_qualified_ref_raw(ctx, &qi)));
    }

    // Check for Profunctor instance → use rmap
    let profunctor_sym = interner::intern("Profunctor");
    if ctx.instance_registry.contains_key(&(profunctor_sym, type_con)) {
        let instance_name = format!("profunctor{short_name}");
        let instance_sym = interner::intern(&instance_name);
        let qi = QualifiedIdent { module: None, name: instance_sym };
        return Some(FunctorResolution::Rmap(gen_qualified_ref_raw(ctx, &qi)));
    }

    // Fallback: assume Functor instance exists (for built-in types, imports, etc.)
    let instance_sym = interner::intern(&functor_instance_name);
    let qi = QualifiedIdent { module: None, name: instance_sym };
    Some(FunctorResolution::Functor(gen_qualified_ref_raw(ctx, &qi)))
}

/// Resolve the `rmap` reference for Bifunctor or Profunctor, depending on which
/// class has an instance for the given type constructor.
fn resolve_rmap_ref(ctx: &CodegenCtx, type_con: Symbol) -> JsExpr {
    let bifunctor_sym = interner::intern("Bifunctor");
    if ctx.instance_registry.contains_key(&(bifunctor_sym, type_con)) {
        // Data_Bifunctor.rmap — try name_source first, else use ModuleAccessor
        let rmap_sym = interner::intern("rmap");
        if let Some(parts) = ctx.name_source.get(&rmap_sym) {
            let js_mod = ctx.import_map.get(parts).cloned()
                .unwrap_or_else(|| module_name_to_js(parts));
            JsExpr::ModuleAccessor(js_mod, "rmap".to_string())
        } else {
            JsExpr::ModuleAccessor("Data_Bifunctor".to_string(), "rmap".to_string())
        }
    } else {
        // Data_Profunctor.rmap
        let rmap_sym = interner::intern("rmap");
        if let Some(parts) = ctx.name_source.get(&rmap_sym) {
            let js_mod = ctx.import_map.get(parts).cloned()
                .unwrap_or_else(|| module_name_to_js(parts));
            JsExpr::ModuleAccessor(js_mod, "rmap".to_string())
        } else {
            JsExpr::ModuleAccessor("Data_Profunctor".to_string(), "rmap".to_string())
        }
    }
}

/// Generate the map expression for a field based on its FunctorFieldKind.
/// `f_var` is the name of the mapping function parameter.
/// `field_expr` is the expression accessing the field (e.g. m.value0).
/// `map_param_expr` is the expression for the parametric functor dict (e.g. dictFunctor), if any.
fn gen_functor_map_field(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    f_var: &str,
    field_expr: JsExpr,
    map_param_expr: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct => {
            // f(field)
            JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_expr])
        }
        FunctorFieldKind::Passthrough => {
            field_expr
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            // map(functorX)(inner_fn)(field) or rmap(bifunctorX)(inner_fn)(field)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            match resolve_functor_or_rmap(ctx, *con) {
                Some(FunctorResolution::Functor(instance)) => {
                    // Data_Functor.map(functorX)(inner_fn)(field)
                    let map_ref = resolve_functor_map_ref(ctx);
                    JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(map_ref),
                                vec![instance],
                            )),
                            vec![inner_fn],
                        )),
                        vec![field_expr],
                    )
                }
                Some(FunctorResolution::Rmap(instance)) => {
                    // rmap(bifunctorX)(inner_fn)(field) or rmap(profunctorX)(inner_fn)(field)
                    let rmap_ref = resolve_rmap_ref(ctx, *con);
                    JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(rmap_ref),
                                vec![instance],
                            )),
                            vec![inner_fn],
                        )),
                        vec![field_expr],
                    )
                }
                None => {
                    // Fallback: just apply f
                    JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_expr])
                }
            }
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            // map(dictFunctor)(inner_fn)(field)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            if let Some(param) = map_param_expr {
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(map_ref),
                            vec![param.clone()],
                        )),
                        vec![inner_fn],
                    )),
                    vec![field_expr],
                )
            } else {
                // No parametric functor available — shouldn't happen, fall back
                JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_expr])
            }
        }
        FunctorFieldKind::FunctionMap(inner) => {
            // map(functorFn)(inner_fn)(field) — function composition
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            let fn_sym = interner::intern("functorFn");
            let fn_qi = QualifiedIdent { module: None, name: fn_sym };
            let fn_instance = gen_qualified_ref_raw(ctx, &fn_qi);
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(map_ref),
                        vec![fn_instance],
                    )),
                    vec![inner_fn],
                )),
                vec![field_expr],
            )
        }
        FunctorFieldKind::Record(fields) => {
            // Build a record literal with per-field mapping
            // Passthrough fields first, then mapped fields (sorted alphabetically)
            let mut obj_fields = Vec::new();
            for (name, field_kind) in fields {
                let name_str = interner::resolve(*name).unwrap_or_default().to_string();
                let field_access = JsExpr::Indexer(
                    Box::new(field_expr.clone()),
                    Box::new(JsExpr::StringLit(name_str.clone())),
                );
                let mapped = gen_functor_map_field(ctx, field_kind, f_var, field_access, map_param_expr);
                obj_fields.push((name_str, mapped));
            }
            // Sort: passthrough fields first, then mapped fields, both alphabetically
            obj_fields.sort_by(|a, b| {
                let a_is_pass = matches!(fields.iter().find(|(n, _)| interner::resolve(*n).unwrap_or_default() == a.0).map(|(_, k)| k), Some(FunctorFieldKind::Passthrough));
                let b_is_pass = matches!(fields.iter().find(|(n, _)| interner::resolve(*n).unwrap_or_default() == b.0).map(|(_, k)| k), Some(FunctorFieldKind::Passthrough));
                match (a_is_pass, b_is_pass) {
                    (true, false) => std::cmp::Ordering::Less,
                    (false, true) => std::cmp::Ordering::Greater,
                    _ => a.0.cmp(&b.0),
                }
            });
            JsExpr::ObjectLit(obj_fields.into_iter().map(|(n, e)| (n, e)).collect())
        }
    }
}

/// Generate a mapping function expression for use as an argument to map.
/// For Direct, this is just `f`. For nested kinds, this wraps in another function.
fn gen_functor_map_fn(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    f_var: &str,
    map_param_expr: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct => {
            // Just f
            JsExpr::Var(f_var.to_string())
        }
        FunctorFieldKind::Passthrough => {
            // Identity — shouldn't normally be called for passthrough
            JsExpr::Var(f_var.to_string())
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            // map(functorX)(inner_fn) or rmap(bifunctorX)(inner_fn)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            match resolve_functor_or_rmap(ctx, *con) {
                Some(FunctorResolution::Functor(instance)) => {
                    let map_ref = resolve_functor_map_ref(ctx);
                    JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(map_ref),
                            vec![instance],
                        )),
                        vec![inner_fn],
                    )
                }
                Some(FunctorResolution::Rmap(instance)) => {
                    let rmap_ref = resolve_rmap_ref(ctx, *con);
                    JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(rmap_ref),
                            vec![instance],
                        )),
                        vec![inner_fn],
                    )
                }
                None => {
                    inner_fn
                }
            }
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            // map(dictFunctor)(inner_fn)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            if let Some(param) = map_param_expr {
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(map_ref),
                        vec![param.clone()],
                    )),
                    vec![inner_fn],
                )
            } else {
                inner_fn
            }
        }
        FunctorFieldKind::FunctionMap(inner) => {
            // map(functorFn)(inner_fn)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            let fn_sym = interner::intern("functorFn");
            let fn_qi = QualifiedIdent { module: None, name: fn_sym };
            let fn_instance = gen_qualified_ref_raw(ctx, &fn_qi);
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(map_ref),
                    vec![fn_instance],
                )),
                vec![inner_fn],
            )
        }
        FunctorFieldKind::Record(fields) => {
            // function(v1) { return { field: mapped, ... }; }
            let v_param = "v1".to_string();
            let v_expr = JsExpr::Var(v_param.clone());
            let mapped = gen_functor_map_field(ctx, &FunctorFieldKind::Record(fields.clone()), f_var, v_expr, map_param_expr);
            JsExpr::Function(None, vec![v_param], vec![JsStmt::Return(mapped)])
        }
    }
}


/// Field classification for Traversable deriving
#[derive(Debug, Clone)]
enum TraversableFieldKind {
    /// The type variable directly (a) - apply f
    Direct,
    /// Known traversable like Array - use traverse2 (Array's traverse)
    KnownTraversable,
    /// The type parameter f - use traverse3 (param's traverse)  
    ParamTraversable,
    /// Concrete type not involving type var - pass through
    Passthrough,
    /// Record type with traversable fields
    Record(Vec<(String, TraversableFieldKind)>),
    /// Nested: outer traversable wrapping inner (e.g., f (f a)) - compose traversals
    Nested(Box<TraversableFieldKind>, Box<TraversableFieldKind>),
}

/// Categorize a field for Traversable deriving.
/// `last_tv` is the last type variable (a), `param_tv` is the functor parameter (f).
fn categorize_traversable_field(
    ty: &crate::typechecker::types::Type,
    last_tv: Option<Symbol>,
    parent_type: Symbol,
    param_tv: Option<Symbol>,
) -> TraversableFieldKind {
    use crate::typechecker::types::Type;
    let last = match last_tv {
        Some(v) => v,
        None => return TraversableFieldKind::Passthrough,
    };
    match ty {
        Type::Var(v) if *v == last => TraversableFieldKind::Direct,
        Type::Var(_) => TraversableFieldKind::Passthrough,
        Type::App(head, arg) => {
            let head_con = extract_app_head(head);
            let inner_kind = categorize_traversable_field(arg, last_tv, parent_type, param_tv);
            
            match head_con {
                Some(con) => {
                    let is_param = match head.as_ref() {
                        Type::Var(v) => param_tv == Some(*v),
                        _ => false,
                    };
                    let array_sym = interner::intern("Array");
                    let is_array = con == array_sym;
                    
                    if is_param {
                        match inner_kind {
                            TraversableFieldKind::Passthrough => TraversableFieldKind::Passthrough,
                            TraversableFieldKind::Direct => TraversableFieldKind::ParamTraversable,
                            other => TraversableFieldKind::Nested(
                                Box::new(TraversableFieldKind::ParamTraversable),
                                Box::new(other),
                            ),
                        }
                    } else if is_array {
                        match inner_kind {
                            TraversableFieldKind::Passthrough => TraversableFieldKind::Passthrough,
                            TraversableFieldKind::Direct => TraversableFieldKind::KnownTraversable,
                            other => TraversableFieldKind::Nested(
                                Box::new(TraversableFieldKind::KnownTraversable),
                                Box::new(other),
                            ),
                        }
                    } else {
                        if type_contains_var(ty, last) {
                            TraversableFieldKind::Direct
                        } else {
                            TraversableFieldKind::Passthrough
                        }
                    }
                }
                None => {
                    let is_param = match head.as_ref() {
                        Type::Var(v) => param_tv == Some(*v),
                        _ => false,
                    };
                    if is_param {
                        match inner_kind {
                            TraversableFieldKind::Passthrough => TraversableFieldKind::Passthrough,
                            TraversableFieldKind::Direct => TraversableFieldKind::ParamTraversable,
                            other => TraversableFieldKind::Nested(
                                Box::new(TraversableFieldKind::ParamTraversable),
                                Box::new(other),
                            ),
                        }
                    } else if type_contains_var(ty, last) {
                        TraversableFieldKind::Direct
                    } else {
                        TraversableFieldKind::Passthrough
                    }
                }
            }
        }
        Type::Record(fields, _tail) => {
            let mut rec_fields = Vec::new();
            let mut has_effectful = false;
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(*name).unwrap_or_default());
            for (name, fty) in &sorted_fields {
                let name_str = interner::resolve(*name).unwrap_or_default();
                let kind = categorize_traversable_field(fty, last_tv, parent_type, param_tv);
                if !matches!(kind, TraversableFieldKind::Passthrough) {
                    has_effectful = true;
                }
                rec_fields.push((name_str, kind));
            }
            if has_effectful {
                TraversableFieldKind::Record(rec_fields)
            } else {
                TraversableFieldKind::Passthrough
            }
        }
        _ => {
            if type_contains_var(ty, last) {
                TraversableFieldKind::Direct
            } else {
                TraversableFieldKind::Passthrough
            }
        }
    }
}

/// Count the number of effectful (non-passthrough) fields in a TraversableFieldKind
fn count_effectful(kind: &TraversableFieldKind) -> usize {
    match kind {
        TraversableFieldKind::Passthrough => 0,
        TraversableFieldKind::Direct | TraversableFieldKind::KnownTraversable | TraversableFieldKind::ParamTraversable => 1,
        TraversableFieldKind::Record(fields) => {
            fields.iter().map(|(_, k)| count_effectful(k)).sum()
        }
        TraversableFieldKind::Nested(_, inner) => count_effectful(inner),
    }
}

/// Generate the traverse expression for a single field
fn gen_traverse_field_expr(
    kind: &TraversableFieldKind,
    field_access: JsExpr,
    f_var: &str,
    var_counter: &mut usize,
    apply_var: &str,
    map1_var: &str,
    _pure1_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
) -> (JsExpr, Vec<JsExpr>) {
    match kind {
        TraversableFieldKind::Direct => {
            (JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_access]), vec![])
        }
        TraversableFieldKind::KnownTraversable => {
            (JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse2_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ), vec![])
        }
        TraversableFieldKind::ParamTraversable => {
            (JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse3_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ), vec![])
        }
        TraversableFieldKind::Passthrough => {
            (field_access, vec![])
        }
        TraversableFieldKind::Record(_fields) => {
            // Records in top-level fields are handled by the caller
            (field_access, vec![])
        }
        TraversableFieldKind::Nested(outer, inner) => {
            let inner_fn = gen_nested_traverse_fn(inner, f_var, var_counter, apply_var, map1_var, _pure1_var, traverse2_var, traverse3_var);
            let outer_traverse = match outer.as_ref() {
                TraversableFieldKind::KnownTraversable => JsExpr::Var(traverse2_var.to_string()),
                TraversableFieldKind::ParamTraversable => JsExpr::Var(traverse3_var.to_string()),
                _ => JsExpr::Var(traverse3_var.to_string()),
            };
            (JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(outer_traverse),
                    vec![inner_fn],
                )),
                vec![field_access],
            ), vec![])
        }
    }
}

/// Generate a traverse function for nested types
fn gen_nested_traverse_fn(
    kind: &TraversableFieldKind,
    f_var: &str,
    var_counter: &mut usize,
    apply_var: &str,
    map1_var: &str,
    pure1_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
) -> JsExpr {
    match kind {
        TraversableFieldKind::Direct => {
            JsExpr::Var(f_var.to_string())
        }
        TraversableFieldKind::KnownTraversable => {
            JsExpr::App(
                Box::new(JsExpr::Var(traverse2_var.to_string())),
                vec![JsExpr::Var(f_var.to_string())],
            )
        }
        TraversableFieldKind::ParamTraversable => {
            JsExpr::App(
                Box::new(JsExpr::Var(traverse3_var.to_string())),
                vec![JsExpr::Var(f_var.to_string())],
            )
        }
        TraversableFieldKind::Record(fields) => {
            let param_name = format!("v{}", *var_counter);
            *var_counter += 1;
            
            // Collect effectful fields with their access expressions
            let mut effects: Vec<JsExpr> = Vec::new();
            let mut param_names: Vec<String> = Vec::new();
            let param_access = JsExpr::Var(param_name.clone());
            
            collect_effects_for_record_fields(fields, &param_access, f_var, traverse2_var, traverse3_var, &mut effects);
            for _ in 0..effects.len() {
                param_names.push(format!("v{}", *var_counter));
                *var_counter += 1;
            }
            
            // Build the record result using params
            let record_obj = build_nested_record_result(fields, &param_access, &param_names, &mut 0);
            
            // Build nested lambda
            let mut lambda: JsExpr = record_obj;
            for i in (0..param_names.len()).rev() {
                lambda = JsExpr::Function(
                    None,
                    vec![param_names[i].clone()],
                    vec![JsStmt::Return(lambda)],
                );
            }
            
            // Build applicative chain
            let result = build_applicative_chain(&lambda, &effects, apply_var, map1_var);
            
            JsExpr::Function(
                None,
                vec![param_name],
                vec![JsStmt::Return(result)],
            )
        }
        TraversableFieldKind::Nested(outer, inner) => {
            let inner_fn = gen_nested_traverse_fn(inner, f_var, var_counter, apply_var, map1_var, pure1_var, traverse2_var, traverse3_var);
            let outer_traverse = match outer.as_ref() {
                TraversableFieldKind::KnownTraversable => JsExpr::Var(traverse2_var.to_string()),
                TraversableFieldKind::ParamTraversable => JsExpr::Var(traverse3_var.to_string()),
                _ => JsExpr::Var(traverse3_var.to_string()),
            };
            JsExpr::App(
                Box::new(outer_traverse),
                vec![inner_fn],
            )
        }
        TraversableFieldKind::Passthrough => {
            JsExpr::Var(f_var.to_string())
        }
    }
}

/// Collect effects from record fields (recursing into nested records)
fn collect_effects_for_record_fields(
    fields: &[(String, TraversableFieldKind)],
    record_access: &JsExpr,
    f_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
    out: &mut Vec<JsExpr>,
) {
    for (name, kind) in fields {
        let field_acc = JsExpr::Indexer(
            Box::new(record_access.clone()),
            Box::new(JsExpr::StringLit(name.clone())),
        );
        match kind {
            TraversableFieldKind::Passthrough => {}
            TraversableFieldKind::Direct => {
                out.push(JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_acc]));
            }
            TraversableFieldKind::KnownTraversable => {
                out.push(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::Var(traverse2_var.to_string())),
                        vec![JsExpr::Var(f_var.to_string())],
                    )),
                    vec![field_acc],
                ));
            }
            TraversableFieldKind::ParamTraversable => {
                out.push(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::Var(traverse3_var.to_string())),
                        vec![JsExpr::Var(f_var.to_string())],
                    )),
                    vec![field_acc],
                ));
            }
            TraversableFieldKind::Record(sub_fields) => {
                collect_effects_for_record_fields(sub_fields, &field_acc, f_var, traverse2_var, traverse3_var, out);
            }
            TraversableFieldKind::Nested(_, _) => {
                out.push(field_acc);
            }
        }
    }
}

/// Build nested record result using param vars
fn build_nested_record_result(
    fields: &[(String, TraversableFieldKind)],
    record_access: &JsExpr,
    param_names: &[String],
    param_idx: &mut usize,
) -> JsExpr {
    let mut obj_fields = Vec::new();
    for (name, kind) in fields {
        match kind {
            TraversableFieldKind::Passthrough => {
                obj_fields.push((name.clone(), JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                )));
            }
            TraversableFieldKind::Record(sub_fields) => {
                let sub_access = JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                );
                let sub_obj = build_nested_record_result(sub_fields, &sub_access, param_names, param_idx);
                obj_fields.push((name.clone(), sub_obj));
            }
            _ => {
                if *param_idx < param_names.len() {
                    obj_fields.push((name.clone(), JsExpr::Var(param_names[*param_idx].clone())));
                    *param_idx += 1;
                }
            }
        }
    }
    JsExpr::ObjectLit(obj_fields)
}

/// Build applicative chain: apply(apply(map1(lambda)(eff0))(eff1))...(effN-1)
fn build_applicative_chain(
    lambda: &JsExpr,
    effects: &[JsExpr],
    apply_var: &str,
    map1_var: &str,
) -> JsExpr {
    if effects.is_empty() {
        return lambda.clone();
    }
    // Start: map1(lambda)(effects[0])
    let mut result = JsExpr::App(
        Box::new(JsExpr::App(
            Box::new(JsExpr::Var(map1_var.to_string())),
            vec![lambda.clone()],
        )),
        vec![effects[0].clone()],
    );
    // Chain: apply(result)(effects[i])
    for eff in &effects[1..] {
        result = JsExpr::App(
            Box::new(JsExpr::App(
                Box::new(JsExpr::Var(apply_var.to_string())),
                vec![result],
            )),
            vec![eff.clone()],
        );
    }
    result
}

/// Collect all effectful expressions for a field (flattening records)
fn collect_effects_for_field(
    kind: &TraversableFieldKind,
    field_access: JsExpr,
    f_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
    out: &mut Vec<JsExpr>,
) {
    match kind {
        TraversableFieldKind::Passthrough => {}
        TraversableFieldKind::Direct => {
            out.push(JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_access]));
        }
        TraversableFieldKind::KnownTraversable => {
            out.push(JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse2_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ));
        }
        TraversableFieldKind::ParamTraversable => {
            out.push(JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse3_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ));
        }
        TraversableFieldKind::Record(fields) => {
            for (name, sub_kind) in fields {
                let sub_access = JsExpr::Indexer(
                    Box::new(field_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                );
                collect_effects_for_field(sub_kind, sub_access, f_var, traverse2_var, traverse3_var, out);
            }
        }
        TraversableFieldKind::Nested(_, _) => {
            out.push(field_access);
        }
    }
}

/// Build the constructor result expression using param variables for effectful fields
fn build_ctor_result_expr(
    ctor_name: &str,
    field_kinds: &[TraversableFieldKind],
    m_var: &str,
    param_names: &[String],
) -> JsExpr {
    let mut args = Vec::new();
    let mut param_idx = 0;
    
    for (i, kind) in field_kinds.iter().enumerate() {
        let field_access = JsExpr::Indexer(
            Box::new(JsExpr::Var(m_var.to_string())),
            Box::new(JsExpr::StringLit(format!("value{i}"))),
        );
        match kind {
            TraversableFieldKind::Passthrough => {
                args.push(field_access);
            }
            TraversableFieldKind::Direct | TraversableFieldKind::KnownTraversable | TraversableFieldKind::ParamTraversable => {
                if param_idx < param_names.len() {
                    args.push(JsExpr::Var(param_names[param_idx].clone()));
                    param_idx += 1;
                }
            }
            TraversableFieldKind::Record(fields) => {
                let record_obj = build_ctor_record_result(fields, &field_access, param_names, &mut param_idx);
                args.push(record_obj);
            }
            TraversableFieldKind::Nested(_, _) => {
                if param_idx < param_names.len() {
                    args.push(JsExpr::Var(param_names[param_idx].clone()));
                    param_idx += 1;
                }
            }
        }
    }
    
    JsExpr::New(Box::new(JsExpr::Var(ctor_name.to_string())), args)
}

/// Build record result for a constructor field
fn build_ctor_record_result(
    fields: &[(String, TraversableFieldKind)],
    record_access: &JsExpr,
    param_names: &[String],
    param_idx: &mut usize,
) -> JsExpr {
    let mut obj_fields = Vec::new();
    for (name, kind) in fields {
        match kind {
            TraversableFieldKind::Passthrough => {
                obj_fields.push((name.clone(), JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                )));
            }
            TraversableFieldKind::Direct | TraversableFieldKind::KnownTraversable | TraversableFieldKind::ParamTraversable => {
                if *param_idx < param_names.len() {
                    obj_fields.push((name.clone(), JsExpr::Var(param_names[*param_idx].clone())));
                    *param_idx += 1;
                }
            }
            TraversableFieldKind::Record(sub_fields) => {
                let sub_access = JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                );
                let sub_obj = build_ctor_record_result(sub_fields, &sub_access, param_names, param_idx);
                obj_fields.push((name.clone(), sub_obj));
            }
            TraversableFieldKind::Nested(_, _) => {
                if *param_idx < param_names.len() {
                    obj_fields.push((name.clone(), JsExpr::Var(param_names[*param_idx].clone())));
                    *param_idx += 1;
                }
            }
        }
    }
    JsExpr::ObjectLit(obj_fields)
}

/// Generate methods for derive Traversable.
fn gen_derive_traversable_methods(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    instance_name: &str,
    dict_params: &[String],
) -> Vec<(String, JsExpr)> {
    let f_var = "f".to_string();
    let m_var = "m".to_string();
    let pure1 = "pure1".to_string();
    let apply_var = "apply".to_string();
    let map1 = "map1".to_string();
    let traverse2 = "traverse2".to_string();
    let traverse3 = "traverse3".to_string();

    let first_ctor = ctors_with_types.first();
    let (last_tv, param_tv, parent_type) = first_ctor
        .and_then(|(name, _, _)| {
            let ctor_sym = interner::intern(name);
            let ctor_qi = unqualified(ctor_sym);
            ctx.ctor_details.get(&ctor_qi).map(|(parent, type_vars, _)| {
                let last = type_vars.last().map(|qi| qi.name);
                let param = if type_vars.len() >= 2 {
                    Some(type_vars[type_vars.len() - 2].name)
                } else {
                    None
                };
                (last, param, parent.name)
            })
        })
        .unwrap_or((None, None, interner::intern("Unknown")));

    let is_sum = ctors_with_types.len() > 1 || (ctors_with_types.len() == 1 && ctors_with_types[0].1 == 0);

    let mut body = Vec::new();

    for (ctor_name, field_count, field_types) in ctors_with_types {
        if *field_count == 0 {
            let m_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(m_var.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
            );
            let result = JsExpr::App(
                Box::new(JsExpr::Var(pure1.clone())),
                vec![JsExpr::Indexer(
                    Box::new(JsExpr::Var(ctor_name.clone())),
                    Box::new(JsExpr::StringLit("value".to_string())),
                )],
            );
            body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
        } else {
            let field_kinds: Vec<TraversableFieldKind> = field_types.iter()
                .map(|ft| categorize_traversable_field(ft, last_tv, parent_type, param_tv))
                .collect();

            let total_effectful: usize = field_kinds.iter().map(|k| count_effectful(k)).sum();

            if total_effectful == 0 {
                let m_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(m_var.clone())),
                    Box::new(JsExpr::Var(ctor_name.clone())),
                );
                let mut args = Vec::new();
                for i in 0..*field_count {
                    args.push(JsExpr::Indexer(
                        Box::new(JsExpr::Var(m_var.clone())),
                        Box::new(JsExpr::StringLit(format!("value{i}"))),
                    ));
                }
                let result = JsExpr::App(
                    Box::new(JsExpr::Var(pure1.clone())),
                    vec![JsExpr::New(Box::new(JsExpr::Var(ctor_name.clone())), args)],
                );
                body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
            } else {
                let m_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(m_var.clone())),
                    Box::new(JsExpr::Var(ctor_name.clone())),
                );

                let mut var_counter = *field_count;

                // Check for single-field nested type (like M7)
                if *field_count == 1 && matches!(&field_kinds[0], TraversableFieldKind::Nested(_, _)) {
                    let field_access = JsExpr::Indexer(
                        Box::new(JsExpr::Var(m_var.clone())),
                        Box::new(JsExpr::StringLit("value0".to_string())),
                    );
                    var_counter = 1;
                    let (eff_expr, _) = gen_traverse_field_expr(
                        &field_kinds[0], field_access, &f_var, &mut var_counter,
                        &apply_var, &map1, &pure1, &traverse2, &traverse3,
                    );
                    let ctor_lambda = JsExpr::Function(
                        None,
                        vec!["v1".to_string()],
                        vec![JsStmt::Return(JsExpr::New(
                            Box::new(JsExpr::Var(ctor_name.clone())),
                            vec![JsExpr::Var("v1".to_string())],
                        ))],
                    );
                    let result = JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(JsExpr::Var(map1.clone())),
                            vec![ctor_lambda],
                        )),
                        vec![eff_expr],
                    );
                    body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
                    continue;
                }

                let mut all_effects: Vec<JsExpr> = Vec::new();
                let mut param_names: Vec<String> = Vec::new();
                
                for (i, kind) in field_kinds.iter().enumerate() {
                    let field_access = JsExpr::Indexer(
                        Box::new(JsExpr::Var(m_var.clone())),
                        Box::new(JsExpr::StringLit(format!("value{i}"))),
                    );
                    collect_effects_for_field(kind, field_access, &f_var, &traverse2, &traverse3, &mut all_effects);
                }
                
                for _ in 0..all_effects.len() {
                    param_names.push(format!("v{var_counter}"));
                    var_counter += 1;
                }

                let ctor_result = build_ctor_result_expr(
                    ctor_name, &field_kinds, &m_var, &param_names,
                );
                
                let mut lambda: JsExpr = ctor_result;
                for i in (0..param_names.len()).rev() {
                    lambda = JsExpr::Function(
                        None,
                        vec![param_names[i].clone()],
                        vec![JsStmt::Return(lambda)],
                    );
                }

                let result = build_applicative_chain(&lambda, &all_effects, &apply_var, &map1);
                
                body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
            }
        }
    }

    if is_sum {
        body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    // Build traverse method body with var decls
    let mut traverse_body = Vec::new();
    let pure_ref = {
        let pure_sym = interner::intern("pure");
        let pure_qi = QualifiedIdent { module: None, name: pure_sym };
        gen_qualified_ref_raw(ctx, &pure_qi)
    };
    traverse_body.push(JsStmt::VarDecl(pure1.clone(), Some(JsExpr::App(
        Box::new(pure_ref),
        vec![JsExpr::Var("dictApplicative".to_string())],
    ))));
    traverse_body.push(JsStmt::VarDecl("Apply0".to_string(), Some(JsExpr::App(
        Box::new(JsExpr::Indexer(
            Box::new(JsExpr::Var("dictApplicative".to_string())),
            Box::new(JsExpr::StringLit("Apply0".to_string())),
        )),
        vec![],
    ))));
    let apply_ref = {
        let apply_sym = interner::intern("apply");
        let apply_qi = QualifiedIdent { module: None, name: apply_sym };
        gen_qualified_ref_raw(ctx, &apply_qi)
    };
    traverse_body.push(JsStmt::VarDecl(apply_var.clone(), Some(JsExpr::App(
        Box::new(apply_ref),
        vec![JsExpr::Var("Apply0".to_string())],
    ))));
    let map_ref = resolve_functor_map_ref(ctx);
    traverse_body.push(JsStmt::VarDecl(map1.clone(), Some(JsExpr::App(
        Box::new(map_ref),
        vec![JsExpr::App(
            Box::new(JsExpr::Indexer(
                Box::new(JsExpr::Var("Apply0".to_string())),
                Box::new(JsExpr::StringLit("Functor0".to_string())),
            )),
            vec![],
        )],
    ))));
    // traverse2 = Data_Traversable.traverse(Data_Traversable.traversableArray)(dictApplicative)
    // This is the Array traverse, fully applied with the Array traversable dict
    let dt_traverse_ref = {
        let traverse_sym = interner::intern("traverse");
        let dt_module = interner::intern("Data.Traversable");
        let traverse_qi = QualifiedIdent { module: Some(dt_module), name: traverse_sym };
        gen_qualified_ref_raw(ctx, &traverse_qi)
    };
    let traversable_array_ref = {
        let ta_sym = interner::intern("traversableArray");
        let dt_module = interner::intern("Data.Traversable");
        let ta_qi = QualifiedIdent { module: Some(dt_module), name: ta_sym };
        gen_qualified_ref_raw(ctx, &ta_qi)
    };
    traverse_body.push(JsStmt::VarDecl(traverse2.clone(), Some(JsExpr::App(
        Box::new(JsExpr::App(
            Box::new(dt_traverse_ref.clone()),
            vec![traversable_array_ref],
        )),
        vec![JsExpr::Var("dictApplicative".to_string())],
    ))));
    // traverse3 = Data_Traversable.traverse(dictTraversable)(dictApplicative)
    // The hoisting mechanism will extract Data_Traversable.traverse(dictTraversable) as traverse1
    if !dict_params.is_empty() {
        traverse_body.push(JsStmt::VarDecl(traverse3.clone(), Some(JsExpr::App(
            Box::new(JsExpr::App(
                Box::new(dt_traverse_ref),
                vec![JsExpr::Var(dict_params[0].clone())],
            )),
            vec![JsExpr::Var("dictApplicative".to_string())],
        ))));
    }

    traverse_body.push(JsStmt::Return(JsExpr::Function(
        None,
        vec![f_var],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![m_var],
            body,
        ))],
    )));

    let traverse_fn = JsExpr::Function(
        None,
        vec!["dictApplicative".to_string()],
        traverse_body,
    );

    // sequence method
    let data_traversable_traverse = {
        let traverse_sym = interner::intern("traverse");
        let dt_module = interner::intern("Data.Traversable");
        let traverse_qi = QualifiedIdent { module: Some(dt_module), name: traverse_sym };
        gen_qualified_ref_raw(ctx, &traverse_qi)
    };
    let identity_ref = {
        // identity needs to be Control_Category.identity(Control_Category.categoryFn)
        let identity_sym = interner::intern("identity");
        let cc_module = interner::intern("Control.Category");
        let identity_qi = QualifiedIdent { module: Some(cc_module), name: identity_sym };
        let identity_base = gen_qualified_ref_raw(ctx, &identity_qi);
        let category_fn_sym = interner::intern("categoryFn");
        let category_fn_qi = QualifiedIdent { module: Some(cc_module), name: category_fn_sym };
        let category_fn_ref = gen_qualified_ref_raw(ctx, &category_fn_qi);
        JsExpr::App(Box::new(identity_base), vec![category_fn_ref])
    };
    let self_ref = if !dict_params.is_empty() {
        JsExpr::App(
            Box::new(JsExpr::Var(instance_name.to_string())),
            vec![JsExpr::Var(dict_params[0].clone())],
        )
    } else {
        JsExpr::Var(instance_name.to_string())
    };
    let sequence_fn = JsExpr::Function(
        None,
        vec!["dictApplicative".to_string()],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec!["v".to_string()],
            vec![JsStmt::Return(JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(data_traversable_traverse),
                            vec![self_ref],
                        )),
                        vec![JsExpr::Var("dictApplicative".to_string())],
                    )),
                    vec![identity_ref],
                )),
                vec![JsExpr::Var("v".to_string())],
            ))],
        ))],
    );

    vec![
        ("traverse".to_string(), traverse_fn),
        ("sequence".to_string(), sequence_fn),
    ]
}

/// Generate methods for derive Newtype class.
/// The original compiler only emits Coercible0: function() { return undefined; }
fn gen_derive_newtype_class_methods() -> Vec<(String, JsExpr)> {
    vec![]
}

/// Generate `bimap` method for derive Bifunctor.
/// For data types with no constructors, generates a bimap that throws (unreachable).
/// For data types with constructors, generates proper bimap logic.
fn gen_derive_bifunctor_methods(ctx: &CodegenCtx, ctors: &[(String, usize)]) -> Vec<(String, JsExpr)> {
    // For empty types or as a simple default, generate bimap that throws
    let bimap_fn = JsExpr::Function(
        None,
        vec!["f".to_string()],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec!["g".to_string()],
            vec![JsStmt::Return(JsExpr::Function(
                None,
                vec!["m".to_string()],
                vec![JsStmt::Throw(gen_failed_pattern_match(ctx))],
            ))],
        ))],
    );
    vec![("bimap".to_string(), bimap_fn)]
}

/// Generate `dimap` method for derive Profunctor.
/// For data types with no constructors, generates a dimap that throws (unreachable).
/// For data types with constructors, generates proper dimap logic.
fn gen_derive_profunctor_methods(ctx: &CodegenCtx, ctors: &[(String, usize)]) -> Vec<(String, JsExpr)> {
    // For empty types or as a simple default, generate dimap that throws
    let dimap_fn = JsExpr::Function(
        None,
        vec!["f".to_string()],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec!["g".to_string()],
            vec![JsStmt::Return(JsExpr::Function(
                None,
                vec!["m".to_string()],
                vec![JsStmt::Throw(gen_failed_pattern_match(ctx))],
            ))],
        ))],
    );
    vec![("dimap".to_string(), dimap_fn)]
}

/// Generate `to` and `from` methods for derive Generic.
/// These convert between the type and its generic representation.
/// For now, generates identity-like stubs since the Generic rep is typically
/// handled at the type level and the runtime is just constructor tagging.
fn gen_derive_generic_methods(ctx: &CodegenCtx, ctors: &[(String, usize)]) -> Vec<(String, JsExpr)> {
    // Resolve Data.Generic.Rep module reference
    let rep_mod = {
        let rep_parts: Vec<Symbol> = vec![
            interner::intern("Data"),
            interner::intern("Generic"),
            interner::intern("Rep"),
        ];
        ctx.import_map.get(&rep_parts).cloned()
    };

    let rep_ref = |name: &str| -> JsExpr {
        if let Some(ref js_mod) = rep_mod {
            JsExpr::ModuleAccessor(js_mod.clone(), name.to_string())
        } else {
            JsExpr::Var(name.to_string())
        }
    };

    // `to`: convert generic rep → value
    // For a single constructor with no fields: to(x) = Ctor.value
    // For sum types: to(x) = if (x instanceof Inl) ... else if (x instanceof Inr) ...
    let x = "x".to_string();

    // Build `to` function body
    let mut to_body = Vec::new();
    for (i, (ctor_name, field_count)) in ctors.iter().enumerate() {
        let ctor_expr = if *field_count == 0 {
            JsExpr::Indexer(
                Box::new(JsExpr::Var(ctor_name.clone())),
                Box::new(JsExpr::StringLit("value".to_string())),
            )
        } else if *field_count == 1 {
            // Single-arg ctor: the value is stored directly in the sum node's value0
            let inner = gen_generic_unwrap_arg(&rep_ref, &x, i, ctors.len());
            JsExpr::New(
                Box::new(JsExpr::Var(ctor_name.clone())),
                vec![inner],
            )
        } else {
            // Multi-field: unwrap Product chain
            let mut args = Vec::new();
            let inner = gen_generic_unwrap_arg(&rep_ref, &x, i, ctors.len());
            for fi in 0..*field_count {
                let field = gen_generic_product_field(&rep_ref, &inner, fi, *field_count);
                args.push(field);
            }
            JsExpr::New(Box::new(JsExpr::Var(ctor_name.clone())), args)
        };

        if ctors.len() == 1 {
            to_body.push(JsStmt::Return(ctor_expr));
        } else {
            let cond = gen_generic_inl_inr_check(&rep_ref, &x, i, ctors.len());
            to_body.push(JsStmt::If(cond, vec![JsStmt::Return(ctor_expr)], None));
        }
    }
    if ctors.len() > 1 {
        to_body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    let to_fn = JsExpr::Function(None, vec![x.clone()], to_body);

    // Build `from` function body
    let mut from_body = Vec::new();
    for (i, (ctor_name, field_count)) in ctors.iter().enumerate() {
        let wrap_in_sum = |expr: JsExpr| -> JsExpr {
            gen_generic_inl_inr_wrap(&rep_ref, expr, i, ctors.len())
        };

        let inner = if *field_count == 0 {
            wrap_in_sum(JsExpr::Indexer(
                Box::new(rep_ref("NoArguments")),
                Box::new(JsExpr::StringLit("value".to_string())),
            ))
        } else if *field_count == 1 {
            // Single-arg ctor: Argument is a newtype (identity), so just use the value directly
            wrap_in_sum(JsExpr::Indexer(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::StringLit("value0".to_string())),
            ))
        } else {
            // Multi-field: build Product chain
            // Argument is a newtype (identity), so use field values directly
            let mut product = JsExpr::Indexer(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::StringLit(format!("value{}", field_count - 1))),
            );
            for fi in (0..field_count - 1).rev() {
                product = JsExpr::New(
                    Box::new(rep_ref("Product")),
                    vec![
                        JsExpr::Indexer(
                            Box::new(JsExpr::Var(x.clone())),
                            Box::new(JsExpr::StringLit(format!("value{fi}"))),
                        ),
                        product,
                    ],
                );
            }
            wrap_in_sum(product)
        };

        if ctors.len() == 1 {
            from_body.push(JsStmt::Return(inner));
        } else {
            let cond = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
            );
            from_body.push(JsStmt::If(cond, vec![JsStmt::Return(inner)], None));
        }
    }
    if ctors.len() > 1 {
        from_body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    let from_fn = JsExpr::Function(None, vec![x], from_body);

    vec![
        ("to".to_string(), to_fn),
        ("from".to_string(), from_fn),
    ]
}

/// Generate the condition for checking if x is in the Nth position of an Inl/Inr sum tree.
fn gen_generic_inl_inr_check(rep_ref: &dyn Fn(&str) -> JsExpr, x: &str, idx: usize, total: usize) -> JsExpr {
    if total == 1 {
        return JsExpr::BoolLit(true);
    }
    if total == 2 {
        if idx == 0 {
            return JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inl")));
        } else {
            return JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inr")));
        }
    }
    // For 3+ constructors: navigate idx levels deep into the Inr chain.
    // Sum(A, Sum(B, Sum(C, D))):
    //   A (0): x instanceof Inl
    //   B (1): x instanceof Inr && x.value0 instanceof Inl
    //   C (2): x instanceof Inr && x.value0 instanceof Inr && x.value0.value0 instanceof Inl
    //   D (3): x instanceof Inr && x.value0 instanceof Inr && x.value0.value0 instanceof Inr
    if idx == 0 {
        JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inl")))
    } else {
        // Build chain: x instanceof Inr && x.value0 instanceof Inr && ... && x.value0...value0 instanceof Inl/Inr
        let mut expr = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.to_string())),
            Box::new(rep_ref("Inr")),
        );
        // Navigate idx-1 levels of .value0 instanceof Inr
        let mut current = JsExpr::Indexer(
            Box::new(JsExpr::Var(x.to_string())),
            Box::new(JsExpr::StringLit("value0".to_string())),
        );
        for _ in 1..idx {
            let check = JsExpr::InstanceOf(
                Box::new(current.clone()),
                Box::new(rep_ref("Inr")),
            );
            expr = JsExpr::Binary(JsBinaryOp::And, Box::new(expr), Box::new(check));
            current = JsExpr::Indexer(
                Box::new(current),
                Box::new(JsExpr::StringLit("value0".to_string())),
            );
        }
        if idx < total - 1 {
            // Middle constructors: final check is Inl
            let final_check = JsExpr::InstanceOf(
                Box::new(current),
                Box::new(rep_ref("Inl")),
            );
            JsExpr::Binary(JsBinaryOp::And, Box::new(expr), Box::new(final_check))
        } else {
            // Last constructor: no extra check needed — being at this Inr depth is sufficient
            expr
        }
    }
}

/// Unwrap the generic arg from the Inl/Inr sum tree at position idx.
/// For Sum(A, Sum(B, Sum(C, D))):
///   A (0): x.value0          (unwrap Inl)
///   B (1): x.value0.value0   (unwrap Inr, then Inl)
///   C (2): x.value0.value0.value0 (unwrap Inr, Inr, then Inl)
///   D (3): x.value0.value0.value0 (unwrap Inr, Inr, then Inr — but last Inr has value0 for its content)
fn gen_generic_unwrap_arg(rep_ref: &dyn Fn(&str) -> JsExpr, x: &str, idx: usize, total: usize) -> JsExpr {
    let _ = rep_ref;
    if total == 1 {
        return JsExpr::Var(x.to_string());
    }
    // For Sum(A, Sum(B, Sum(C, D))):
    //   A (idx=0): x.value0              (1 level)
    //   B (idx=1): x.value0.value0       (2 levels)
    //   C (idx=2): x.value0.value0.value0 (3 levels)
    //   D (idx=3): x.value0.value0.value0 (3 levels — same as C, last shares depth)
    // Non-last: depth = idx + 1. Last: depth = idx.
    let depth = if idx < total - 1 { idx + 1 } else { idx };
    let mut expr = JsExpr::Var(x.to_string());
    for _ in 0..depth {
        expr = JsExpr::Indexer(
            Box::new(expr),
            Box::new(JsExpr::StringLit("value0".to_string())),
        );
    }
    expr
}

/// Extract a field from a Product chain at position fi.
fn gen_generic_product_field(_rep_ref: &dyn Fn(&str) -> JsExpr, inner: &JsExpr, fi: usize, total: usize) -> JsExpr {
    // Argument is a newtype (identity), so Product contains raw values, not Argument objects.
    // Product(a, Product(b, c)) has value0=a, value1=Product(b,c)
    if total == 1 {
        // Single field: inner is the value itself (no Product wrapping)
        inner.clone()
    } else if fi < total - 1 {
        // Navigate Product chain: inner.value0 (first), inner.value1.value0 (second), etc.
        let mut expr = inner.clone();
        for _ in 0..fi {
            expr = JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())));
        }
        JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value0".to_string())))
    } else {
        // Last field: navigate to the end of the product chain
        let mut expr = inner.clone();
        for _ in 0..(fi - 1) {
            expr = JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())));
        }
        JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())))
    }
}

/// Wrap a value in Inl/Inr constructors for the generic sum position.
fn gen_generic_inl_inr_wrap(rep_ref: &dyn Fn(&str) -> JsExpr, inner: JsExpr, idx: usize, total: usize) -> JsExpr {
    if total == 1 {
        return inner;
    }
    // For Sum(A, Sum(B, Sum(C, D))):
    //   A (idx=0): Inl(inner)
    //   B (idx=1): Inr(Inl(inner))
    //   C (idx=2): Inr(Inr(Inl(inner)))
    //   D (idx=3): Inr(Inr(Inr(inner)))
    // Pattern: wrap in Inl for non-last, then wrap in idx Inr's from inside out
    let mut wrapped = if idx < total - 1 {
        JsExpr::New(Box::new(rep_ref("Inl")), vec![inner])
    } else {
        inner
    };
    for _ in 0..idx {
        wrapped = JsExpr::New(Box::new(rep_ref("Inr")), vec![wrapped]);
    }
    wrapped
}

/// Generate dict parameter names for constraints, numbering duplicates.
/// E.g., [Eq, Eq] → ["dictEq", "dictEq1"], [Show, Eq] → ["dictShow", "dictEq"]
fn constraint_dict_params(constraints: &[Constraint]) -> Vec<String> {
    let mut counts: HashMap<Symbol, usize> = HashMap::new();
    let mut result = Vec::new();
    for c in constraints {
        let count = counts.entry(c.class.name).or_insert(0);
        let class_name = interner::resolve(c.class.name).unwrap_or_default();
        if *count == 0 {
            result.push(format!("dict{class_name}"));
        } else {
            result.push(format!("dict{class_name}{count}"));
        }
        *count += 1;
    }
    result
}

/// Generate a dict parameter name from a constraint, e.g. `Show a` → `dictShow`
fn constraint_to_dict_param(constraint: &Constraint) -> String {
    let class_name = interner::resolve(constraint.class.name).unwrap_or_default();
    format!("dict{class_name}")
}

/// Generate superclass accessor fields for an instance dict.
///
/// For `class (Applicative m, Bind m) <= Monad m`, an instance like `monadEffect`
/// needs fields:
///   Applicative0: function() { return applicativeEffect; },
///   Bind1: function() { return bindEffect; },
fn gen_superclass_accessors(
    ctx: &CodegenCtx,
    class_name: &QualifiedIdent,
    instance_types: &[crate::cst::TypeExpr],
    instance_constraints: &[Constraint],
    fields: &mut Vec<(String, JsExpr)>,
) {
    // Look up class superclasses
    let superclasses = find_class_superclasses(ctx, class_name.name);
    if superclasses.is_empty() {
        return;
    }

    // Get the class's type variable names (for matching superclass args to instance types)
    let class_tvs = find_class_type_vars(ctx, class_name.name);

    // Extract head type constructor from instance types (for registry lookup)
    let head_type = extract_head_type_con_from_cst(instance_types, &ctx.type_op_targets);

    for (idx, (super_class_qi, super_args)) in superclasses.iter().enumerate() {
        let super_name = interner::resolve(super_class_qi.name).unwrap_or_default();
        let accessor_name = format!("{super_name}{idx}");

        // Type-level classes (Coercible, etc.) have no runtime dict — return undefined
        if !ctx.known_runtime_classes.contains(&super_class_qi.name) {
            let thunk = JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(JsExpr::Var("undefined".to_string()))],
            );
            fields.push((accessor_name, thunk));
            continue;
        }

        // Try to resolve the superclass instance:
        // 1. If the instance has constraints, the superclass dict may come from a constraint param
        // 2. Otherwise, look up in instance registry
        let dict_expr = if let Some(dict) = find_superclass_from_constraints(
            instance_constraints, super_class_qi.name,
        ) {
            // The superclass dict comes from the instance's own constraint parameter
            dict
        } else {
            // Determine which instance type the superclass applies to.
            // For multi-param classes like `MonadWriter w m` with superclass `Monad m`,
            // we need to find which instance type corresponds to the superclass's type var.
            let effective_head = if !class_tvs.is_empty() && !super_args.is_empty() {
                // Find which class type var the superclass uses
                if let Some(tv) = super_args.first().and_then(|a| {
                    if let crate::typechecker::types::Type::Var(v) = a { Some(*v) } else { None }
                }) {
                    // Find the position of this type var in the class's type vars
                    if let Some(pos) = class_tvs.iter().position(|v| *v == tv) {
                        // Use the corresponding instance type
                        instance_types.get(pos).and_then(|t| extract_head_from_type_expr(t, &ctx.type_op_targets))
                    } else {
                        head_type
                    }
                } else {
                    head_type
                }
            } else {
                head_type
            };

            let Some(head) = effective_head else { continue };
            // Look up the superclass instance for the correct head type
            let base_ref = resolve_instance_ref(ctx, super_class_qi.name, head);

            // If the resolved instance is a local constrained instance,
            // apply the matching constraint dicts from the parent instance.
            // E.g., monoidAdditive has constraint Semiring a, its Semigroup superclass
            // instance is semigroupAdditive which also needs Semiring a → semigroupAdditive(dictSemiring)
            let inst_sym = ctx.instance_registry.get(&(super_class_qi.name, head)).cloned();
            if let Some(inst_name) = inst_sym {
                if let Some(constraint_classes) = ctx.instance_constraint_classes.get(&inst_name) {
                    if !constraint_classes.is_empty() {
                        // Apply matching dict params from the parent instance's constraints
                        let parent_dict_params = constraint_dict_params(instance_constraints);
                        let mut applied = base_ref;
                        for sc_class in constraint_classes {
                            // Type-level constraints (RowToList, Cons, Nub, etc.)
                            // are erased to zero-arg function wrappers — call with no args
                            if !ctx.known_runtime_classes.contains(sc_class) {
                                applied = JsExpr::App(Box::new(applied), vec![]);
                                continue;
                            }
                            // Find matching constraint in parent
                            if let Some(pos) = instance_constraints.iter().position(|c| c.class.name == *sc_class) {
                                applied = JsExpr::App(
                                    Box::new(applied),
                                    vec![JsExpr::Var(parent_dict_params[pos].clone())],
                                );
                            } else {
                                // Try superclass accessor: e.g., Semigroup from Semigroupoid via dictCategory.Semigroupoid0()
                                // For now, check dict scope for a matching class
                                let class_str = interner::resolve(*sc_class).unwrap_or_default();
                                let mut found_dict = false;
                                for (i, parent_c) in instance_constraints.iter().enumerate() {
                                    // Check if the parent constraint's class has a superclass matching sc_class
                                    let parent_supers = find_class_superclasses(ctx, parent_c.class.name);
                                    for (si, (super_qi, _)) in parent_supers.iter().enumerate() {
                                        if super_qi.name == *sc_class {
                                            let super_name = interner::resolve(super_qi.name).unwrap_or_default();
                                            let accessor = format!("{super_name}{si}");
                                            let dict_access = JsExpr::App(
                                                Box::new(JsExpr::Indexer(
                                                    Box::new(JsExpr::Var(parent_dict_params[i].clone())),
                                                    Box::new(JsExpr::StringLit(accessor)),
                                                )),
                                                vec![],
                                            );
                                            applied = JsExpr::App(Box::new(applied), vec![dict_access]);
                                            found_dict = true;
                                            break;
                                        }
                                    }
                                    if found_dict { break; }
                                }
                                if !found_dict {
                                    // Last resort: just pass dictClassName
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
fn find_class_superclasses(
    ctx: &CodegenCtx,
    class_name: Symbol,
) -> Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)> {
    ctx.all_class_superclasses.get(&class_name).map(|(_, supers)| supers.clone()).unwrap_or_default()
}

fn find_class_type_vars(
    ctx: &CodegenCtx,
    class_name: Symbol,
) -> Vec<Symbol> {
    ctx.all_class_superclasses.get(&class_name).map(|(tvs, _)| tvs.clone()).unwrap_or_default()
}

/// Check if a superclass dict can be obtained from the instance's own constraint parameters.
/// E.g., for `instance (Semigroup a) => Semigroup (Maybe a)`, the `Semigroup` constraint
/// on `a` comes from the instance constraint parameter.
fn find_superclass_from_constraints(
    instance_constraints: &[Constraint],
    super_class: Symbol,
) -> Option<JsExpr> {
    for constraint in instance_constraints {
        if constraint.class.name == super_class {
            let class_name_str = interner::resolve(super_class).unwrap_or_default();
            let dict_param = format!("dict{class_name_str}");
            return Some(JsExpr::Var(dict_param));
        }
    }
    None
}

/// Resolve an instance reference: given a class and head type constructor,
/// find the instance name and generate a JS reference to it.
fn resolve_instance_ref(ctx: &CodegenCtx, class_name: Symbol, head: Symbol) -> JsExpr {
    // Check local instance registry first
    if let Some(inst_name) = ctx.instance_registry.get(&(class_name, head)) {
        let inst_js = ident_to_js(*inst_name);
        if ctx.local_names.contains(inst_name) {
            return JsExpr::Var(inst_js.clone());
        }
        if let Some(source) = ctx.instance_sources.get(inst_name) {
            match source {
                None => return JsExpr::Var(inst_js.clone()),
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
            if let Some(inst_name) = mod_exports.instance_registry.get(&(class_name, head)) {
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
fn find_local_eq_instance_for_type(ctx: &CodegenCtx, head_type: Option<Symbol>, eq_sym: Symbol) -> Option<String> {
    let head = head_type?;
    // Check instance registry for (Eq, head_type)
    if let Some(inst_name) = ctx.instance_registry.get(&(eq_sym, head)) {
        return Some(ident_to_js(*inst_name));
    }
    // Synthesize the name: eqTypeName
    let head_str = interner::resolve(head).unwrap_or_default();
    Some(format!("eq{head_str}"))
}

// ===== Expression translation =====

/// Check if an expression contains any Expr::Wildcard nodes (for section syntax).
fn contains_wildcard(expr: &Expr) -> bool {
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
fn extract_app_head_and_depth(expr: &Expr) -> (Option<Symbol>, Option<crate::span::Span>, usize) {
    match expr {
        Expr::Var { name, span, .. } => (Some(name.name), Some(*span), 0),
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

fn gen_expr(ctx: &CodegenCtx, expr: &Expr) -> JsExpr {
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

fn gen_expr_inner(ctx: &CodegenCtx, expr: &Expr) -> JsExpr {
    match expr {
        Expr::Var { span, name, .. } => {
            // Debug: log dict miss for class methods and constrained functions at module level
            let result = gen_qualified_ref_with_span(ctx, name, Some(*span));
            // Check if this is a constrained higher-rank parameter that needs eta-expansion
            if name.module.is_none() {
                if let Some(dict_name) = ctx.constrained_hr_params.borrow().get(&name.name) {
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
            if ctx.discharging_partial.get() && ctx.partial_fns.contains(&name.name)
                && ctx.local_names.contains(&name.name)
            {
                return JsExpr::App(Box::new(result), vec![]);
            }
            result
        }

        Expr::Constructor { name, .. } => {
            let ctor_name = name.name;
            // Check newtype first — newtype constructors are identity functions
            if ctx.newtype_names.contains(&ctor_name) {
                gen_qualified_ref_raw(ctx, name)
            } else if let Some((_, _, fields)) = ctx.ctor_details.get(&unqualified(ctor_name)) {
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
            } else {
                // Try looking up in imported modules' ctor_details
                let imported_ctor = ctx.name_source.get(&ctor_name).and_then(|parts| {
                    ctx.registry.lookup(parts).and_then(|mod_exports| {
                        mod_exports.ctor_details.get(&unqualified(ctor_name))
                    })
                });
                if let Some((_, _, fields)) = imported_ctor {
                    let base = gen_qualified_ref_raw(ctx, name);
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
                    let base = gen_qualified_ref_raw(ctx, name);
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
                if ctx.newtype_names.contains(&name.name) {
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
                let depth_key = unqualified(head_sym);
                if let Some(&arrow_depth) = ctx.exports.return_type_arrow_depth.get(&depth_key) {
                    if app_depth + 1 == arrow_depth {
                        // Insert return-type dicts at this point
                        if let Some(dicts) = head_span.and_then(|s| ctx.resolved_dict_map.get(&s)) {
                            let rt_class_names: Vec<Symbol> = ctx.exports.return_type_constraints
                                .get(&depth_key)
                                .map(|cs| cs.iter().map(|(c, _)| c.name).collect())
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
                                .map(|cs| cs.iter().map(|(c, _)| c.name).collect())
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

        Expr::VisibleTypeApp { func, .. } => {
            // Type applications are erased at runtime
            gen_expr(ctx, func)
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
            let op_str = interner::resolve(op.value.name).unwrap_or_default();
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
            let body_expr = gen_expr(ctx, body);
            *ctx.local_bindings.borrow_mut() = prev_bindings;
            iife_body.push(JsStmt::Return(body_expr));
            JsExpr::App(
                Box::new(JsExpr::Function(None, vec![], iife_body)),
                vec![],
            )
        }

        Expr::Do { span, statements, module: qual_mod } => {
            gen_do_expr(ctx, *span, statements, qual_mod.as_ref())
        }

        Expr::Ado { span, statements, result, module: qual_mod } => {
            gen_ado_expr(ctx, *span, statements, result, qual_mod.as_ref())
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
            let obj = gen_expr_inner(ctx, expr);
            let label = interner::resolve(field.value).unwrap_or_default();
            JsExpr::Indexer(Box::new(obj), Box::new(JsExpr::StringLit(label)))
        }

        Expr::RecordUpdate { span, expr, updates } => {
            gen_record_update(ctx, *span, expr, updates)
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

fn gen_qualified_ref_with_span(ctx: &CodegenCtx, qident: &QualifiedIdent, span: Option<crate::span::Span>) -> JsExpr {
    let name = qident.name;

    // Check if it's a foreign import in the current module
    if qident.module.is_none() && ctx.foreign_imports.contains(&name) {
        let original_name = interner::resolve(name).unwrap_or_default();
        return JsExpr::ModuleAccessor("$foreign".to_string(), original_name);
    }

    let base = gen_qualified_ref_raw(ctx, qident);

    // Local bindings (lambda params, let/where bindings, case binders) are never class methods
    // or constrained functions — skip all dict application for them. This prevents a local
    // binding like `append = \o -> ...` from getting the Prelude `append`'s Semigroup dict.
    if qident.module.is_none() && ctx.local_bindings.borrow().contains(&name) {
        if !ctx.local_constrained_bindings.borrow().contains(&name) {
            return base;
        }
    }

    // Module-level names that shadow imported class methods/constrained functions
    // should not get dict application unless they have their own constraints.
    // E.g., local `append = \o -> ...` (in Objects test) shadows Prelude's `append`.
    if qident.module.is_none() && ctx.local_names.contains(&name) {
        let has_own_constraints = ctx.exports.signature_constraints.contains_key(&unqualified(name))
            || ctx.exports.return_type_constraints.contains_key(&unqualified(name));
        let is_own_class_method = ctx.exports.class_methods.contains_key(&unqualified(name));
        if !has_own_constraints && !is_own_class_method {
            return base;
        }
    }

    // If this is a class method and we have a matching dict in scope, apply it
    if let Some(dict_app) = try_apply_dict(ctx, qident, base.clone(), span) {
        return dict_app;
    }

    // Fallback: if the function has constraints that are ALL zero-cost (e.g. Coercible),
    // strip each phantom wrapper with an empty `()` call. This handles both:
    // 1. Module-level concrete calls where resolved_dict_map has ZeroCost entries
    // 2. Polymorphic calls inside constrained functions where scope has no entry
    //    (because zero-cost constraints are not pushed to dict_scope)
    {
        let fn_constraints = ctx.all_fn_constraints.borrow().get(&qident.name).cloned().unwrap_or_default();
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
    if ctx.partial_fns.contains(&qident.name) {
        return JsExpr::App(Box::new(base), vec![]);
    }

    base
}

/// If `name` is a class method or constrained function and we have matching dicts in scope,
/// return the expression with dict args applied.
fn try_apply_dict(ctx: &CodegenCtx, qident: &QualifiedIdent, base: JsExpr, span: Option<crate::span::Span>) -> Option<JsExpr> {
    let scope = ctx.dict_scope.borrow();

    if !scope.is_empty() {
        // First, check if this is a class method — try all classes that define this method
        let method_qi = unqualified(qident.name);
        if let Some(class_entries) = find_class_method_all(ctx, &method_qi) {
            for (class_qi, _) in &class_entries {
                // Before using scope-based lookup, check if the resolved_dict_map has a
                // concrete zero-arg instance for this call site. This handles cases like
                // `show(showString)` inside a function with `Show a` in scope, where
                // scope-based lookup would incorrectly return `dictShow`.
                if let Some(resolved) = try_apply_resolved_dict_for_class(ctx, &base, span, class_qi.name) {
                    return Some(resolved);
                }
                if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, class_qi.name) {
                    let mut result = JsExpr::App(Box::new(base), vec![dict_expr]);
                    // Also apply method-own constraints (e.g., eq1 :: forall a. Eq a => ...)
                    // These are constraints on the method's signature beyond the class constraint.
                    let method_own = find_method_own_constraints(ctx, qident.name, class_qi.name);
                    for own_class in &method_own {
                        if let Some(own_dict) = find_dict_in_scope(ctx, &scope, *own_class) {
                            result = JsExpr::App(Box::new(result), vec![own_dict]);
                        }
                    }
                    return Some(result);
                }
            }
        }

        // Second, check if this is a constrained function (not a class method but has constraints)
        let fn_constraints = find_fn_constraints(ctx, qident);
        if !fn_constraints.is_empty() {
            let resolved_dicts = span.and_then(|s| ctx.resolved_dict_map.get(&s));
            // First try: resolve ALL from resolved_dict_map (pure concrete case)
            if let Some(dicts) = resolved_dicts {
                let mut result = base.clone();
                let mut all_resolved = true;
                for class_name in &fn_constraints {
                    if let Some((_, dict_expr)) = dicts.iter().find(|(cn, _)| *cn == *class_name) {
                        if is_concrete_zero_arg_dict(dict_expr, ctx) {
                            let js_dict = dict_expr_to_js(ctx, dict_expr);
                            result = JsExpr::App(Box::new(result), vec![js_dict]);
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
                for class_name in &fn_constraints {
                    if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, *class_name) {
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
                for class_name in &fn_constraints {
                    // Try resolved_dict_map first (concrete instances)
                    let from_resolved = resolved_dicts.and_then(|dicts| {
                        dicts.iter().find(|(cn, _)| *cn == *class_name).and_then(|(_, dict_expr)| {
                            if is_concrete_zero_arg_dict(dict_expr, ctx) {
                                Some(dict_expr_to_js(ctx, dict_expr))
                            } else {
                                None
                            }
                        })
                    });
                    if let Some(js_dict) = from_resolved {
                        result = JsExpr::App(Box::new(result), vec![js_dict]);
                    } else if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, *class_name) {
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
                if all_found {
                    return Some(result);
                }
            }
        }
    }

    // Drop the scope borrow before trying resolved_dict_map
    drop(scope);

    // Fallback: try resolved_dict_map for module-level dict resolution
    try_apply_resolved_dict(ctx, qident, base.clone(), span)
}

/// Try to resolve a class method call using the resolved_dict_map for a specific class.
/// Returns Some if the resolved dict is:
/// - A concrete zero-arg instance (showString, eqInt), OR
/// - A ConstraintArg (reference to a specific constraint parameter)
fn try_apply_resolved_dict_for_class(ctx: &CodegenCtx, base: &JsExpr, span: Option<crate::span::Span>, class_name: Symbol) -> Option<JsExpr> {
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
        if matches!(dict_expr, crate::typechecker::registry::DictExpr::App(_, _)) {
            let js_dict = dict_expr_to_js(ctx, dict_expr);
            return Some(JsExpr::App(Box::new(base.clone()), vec![js_dict]));
        }
        // Only use the resolved dict if it's a concrete zero-arg instance
        // (like showString, eqInt).
        if !is_concrete_zero_arg_dict(dict_expr, ctx) {
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
fn is_concrete_zero_arg_dict(dict: &crate::typechecker::registry::DictExpr, ctx: &CodegenCtx) -> bool {
    use crate::typechecker::registry::DictExpr;
    match dict {
        DictExpr::Var(name) => {
            // Check if this is an instance with NO constraints (zero-arg)
            if let Some(constraints) = ctx.instance_constraint_classes.get(name) {
                return constraints.is_empty();
            }
            // Not in instance_constraint_classes — check if it looks like a dict parameter
            let name_str = interner::resolve(*name).unwrap_or_default();
            !name_str.starts_with("dict")
        }
        DictExpr::App(_, _) => false, // Applied instances are not zero-arg
        DictExpr::ConstraintArg(_) => false, // Constraint param, not a concrete instance
        DictExpr::InlineIsSymbol(_) => true, // Inline IsSymbol is fully concrete
        DictExpr::InlineReflectable(_) => true, // Inline Reflectable is fully concrete
        DictExpr::ZeroCost => true, // Zero-cost constraint, no actual dict needed
    }
}

/// Try to resolve a class method or constrained function call using the pre-resolved dict map.
/// This handles module-level calls where dict_scope is empty but the typechecker resolved
/// the concrete instance dict. Uses expression span for unambiguous lookup.
fn try_apply_resolved_dict(ctx: &CodegenCtx, qident: &QualifiedIdent, base: JsExpr, span: Option<crate::span::Span>) -> Option<JsExpr> {
    let span = span?;

    // Look up pre-resolved dicts at this expression span.
    // The typechecker stores resolved dicts keyed by expression span,
    // so this is unambiguous regardless of name collisions.
    let dicts = ctx.resolved_dict_map.get(&span)?;

    if dicts.is_empty() {
        return None;
    }

    // Check if this is a class method — if so, apply only the matching class dict
    if let Some(class_entries) = ctx.all_class_methods.get(&qident.name) {
        for (class_qi, _) in class_entries {
            let class_name = class_qi.name;
            if let Some((_, dict_expr)) = dicts.iter().find(|(cn, _)| *cn == class_name) {
                if matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                    return Some(JsExpr::App(Box::new(base), vec![]));
                }
                let js_dict = dict_expr_to_js(ctx, dict_expr);
                return Some(JsExpr::App(Box::new(base), vec![js_dict]));
            }
        }
    }

    // For constrained functions, apply dicts in the order of their signature constraints.
    // This ensures the right dict is applied for each constraint parameter.
    let fn_constraints = ctx.all_fn_constraints.borrow().get(&qident.name).cloned().unwrap_or_default();
    if !fn_constraints.is_empty() {
        let mut result = base;
        // Extract head type from existing resolved dicts for resolving missing ones.
        // For a function like abs :: Ord a => Ring a => a -> a, if Ord Int is resolved,
        // we know the head type is Int and can resolve Ring Int from the instance registry.
        let head_type: Option<Symbol> = dicts.iter().find_map(|(_, dict_expr)| {
            extract_head_from_dict_expr(dict_expr, ctx)
        });
        for class_name in &fn_constraints {
            if let Some((_, dict_expr)) = dicts.iter().find(|(cn, _)| cn == class_name) {
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
                // Try to resolve from instance registry
                if let Some(inst_name) = ctx.instance_registry.get(&(*class_name, head)) {
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

    // Apply all resolved dicts at this span, deduplicating by class name.
    // This handles: constrained functions, let-bound constrained functions,
    // and class methods where the class name didn't match all_class_methods
    // (e.g. methods from support modules with different symbol interning).
    // Skip dicts that belong to return-type constraints — those are handled
    // by the RT_DICT mechanism in the App handler after enough args are applied.
    let rt_class_names: HashSet<Symbol> = ctx.exports.return_type_constraints
        .get(&unqualified(qident.name))
        .map(|cs| cs.iter().map(|(c, _)| c.name).collect())
        .unwrap_or_default();
    let mut result = base;
    let mut seen_classes: HashSet<Symbol> = HashSet::new();
    let mut applied_any = false;
    for (class_name, dict_expr) in dicts {
        if rt_class_names.contains(class_name) {
            continue; // handled by RT_DICT in App
        }
        if seen_classes.insert(*class_name) {
            applied_any = true;
            if matches!(dict_expr, crate::typechecker::registry::DictExpr::ZeroCost) {
                result = JsExpr::App(Box::new(result), vec![]);
            } else {
                let js_dict = dict_expr_to_js(ctx, dict_expr);
                result = JsExpr::App(Box::new(result), vec![js_dict]);
            }
        }
    }
    if applied_any { Some(result) } else { None }
}

/// Extract the head type constructor from a DictExpr by looking up the instance
/// in the instance registry. E.g., ordInt → Int, eqArray → Array.
fn extract_head_from_dict_expr(dict: &crate::typechecker::registry::DictExpr, ctx: &CodegenCtx) -> Option<Symbol> {
    use crate::typechecker::registry::DictExpr;
    match dict {
        DictExpr::Var(name) => {
            // Look through instance_registry for any entry whose value matches this name
            for ((_, head), inst) in &ctx.instance_registry {
                if inst == name {
                    return Some(*head);
                }
            }
            None
        }
        DictExpr::App(name, _) => {
            for ((_, head), inst) in &ctx.instance_registry {
                if inst == name {
                    return Some(*head);
                }
            }
            None
        }
        _ => None,
    }
}

/// Convert a DictExpr from the typechecker into a JS expression.
fn dict_expr_to_js(ctx: &CodegenCtx, dict: &crate::typechecker::registry::DictExpr) -> JsExpr {
    use crate::typechecker::registry::DictExpr;
    match dict {
        DictExpr::Var(name) => {
            // Check if this instance name was deduplicated (collision avoidance)
            let js_name = if let Some(deduped) = ctx.deduped_instance_names.borrow().get(name) {
                deduped.clone()
            } else {
                ident_to_js(*name)
            };
            let ext_name = export_name(*name);
            // Check if local or imported
            if ctx.local_names.contains(name) {
                JsExpr::Var(js_name)
            } else if let Some(source_parts) = ctx.name_source.get(name) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    JsExpr::ModuleAccessor(js_mod.clone(), ext_name)
                } else {
                    JsExpr::Var(js_name)
                }
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
                        if mod_exports.values.contains_key(&unqualified(*name)) {
                            found = Some(JsExpr::ModuleAccessor(js_mod.clone(), ext_name.clone()));
                            break;
                        }
                    }
                }
                found.unwrap_or(JsExpr::Var(js_name))
            }
        }
        DictExpr::App(name, sub_dicts) => {
            let base = dict_expr_to_js(ctx, &DictExpr::Var(*name));
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
                            let sub_js = dict_expr_to_js(ctx, &sub_dicts[sub_idx]);
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
fn find_class_method_all(ctx: &CodegenCtx, method_qi: &QualifiedIdent) -> Option<Vec<(QualifiedIdent, Vec<QualifiedIdent>)>> {
    ctx.all_class_methods.get(&method_qi.name).cloned()
}

/// Find class method info for a name (returns first matching class).
fn find_class_method(ctx: &CodegenCtx, method_qi: &QualifiedIdent) -> Option<(QualifiedIdent, Vec<QualifiedIdent>)> {
    ctx.all_class_methods.get(&method_qi.name).and_then(|v| v.first().cloned())
}

/// Find a class method's own constraints — constraints on the method's signature
/// that are NOT the class constraint itself. For example, `eq1 :: forall a. Eq a => ...`
/// has own constraint `Eq` (while the class constraint is `Eq1`).
fn find_method_own_constraints(ctx: &CodegenCtx, method_name: Symbol, _class_name: Symbol) -> Vec<Symbol> {
    let method_qi = unqualified(method_name);
    // Check local exports first
    if let Some(constraints) = ctx.exports.method_own_constraints.get(&method_qi) {
        return constraints.clone();
    }
    // Check registry modules
    for (_, mod_exports) in ctx.registry.iter_all() {
        if let Some(constraints) = mod_exports.method_own_constraints.get(&method_qi) {
            return constraints.clone();
        }
    }
    vec![]
}

/// Filter out constraints that are redundant because they are superclasses of other
/// constraints in the list. E.g. if both `Monad m` and `MonadState s m` are present,
/// `Monad m` is redundant because it's a superclass of `MonadState`.
fn filter_redundant_superclass_constraints(
    constraints: &[(QualifiedIdent, Vec<crate::typechecker::types::Type>)],
    all_class_superclasses: &HashMap<Symbol, (Vec<Symbol>, Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)>)>,
) -> Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)> {
    if constraints.len() <= 1 {
        return constraints.to_vec();
    }

    let constraint_classes: Vec<Symbol> = constraints.iter().map(|(qi, _)| qi.name).collect();
    let mut redundant: HashSet<Symbol> = HashSet::new();

    for (class_qi, _) in constraints {
        let mut stack = vec![class_qi.name];
        let mut visited = HashSet::new();
        while let Some(cls) = stack.pop() {
            if !visited.insert(cls) { continue; }
            if let Some((_, supers)) = all_class_superclasses.get(&cls) {
                for (sc, _) in supers {
                    if constraint_classes.contains(&sc.name) && sc.name != class_qi.name {
                        redundant.insert(sc.name);
                    }
                    stack.push(sc.name);
                }
            }
        }
    }

    constraints.iter()
        .filter(|(qi, _)| !redundant.contains(&qi.name))
        .cloned()
        .collect()
}

/// Find constraint class names for a function (non-class-method).
fn find_fn_constraints(ctx: &CodegenCtx, qident: &QualifiedIdent) -> Vec<Symbol> {
    // Don't apply to class methods (handled separately) — but only if not locally defined
    // as a regular function (e.g., local `discard` shadows imported class method `discard`)
    if ctx.all_class_methods.contains_key(&qident.name) && !ctx.all_fn_constraints.borrow().contains_key(&qident.name) {
        return vec![];
    }
    ctx.all_fn_constraints.borrow().get(&qident.name).cloned().unwrap_or_default()
}

/// Find a dict expression for a given class name in the current scope.
fn find_dict_in_scope(ctx: &CodegenCtx, scope: &[(Symbol, String)], class_name: Symbol) -> Option<JsExpr> {
    // Direct match
    for (scope_class, dict_param) in scope.iter().rev() {
        if *scope_class == class_name {
            return Some(JsExpr::Var(dict_param.clone()));
        }
    }

    // Superclass chain: e.g., dictApplicative["Apply0"]()["Functor0"]()
    for (scope_class, dict_param) in scope.iter().rev() {
        let mut accessors = Vec::new();
        if find_superclass_chain(ctx, *scope_class, class_name, &mut accessors) {
            let mut expr = JsExpr::Var(dict_param.clone());
            for accessor in accessors {
                expr = JsExpr::App(
                    Box::new(JsExpr::Indexer(
                        Box::new(expr),
                        Box::new(JsExpr::StringLit(accessor)),
                    )),
                    vec![],
                );
            }
            return Some(expr);
        }
    }

    None
}

/// Resolve a class constraint to a concrete dict JS expression using the instance registry.
/// E.g. for class `Bind` with type `Effect`, finds `bindEffect` in registry.
fn resolve_dict_from_registry(ctx: &CodegenCtx, class_name: Symbol, type_args: &[crate::typechecker::types::Type]) -> Option<JsExpr> {
    use crate::typechecker::types::Type;

    // Extract head type constructor from the type args
    let head = type_args.first().and_then(|t| extract_head_from_type(t))?;

    // Look up in instance registry
    let inst_name = ctx.instance_registry.get(&(class_name, head))?;

    let inst_js = ident_to_js(*inst_name);

    // Resolve to JS: check if local or from a module
    let js_expr = if let Some(source) = ctx.instance_sources.get(inst_name) {
        match source {
            None => JsExpr::Var(inst_js.clone()), // local
            Some(parts) => {
                if let Some(js_mod) = ctx.import_map.get(parts) {
                    JsExpr::ModuleAccessor(js_mod.clone(), inst_js)
                } else {
                    JsExpr::Var(inst_js)
                }
            }
        }
    } else {
        // Try name_source
        if let Some(source_parts) = ctx.name_source.get(inst_name) {
            if let Some(js_mod) = ctx.import_map.get(source_parts) {
                JsExpr::ModuleAccessor(js_mod.clone(), inst_js)
            } else {
                JsExpr::Var(inst_js)
            }
        } else {
            JsExpr::Var(inst_js)
        }
    };

    // TODO: handle parameterized instances (where the instance itself has constraints)
    // For now, just return the simple instance reference
    Some(js_expr)
}

/// Find superclass accessor name: if `to_class` is a superclass of `from_class`,
/// return the accessor name (e.g., "Applicative0") to get the sub-dict.
/// Returns None if not a direct superclass.
/// Find the full chain of superclass accessors from `from_class` to `to_class`.
/// E.g., Applicative → Functor produces ["Apply0", "Functor0"].
/// Returns true if a chain was found, with accessors appended to `chain`.
fn find_superclass_chain(ctx: &CodegenCtx, from_class: Symbol, to_class: Symbol, chain: &mut Vec<String>) -> bool {
    if from_class == to_class {
        return true;
    }
    if let Some((_, supers)) = ctx.all_class_superclasses.get(&from_class) {
        let supers = supers.clone(); // avoid borrow conflict with recursive calls
        for (idx, (super_qi, _)) in supers.iter().enumerate() {
            let super_name = interner::resolve(super_qi.name).unwrap_or_default();
            let accessor = format!("{super_name}{idx}");
            chain.push(accessor);
            if find_superclass_chain(ctx, super_qi.name, to_class, chain) {
                return true;
            }
            chain.pop();
        }
    }
    false
}

/// Like gen_qualified_ref_raw, but uses Indexer (bracket) notation for external module
/// constructor references, matching the original PureScript compiler's output.
fn gen_qualified_ctor_ref(ctx: &CodegenCtx, qident: &QualifiedIdent) -> JsExpr {
    let js_name = ident_to_js(qident.name);
    let ps_name = interner::resolve(qident.name).unwrap_or_default().to_string();

    // Local constructors use Var
    if ctx.local_names.contains(&qident.name) {
        return JsExpr::Var(js_name);
    }
    if ctx.local_bindings.borrow().contains(&qident.name) {
        return JsExpr::Var(js_name);
    }

    // External constructors: use Indexer (bracket) on the module var
    if let Some(origin_sym) = ctx.exports.value_origins.get(&qident.name) {
        let origin_str = interner::resolve(*origin_sym).unwrap_or_default();
        let origin_parts: Vec<Symbol> = origin_str.split('.').map(|s| interner::intern(s)).collect();
        if let Some(js_mod) = ctx.import_map.get(&origin_parts) {
            return JsExpr::Indexer(
                Box::new(JsExpr::Var(js_mod.clone())),
                Box::new(JsExpr::StringLit(ps_name)),
            );
        }
    }
    if let Some(source_parts) = ctx.name_source.get(&qident.name) {
        if let Some(js_mod) = ctx.import_map.get(source_parts) {
            return JsExpr::Indexer(
                Box::new(JsExpr::Var(js_mod.clone())),
                Box::new(JsExpr::StringLit(ps_name)),
            );
        }
    }

    // Fallback
    JsExpr::Var(js_name)
}

fn gen_qualified_ref_raw(ctx: &CodegenCtx, qident: &QualifiedIdent) -> JsExpr {
    let js_name = ident_to_js(qident.name);
    // The name used in ModuleAccessor must match what the exporting module exposes.
    // For reserved words (new → $$new internally, exported `as new`) the export name is `new`.
    // For special chars (assert' → assert$prime) the export name is `assert$prime`.
    let ext_name = export_name(qident.name);

    match &qident.module {
        None => {
            // Check if this is a locally-defined name (module-level declaration)
            if ctx.local_names.contains(&qident.name) {
                return JsExpr::Var(js_name);
            }
            // Check if this is a locally-bound name (lambda param, let/where binding, case binder)
            if ctx.local_bindings.borrow().contains(&qident.name) {
                return JsExpr::Var(js_name);
            }
            // Check if this is an imported name.
            // Use value_origins to find the *defining* module (not the re-exporting module).
            // E.g., `show` imported from Prelude should resolve to Data_Show, not Prelude.
            if let Some(origin_sym) = ctx.exports.value_origins.get(&qident.name) {
                let origin_str = interner::resolve(*origin_sym).unwrap_or_default();
                // Parse origin module string to parts and look up in import_map
                let origin_parts: Vec<Symbol> = origin_str.split('.').map(|s| interner::intern(s)).collect();
                if let Some(js_mod) = ctx.import_map.get(&origin_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                }
            }
            // Fallback: use the import source (may be a re-exporter like Prelude)
            if let Some(source_parts) = ctx.name_source.get(&qident.name) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                }
            }
            // Check if this is an imported instance (globally visible)
            if let Some(Some(source_parts)) = ctx.instance_sources.get(&qident.name) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), ext_name);
                }
            }
            // Check if this is a class method — search imported modules for the method
            if ctx.all_class_methods.contains_key(&qident.name) {
                // Sort for deterministic output
                let mut sorted_imports: Vec<_> = ctx.import_map.iter().collect();
                sorted_imports.sort_by_key(|(_, js_mod)| (*js_mod).clone());
                for (mod_parts, js_mod) in &sorted_imports {
                    if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
                        if mod_exports.class_methods.contains_key(&unqualified(qident.name))
                            || mod_exports.values.contains_key(&unqualified(qident.name)) {
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
            // Fallback: use the module name directly
            let js_mod = any_name_to_js(&mod_str.replace('.', "_"));
            JsExpr::ModuleAccessor(js_mod, ext_name)
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
        GuardedExpr::Unconditional(expr) => gen_return_stmts(ctx, expr),
        GuardedExpr::Guarded(guards) => gen_guards_stmts(ctx, guards),
    }
}

/// Generate return statements for an expression. For case expressions, this
/// inlines the if/instanceof chains directly instead of wrapping in an IIFE.
fn gen_return_stmts(ctx: &CodegenCtx, expr: &Expr) -> Vec<JsStmt> {
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
fn gen_case_stmts(ctx: &CodegenCtx, scrutinees: &[Expr], alts: &[CaseAlternative]) -> Vec<JsStmt> {
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

fn has_pattern_guards(patterns: &[GuardPattern]) -> bool {
    patterns.iter().any(|p| matches!(p, GuardPattern::Pattern(..)))
}

fn gen_guards_expr(ctx: &CodegenCtx, guards: &[Guard]) -> JsExpr {
    // If any guard has pattern guards, we need an IIFE to introduce variable bindings
    if guards.iter().any(|g| has_pattern_guards(&g.patterns)) {
        let stmts = gen_guards_stmts(ctx, guards);
        return JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], stmts)),
            vec![],
        );
    }

    // Simple case: build nested ternary: cond1 ? e1 : cond2 ? e2 : error
    let mut result = JsExpr::New(
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
        if has_pattern_guards(&guard.patterns) {
            // Build the guard body with pattern guard bindings and boolean conditions
            let body_stmts = gen_return_stmts(ctx, &guard.expr);
            // Process patterns, wrapping body in nested if-blocks with bindings
            let result = gen_guard_patterns_stmts(ctx, &guard.patterns, body_stmts);
            stmts.extend(result);
        } else {
            let cond = gen_guard_condition(ctx, &guard.patterns);
            // Use gen_return_stmts to inline let-expressions in guard bodies
            let body_stmts = gen_return_stmts(ctx, &guard.expr);
            // If guard condition is `true` (i.e. `| otherwise`), emit body directly
            if matches!(&cond, JsExpr::BoolLit(true)) {
                stmts.extend(body_stmts);
                return stmts;
            }
            stmts.push(JsStmt::If(
                cond,
                body_stmts,
                None,
            ));
        }
    }
    stmts.push(JsStmt::Throw(JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )));
    stmts
}

/// Generate statements for a guard's patterns, handling pattern guards properly.
/// For pattern guards (`pat <- expr`), generates:
///   var $tmp = expr;
///   if (condition_from_binder) { bindings; ...inner_body... }
/// For boolean guards, generates:
///   if (expr) { ...inner_body... }
/// Multiple patterns are nested from left to right.
fn gen_guard_patterns_stmts(
    ctx: &CodegenCtx,
    patterns: &[GuardPattern],
    inner_body: Vec<JsStmt>,
) -> Vec<JsStmt> {
    // Process patterns right-to-left, building nested if-blocks
    let mut current_body = inner_body;

    for pattern in patterns.iter().rev() {
        match pattern {
            GuardPattern::Boolean(expr) => {
                let cond = gen_expr(ctx, expr);
                current_body = vec![JsStmt::If(cond, current_body, None)];
            }
            GuardPattern::Pattern(binder, expr) => {
                let tmp_name = ctx.fresh_name("$pat_guard");
                let scrutinee = JsExpr::Var(tmp_name.clone());
                let (cond, bindings) = gen_binder_match(ctx, binder, &scrutinee);

                let mut if_body = Vec::new();
                if_body.extend(bindings);
                if_body.extend(current_body);

                let mut block = Vec::new();
                block.push(JsStmt::VarDecl(tmp_name, Some(gen_expr(ctx, expr))));
                if let Some(cond) = cond {
                    block.push(JsStmt::If(cond, if_body, None));
                } else {
                    // Wildcard/var pattern always matches
                    block.extend(if_body);
                }

                current_body = block;
            }
        }
    }

    current_body
}

fn gen_guard_condition(ctx: &CodegenCtx, patterns: &[GuardPattern]) -> JsExpr {
    let mut conditions: Vec<JsExpr> = Vec::new();
    for pattern in patterns {
        match pattern {
            GuardPattern::Boolean(expr) => {
                conditions.push(gen_expr(ctx, expr));
            }
            GuardPattern::Pattern(_binder, expr) => {
                // This should only be called for boolean-only guards,
                // but as a fallback just evaluate the expression
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

/// Pre-allocate parameter names for binders before generating the function body.
/// This ensures params get the lowest fresh counter values (v, v1, v2...).
fn pre_allocate_param_names(ctx: &CodegenCtx, binders: &[Binder]) -> Vec<Option<String>> {
    binders.iter().map(|b| {
        match b {
            Binder::Var { .. } => None,
            Binder::Wildcard { .. } => Some(ctx.fresh_name("v")),
            _ => Some(ctx.fresh_name("v")),
        }
    }).collect()
}

/// Like gen_curried_function but uses pre-allocated param names.
fn gen_curried_function_with_params(ctx: &CodegenCtx, binders: &[Binder], body: Vec<JsStmt>, param_names: &[Option<String>]) -> JsExpr {
    if binders.is_empty() {
        return JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], body)),
            vec![],
        );
    }
    build_curried_function_body(ctx, binders, body, param_names)
}

fn gen_curried_function(ctx: &CodegenCtx, binders: &[Binder], body: Vec<JsStmt>) -> JsExpr {
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

fn build_curried_function_body(ctx: &CodegenCtx, binders: &[Binder], body: Vec<JsStmt>, param_names: &[Option<String>]) -> JsExpr {

    // Build from inside out
    let mut current_body = body;

    for (i, binder) in binders.iter().enumerate().rev() {
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

fn gen_curried_function_from_stmts(
    ctx: &CodegenCtx,
    binders: &[Binder],
    body: Vec<JsStmt>,
) -> JsExpr {
    gen_curried_function(ctx, binders, body)
}

// ===== Let bindings =====

fn gen_let_bindings(ctx: &CodegenCtx, bindings: &[LetBinding], stmts: &mut Vec<JsStmt>) {
    // Group consecutive same-name Var bindings for multi-equation functions
    let mut i = 0;
    while i < bindings.len() {
        match &bindings[i] {
            LetBinding::Value { binder: Binder::Var { name, .. }, .. } => {
                let binding_name = name.value;
                // Collect all consecutive bindings with same name
                let start = i;
                i += 1;
                while i < bindings.len() {
                    if let LetBinding::Value { binder: Binder::Var { name: n2, .. }, .. } = &bindings[i] {
                        if n2.value == binding_name {
                            i += 1;
                            continue;
                        }
                    }
                    // Also skip type signatures for the same name
                    if let LetBinding::Signature { name: n2, .. } = &bindings[i] {
                        if n2.value == binding_name {
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
                        let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name).collect();
                        ctx.all_fn_constraints.borrow_mut().insert(binding_name, class_names);
                        ctx.local_constrained_bindings.borrow_mut().insert(binding_name);
                    }
                }

                // Push dict scope entries for constraints (unique names for duplicate classes)
                let prev_scope_len = ctx.dict_scope.borrow().len();
                if let Some(ref constraints) = constraints {
                    let mut dict_name_counts: HashMap<String, usize> = HashMap::new();
                    for (class_qi, _) in constraints {
                        if !ctx.known_runtime_classes.contains(&class_qi.name) {
                            continue; // Zero-cost constraint — no runtime dict param
                        }
                        let class_name_str = interner::resolve(class_qi.name).unwrap_or_default();
                        let count = dict_name_counts.entry(class_name_str.to_string()).or_insert(0);
                        let dict_param = if *count == 0 {
                            format!("dict{class_name_str}")
                        } else {
                            format!("dict{class_name_str}{count}")
                        };
                        *count += 1;
                        ctx.dict_scope.borrow_mut().push((class_qi.name, dict_param));
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
}

/// Compile multi-equation let bindings into a single function.
/// Each binding has form `LetBinding::Value { binder: Var(name), expr: Lambda(...) | body }`.
/// The lambda bodies become case alternatives in a merged function.
fn gen_multi_equation_let(ctx: &CodegenCtx, js_name: &str, group: &[LetBinding]) -> Vec<JsStmt> {
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

    let params: Vec<String> = (0..arity).map(|i| ctx.fresh_name("v")).collect();

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
                                    let guard_cond = gen_guard_condition(ctx, &guard.patterns);
                                    let guard_body = gen_expr(ctx, &guard.expr);
                                    alt_body.push(JsStmt::If(
                                        guard_cond,
                                        vec![JsStmt::Return(guard_body)],
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

fn gen_case_expr(ctx: &CodegenCtx, scrutinees: &[Expr], alts: &[CaseAlternative]) -> JsExpr {
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
fn collect_binder_names(binder: &Binder, names: &mut HashSet<Symbol>) {
    match binder {
        Binder::Var { name, .. } => { names.insert(name.value); }
        Binder::As { name, binder, .. } => {
            names.insert(name.value);
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
                    names.insert(field.label.value);
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
            let is_sum = if let Some((parent, _, _)) = ctx.ctor_details.get(&unqualified(ctor_name)) {
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
            let is_function_op = ctx.function_op_aliases.contains(&unqualified(op_name.name));

            if !is_function_op {
                // Constructor operator — treat as constructor binder with 2 args.
                // Resolve the operator to its target constructor name (e.g., `!` → `Cons`).
                let resolved_name = if let Some((_, target_name)) = ctx.operator_targets.get(&op_name.name) {
                    QualifiedIdent { module: op_name.module, name: *target_name }
                } else {
                    op_name.clone()
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

fn gen_record_update(ctx: &CodegenCtx, span: crate::span::Span, base: &Expr, updates: &[RecordUpdate]) -> JsExpr {
    let base_expr = gen_expr(ctx, base);

    // Build set of updated field names
    let update_label_set: HashSet<String> = updates.iter().map(|u| {
        interner::resolve(u.label.value).unwrap_or_default()
    }).collect();

    // If we know all the record fields from typechecking, generate an object literal
    if let Some(all_fields) = ctx.record_update_fields.get(&span) {
        let mut fields = Vec::new();
        // Non-updated fields first (preserve from base), then updated fields
        for field_sym in all_fields {
            let label = interner::resolve(*field_sym).unwrap_or_default();
            if !update_label_set.contains(&label) {
                fields.push((label.clone(), JsExpr::Indexer(
                    Box::new(base_expr.clone()),
                    Box::new(JsExpr::StringLit(label)),
                )));
            }
        }
        for update in updates {
            let label = interner::resolve(update.label.value).unwrap_or_default();
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
        let label = interner::resolve(update.label.value).unwrap_or_default();
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

fn gen_do_expr(ctx: &CodegenCtx, span: crate::span::Span, statements: &[DoStatement], qual_mod: Option<&Ident>) -> JsExpr {
    // Do notation desugars to bind chains:
    // do { x <- a; b } → bind(a)(function(x) { return b; })
    // do { a; b } → discard(a)(b) or bind(a)(function(_) { return b; })

    let bind_ref = make_qualified_ref_with_span(ctx, qual_mod, "bind", Some(span));

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
        DoStatement::Discard { expr, span, .. } => {
            let action = gen_expr(ctx, expr);
            let rest_expr = gen_do_stmts(ctx, rest, bind_ref, qual_mod);
            // If `discard` is defined locally in this module, use it (matches original compiler).
            // Otherwise, use `bind` directly since Control.Bind.discard is a class accessor
            // that requires Discard + Bind dictionaries we can't resolve from the CST.
            // Semantically equivalent: discard(discardUnit)(dictBind) = bind(dictBind) for Unit.
            let discard_sym = interner::intern("discard");
            let call_ref = if ctx.local_names.contains(&discard_sym) {
                let discard_qi = QualifiedIdent {
                    module: qual_mod.copied(),
                    name: discard_sym,
                };
                gen_qualified_ref_with_span(ctx, &discard_qi, Some(*span))
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
            // Register let binding names so they shadow operators in rest
            let prev_bindings = ctx.local_bindings.borrow().clone();
            for lb in bindings.iter() {
                if let LetBinding::Value { binder: Binder::Var { name, .. }, .. } = lb {
                    ctx.local_bindings.borrow_mut().insert(name.value);
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

fn gen_ado_expr(
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
                    Binder::Var { name, .. } => ident_to_js(name.value),
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

fn make_qualified_ref_with_span(ctx: &CodegenCtx, qual_mod: Option<&Ident>, name: &str, span: Option<crate::span::Span>) -> JsExpr {
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
                sorted_imports.sort_by_key(|(_, js_mod)| js_mod.clone());
                for (mod_parts, js_mod) in sorted_imports {
                    if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
                        if mod_exports.class_methods.contains_key(&unqualified(name_sym))
                            || mod_exports.values.contains_key(&unqualified(name_sym)) {
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
    let qident = QualifiedIdent { module: None, name: name_sym };
    if let Some(dict_app) = try_apply_dict(ctx, &qident, base.clone(), span) {
        return dict_app;
    }

    base
}

// ===== Topological sort =====

/// Collect all `Var` references from a JsExpr.
fn collect_var_refs(expr: &JsExpr, refs: &mut HashSet<String>) {
    match expr {
        JsExpr::Var(name) => { refs.insert(name.clone()); }
        JsExpr::App(f, args) => {
            collect_var_refs(f, refs);
            for a in args { collect_var_refs(a, refs); }
        }
        JsExpr::Function(_, _, body) => {
            for stmt in body { collect_stmt_refs(stmt, refs); }
        }
        JsExpr::ArrayLit(elems) => {
            for e in elems { collect_var_refs(e, refs); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_var_refs(v, refs); }
        }
        JsExpr::Indexer(a, b) => {
            collect_var_refs(a, refs);
            collect_var_refs(b, refs);
        }
        JsExpr::Unary(_, e) => collect_var_refs(e, refs),
        JsExpr::Binary(_, a, b) => {
            collect_var_refs(a, refs);
            collect_var_refs(b, refs);
        }
        JsExpr::Ternary(c, t, e) => {
            collect_var_refs(c, refs);
            collect_var_refs(t, refs);
            collect_var_refs(e, refs);
        }
        JsExpr::InstanceOf(a, b) => {
            collect_var_refs(a, refs);
            collect_var_refs(b, refs);
        }
        JsExpr::New(f, args) => {
            collect_var_refs(f, refs);
            for a in args { collect_var_refs(a, refs); }
        }
        JsExpr::ModuleAccessor(_, _) | JsExpr::NumericLit(_) | JsExpr::IntLit(_)
        | JsExpr::StringLit(_) | JsExpr::BoolLit(_) | JsExpr::RawJs(_) => {}
    }
}

fn collect_stmt_refs(stmt: &JsStmt, refs: &mut HashSet<String>) {
    match stmt {
        JsStmt::Expr(e) | JsStmt::Return(e) | JsStmt::Throw(e) => collect_var_refs(e, refs),
        JsStmt::VarDecl(_, Some(e)) => collect_var_refs(e, refs),
        JsStmt::VarDecl(_, None) => {}
        JsStmt::Assign(l, r) => { collect_var_refs(l, refs); collect_var_refs(r, refs); }
        JsStmt::If(c, t, e) => {
            collect_var_refs(c, refs);
            for s in t { collect_stmt_refs(s, refs); }
            if let Some(es) = e { for s in es { collect_stmt_refs(s, refs); } }
        }
        JsStmt::Block(stmts) => { for s in stmts { collect_stmt_refs(s, refs); } }
        JsStmt::For(_, init, bound, body) => {
            collect_var_refs(init, refs);
            collect_var_refs(bound, refs);
            for s in body { collect_stmt_refs(s, refs); }
        }
        JsStmt::ForIn(_, obj, body) => {
            collect_var_refs(obj, refs);
            for s in body { collect_stmt_refs(s, refs); }
        }
        JsStmt::While(c, body) => {
            collect_var_refs(c, refs);
            for s in body { collect_stmt_refs(s, refs); }
        }
        JsStmt::FunctionDecl(_, _, body) => {
            for s in body { collect_stmt_refs(s, refs); }
        }
        JsStmt::ReturnVoid | JsStmt::Comment(_) | JsStmt::Import { .. }
        | JsStmt::Export(_) | JsStmt::ExportFrom(_, _) | JsStmt::RawJs(_)
        => {}
    }
}

/// Generate code for an operator expression, handling operator precedence via shunting-yard.
/// The CST parses operator chains as right-associative trees, but we need to respect
/// declared fixities (e.g., `*` binds tighter than `+`).
fn gen_op_chain(ctx: &CodegenCtx, left: &Expr, op: &Spanned<QualifiedIdent>, right: &Expr, expr_span: crate::span::Span) -> JsExpr {
    // Flatten the right-recursive Op chain
    let mut operands: Vec<&Expr> = vec![left];
    let mut operators: Vec<&Spanned<QualifiedIdent>> = vec![op];
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

    for i in 0..operators.len() {
        let (assoc_i, prec_i) = ctx.op_fixities.get(&operators[i].value.name)
            .copied()
            .unwrap_or((Associativity::Left, 9));

        while let Some(&top_idx) = op_stack.last() {
            let (_assoc_top, prec_top) = ctx.op_fixities.get(&operators[top_idx].value.name)
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
fn gen_single_op(ctx: &CodegenCtx, left: &Expr, op: &Spanned<QualifiedIdent>, right: &Expr, expr_span: crate::span::Span) -> JsExpr {
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
fn apply_op(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>, lhs: JsExpr, rhs: JsExpr) -> JsExpr {
    // Optimize `f $ x` (apply) to `f(x)` and `x # f` (applyFlipped) to `f(x)`
    if is_apply_operator(ctx, op) {
        if is_apply_flipped_operator(ctx, op) {
            return JsExpr::App(Box::new(rhs), vec![lhs]);
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
fn try_inline_bare_op(module: &str, method: &str, a: &JsExpr, b: &JsExpr) -> Option<JsExpr> {
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
fn is_apply_operator(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>) -> bool {
    if let Some((_, target_name)) = ctx.operator_targets.get(&op.value.name) {
        let name = interner::resolve(*target_name).unwrap_or_default();
        if name != "apply" && name != "applyFlipped" {
            return false;
        }
        // Exclude class method operators like <*> (Control.Apply.apply)
        // by checking the operator symbol name — $ and # are the only
        // function-application operators
        let op_name = interner::resolve(op.value.name).unwrap_or_default();
        op_name == "$" || op_name == "#"
    } else {
        false
    }
}

/// Check if an operator is `#` (applyFlipped), meaning arguments should be swapped: `a # f` = `f(a)`
fn is_apply_flipped_operator(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>) -> bool {
    if let Some((_, target_name)) = ctx.operator_targets.get(&op.value.name) {
        let name = interner::resolve(*target_name).unwrap_or_default();
        if name != "applyFlipped" {
            return false;
        }
        let op_name = interner::resolve(op.value.name).unwrap_or_default();
        op_name == "#"
    } else {
        false
    }
}

/// Resolve an operator to its JS reference (target function + dict application).
fn resolve_op_ref(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>, expr_span: Option<crate::span::Span>) -> JsExpr {
    let op_sym = op.value.name;
    // Use expr_span for dict lookup (matches typechecker's span for OpParens vs Op)
    let lookup_span = expr_span.or(Some(op.span));

    // If the operator name itself is a local let-binding (e.g., backtick `div` where
    // `div` is locally defined), use the local variable instead of the imported operator.
    if op.value.module.is_none() && ctx.local_bindings.borrow().contains(&op_sym) {
        return JsExpr::Var(ident_to_js(op_sym));
    }

    if let Some((source_parts, target_name)) = ctx.operator_targets.get(&op_sym) {
        let target_js = ident_to_js(*target_name);
        // Check if the target is a data constructor by looking it up in ctor_details
        let is_ctor = is_constructor_name(ctx, *target_name);
        if is_ctor {
            // Constructor operator: emit Ctor.create (curried constructor)
            let target_qi = QualifiedIdent { module: None, name: *target_name };
            let base = gen_qualified_ref_raw(ctx, &target_qi);
            return JsExpr::Indexer(
                Box::new(base),
                Box::new(JsExpr::StringLit("create".to_string())),
            );
        }
        if ctx.local_names.contains(target_name) || ctx.name_source.contains_key(target_name) {
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
                            if dname.value == *target_name && binders.is_empty() {
                                // Generate the expression for the module-level definition
                                resolved = Some(gen_expr(ctx, body));
                                break;
                            }
                        }
                    }
                    resolved.unwrap_or_else(|| {
                        let target_qi = QualifiedIdent { module: None, name: *target_name };
                        gen_qualified_ref_with_span(ctx, &target_qi, lookup_span)
                    })
                }
            } else {
                let target_qi = QualifiedIdent { module: None, name: *target_name };
                let result = gen_qualified_ref_with_span(ctx, &target_qi, lookup_span);
                if was_bound {
                    ctx.local_bindings.borrow_mut().insert(*target_name);
                }
                result
            }
        } else if let Some(parts) = source_parts {
            // Target not in name_source — resolve via operator's source module
            if let Some(js_mod) = ctx.import_map.get(parts) {
                let target_ps = interner::resolve(*target_name).unwrap_or_default().to_string();
                let base = JsExpr::ModuleAccessor(js_mod.clone(), target_ps);
                // Try to apply dict
                let target_qi = QualifiedIdent { module: None, name: *target_name };
                if let Some(dict_applied) = try_apply_dict(ctx, &target_qi, base.clone(), lookup_span) {
                    dict_applied
                } else {
                    base
                }
            } else {
                let target_qi = QualifiedIdent { module: None, name: *target_name };
                gen_qualified_ref_with_span(ctx, &target_qi, lookup_span)
            }
        } else {
            let target_qi = QualifiedIdent { module: None, name: *target_name };
            gen_qualified_ref_with_span(ctx, &target_qi, lookup_span)
        }
    } else {
        // No operator_targets entry — this is a backtick-infixed function or constructor.
        // Check if it's a constructor name and emit .create if so.
        if is_constructor_name(ctx, op_sym) {
            let base = gen_qualified_ref_raw(ctx, &op.value);
            return JsExpr::Indexer(
                Box::new(base),
                Box::new(JsExpr::StringLit("create".to_string())),
            );
        }
        gen_qualified_ref_with_span(ctx, &op.value, lookup_span)
    }
}

/// Check if a name refers to a data constructor (local or imported).
fn is_constructor_name(ctx: &CodegenCtx, name: Symbol) -> bool {
    // Check local ctor_details
    if ctx.ctor_details.contains_key(&unqualified(name)) {
        return true;
    }
    // Check imported modules' ctor_details
    if let Some(source_parts) = ctx.name_source.get(&name) {
        if let Some(mod_exports) = ctx.registry.lookup(source_parts) {
            if mod_exports.ctor_details.contains_key(&unqualified(name)) {
                return true;
            }
        }
    }
    false
}

// ===== Post-processing: inline known typeclass operations =====

/// Extract method name and dict name from a 3-level nested application:
/// App(ModuleAccessor(mod, method), [ModuleAccessor(_, dict)])
fn extract_method_dict_from_expr(expr: &JsExpr) -> Option<(&str, &str)> {
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
fn try_inline_binary_op_post(expr: &JsExpr) -> Option<JsExpr> {
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
fn try_inline_unary_op_post(expr: &JsExpr) -> Option<JsExpr> {
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
fn try_inline_constant_post(expr: &JsExpr) -> Option<JsExpr> {
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

fn inline_known_ops_expr(expr: &mut JsExpr) {
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

fn inline_known_ops_stmt(stmt: &mut JsStmt) {
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
        JsStmt::Block(stmts) | JsStmt::While(_, stmts) => {
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

/// Collect all module names referenced via ModuleAccessor in a list of statements.
fn collect_used_modules(body: &[JsStmt]) -> HashSet<String> {
    let mut used = HashSet::new();
    for stmt in body {
        collect_used_modules_stmt(stmt, &mut used);
    }
    used
}

fn collect_used_modules_stmt(stmt: &JsStmt, used: &mut HashSet<String>) {
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

fn collect_used_modules_expr(expr: &JsExpr, used: &mut HashSet<String>) {
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
fn is_constructor_iife(stmt: &JsStmt) -> bool {
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
fn topo_sort_body(body: Vec<JsStmt>) -> Vec<JsStmt> {
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
    let mut dict_accessor_returns: HashMap<String, HashSet<String>> = HashMap::new();
    for stmt in &body {
        if let JsStmt::VarDecl(name, Some(JsExpr::ObjectLit(fields))) = stmt {
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

            // Add transitive deps through instance dict accessors:
            // if this decl eagerly references a dict D, and D has accessor
            // fields that return vars V1, V2, ..., add those as deps too.
            let mut transitive: HashSet<String> = HashSet::new();
            for r in &refs {
                if let Some(accessor_vars) = dict_accessor_returns.get(r) {
                    for v in accessor_vars {
                        transitive.insert(v.clone());
                    }
                }
                // Add transitive deps through function calls:
                // if this decl eagerly references a function F, and F's body
                // references vars V1, V2, ..., add those as deps too.
                if let Some(body_refs) = function_body_refs.get(r) {
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
fn collect_all_var_refs_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
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
fn collect_all_var_refs_stmt(stmt: &JsStmt, refs: &mut HashSet<String>) {
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
fn collect_eager_refs_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
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
fn collect_eager_refs_stmt_eager(stmt: &JsStmt, refs: &mut HashSet<String>) {
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
fn collect_all_refs_expr(expr: &JsExpr, refs: &mut HashSet<String>) {
    match expr {
        JsExpr::Var(name) => { refs.insert(name.clone()); }
        JsExpr::App(f, args) => {
            collect_all_refs_expr(f, refs);
            for a in args { collect_all_refs_expr(a, refs); }
        }
        JsExpr::Function(_, params, body) => {
            // Collect refs from function body too (unlike collect_eager_refs)
            let param_set: HashSet<&str> = params.iter().map(|s| s.as_str()).collect();
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
fn collect_all_refs_stmt(stmt: &JsStmt, refs: &mut HashSet<String>) {
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
fn extract_head_type_con_from_cst(types: &[crate::cst::TypeExpr], type_op_targets: &HashMap<Symbol, Symbol>) -> Option<Symbol> {
    types.first().and_then(|t| extract_head_from_type_expr(t, type_op_targets))
}

fn extract_head_from_type_expr(te: &crate::cst::TypeExpr, type_op_targets: &HashMap<Symbol, Symbol>) -> Option<Symbol> {
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
fn extract_head_type_con_from_types(types: &[crate::typechecker::types::Type]) -> Option<Symbol> {
    types.first().and_then(|t| extract_head_from_type(t))
}

fn extract_head_from_type(ty: &crate::typechecker::types::Type) -> Option<Symbol> {
    use crate::typechecker::types::Type;
    match ty {
        Type::Con(qi) => Some(qi.name),
        Type::App(f, _) => extract_head_from_type(f),
        Type::Record(_, _) => Some(interner::intern("Record")),
        Type::Fun(_, _) => Some(interner::intern("Function")),
        _ => None,
    }
}

/// Check if a CST type expression has a Partial constraint.
/// Extract binder name from a simple Var binder pattern (CST).
fn extract_simple_binder_name(binder: &Binder) -> Option<Symbol> {
    match binder {
        Binder::Var { name, .. } => Some(name.value),
        _ => None,
    }
}

/// Walk a type signature and find parameter positions with constrained higher-rank types.
/// Returns Vec<(param_index, dict_param_name)> where dict_param_name is e.g. "dictIsSymbol".
fn extract_constrained_param_indices(ty: &TypeExpr) -> Vec<(usize, String)> {
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

fn strip_outer_forall(ty: &TypeExpr) -> &TypeExpr {
    match ty {
        TypeExpr::Forall { ty, .. } => strip_outer_forall(ty),
        TypeExpr::Parens { ty, .. } => strip_outer_forall(ty),
        other => other,
    }
}

/// Check if a type expression has a nested constraint (after stripping Forall/Parens).
/// Returns the first constraint class name if found.
fn find_nested_constraint_class(ty: &TypeExpr) -> Option<String> {
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
fn is_unsafe_partial_call(expr: &Expr) -> bool {
    match expr {
        Expr::Var { name, .. } => {
            let name_str = interner::resolve(name.name).unwrap_or_default();
            name_str == "unsafePartial"
        }
        _ => false,
    }
}

fn has_partial_constraint(ty: &crate::cst::TypeExpr) -> bool {
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
