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

use super::common::{any_name_to_js, ident_to_js, is_valid_js_identifier, module_name_to_js};
use super::js_ast::*;
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
    /// Pre-built: class method → list of (class_name, type_vars) — multiple classes may have same method name
    all_class_methods: HashMap<Symbol, Vec<(QualifiedIdent, Vec<QualifiedIdent>)>>,
    /// Pre-built: fn_name → constraint class names (from signature_constraints)
    /// Uses RefCell because local let-bound constrained functions are added during codegen.
    all_fn_constraints: std::cell::RefCell<HashMap<Symbol, Vec<Symbol>>>,
    /// Pre-built: class_name → superclass list
    all_class_superclasses: HashMap<Symbol, Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)>>,
    /// Resolved dicts from typechecker: expression_span → [(class_name, dict_expr)].
    /// Used to resolve class method dicts at module level (outside dict scope).
    /// Each span uniquely identifies a call site, so lookups are unambiguous.
    resolved_dict_map: HashMap<crate::span::Span, Vec<(Symbol, crate::typechecker::registry::DictExpr)>>,
    /// Functions with Partial => constraint (need dict wrapper but not in signature_constraints)
    partial_fns: HashSet<Symbol>,
    /// Operator fixities: op_symbol → (associativity, precedence)
    op_fixities: HashMap<Symbol, (Associativity, u8)>,
    /// Wildcard section parameter names (collected during gen_expr for Expr::Wildcard)
    wildcard_params: std::cell::RefCell<Vec<String>>,
    /// Classes that have methods (and thus runtime dictionaries).
    /// Type-level classes (IsSymbol, RowToList, etc.) are NOT in this set.
    known_runtime_classes: HashSet<Symbol>,
    /// Locally-bound names (lambda params, let/where bindings, case binders).
    /// Used to distinguish local bindings from imported names with the same name.
    local_bindings: std::cell::RefCell<HashSet<Symbol>>,
    /// Record update field info from typechecker: span → all field names.
    record_update_fields: &'a HashMap<crate::span::Span, Vec<Symbol>>,
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

/// Generate a JS module from a typechecked PureScript module.
pub fn module_to_js(
    module: &Module,
    module_name: &str,
    module_parts: &[Symbol],
    exports: &ModuleExports,
    registry: &ModuleRegistry,
    has_ffi: bool,
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
                        // import M — import all names
                        for name in all_names.iter().chain(all_ctor_names.iter()) {
                            if !local_names.contains(name) {
                                name_source.entry(*name).or_insert_with(|| parts.clone());
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
                                    // Import all constructors of this type
                                    for ctor_name in &all_ctor_names {
                                        if !local_names.contains(ctor_name) {
                                            name_source.entry(*ctor_name).or_insert_with(|| parts.clone());
                                        }
                                    }
                                }
                                Import::Type(_, Some(DataMembers::Explicit(ctors))) => {
                                    for ctor in ctors {
                                        if !local_names.contains(&ctor.value) {
                                            name_source.entry(ctor.value).or_insert_with(|| parts.clone());
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
                                name_source.entry(*name).or_insert_with(|| parts.clone());
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
        instance_registry: HashMap::new(),
        instance_sources: HashMap::new(),
        all_class_methods: HashMap::new(),
        all_fn_constraints: std::cell::RefCell::new(HashMap::new()),
        all_class_superclasses: HashMap::new(),
        resolved_dict_map: exports.resolved_dicts.clone(),
        partial_fns,
        op_fixities: HashMap::new(),
        wildcard_params: std::cell::RefCell::new(Vec::new()),
        known_runtime_classes: HashSet::new(),
        local_bindings: std::cell::RefCell::new(HashSet::new()),
        record_update_fields: &exports.record_update_fields,
    };

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

    // Build operator fixity table from this module and all imported modules
    for (op_qi, (assoc, prec)) in &exports.value_fixities {
        ctx.op_fixities.entry(op_qi.name).or_insert((*assoc, *prec));
    }
    for (_, mod_exports) in registry.iter_all() {
        for (op_qi, (assoc, prec)) in &mod_exports.value_fixities {
            ctx.op_fixities.entry(op_qi.name).or_insert((*assoc, *prec));
        }
    }

    // Pre-build class method, constraint, and superclass lookup tables
    // (avoids expensive iter_all() on every reference)
    {
        // From this module's exports
        for (method, (class, tvs)) in &exports.class_methods {
            ctx.all_class_methods.entry(method.name).or_insert_with(Vec::new).push((class.clone(), tvs.clone()));
        }
        for (name, constraints) in &exports.signature_constraints {
            let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name).collect();
            ctx.all_fn_constraints.borrow_mut().entry(name.name).or_insert(class_names);
        }
        for (name, (_, supers)) in &exports.class_superclasses {
            ctx.all_class_superclasses.entry(name.name).or_insert_with(|| supers.clone());
        }
        // From all registry modules
        for (_, mod_exports) in registry.iter_all() {
            for (method, (class, tvs)) in &mod_exports.class_methods {
                ctx.all_class_methods.entry(method.name).or_insert_with(Vec::new).push((class.clone(), tvs.clone()));
            }
            for (name, constraints) in &mod_exports.signature_constraints {
                let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name).collect();
                ctx.all_fn_constraints.borrow_mut().entry(name.name).or_insert(class_names);
            }
            for (name, (_, supers)) in &mod_exports.class_superclasses {
                ctx.all_class_superclasses.entry(name.name).or_insert_with(|| supers.clone());
            }
        }

        // Build known_runtime_classes: classes that have methods (and thus runtime dictionaries).
        // Type-level classes (IsSymbol, RowToList, Lacks, etc.) have no methods and won't appear here.
        for (_, entries) in &ctx.all_class_methods {
            for (class_qi, _) in entries {
                ctx.known_runtime_classes.insert(class_qi.name);
            }
        }
    }

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

    // Ensure origin modules referenced by name_source have JS imports.
    // When we trace through value_origins, we may reference modules not
    // directly in module.imports (e.g., Data.Function via Prelude).
    // Add imports for origin modules referenced by operator_targets
    // (these may differ from the direct import modules due to value_origins tracing)
    {
        let mut origin_modules: Vec<Vec<Symbol>> = Vec::new();
        for (source_parts, _) in ctx.operator_targets.values() {
            if let Some(parts) = source_parts {
                if !ctx.import_map.contains_key(parts) {
                    origin_modules.push(parts.clone());
                }
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

    // Build instance registry for dict resolution
    // 1. From this module's own exports (populated by the typechecker)
    for ((class_sym, head_sym), inst_sym) in &exports.instance_registry {
        ctx.instance_registry.insert((*class_sym, *head_sym), *inst_sym);
        ctx.instance_sources.insert(*inst_sym, None);
    }
    // 2. Also scan CST for local instances (in case typechecker didn't populate all)
    for decl in &module.decls {
        if let Decl::Instance { name: Some(n), class_name, types, .. } = decl {
            if let Some(head) = extract_head_type_con_from_cst(types) {
                ctx.instance_registry.entry((class_name.name, head)).or_insert(n.value);
                ctx.instance_sources.entry(n.value).or_insert(None);
            }
        }
    }
    // 3. From ALL modules in the registry (instances are globally visible in PureScript)
    for (mod_parts, mod_exports) in registry.iter_all() {
        for ((class_sym, head_sym), inst_sym) in &mod_exports.instance_registry {
            ctx.instance_registry.entry((*class_sym, *head_sym)).or_insert(*inst_sym);
            ctx.instance_sources.entry(*inst_sym).or_insert(Some(mod_parts.to_vec()));
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
                if let Some(head) = extract_head_type_con_from_cst(types) {
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
                if let Decl::Instance { name: Some(n), .. } = decl {
                    // Instances are always exported in PureScript (globally visible)
                    exported_names.push(export_entry(n.value));
                }
                let stmts = gen_instance_decl(&ctx, decl);
                body.extend(stmts);
            }
            DeclGroup::Class(decl) => {
                let stmts = gen_class_decl(&ctx, decl);
                for stmt in &stmts {
                    if let JsStmt::VarDecl(name, _) = stmt {
                        // Check if this class method is exported
                        let name_sym = interner::intern(name);
                        if is_exported(&ctx, name_sym) {
                            exported_names.push(export_entry(name_sym));
                        }
                    }
                }
                body.extend(stmts);
            }
            DeclGroup::Fixity(_decl) => {
                // Operator aliases produce no JS output — operators are resolved to
                // their targets at usage sites.
            }
            DeclGroup::Derive(decl) => {
                if let Decl::Derive { name: Some(name), .. } = decl {
                    // Instances are always exported in PureScript
                    exported_names.push(export_entry(name.value));
                }
                let stmts = gen_derive_decl(&ctx, decl);
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

    // Generate re-export bindings: for names exported by this module but defined elsewhere
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

    // Check value_origins to find re-exported names.
    // Only generate re-export bindings when the module has an explicit export list.
    // Modules with no export list (module M where) technically export everything,
    // but generating bindings for ALL imported names is wasteful and can cause issues
    // (e.g., duplicate declarations, massive output).
    let has_explicit_exports = module.exports.is_some();
    let mut sorted_value_origins: Vec<_> = exports.value_origins.iter().collect();
    sorted_value_origins.sort_by_key(|(name, _)| interner::resolve(**name).unwrap_or_default().to_string());
    for (name_sym, origin_mod_sym) in sorted_value_origins {
        if !has_explicit_exports {
            // Without explicit exports, skip re-export bindings for imported names.
            // Local names are already in the body. The module still exports local names.
            if !ctx.local_names.contains(name_sym) {
                continue;
            }
        }
        let js_name = ident_to_js(*name_sym);
        if defined_names.contains(&js_name) {
            continue; // Already defined locally
        }
        if !is_exported(&ctx, *name_sym) {
            continue; // Not exported
        }
        // Skip type-only names (e.g. type operators like ~>)
        // Check if the origin module actually exports this value
        let origin_qi = unqualified(*name_sym);
        let origin_has_value = exports.values.contains_key(&origin_qi)
            || ctx.ctor_details.contains_key(&origin_qi);
        if !origin_has_value {
            // Also check imported modules
            let mut found_in_any = false;
            for (_, mod_exports) in ctx.registry.iter_all() {
                if mod_exports.values.contains_key(&origin_qi)
                    || mod_exports.ctor_details.contains_key(&origin_qi)
                {
                    found_in_any = true;
                    break;
                }
            }
            if !found_in_any {
                continue;
            }
        }
        // Find the module parts for the origin module
        let origin_str = interner::resolve(*origin_mod_sym).unwrap_or_default();
        // Look up in import_map
        let mut found = false;
        for (parts, js_mod) in &ctx.import_map {
            let mod_str = parts
                .iter()
                .map(|s| interner::resolve(*s).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".");
            if mod_str == origin_str {
                body.push(JsStmt::VarDecl(
                    js_name.clone(),
                    Some(JsExpr::ModuleAccessor(js_mod.clone(), js_name.clone())),
                ));
                exported_names.push(export_entry(*name_sym));
                found = true;
                break;
            }
        }
        if !found {
            // Try name_source as fallback
            if let Some(source_parts) = ctx.name_source.get(name_sym) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    body.push(JsStmt::VarDecl(
                        js_name.clone(),
                        Some(JsExpr::ModuleAccessor(js_mod.clone(), js_name.clone())),
                    ));
                    exported_names.push(export_entry(*name_sym));
                }
            }
        }
    }

    let foreign_module_path = if has_ffi {
        Some("./foreign.js".to_string())
    } else {
        None
    };

    // Topologically sort body declarations so that dependencies come before dependents
    let body = topo_sort_body(body);

    // Eliminate unused imports: only keep imports whose module name is actually
    // referenced in the generated body via ModuleAccessor expressions.
    let used_modules = collect_used_modules(&body);
    let mut imports: Vec<JsStmt> = imports.into_iter().filter(|stmt| {
        if let JsStmt::Import { name, .. } = stmt {
            used_modules.contains(name.as_str())
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
    Fixity(&'a Decl),
    TypeSig,
    ForeignData,
    Derive(&'a Decl),
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
            Decl::Fixity { .. } => groups.push(DeclGroup::Fixity(decl)),
            Decl::TypeSignature { .. } => groups.push(DeclGroup::TypeSig),
            Decl::ForeignData { .. } => groups.push(DeclGroup::ForeignData),
            Decl::Derive { .. } => groups.push(DeclGroup::Derive(decl)),
        }
    }

    // Non-value groups (data, class, instance, etc.) come first,
    // then value groups in source order. This ensures constructors and
    // class methods are defined before value declarations that reference them.
    let mut final_result: Vec<DeclGroup<'_>> = groups;
    for sym in value_order {
        if let Some(decls) = value_map.remove(&sym) {
            final_result.push(DeclGroup::Value(sym, decls));
        }
    }
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

    // Check if this value has type class constraints (needs dict params)
    let constraints = ctx.exports.signature_constraints.get(&unqualified(name)).cloned();


    // Push dict scope entries for constraints
    let prev_scope_len = ctx.dict_scope.borrow().len();
    if let Some(ref constraints) = constraints {
        for (class_qi, _) in constraints {
            let class_name_str = interner::resolve(class_qi.name).unwrap_or_default();
            let dict_param = format!("dict{class_name_str}");
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
                expr = wrap_with_dict_params(expr, constraints.as_ref());
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
                func = wrap_with_dict_params(func, constraints.as_ref());
                vec![JsStmt::VarDecl(js_name, Some(func))]
            } else {
                let mut iife_body = Vec::new();
                gen_let_bindings(ctx, where_clause, &mut iife_body);

                if binders.is_empty() {
                    // Try to inline where bindings at top level (no IIFE)
                    if let GuardedExpr::Unconditional(body) = guarded {
                        let no_constraints = constraints.as_ref().map_or(true, |c| c.is_empty());
                        if no_constraints {
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
                    let wrapped = wrap_with_dict_params(iife, constraints.as_ref());
                    vec![JsStmt::VarDecl(js_name, Some(wrapped))]
                } else {
                    let body_stmts = gen_guarded_expr_stmts(ctx, guarded);
                    iife_body.extend(body_stmts);
                    // Inline trivial aliases: var x = y → replace x with y
                    inline_trivial_aliases(&mut iife_body);
                    let mut func = gen_curried_function_from_stmts(ctx, binders, iife_body);
                    func = wrap_with_dict_params(func, constraints.as_ref());
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
                    let wrapped = wrap_with_dict_params(expr.clone(), Some(constraints));
                    *expr = wrapped;
                }
            }
        }
        stmts
    };

    // Pop dict scope
    ctx.dict_scope.borrow_mut().truncate(prev_scope_len);

    // If this function has a Partial constraint, wrap with dictPartial parameter
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
                    return Some(stmts);
                }
            }
        }
    }

    stmts.push(JsStmt::VarDecl(name.to_string(), Some(body_expr)));
    Some(stmts)
}

/// Wrap an expression with curried dict parameters from type class constraints.
/// E.g. `Show a => Eq a => ...` → `function(dictShow) { return function(dictEq) { return expr; }; }`
fn wrap_with_dict_params(
    expr: JsExpr,
    constraints: Option<&Vec<(QualifiedIdent, Vec<crate::typechecker::types::Type>)>>,
) -> JsExpr {
    let Some(constraints) = constraints else { return expr };
    if constraints.is_empty() { return expr; }

    let mut result = expr;
    for (class_qi, _) in constraints.iter().rev() {
        let class_name = interner::resolve(class_qi.name).unwrap_or_default();
        let dict_param = format!("dict{class_name}");
        result = JsExpr::Function(
            None,
            vec![dict_param.clone()],
            hoist_dict_applications(&dict_param, vec![JsStmt::Return(result)]),
        );
    }
    result
}

/// Scan a function body for `method(dictParam)` or `method(dictParam.Super0())`
/// applications that appear inside nested functions, and hoist them to
/// `var method1 = method(dictParam);` bindings at the top of the body.
/// Only hoists when the dict app is used inside an inner lambda, not when
/// it's the direct return value.
fn hoist_dict_applications(dict_param: &str, body: Vec<JsStmt>) -> Vec<JsStmt> {
    // Collect dict applications that appear inside nested functions
    let mut hoisted: Vec<(JsExpr, String)> = Vec::new();
    let mut counter: HashMap<String, usize> = HashMap::new();

    // Only collect from inside nested functions (depth > 0)
    collect_dict_apps_nested(dict_param, &body, &mut hoisted, &mut counter, 0);

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

/// Check if an expression is a dict application: `method(dictParam)` or
/// `method(dictParam.Superclass0())`.
fn is_dict_app(dict_param: &str, expr: &JsExpr) -> Option<String> {
    if let JsExpr::App(callee, args) = expr {
        if args.len() == 1 && is_dict_ref(dict_param, &args[0]) {
            if let JsExpr::Var(method_name) = callee.as_ref() {
                return Some(method_name.clone());
            }
            if let JsExpr::ModuleAccessor(_, method_name) = callee.as_ref() {
                return Some(method_name.clone());
            }
        }
    }
    None
}

/// Check if an expression refers to the dict param: either `dictParam` itself
/// or `dictParam.Superclass0()`.
fn is_dict_ref(dict_param: &str, expr: &JsExpr) -> bool {
    match expr {
        JsExpr::Var(name) => name == dict_param,
        // dictParam.Superclass0()
        JsExpr::App(callee, args) if args.is_empty() => {
            if let JsExpr::Indexer(obj, _) = callee.as_ref() {
                if let JsExpr::Var(name) = obj.as_ref() {
                    return name == dict_param;
                }
            }
            false
        }
        _ => false,
    }
}

/// Recursively collect dict applications from statements, tracking function nesting depth.
/// Only collects apps that appear at depth > 0 (inside nested functions).
fn collect_dict_apps_nested(dict_param: &str, stmts: &[JsStmt], hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize) {
    for stmt in stmts {
        collect_dict_apps_stmt_nested(dict_param, stmt, hoisted, counter, depth);
    }
}

fn collect_dict_apps_stmt_nested(dict_param: &str, stmt: &JsStmt, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize) {
    match stmt {
        JsStmt::Return(expr) => collect_dict_apps_expr_nested(dict_param, expr, hoisted, counter, depth),
        JsStmt::VarDecl(_, Some(expr)) => collect_dict_apps_expr_nested(dict_param, expr, hoisted, counter, depth),
        JsStmt::If(cond, then_body, else_body) => {
            collect_dict_apps_expr_nested(dict_param, cond, hoisted, counter, depth);
            collect_dict_apps_nested(dict_param, then_body, hoisted, counter, depth);
            if let Some(else_stmts) = else_body {
                collect_dict_apps_nested(dict_param, else_stmts, hoisted, counter, depth);
            }
        }
        JsStmt::Expr(expr) => collect_dict_apps_expr_nested(dict_param, expr, hoisted, counter, depth),
        _ => {}
    }
}

fn collect_dict_apps_expr_nested(dict_param: &str, expr: &JsExpr, hoisted: &mut Vec<(JsExpr, String)>, counter: &mut HashMap<String, usize>, depth: usize) {
    if let Some(method_name) = is_dict_app(dict_param, expr) {
        if depth > 0 {
            // Only hoist if inside a nested function
            if !hoisted.iter().any(|(e, _)| e == expr) {
                let count = counter.entry(method_name.clone()).or_insert(0);
                *count += 1;
                // For module accessors (imported methods), use bare name for first occurrence
                // For local methods, always use numbered name (method1, method2, ...)
                let is_module_accessor = matches!(expr, JsExpr::App(callee, _) if matches!(callee.as_ref(), JsExpr::ModuleAccessor(..)));
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
            collect_dict_apps_expr_nested(dict_param, callee, hoisted, counter, depth);
            for arg in args {
                collect_dict_apps_expr_nested(dict_param, arg, hoisted, counter, depth);
            }
        }
        JsExpr::Function(_, _, body) => {
            // Entering a nested function — increment depth
            collect_dict_apps_nested(dict_param, body, hoisted, counter, depth + 1);
        }
        JsExpr::Ternary(a, b, c) => {
            collect_dict_apps_expr_nested(dict_param, a, hoisted, counter, depth);
            collect_dict_apps_expr_nested(dict_param, b, hoisted, counter, depth);
            collect_dict_apps_expr_nested(dict_param, c, hoisted, counter, depth);
        }
        JsExpr::ArrayLit(items) => {
            for item in items {
                collect_dict_apps_expr_nested(dict_param, item, hoisted, counter, depth);
            }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, val) in fields {
                collect_dict_apps_expr_nested(dict_param, val, hoisted, counter, depth);
            }
        }
        JsExpr::Indexer(a, b) | JsExpr::Binary(_, a, b) => {
            collect_dict_apps_expr_nested(dict_param, a, hoisted, counter, depth);
            collect_dict_apps_expr_nested(dict_param, b, hoisted, counter, depth);
        }
        JsExpr::Unary(_, a) | JsExpr::InstanceOf(a, _) | JsExpr::New(a, _) => {
            collect_dict_apps_expr_nested(dict_param, a, hoisted, counter, depth);
        }
        _ => {}
    }
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
            JsExpr::Function(
                name,
                params,
                body.into_iter().map(|s| replace_dict_apps_stmt(s, hoisted)).collect(),
            )
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
        other => other,
    }
}

/// Convert fully-saturated `Ctor.create(a)(b)` into `new Ctor(a, b)`.
/// Recursively collects curried args and checks if the base is a `.create` accessor.
fn uncurry_create_to_new(expr: JsExpr) -> JsExpr {
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

/// Check if a JS expression references a constructor (.value or .create or new Ctor).
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
        _ => false,
    }
}

/// Inline trivial alias bindings: if `var x = y;` where y is a simple variable
/// that's a function parameter (not another where binding), replace all
/// subsequent uses of `x` with `y` and remove the binding.
fn inline_trivial_aliases(stmts: &mut Vec<JsStmt>) {
    let mut aliases: Vec<(String, String)> = Vec::new(); // (alias_name, target_name)
    let mut to_remove: Vec<usize> = Vec::new();

    // First pass: find trivial alias bindings
    let binding_names: HashSet<String> = stmts.iter().filter_map(|s| {
        if let JsStmt::VarDecl(name, _) = s { Some(name.clone()) } else { None }
    }).collect();

    for (i, stmt) in stmts.iter().enumerate() {
        if let JsStmt::VarDecl(name, Some(JsExpr::Var(target))) = stmt {
            // Only inline if target is NOT another where binding (it's a param)
            if !binding_names.contains(target) || aliases.iter().any(|(_, t)| t == target) {
                aliases.push((name.clone(), target.clone()));
                to_remove.push(i);
            }
        }
    }

    if aliases.is_empty() {
        return;
    }

    // Remove alias bindings (in reverse to preserve indices)
    for i in to_remove.into_iter().rev() {
        stmts.remove(i);
    }

    // Replace all occurrences
    for (alias_name, target_name) in &aliases {
        for stmt in stmts.iter_mut() {
            substitute_var_in_stmt(stmt, alias_name, target_name);
        }
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

/// Inline patterns like `var x = <expr>; return x;` → `return <expr>;`
/// Also handles `var x = <expr>; <other stmts using x once>`.
fn inline_single_use_bindings(stmts: &mut Vec<JsStmt>) {
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

    body.push(JsStmt::Throw(JsExpr::New(
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
        // Generate: var method = function(dict) { return dict["method"]; };
        let accessor = JsExpr::Function(
            None,
            vec!["dict".to_string()],
            vec![JsStmt::Return(JsExpr::Indexer(
                Box::new(JsExpr::Var("dict".to_string())),
                Box::new(JsExpr::StringLit(method_js.clone())),
            ))],
        );
        stmts.push(JsStmt::VarDecl(method_js, Some(accessor)));
    }
    stmts
}

// ===== Instance declarations =====

fn gen_instance_decl(ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Instance { name, members, constraints, class_name, types, .. } = decl else { return vec![] };

    // Instances become object literals with method implementations
    let instance_name = match name {
        Some(n) => ident_to_js(n.value),
        None => ctx.fresh_name("instance_"),
    };

    // Push dict scope entries for instance constraints
    let prev_scope_len = ctx.dict_scope.borrow().len();
    for constraint in constraints {
        let class_name_str = interner::resolve(constraint.class.name).unwrap_or_default();
        let dict_param = format!("dict{class_name_str}");
        ctx.dict_scope.borrow_mut().push((constraint.class.name, dict_param));
    }

    // Build multi-equation groups for instance methods (preserving order)
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
        let method_expr = if decls.len() == 1 {
            if let Decl::Value { binders, guarded, where_clause, .. } = decls[0] {
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
        fields.push((method_js, method_expr));
    }

    // Add superclass accessor fields
    // For `class (Super1 m, Super2 m) <= MyClass m`, instance dicts need:
    //   Super10: function() { return super1Instance; },
    //   Super21: function() { return super2Instance; },
    gen_superclass_accessors(ctx, class_name, types, constraints, &mut fields);

    let mut obj: JsExpr = JsExpr::ObjectLit(fields);

    // If the instance has constraints, wrap in curried functions taking dict params
    if !constraints.is_empty() {
        let dict_params = constraint_dict_params(constraints);
        for (ci, _constraint) in constraints.iter().enumerate().rev() {
            let dict_param = dict_params[ci].clone();
            obj = JsExpr::Function(
                None,
                vec![dict_param],
                vec![JsStmt::Return(obj)],
            );
        }
    }

    // Pop dict scope
    ctx.dict_scope.borrow_mut().truncate(prev_scope_len);

    vec![JsStmt::VarDecl(instance_name, Some(obj))]
}

/// Known derivable classes from the PureScript standard library.
/// Each variant corresponds to a class that can appear in `derive instance`.
#[derive(Debug, Clone, Copy, PartialEq)]
enum DeriveClass {
    Eq,       // Data.Eq.Eq
    Ord,      // Data.Ord.Ord
    Functor,  // Data.Functor.Functor
    Newtype,  // Data.Newtype.Newtype
    Generic,  // Data.Generic.Rep.Generic
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
        ("Functor", Some("Data.Functor")) => DeriveClass::Functor,
        ("Newtype", Some("Data.Newtype")) => DeriveClass::Newtype,
        ("Generic", Some("Data.Generic.Rep")) => DeriveClass::Generic,
        // Unqualified fallback (for locally-defined classes in single-module tests)
        ("Eq", None) => DeriveClass::Eq,
        ("Ord", None) => DeriveClass::Ord,
        ("Functor", None) => DeriveClass::Functor,
        ("Newtype", None) => DeriveClass::Newtype,
        ("Generic", None) => DeriveClass::Generic,
        _ => DeriveClass::Unknown,
    }
}

/// Generate code for a `derive instance` declaration.
/// Produces actual method implementations based on the class being derived.
fn gen_derive_decl(ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Derive { name, newtype, constraints, class_name, types, .. } = decl else { return vec![] };

    let instance_name = match name {
        Some(n) => ident_to_js(n.value),
        None => ctx.fresh_name("derive_"),
    };

    let class_str = interner::resolve(class_name.name).unwrap_or_default();
    let class_module = class_name.module.and_then(|m| interner::resolve(m));
    let derive_kind = resolve_derive_class(&class_str, class_module.as_deref());

    // For derive newtype: delegate to the underlying type's instance
    if *newtype {
        return gen_derive_newtype_instance(ctx, &instance_name, &class_str, class_name, types, constraints);
    }

    // Extract the target type constructor name
    let target_type = extract_head_type_con_from_cst(types);

    // Look up constructors for the target type
    let ctors = target_type.and_then(|t| {
        let qi = unqualified(t);
        ctx.data_constructors.get(&qi).map(|ctor_names| {
            ctor_names.iter().filter_map(|cn| {
                ctx.ctor_details.get(cn).map(|(_, _, field_types)| {
                    let name_str = interner::resolve(cn.name).unwrap_or_default();
                    (name_str, field_types.len())
                })
            }).collect::<Vec<_>>()
        })
    }).unwrap_or_default();

    // Build hoisted method var names for constrained derives.
    // Each constraint gets a hoisted var like `var eq1 = Data_Eq.eq(dictEq)`.
    // For Ord: also adds the Eq superclass instance var.
    // Each entry: (constraint_index, var_name, HoistedKind)
    #[derive(Clone)]
    enum HoistedKind {
        /// Method reference applied to dict param: var X = Module.method(dictParam)
        MethodApply(JsExpr),
        /// Direct expression: var X = expr (already fully formed)
        DirectExpr(JsExpr),
    }
    let mut hoisted_vars: Vec<(usize, String, HoistedKind)> = Vec::new();
    let dict_params_for_all = if !constraints.is_empty() { constraint_dict_params(constraints) } else { vec![] };
    if !constraints.is_empty() {
        let method_name = match derive_kind {
            DeriveClass::Eq => Some("eq"),
            DeriveClass::Ord => Some("compare"),
            _ => None,
        };
        if let Some(mname) = method_name {
            for (i, _constraint) in constraints.iter().enumerate() {
                let var_name = format!("{mname}{}", i + 1);
                let method_sym = interner::intern(mname);
                let method_qi = QualifiedIdent { module: None, name: method_sym };
                let method_ref = gen_qualified_ref_raw(ctx, &method_qi);
                hoisted_vars.push((i, var_name, HoistedKind::MethodApply(method_ref)));
            }
        }
    }

    let hoisted_eq_names: Vec<String> = hoisted_vars.iter().map(|(_, v, _)| v.clone()).collect();

    let mut fields: Vec<(String, JsExpr)> = match derive_kind {
        DeriveClass::Eq => gen_derive_eq_methods(&ctors, &hoisted_eq_names),
        DeriveClass::Ord => gen_derive_ord_methods(ctx, &ctors, &hoisted_eq_names),
        DeriveClass::Functor => gen_derive_functor_methods(ctx, &ctors),
        DeriveClass::Newtype => gen_derive_newtype_class_methods(),
        DeriveClass::Generic => gen_derive_generic_methods(ctx, &ctors),
        DeriveClass::Unknown => vec![],
    };

    // Add superclass accessors (e.g., Ord needs Eq0)
    if constraints.is_empty() {
        // Unconstrained: direct reference to local superclass instance
        gen_superclass_accessors(ctx, class_name, types, constraints, &mut fields);
    } else if derive_kind == DeriveClass::Ord {
        // Constrained Ord: Eq0 references a hoisted var that applies the local Eq instance
        // to dictOrd.Eq0(). The hoisted var is created below in the constraint wrapper.
        let dict_params = constraint_dict_params(constraints);
        // Find the local Eq instance name for the same type
        let eq_sym = interner::intern("Eq");
        let eq_instance_name = find_local_eq_instance_for_type(ctx, target_type, eq_sym);
        if let Some(eq_inst_js) = eq_instance_name {
            let eq_hoisted_var = format!("{eq_inst_js}1");
            // Add Eq0 accessor to fields referencing the hoisted var
            fields.push(("Eq0".to_string(), JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(JsExpr::Var(eq_hoisted_var.clone()))],
            )));
            // Add the hoisted Eq instance var to hoisted_vars
            // var eqMaybe1 = eqMaybe(dictOrd.Eq0())
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
            // Store as extra hoisted var for constraint 0
            hoisted_vars.push((0, eq_hoisted_var, HoistedKind::DirectExpr(eq_applied)));
        }
    }

    let mut obj: JsExpr = JsExpr::ObjectLit(fields);

    // Wrap in constraint functions with hoisted dict method vars
    if !constraints.is_empty() {
        // Build from inside out: each constraint wraps the current obj
        // with a function that hoists the dict method call
        for (ci, _constraint) in constraints.iter().enumerate().rev() {
            let dict_param = &dict_params_for_all[ci];
            let mut fn_body: Vec<JsStmt> = Vec::new();
            // Add all hoisted vars for this constraint level
            for (constraint_idx, var_name, kind) in &hoisted_vars {
                if *constraint_idx != ci { continue; }
                match kind {
                    HoistedKind::MethodApply(method_ref) => {
                        fn_body.push(JsStmt::VarDecl(
                            var_name.clone(),
                            Some(JsExpr::App(
                                Box::new(method_ref.clone()),
                                vec![JsExpr::Var(dict_param.clone())],
                            )),
                        ));
                    }
                    HoistedKind::DirectExpr(expr) => {
                        fn_body.push(JsStmt::VarDecl(
                            var_name.clone(),
                            Some(expr.clone()),
                        ));
                    }
                }
            }
            fn_body.push(JsStmt::Return(obj));
            obj = JsExpr::Function(None, vec![dict_param.clone()], fn_body);
        }
    }

    vec![JsStmt::VarDecl(instance_name, Some(obj))]
}

/// Generate derive newtype instance: delegates to the underlying type's instance.
/// `derive newtype instance showName :: Show Name` → uses the Show String instance.
fn gen_derive_newtype_instance(
    ctx: &CodegenCtx,
    instance_name: &str,
    _class_str: &str,
    class_name: &QualifiedIdent,
    types: &[crate::cst::TypeExpr],
    constraints: &[Constraint],
) -> Vec<JsStmt> {
    // For derive newtype, we just reference the underlying instance
    // The typechecker has already validated this is valid
    let head_type = extract_head_type_con_from_cst(types);

    // Find the newtype's underlying type and look up its instance
    let mut obj = if let Some(head) = head_type {
        // Look for the underlying type's instance in the registry
        let qi = unqualified(head);
        if let Some(ctor_names) = ctx.data_constructors.get(&qi) {
            if let Some(ctor_qi) = ctor_names.first() {
                if let Some((_, _, field_types)) = ctx.ctor_details.get(ctor_qi) {
                    if let Some(underlying_ty) = field_types.first() {
                        // Extract the head type con from the underlying type
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
            // For derive newtype, pass the constraint dict through
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
/// `hoisted_eq_vars` contains the hoisted variable names for each constraint's eq method
/// (e.g., `["eq1"]` for single constraint, `["eq1", "eq2"]` for two constraints).
/// When empty (unconstrained), uses strict equality for field comparison.
fn gen_derive_eq_methods(
    ctors: &[(String, usize)],
    hoisted_eq_vars: &[String],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    let mut body = Vec::new();
    let is_sum = ctors.len() > 1 || (ctors.len() == 1 && ctors[0].1 == 0);

    for (ctor_name, field_count) in ctors {
        if *field_count == 0 {
            // Nullary constructor: instanceof check → return true
            let x_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
            );
            let y_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(y.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
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
            for i in 0..*field_count {
                let field_name = format!("value{i}");
                let x_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::StringLit(field_name)),
                );
                let eq_call = if i < hoisted_eq_vars.len() {
                    // Use hoisted eq var: eqN(x.valueI)(y.valueI)
                    JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(JsExpr::Var(hoisted_eq_vars[i].clone())),
                            vec![x_field],
                        )),
                        vec![y_field],
                    )
                } else {
                    // Strict equality for primitive fields
                    JsExpr::Binary(JsBinaryOp::StrictEq, Box::new(x_field), Box::new(y_field))
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
                    Box::new(JsExpr::Var(ctor_name.clone())),
                );
                let y_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::Var(ctor_name.clone())),
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
    if is_sum {
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

/// Generate `compare` method for derive Ord.
/// Returns Data_Ordering.LT/EQ/GT based on constructor order and field comparison.
/// `hoisted_compare_vars` contains the hoisted variable names for each constraint's compare method.
fn gen_derive_ord_methods(
    ctx: &CodegenCtx,
    ctors: &[(String, usize)],
    hoisted_compare_vars: &[String],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    // Resolve Data_Ordering.EQ/LT/GT references
    let ordering_eq = resolve_ordering_ref(ctx, "EQ");
    let ordering_lt = resolve_ordering_ref(ctx, "LT");
    let ordering_gt = resolve_ordering_ref(ctx, "GT");

    let mut body = Vec::new();

    for (_i, (ctor_name, field_count)) in ctors.iter().enumerate() {
        let x_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );
        let y_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(y.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );
        let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check.clone()), Box::new(y_check.clone()));

        if *field_count == 0 {
            // Both same nullary: return EQ
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(ordering_eq.clone())],
                None,
            ));
        } else {
            // Both same with fields: compare fields
            let mut inner_body = Vec::new();
            for fi in 0..*field_count {
                let field_name = format!("value{fi}");
                let x_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::StringLit(field_name)),
                );
                if fi < hoisted_compare_vars.len() {
                    // Use hoisted compare var: compareN(x.valueI)(y.valueI)
                    inner_body.push(JsStmt::Return(JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(JsExpr::Var(hoisted_compare_vars[fi].clone())),
                            vec![x_field],
                        )),
                        vec![y_field],
                    )));
                }
            }
            if inner_body.is_empty() {
                inner_body.push(JsStmt::Return(ordering_eq.clone()));
            }
            body.push(JsStmt::If(both_check, inner_body, None));
        }

        // If only x matches this ctor: x comes before y → LT
        // Skip LT/GT for the last constructor — it's the catch-all before the throw
        if ctors.len() > 1 && _i < ctors.len() - 1 {
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
fn gen_derive_functor_methods(ctx: &CodegenCtx, ctors: &[(String, usize)]) -> Vec<(String, JsExpr)> {
    let f = "f".to_string();
    let m = "m".to_string();

    let mut body = Vec::new();
    let is_sum = ctors.len() > 1 || (ctors.len() == 1 && ctors[0].1 == 0);

    for (ctor_name, field_count) in ctors {
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
            let field_types = ctx.ctor_details.get(&ctor_qi)
                .map(|(parent, type_vars, ftypes)| {
                    let last_tv = type_vars.last().map(|qi| qi.name);
                    let parent_name = parent.name;
                    ftypes.iter().map(|ft| categorize_functor_field(ft, last_tv, parent_name)).collect::<Vec<_>>()
                })
                .unwrap_or_else(|| vec![FunctorFieldKind::Direct; *field_count]);

            // Build args for new Ctor(arg0, arg1, ...)
            let mut args = Vec::new();
            for i in 0..*field_count {
                let field_access = JsExpr::Indexer(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::StringLit(format!("value{i}"))),
                );
                let kind = field_types.get(i).copied().unwrap_or(FunctorFieldKind::Direct);
                let arg = match kind {
                    FunctorFieldKind::Direct => {
                        // f(m.valueN)
                        JsExpr::App(Box::new(JsExpr::Var(f.clone())), vec![field_access])
                    }
                    FunctorFieldKind::Recursive(instance_name) => {
                        // Data_Functor.map(functorSelf)(f)(m.valueN)
                        let inst_js = ident_to_js(instance_name);
                        let map_ref = resolve_functor_map_ref(ctx);
                        JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(JsExpr::App(
                                    Box::new(map_ref),
                                    vec![JsExpr::Var(inst_js)],
                                )),
                                vec![JsExpr::Var(f.clone())],
                            )),
                            vec![field_access],
                        )
                    }
                    FunctorFieldKind::Passthrough => {
                        // Pass through unchanged
                        field_access
                    }
                };
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

#[derive(Debug, Clone, Copy)]
enum FunctorFieldKind {
    /// The field is the type variable directly (a) → apply f
    Direct,
    /// The field is a recursive application (F a) → apply map(functorF)(f)
    Recursive(Symbol),
    /// The field is a concrete type not involving the type var → pass through
    Passthrough,
}

/// Categorize a constructor field for Functor deriving.
fn categorize_functor_field(
    ty: &crate::typechecker::types::Type,
    last_type_var: Option<Symbol>,
    parent_type: Symbol,
) -> FunctorFieldKind {
    use crate::typechecker::types::Type;
    match ty {
        Type::Var(v) if last_type_var == Some(*v) => FunctorFieldKind::Direct,
        Type::App(head, _arg) => {
            // Extract the head type constructor from nested Apps
            let head_con = extract_app_head(head);
            if let Some(con_name) = head_con {
                if con_name == parent_type {
                    // Recursive: the same type constructor applied to the type var
                    let type_str = interner::resolve(parent_type).unwrap_or_default();
                    let instance_name = format!("functor{type_str}");
                    return FunctorFieldKind::Recursive(interner::intern(&instance_name));
                }
            }
            // Check if the type involves the type var at all
            if last_type_var.is_some() && type_contains_var(ty, last_type_var.unwrap()) {
                FunctorFieldKind::Direct
            } else {
                FunctorFieldKind::Passthrough
            }
        }
        _ => {
            if last_type_var.is_some() && type_contains_var(ty, last_type_var.unwrap()) {
                FunctorFieldKind::Direct
            } else {
                FunctorFieldKind::Passthrough
            }
        }
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

/// Generate methods for derive Newtype class.
/// The original compiler only emits Coercible0: function() { return undefined; }
fn gen_derive_newtype_class_methods() -> Vec<(String, JsExpr)> {
    vec![]
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
            // Single-arg ctor: store value directly (no Argument wrapper)
            wrap_in_sum(JsExpr::Indexer(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::StringLit("value0".to_string())),
            ))
        } else {
            // Multi-field: build Product chain
            let mut product = JsExpr::New(
                Box::new(rep_ref("Argument")),
                vec![JsExpr::Indexer(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::StringLit(format!("value{}", field_count - 1))),
                )],
            );
            for fi in (0..field_count - 1).rev() {
                product = JsExpr::New(
                    Box::new(rep_ref("Product")),
                    vec![
                        JsExpr::New(
                            Box::new(rep_ref("Argument")),
                            vec![JsExpr::Indexer(
                                Box::new(JsExpr::Var(x.clone())),
                                Box::new(JsExpr::StringLit(format!("value{fi}"))),
                            )],
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
    // For 3+ constructors: first is Inl, middle are Inr(Inl), last is Inr(Inr)
    if idx == 0 {
        JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inl")))
    } else if idx < total - 1 {
        // x instanceof Inr && x.value0 instanceof Inl
        let outer = JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inr")));
        let inner = JsExpr::InstanceOf(
            Box::new(JsExpr::Indexer(
                Box::new(JsExpr::Var(x.to_string())),
                Box::new(JsExpr::StringLit("value0".to_string())),
            )),
            Box::new(rep_ref("Inl")),
        );
        JsExpr::Binary(JsBinaryOp::And, Box::new(outer), Box::new(inner))
    } else {
        // Last: x instanceof Inr && x.value0 instanceof Inr
        let outer = JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inr")));
        let inner = JsExpr::InstanceOf(
            Box::new(JsExpr::Indexer(
                Box::new(JsExpr::Var(x.to_string())),
                Box::new(JsExpr::StringLit("value0".to_string())),
            )),
            Box::new(rep_ref("Inr")),
        );
        JsExpr::Binary(JsBinaryOp::And, Box::new(outer), Box::new(inner))
    }
}

/// Unwrap the generic arg from the Inl/Inr sum tree at position idx.
fn gen_generic_unwrap_arg(rep_ref: &dyn Fn(&str) -> JsExpr, x: &str, idx: usize, total: usize) -> JsExpr {
    let _ = rep_ref;
    if total == 1 {
        return JsExpr::Var(x.to_string());
    }
    if idx == 0 {
        // x.value0 (unwrap Inl)
        JsExpr::Indexer(
            Box::new(JsExpr::Var(x.to_string())),
            Box::new(JsExpr::StringLit("value0".to_string())),
        )
    } else if total == 2 {
        // x.value0 (unwrap Inr)
        JsExpr::Indexer(
            Box::new(JsExpr::Var(x.to_string())),
            Box::new(JsExpr::StringLit("value0".to_string())),
        )
    } else {
        // x.value0.value0 (unwrap Inr then Inl/Inr)
        JsExpr::Indexer(
            Box::new(JsExpr::Indexer(
                Box::new(JsExpr::Var(x.to_string())),
                Box::new(JsExpr::StringLit("value0".to_string())),
            )),
            Box::new(JsExpr::StringLit("value0".to_string())),
        )
    }
}

/// Extract a field from a Product chain at position fi.
fn gen_generic_product_field(_rep_ref: &dyn Fn(&str) -> JsExpr, inner: &JsExpr, fi: usize, total: usize) -> JsExpr {
    if total == 1 {
        // Single field: inner.value0
        JsExpr::Indexer(
            Box::new(inner.clone()),
            Box::new(JsExpr::StringLit("value0".to_string())),
        )
    } else if fi < total - 1 {
        // Product: inner.value0.value0 (first), inner.value1.value0 (second of product chain)
        // Actually Product(a, b) has value0=a, value1=b
        // For field 0: inner.value0.value0
        // For field 1 of 3: inner.value1.value0.value0
        // This gets complex. For simplicity:
        let mut expr = inner.clone();
        for _ in 0..fi {
            expr = JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())));
        }
        JsExpr::Indexer(
            Box::new(JsExpr::Indexer(
                Box::new(expr),
                Box::new(JsExpr::StringLit("value0".to_string())),
            )),
            Box::new(JsExpr::StringLit("value0".to_string())),
        )
    } else {
        // Last field: navigate to the end of the product chain
        let mut expr = inner.clone();
        for _ in 0..fi {
            expr = JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())));
        }
        JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value0".to_string())))
    }
}

/// Wrap a value in Inl/Inr constructors for the generic sum position.
fn gen_generic_inl_inr_wrap(rep_ref: &dyn Fn(&str) -> JsExpr, inner: JsExpr, idx: usize, total: usize) -> JsExpr {
    if total == 1 {
        return inner;
    }
    if idx == 0 {
        // First: wrap in Inl
        JsExpr::New(Box::new(rep_ref("Inl")), vec![inner])
    } else if idx < total - 1 {
        // Middle: Inr(Inl(inner))
        JsExpr::New(
            Box::new(rep_ref("Inr")),
            vec![JsExpr::New(Box::new(rep_ref("Inl")), vec![inner])],
        )
    } else {
        // Last: Inr(Inr(...)) — but for 3 ctors it's Inr(Inr(inner))
        // Actually for the last one: wrap in as many Inr as needed
        let mut wrapped = inner;
        // For total=3, idx=2: Inr(Inr(value))
        // For total=2, idx=1: Inr(value)
        for _ in 0..(total - 1 - (total - 2).min(idx - 1).min(1)) {
            // This is getting complex. Let's simplify:
            // For total=2: idx=1 → Inr(inner)
            // For total=3: idx=1 → Inr(Inl(inner)), idx=2 → Inr(Inr(inner))
            break;
        }
        // Simple: last element is wrapped in enough Inrs
        if total == 2 {
            JsExpr::New(Box::new(rep_ref("Inr")), vec![wrapped])
        } else {
            // For idx = total-1, wrap in Inr(Inr(...))
            wrapped = JsExpr::New(Box::new(rep_ref("Inr")), vec![wrapped]);
            // Need idx-1 more Inr wrappings? No...
            // Actually for 3 ctors: idx=2 is Inr(Inr(NoArguments))
            // But we already wrapped once, so wrap once more
            for _ in 1..idx {
                // No, this isn't right either. Let me think...
                // For 3 ctors: 0=Inl, 1=Inr(Inl), 2=Inr(Inr)
                // So for idx=2 in total=3: new Inr(new Inr(inner)) — but only 1 Inr already added
            }
            // Just wrap in one more Inr for total >= 3 and idx == total-1
            wrapped = JsExpr::New(Box::new(rep_ref("Inr")), vec![wrapped]);
            wrapped
        }
    }
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

    // Extract head type constructor from instance types (for registry lookup)
    let head_type = extract_head_type_con_from_cst(instance_types);

    for (idx, (super_class_qi, _super_args)) in superclasses.iter().enumerate() {
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
        } else if let Some(head) = head_type {
            // Look up the superclass instance for the same head type
            resolve_instance_ref(ctx, super_class_qi.name, head)
        } else {
            continue;
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
    ctx.all_class_superclasses.get(&class_name).cloned().unwrap_or_default()
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
        Expr::RecordUpdate { expr, .. } => contains_wildcard(expr),
        _ => false,
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
        Expr::Var { span, name, .. } => gen_qualified_ref_with_span(ctx, name, Some(*span)),

        Expr::Constructor { name, .. } => {
            let ctor_name = name.name;
            // Check if nullary (use .value) or n-ary (use .create)
            if let Some((_, _, fields)) = ctx.ctor_details.get(&unqualified(ctor_name)) {
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
                // Newtype constructor is identity function — just reference it
                gen_qualified_ref_raw(ctx, name)
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
            let f = gen_expr(ctx, func);
            let a = gen_expr(ctx, arg);
            JsExpr::App(Box::new(f), vec![a])
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
            let body_expr = gen_expr(ctx, body);
            *ctx.local_bindings.borrow_mut() = prev_bindings;
            gen_curried_function(ctx, binders, vec![JsStmt::Return(body_expr)])
        }

        Expr::Op { left, op, right, .. } => {
            gen_op_chain(ctx, left, op, right)
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
            JsExpr::Unary(JsUnaryOp::Negate, Box::new(e))
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

    // If this is a class method and we have a matching dict in scope, apply it
    if let Some(dict_app) = try_apply_dict(ctx, qident, base.clone(), span) {
        return dict_app;
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
                if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, class_qi.name) {
                    return Some(JsExpr::App(Box::new(base), vec![dict_expr]));
                }
            }
        }

        // Second, check if this is a constrained function (not a class method but has constraints)
        let fn_constraints = find_fn_constraints(ctx, qident);
        if !fn_constraints.is_empty() {
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
            // Fall through to resolved_dict_map if scope couldn't resolve all dicts
        }
    }

    // Drop the scope borrow before trying resolved_dict_map
    drop(scope);

    // Fallback: try resolved_dict_map for module-level dict resolution
    try_apply_resolved_dict(ctx, qident, base.clone(), span)
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
                let js_dict = dict_expr_to_js(ctx, dict_expr);
                return Some(JsExpr::App(Box::new(base), vec![js_dict]));
            }
        }
    }

    // Apply all resolved dicts at this span, deduplicating by class name.
    // This handles: constrained functions, let-bound constrained functions,
    // and class methods where the class name didn't match all_class_methods
    // (e.g. methods from support modules with different symbol interning).
    let mut result = base;
    let mut seen_classes: HashSet<Symbol> = HashSet::new();
    for (class_name, dict_expr) in dicts {
        if seen_classes.insert(*class_name) {
            let js_dict = dict_expr_to_js(ctx, dict_expr);
            result = JsExpr::App(Box::new(result), vec![js_dict]);
        }
    }
    Some(result)
}

/// Convert a DictExpr from the typechecker into a JS expression.
fn dict_expr_to_js(ctx: &CodegenCtx, dict: &crate::typechecker::registry::DictExpr) -> JsExpr {
    use crate::typechecker::registry::DictExpr;
    match dict {
        DictExpr::Var(name) => {
            let js_name = ident_to_js(*name);
            // Check if local or imported
            if ctx.local_names.contains(name) {
                JsExpr::Var(js_name)
            } else if let Some(source_parts) = ctx.name_source.get(name) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    JsExpr::ModuleAccessor(js_mod.clone(), js_name.clone())
                } else {
                    JsExpr::Var(js_name)
                }
            } else if let Some(source) = ctx.instance_sources.get(name) {
                match source {
                    None => JsExpr::Var(js_name),
                    Some(parts) => {
                        if let Some(js_mod) = ctx.import_map.get(parts) {
                            JsExpr::ModuleAccessor(js_mod.clone(), js_name.clone())
                        } else {
                            JsExpr::Var(js_name)
                        }
                    }
                }
            } else {
                // Fallback: search imported modules for this instance name
                // (handles transitive re-exports, e.g., import Prelude → showNumber from Data.Show)
                let mut found = None;
                for (mod_parts, js_mod) in &ctx.import_map {
                    if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
                        // Check instance_registry
                        for (_, inst_name) in &mod_exports.instance_registry {
                            if *inst_name == *name {
                                found = Some(JsExpr::ModuleAccessor(js_mod.clone(), js_name.clone()));
                                break;
                            }
                        }
                        if found.is_some() { break; }
                        // Also check if it's a value exported by this module
                        if mod_exports.values.contains_key(&unqualified(*name)) {
                            found = Some(JsExpr::ModuleAccessor(js_mod.clone(), js_name.clone()));
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
            for sub in sub_dicts {
                let sub_js = dict_expr_to_js(ctx, sub);
                result = JsExpr::App(Box::new(result), vec![sub_js]);
            }
            result
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
    if let Some(supers) = ctx.all_class_superclasses.get(&from_class) {
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

fn gen_qualified_ref_raw(ctx: &CodegenCtx, qident: &QualifiedIdent) -> JsExpr {
    let js_name = ident_to_js(qident.name);

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
            // Check if this is an imported name
            if let Some(source_parts) = ctx.name_source.get(&qident.name) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), js_name);
                }
            }
            // Check if this is an imported instance (globally visible)
            if let Some(Some(source_parts)) = ctx.instance_sources.get(&qident.name) {
                if let Some(js_mod) = ctx.import_map.get(source_parts) {
                    return JsExpr::ModuleAccessor(js_mod.clone(), js_name);
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
                            return JsExpr::ModuleAccessor((*js_mod).clone(), js_name);
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
        GuardedExpr::Unconditional(expr) => gen_return_stmts(ctx, expr),
        GuardedExpr::Guarded(guards) => gen_guards_stmts(ctx, guards),
    }
}

/// Generate return statements for an expression. For case expressions, this
/// inlines the if/instanceof chains directly instead of wrapping in an IIFE.
fn gen_return_stmts(ctx: &CodegenCtx, expr: &Expr) -> Vec<JsStmt> {
    match expr {
        Expr::Case { exprs, alts, .. } => gen_case_stmts(ctx, exprs, alts),
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
            *ctx.local_bindings.borrow_mut() = prev_bindings;
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
    let scrut_names: Vec<String> = scrut_exprs.iter().enumerate().map(|(i, e)| {
        if let JsExpr::Var(name) = e {
            name.clone()
        } else {
            let name = ctx.fresh_name(&format!("case{i}_"));
            stmts.push(JsStmt::VarDecl(name.clone(), Some(e.clone())));
            name
        }
    }).collect();

    let mut has_unconditional = false;
    for alt in alts {
        let (cond, bindings) = gen_binders_match(ctx, &alt.binders, &scrut_names);
        let mut alt_body = Vec::new();
        alt_body.extend(bindings);

        let result_stmts = gen_guarded_expr_stmts(ctx, &alt.result);
        alt_body.extend(result_stmts);
        // Inline binding-then-return: var x = <expr>; return x; → return <expr>;
        inline_single_use_bindings(&mut alt_body);

        if let Some(cond) = cond {
            stmts.push(JsStmt::If(cond, alt_body, None));
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

fn gen_guards_expr(ctx: &CodegenCtx, guards: &[Guard]) -> JsExpr {
    // Build nested ternary: cond1 ? e1 : cond2 ? e2 : error
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
        let cond = gen_guard_condition(ctx, &guard.patterns);
        let body = gen_expr(ctx, &guard.expr);
        // If guard condition is `true` (i.e. `| otherwise`), emit return directly
        if matches!(&cond, JsExpr::BoolLit(true)) {
            stmts.push(JsStmt::Return(body));
            return stmts;
        }
        stmts.push(JsStmt::If(
            cond,
            vec![JsStmt::Return(body)],
            None,
        ));
    }
    stmts.push(JsStmt::Throw(JsExpr::New(
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

    // Pre-generate param names in forward order so wildcards get v, v1, v2...
    let param_names: Vec<Option<String>> = binders.iter().map(|b| {
        match b {
            Binder::Var { .. } => None, // Will use the actual var name
            Binder::Wildcard { .. } => Some(ctx.fresh_name("v")),
            _ => Some(ctx.fresh_name("v")),
        }
    }).collect();

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
                    }
                }

                // Push dict scope entries for constraints
                let prev_scope_len = ctx.dict_scope.borrow().len();
                if let Some(ref constraints) = constraints {
                    for (class_qi, _) in constraints {
                        let class_name_str = interner::resolve(class_qi.name).unwrap_or_default();
                        let dict_param = format!("dict{class_name_str}");
                        ctx.dict_scope.borrow_mut().push((class_qi.name, dict_param));
                    }
                }

                let group = &bindings[start..i];
                if group.len() == 1 {
                    // Single equation — generate normally
                    if let LetBinding::Value { expr, .. } = &group[0] {
                        let mut val = gen_expr(ctx, expr);
                        val = wrap_with_dict_params(val, constraints.as_ref());
                        let js_name = ident_to_js(binding_name);
                        stmts.push(JsStmt::VarDecl(js_name, Some(val)));
                    }
                } else {
                    // Multi-equation: collect the lambda bodies and compile as case alternatives
                    let js_name = ident_to_js(binding_name);
                    let mut result = gen_multi_equation_let(ctx, &js_name, group);
                    if let Some(ref constraints) = constraints {
                        if !constraints.is_empty() {
                            if let Some(JsStmt::VarDecl(_, Some(expr))) = result.first_mut() {
                                *expr = wrap_with_dict_params(expr.clone(), Some(constraints));
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

    let params: Vec<String> = (0..arity).map(|i| ctx.fresh_name(&format!("arg{i}_"))).collect();

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
            let value = gen_expr(ctx, &update.value);
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
            // discard(dictBind)(action)(function() { return rest; })
            let discard_sym = interner::intern("discard");
            let discard_qi = QualifiedIdent {
                module: qual_mod.copied(),
                name: discard_sym,
            };
            let discard_ref = gen_qualified_ref_with_span(ctx, &discard_qi, Some(*span));
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(discard_ref),
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

fn make_qualified_ref_with_span(ctx: &CodegenCtx, qual_mod: Option<&Ident>, name: &str, span: Option<crate::span::Span>) -> JsExpr {
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
                        resolved = Some(JsExpr::ModuleAccessor(js_mod.clone(), any_name_to_js(name)));
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
                    resolved = Some(JsExpr::ModuleAccessor(js_mod.clone(), any_name_to_js(name)));
                    break;
                }
            }
        }
        resolved.unwrap_or_else(|| {
            let js_mod = any_name_to_js(&mod_str.replace('.', "_"));
            JsExpr::ModuleAccessor(js_mod, any_name_to_js(name))
        })
    } else {
        let name_sym = interner::intern(name);
        if let Some(source_parts) = ctx.name_source.get(&name_sym) {
            if let Some(js_mod) = ctx.import_map.get(source_parts) {
                JsExpr::ModuleAccessor(js_mod.clone(), any_name_to_js(name))
            } else {
                JsExpr::Var(any_name_to_js(name))
            }
        } else {
            // Search imported modules for class methods (e.g., bind from do-notation)
            let name_sym2 = interner::intern(name);
            let mut found_mod = None;
            if ctx.all_class_methods.contains_key(&name_sym2) {
                // Sort import_map entries for deterministic output
                let mut sorted_imports: Vec<_> = ctx.import_map.iter().collect();
                sorted_imports.sort_by_key(|(_, js_mod)| js_mod.clone());
                for (mod_parts, js_mod) in sorted_imports {
                    if let Some(mod_exports) = ctx.registry.lookup(mod_parts) {
                        if mod_exports.class_methods.contains_key(&unqualified(name_sym2))
                            || mod_exports.values.contains_key(&unqualified(name_sym2)) {
                            found_mod = Some(JsExpr::ModuleAccessor(js_mod.clone(), any_name_to_js(name)));
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
        JsStmt::ReturnVoid | JsStmt::Comment(_) | JsStmt::Import { .. }
        | JsStmt::Export(_) | JsStmt::ExportFrom(_, _) | JsStmt::RawJs(_)
        => {}
    }
}

/// Generate code for an operator expression, handling operator precedence via shunting-yard.
/// The CST parses operator chains as right-associative trees, but we need to respect
/// declared fixities (e.g., `*` binds tighter than `+`).
fn gen_op_chain(ctx: &CodegenCtx, left: &Expr, op: &Spanned<QualifiedIdent>, right: &Expr) -> JsExpr {
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
        return gen_single_op(ctx, &operands[0], operators[0], &operands[1]);
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
fn gen_single_op(ctx: &CodegenCtx, left: &Expr, op: &Spanned<QualifiedIdent>, right: &Expr) -> JsExpr {
    let op_ref = resolve_op_ref(ctx, op, Some(op.span));
    let l = gen_expr(ctx, left);
    let r = gen_expr(ctx, right);
    JsExpr::App(
        Box::new(JsExpr::App(Box::new(op_ref), vec![l])),
        vec![r],
    )
}

/// Apply an operator to two JS expressions.
fn apply_op(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>, lhs: JsExpr, rhs: JsExpr) -> JsExpr {
    let op_ref = resolve_op_ref(ctx, op, Some(op.span));
    JsExpr::App(
        Box::new(JsExpr::App(Box::new(op_ref), vec![lhs])),
        vec![rhs],
    )
}

/// Resolve an operator to its JS reference (target function + dict application).
fn resolve_op_ref(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>, expr_span: Option<crate::span::Span>) -> JsExpr {
    let op_sym = op.value.name;
    // Use expr_span for dict lookup (matches typechecker's span for OpParens vs Op)
    let lookup_span = expr_span.or(Some(op.span));
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
            let target_qi = QualifiedIdent { module: None, name: *target_name };
            gen_qualified_ref_with_span(ctx, &target_qi, lookup_span)
        } else if let Some(parts) = source_parts {
            // Target not in name_source — resolve via operator's source module
            if let Some(js_mod) = ctx.import_map.get(parts) {
                let target_js = ident_to_js(*target_name);
                let base = JsExpr::ModuleAccessor(js_mod.clone(), target_js);
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

/// Topologically sort VarDecl statements so dependencies come first.
/// Non-VarDecl statements maintain their relative position.
fn topo_sort_body(body: Vec<JsStmt>) -> Vec<JsStmt> {
    // Build dependency graph for VarDecl statements
    let mut decl_indices: HashMap<String, usize> = HashMap::new();
    let mut decl_refs: Vec<HashSet<String>> = Vec::new();

    for (i, stmt) in body.iter().enumerate() {
        if let JsStmt::VarDecl(name, _) = stmt {
            decl_indices.insert(name.clone(), i);
        }
    }

    // For each VarDecl, find which other VarDecls it references
    // Only consider "eager" references (not inside function bodies)
    for stmt in &body {
        let mut refs = HashSet::new();
        if let JsStmt::VarDecl(_, Some(expr)) = stmt {
            collect_eager_refs(expr, &mut refs);
        }
        decl_refs.push(refs);
    }

    // Simple topological sort using DFS
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

        for dep_name in &decl_refs[i] {
            if let Some(&dep_idx) = decl_indices.get(dep_name) {
                if dep_idx != i {
                    visit(dep_idx, body, decl_indices, decl_refs, visited, in_stack, order);
                }
            }
        }

        in_stack[i] = false;
        visited[i] = true;
        order.push(i);
    }

    for i in 0..n {
        visit(i, &body, &decl_indices, &decl_refs, &mut visited, &mut in_stack, &mut order);
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

/// Collect "eager" variable references — references that execute at load time,
/// NOT inside function bodies (which are deferred).
fn collect_eager_refs(expr: &JsExpr, refs: &mut HashSet<String>) {
    match expr {
        JsExpr::Var(name) => { refs.insert(name.clone()); }
        JsExpr::App(f, args) => {
            // Detect IIFEs: App(Function(_, _, body), []) — the body executes eagerly
            if args.is_empty() {
                if let JsExpr::Function(_, _, body) = f.as_ref() {
                    for stmt in body {
                        collect_eager_refs_stmt(stmt, refs);
                    }
                } else {
                    collect_eager_refs(f, refs);
                }
            } else {
                collect_eager_refs(f, refs);
                for a in args { collect_eager_refs(a, refs); }
            }
        }
        JsExpr::Function(_, _, _) => {
            // Function bodies are deferred — don't collect refs from inside
        }
        JsExpr::ArrayLit(elems) => {
            for e in elems { collect_eager_refs(e, refs); }
        }
        JsExpr::ObjectLit(fields) => {
            for (_, v) in fields { collect_eager_refs(v, refs); }
        }
        JsExpr::Indexer(a, b) => {
            collect_eager_refs(a, refs);
            collect_eager_refs(b, refs);
        }
        JsExpr::Unary(_, e) => collect_eager_refs(e, refs),
        JsExpr::Binary(_, a, b) => {
            collect_eager_refs(a, refs);
            collect_eager_refs(b, refs);
        }
        JsExpr::Ternary(c, t, e) => {
            collect_eager_refs(c, refs);
            collect_eager_refs(t, refs);
            collect_eager_refs(e, refs);
        }
        JsExpr::InstanceOf(a, b) => {
            collect_eager_refs(a, refs);
            collect_eager_refs(b, refs);
        }
        JsExpr::New(f, args) => {
            collect_eager_refs(f, refs);
            for a in args { collect_eager_refs(a, refs); }
        }
        JsExpr::ModuleAccessor(_, _) | JsExpr::NumericLit(_) | JsExpr::IntLit(_)
        | JsExpr::StringLit(_) | JsExpr::BoolLit(_) | JsExpr::RawJs(_) => {}
    }
}


/// Collect eager refs from a JS statement (for IIFE body traversal).
fn collect_eager_refs_stmt(stmt: &JsStmt, refs: &mut HashSet<String>) {
    match stmt {
        JsStmt::VarDecl(_, Some(expr)) => collect_eager_refs(expr, refs),
        JsStmt::VarDecl(_, None) => {}
        JsStmt::Return(expr) => collect_eager_refs(expr, refs),
        JsStmt::Throw(expr) => collect_eager_refs(expr, refs),
        JsStmt::If(cond, then_stmts, else_stmts) => {
            collect_eager_refs(cond, refs);
            for s in then_stmts { collect_eager_refs_stmt(s, refs); }
            if let Some(else_s) = else_stmts {
                for s in else_s { collect_eager_refs_stmt(s, refs); }
            }
        }
        JsStmt::Expr(expr) => collect_eager_refs(expr, refs),
        JsStmt::Assign(_, expr) => collect_eager_refs(expr, refs),
        JsStmt::Block(stmts) | JsStmt::While(_, stmts) => {
            for s in stmts { collect_eager_refs_stmt(s, refs); }
        }
        JsStmt::For(_, init, bound, stmts) => {
            collect_eager_refs(init, refs);
            collect_eager_refs(bound, refs);
            for s in stmts { collect_eager_refs_stmt(s, refs); }
        }
        JsStmt::ForIn(_, obj, stmts) => {
            collect_eager_refs(obj, refs);
            for s in stmts { collect_eager_refs_stmt(s, refs); }
        }
        _ => {}
    }
}

/// Extract head type constructor from CST type expressions.
fn extract_head_type_con_from_cst(types: &[crate::cst::TypeExpr]) -> Option<Symbol> {
    types.first().and_then(|t| extract_head_from_type_expr(t))
}

fn extract_head_from_type_expr(te: &crate::cst::TypeExpr) -> Option<Symbol> {
    use crate::cst::TypeExpr;
    match te {
        TypeExpr::Constructor { name, .. } => Some(name.name),
        TypeExpr::App { constructor, .. } => extract_head_from_type_expr(constructor),
        TypeExpr::Record { .. } => Some(interner::intern("Record")),
        TypeExpr::Forall { ty, .. } => extract_head_from_type_expr(ty),
        TypeExpr::Constrained { ty, .. } => extract_head_from_type_expr(ty),
        TypeExpr::Parens { ty, .. } => extract_head_from_type_expr(ty),
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
        _ => None,
    }
}

/// Check if a CST type expression has a Partial constraint.
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
