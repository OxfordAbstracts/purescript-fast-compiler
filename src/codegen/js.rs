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

use super::common::{any_name_to_js, ident_to_js, module_name_to_js};
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
    newtype_names: &'a HashSet<Symbol>,
    /// Mapping from constructor name → (parent_type, type_vars, field_types)
    ctor_details: &'a HashMap<QualifiedIdent, (QualifiedIdent, Vec<QualifiedIdent>, Vec<crate::typechecker::types::Type>)>,
    /// Data type → constructor names (to determine sum vs product)
    data_constructors: &'a HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
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
    /// Pre-built: class method → (class_name, type_vars)
    all_class_methods: HashMap<Symbol, (QualifiedIdent, Vec<QualifiedIdent>)>,
    /// Pre-built: fn_name → constraint class names (from signature_constraints)
    all_fn_constraints: HashMap<Symbol, Vec<Symbol>>,
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
                                        name_source.entry(n.value).or_insert_with(|| parts.clone());
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
                                    // Import class method names
                                    for (method_qi, (class_qi, _)) in &mod_exports.class_methods {
                                        if class_qi.name == n.value {
                                            if !local_names.contains(&method_qi.name) {
                                                name_source.entry(method_qi.name).or_insert_with(|| parts.clone());
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
        newtype_names: &exports.newtype_names,
        ctor_details: &exports.ctor_details,
        data_constructors: &exports.data_constructors,
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
        all_fn_constraints: HashMap::new(),
        all_class_superclasses: HashMap::new(),
        resolved_dict_map: exports.resolved_dicts.clone(),
        partial_fns,
        op_fixities: HashMap::new(),
        wildcard_params: std::cell::RefCell::new(Vec::new()),
        known_runtime_classes: HashSet::new(),
        local_bindings: std::cell::RefCell::new(HashSet::new()),
    };

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
            ctx.all_class_methods.entry(method.name).or_insert_with(|| (class.clone(), tvs.clone()));
        }
        for (name, constraints) in &exports.signature_constraints {
            let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name).collect();
            ctx.all_fn_constraints.entry(name.name).or_insert(class_names);
        }
        for (name, (_, supers)) in &exports.class_superclasses {
            ctx.all_class_superclasses.entry(name.name).or_insert_with(|| supers.clone());
        }
        // From all registry modules
        for (_, mod_exports) in registry.iter_all() {
            for (method, (class, tvs)) in &mod_exports.class_methods {
                ctx.all_class_methods.entry(method.name).or_insert_with(|| (class.clone(), tvs.clone()));
            }
            for (name, constraints) in &mod_exports.signature_constraints {
                let class_names: Vec<Symbol> = constraints.iter().map(|(c, _)| c.name).collect();
                ctx.all_fn_constraints.entry(name.name).or_insert(class_names);
            }
            for (name, (_, supers)) in &mod_exports.class_superclasses {
                ctx.all_class_superclasses.entry(name.name).or_insert_with(|| supers.clone());
            }
        }

        // Build known_runtime_classes: classes that have methods (and thus runtime dictionaries).
        // Type-level classes (IsSymbol, RowToList, Lacks, etc.) have no methods and won't appear here.
        for (_, (class_qi, _)) in &ctx.all_class_methods {
            ctx.known_runtime_classes.insert(class_qi.name);
        }
    }

    let mut exported_names: Vec<String> = Vec::new();
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
        for parts in needed_modules {
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
        for parts in needed_modules {
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
                if let Decl::Data { name: data_name, type_vars, constructors, .. } = decl {
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
                if let Decl::Newtype { name: nt_name, type_vars, constructor, .. } = decl {
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
                let original_name = interner::resolve(*name_sym).unwrap_or_default();
                body.push(JsStmt::VarDecl(
                    js_name.clone(),
                    Some(JsExpr::ModuleAccessor("$foreign".to_string(), original_name)),
                ));
                if is_exported(&ctx, *name_sym) {
                    foreign_re_exports.push(js_name);
                }
            }
            DeclGroup::Instance(decl) => {
                if let Decl::Instance { name: Some(n), .. } = decl {
                    let inst_js = ident_to_js(n.value);
                    // Instances are always exported in PureScript (globally visible)
                    exported_names.push(inst_js);
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
                            exported_names.push(name.clone());
                        }
                    }
                }
                body.extend(stmts);
            }
            DeclGroup::Fixity(decl) => {
                if let Decl::Fixity { operator, target, is_type, .. } = decl {
                    if !is_type {
                        let op_js = ident_to_js(operator.value);
                        let target_js = ident_to_js(target.name);
                        if op_js != target_js {
                            body.push(JsStmt::VarDecl(
                                op_js.clone(),
                                Some(JsExpr::Var(target_js)),
                            ));
                            if is_exported(&ctx, operator.value) {
                                exported_names.push(op_js);
                            }
                        }
                    }
                }
            }
            DeclGroup::Derive(decl) => {
                if let Decl::Derive { name: Some(name), .. } = decl {
                    let inst_js = ident_to_js(name.value);
                    // Instances are always exported in PureScript
                    exported_names.push(inst_js);
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
    for (name_sym, origin_mod_sym) in &exports.value_origins {
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
                exported_names.push(js_name.clone());
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
                    exported_names.push(js_name);
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
            let dict_param = format!("$dict{class_name_str}");
            ctx.dict_scope.borrow_mut().push((class_qi.name, dict_param));
        }
    }

    let mut result = if decls.len() == 1 {
        if let Decl::Value { binders, guarded, where_clause, .. } = decls[0] {
            if binders.is_empty() && where_clause.is_empty() {
                let mut expr = gen_guarded_expr(ctx, guarded);
                expr = wrap_with_dict_params(expr, constraints.as_ref());
                vec![JsStmt::VarDecl(js_name, Some(expr))]
            } else if where_clause.is_empty() {
                let body_expr = gen_guarded_expr_stmts(ctx, guarded);
                let mut func = gen_curried_function(ctx, binders, body_expr);
                func = wrap_with_dict_params(func, constraints.as_ref());
                vec![JsStmt::VarDecl(js_name, Some(func))]
            } else {
                let mut iife_body = Vec::new();
                gen_let_bindings(ctx, where_clause, &mut iife_body);

                if binders.is_empty() {
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
        let dict_param = format!("$dict{class_name}");
        result = JsExpr::Function(
            None,
            vec![dict_param],
            vec![JsStmt::Return(result)],
        );
    }
    result
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

// ===== Class declarations =====

fn gen_class_decl(_ctx: &CodegenCtx, decl: &Decl) -> Vec<JsStmt> {
    let Decl::Class { members, .. } = decl else { return vec![] };

    let mut stmts = Vec::new();
    for member in members {
        let method_js = ident_to_js(member.name.value);
        // Generate: var method = function(dict) { return dict["method"]; };
        let accessor = JsExpr::Function(
            None,
            vec!["$dict".to_string()],
            vec![JsStmt::Return(JsExpr::Indexer(
                Box::new(JsExpr::Var("$dict".to_string())),
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
        let dict_param = format!("$dict{class_name_str}");
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
        for constraint in constraints.iter().rev() {
            let dict_param = constraint_to_dict_param(constraint);
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

    let mut fields: Vec<(String, JsExpr)> = match derive_kind {
        DeriveClass::Eq => gen_derive_eq_methods(ctx, &ctors, constraints),
        DeriveClass::Ord => gen_derive_ord_methods(ctx, &ctors, constraints, class_name, types),
        DeriveClass::Functor => gen_derive_functor_methods(&ctors),
        DeriveClass::Newtype => gen_derive_newtype_class_methods(),
        DeriveClass::Generic => gen_derive_generic_methods(&ctors),
        DeriveClass::Unknown => vec![],
    };

    // Add superclass accessors (e.g., Ord needs Eq0)
    // Only for unconstrained derives — constrained derives pass dicts through
    if constraints.is_empty() {
        gen_superclass_accessors(ctx, class_name, types, constraints, &mut fields);
    }

    let mut obj: JsExpr = JsExpr::ObjectLit(fields);

    // Push dict scope for constraints
    let prev_scope_len = ctx.dict_scope.borrow().len();
    if !constraints.is_empty() {
        for constraint in constraints {
            let c_name_str = interner::resolve(constraint.class.name).unwrap_or_default();
            let dict_param = format!("$dict{c_name_str}");
            ctx.dict_scope.borrow_mut().push((constraint.class.name, dict_param));
        }
        for constraint in constraints.iter().rev() {
            let dict_param = constraint_to_dict_param(constraint);
            obj = JsExpr::Function(
                None,
                vec![dict_param],
                vec![JsStmt::Return(obj)],
            );
        }
    }
    ctx.dict_scope.borrow_mut().truncate(prev_scope_len);

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
/// ```js
/// eq: function(x) { return function(y) {
///   if (x instanceof Red && y instanceof Red) return true;
///   if (x instanceof Just && y instanceof Just) return eq(dictEq)(x.value0)(y.value0);
///   return false;
/// }}
/// ```
fn gen_derive_eq_methods(
    ctx: &CodegenCtx,
    ctors: &[(String, usize)],
    constraints: &[Constraint],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    let mut body = Vec::new();

    for (ctor_name, field_count) in ctors {
        let x_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );
        let y_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(y.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );
        let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check), Box::new(y_check));

        if *field_count == 0 {
            // Nullary constructor: just check both are same constructor
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(JsExpr::BoolLit(true))],
                None,
            ));
        } else {
            // Constructor with fields: compare each field
            let mut field_eq = JsExpr::BoolLit(true);
            // Cast to any to prevent instanceof narrowing by tsc
            let x_any = JsExpr::Var(x.clone());
            let y_any = JsExpr::Var(y.clone());
            for i in 0..*field_count {
                let field_name = format!("value{i}");
                let x_field = JsExpr::Indexer(
                    Box::new(x_any.clone()),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(y_any.clone()),
                    Box::new(JsExpr::StringLit(field_name)),
                );
                // Use eq from dict if we have constraints
                let eq_call = if !constraints.is_empty() {
                    // eq($dictEq)(x.valueN)(y.valueN)
                    let dict_param = constraint_to_dict_param(&constraints[0]);
                    JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(JsExpr::Var("eq".to_string())),
                                vec![JsExpr::Var(dict_param)],
                            )),
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
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(field_eq)],
                None,
            ));
        }
    }

    // Default: constructors don't match
    body.push(JsStmt::Return(JsExpr::BoolLit(false)));

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
/// Returns LT, EQ, or GT based on constructor order and field comparison.
fn gen_derive_ord_methods(
    ctx: &CodegenCtx,
    ctors: &[(String, usize)],
    constraints: &[Constraint],
    class_name: &QualifiedIdent,
    types: &[crate::cst::TypeExpr],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    let mut body = Vec::new();

    // Assign index to each constructor for ordering
    for (i, (ctor_name, field_count)) in ctors.iter().enumerate() {
        let x_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );
        let y_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(y.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );
        let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check.clone()), Box::new(y_check));

        if *field_count == 0 {
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(JsExpr::Indexer(Box::new(JsExpr::Var("EQ".to_string())), Box::new(JsExpr::StringLit("value".to_string()))))],
                None,
            ));
        } else {
            // Compare fields in order, short-circuiting on non-EQ
            let mut inner_body = Vec::new();
            let x_any = JsExpr::Var(x.clone());
            let y_any = JsExpr::Var(y.clone());
            for fi in 0..*field_count {
                let field_name = format!("value{fi}");
                let x_field = JsExpr::Indexer(
                    Box::new(x_any.clone()),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(y_any.clone()),
                    Box::new(JsExpr::StringLit(field_name)),
                );
                if !constraints.is_empty() {
                    // compare($dictOrd)(x.valueN)(y.valueN)
                    let ord_constraint = constraints.iter().find(|c| {
                        let cname = interner::resolve(c.class.name).unwrap_or_default();
                        cname == "Ord"
                    });
                    if let Some(c) = ord_constraint {
                        let dict_param = constraint_to_dict_param(c);
                        let cmp = JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(JsExpr::App(
                                    Box::new(JsExpr::Var("compare".to_string())),
                                    vec![JsExpr::Var(dict_param)],
                                )),
                                vec![x_field],
                            )),
                            vec![y_field],
                        );
                        let v = format!("$cmp{fi}");
                        inner_body.push(JsStmt::VarDecl(v.clone(), Some(cmp)));
                        inner_body.push(JsStmt::If(
                            JsExpr::Binary(
                                JsBinaryOp::StrictNeq,
                                Box::new(JsExpr::Var(v.clone())),
                                Box::new(JsExpr::Indexer(Box::new(JsExpr::Var("EQ".to_string())), Box::new(JsExpr::StringLit("value".to_string())))),
                            ),
                            vec![JsStmt::Return(JsExpr::Var(v))],
                            None,
                        ));
                    }
                }
            }
            inner_body.push(JsStmt::Return(JsExpr::Indexer(Box::new(JsExpr::Var("EQ".to_string())), Box::new(JsExpr::StringLit("value".to_string())))));
            body.push(JsStmt::If(both_check, inner_body, None));
        }

        // If x matches this ctor but y doesn't, x < y iff x's ctor index < y's
        // For simplicity: if x is this ctor (and we didn't return above), compare indices
        if ctors.len() > 1 {
            body.push(JsStmt::If(
                x_check,
                vec![JsStmt::Return(JsExpr::Indexer(Box::new(JsExpr::Var("LT".to_string())), Box::new(JsExpr::StringLit("value".to_string()))))],
                None,
            ));
        }
    }

    // Fallback (shouldn't reach here)
    body.push(JsStmt::Return(JsExpr::Indexer(Box::new(JsExpr::Var("GT".to_string())), Box::new(JsExpr::StringLit("value".to_string())))));

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

/// Generate `map` method for derive Functor.
/// ```js
/// map: function(f) { return function(x) {
///   if (x instanceof Nothing) return Nothing.value;
///   if (x instanceof Just) return Just.create(f(x.value0));
///   ...
/// }}
/// ```
fn gen_derive_functor_methods(ctors: &[(String, usize)]) -> Vec<(String, JsExpr)> {
    let f = "f".to_string();
    let x = "x".to_string();

    let mut body = Vec::new();

    for (ctor_name, field_count) in ctors {
        let x_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );

        if *field_count == 0 {
            // Nullary constructor: return as-is
            body.push(JsStmt::If(
                x_check,
                vec![JsStmt::Return(JsExpr::Indexer(
                    Box::new(JsExpr::Var(ctor_name.clone())),
                    Box::new(JsExpr::StringLit("value".to_string())),
                ))],
                None,
            ));
        } else {
            // Apply f to the last field (the one containing the type parameter)
            // and reconstruct via create
            let last_idx = field_count - 1;
            let x_any = JsExpr::Var(x.clone());
            let mapped_value = JsExpr::App(
                Box::new(JsExpr::Var(f.clone())),
                vec![JsExpr::Indexer(
                    Box::new(x_any.clone()),
                    Box::new(JsExpr::StringLit(format!("value{last_idx}"))),
                )],
            );

            // Build create call: Ctor.create(x.value0)(x.value1)...(f(x.valueN))
            let mut result: JsExpr = JsExpr::Indexer(
                Box::new(JsExpr::Var(ctor_name.clone())),
                Box::new(JsExpr::StringLit("create".to_string())),
            );
            for i in 0..*field_count {
                let arg = if i == last_idx {
                    mapped_value.clone()
                } else {
                    JsExpr::Indexer(
                        Box::new(x_any.clone()),
                        Box::new(JsExpr::StringLit(format!("value{i}"))),
                    )
                };
                result = JsExpr::App(Box::new(result), vec![arg]);
            }

            body.push(JsStmt::If(
                x_check,
                vec![JsStmt::Return(result)],
                None,
            ));
        }
    }

    // Fallback (shouldn't be reached)
    body.push(JsStmt::Return(JsExpr::Var(x.clone())));

    let map_fn = JsExpr::Function(
        None,
        vec![f],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![x],
            body,
        ))],
    );

    vec![("map".to_string(), map_fn)]
}

/// Generate `wrap` and `unwrap` methods for derive Newtype class.
fn gen_derive_newtype_class_methods() -> Vec<(String, JsExpr)> {
    // wrap: function(x) { return x; }
    let wrap = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );
    // unwrap: function(x) { return x; }
    let unwrap = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );
    vec![
        ("wrap".to_string(), wrap),
        ("unwrap".to_string(), unwrap),
    ]
}

/// Generate `to` and `from` methods for derive Generic.
/// These convert between the type and its generic representation.
/// For now, generates identity-like stubs since the Generic rep is typically
/// handled at the type level and the runtime is just constructor tagging.
fn gen_derive_generic_methods(ctors: &[(String, usize)]) -> Vec<(String, JsExpr)> {
    // to: function(x) { return x; }
    let to = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );
    // from: function(x) { return x; }
    let from = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );
    vec![
        ("to".to_string(), to),
        ("from".to_string(), from),
    ]
}

/// Generate a dict parameter name from a constraint, e.g. `Show a` → `dictShow`
fn constraint_to_dict_param(constraint: &Constraint) -> String {
    let class_name = interner::resolve(constraint.class.name).unwrap_or_default();
    format!("$dict{class_name}")
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
            let dict_param = format!("$dict{class_name_str}");
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
            return JsExpr::Var(inst_js);
        }
        if let Some(source) = ctx.instance_sources.get(inst_name) {
            match source {
                None => return JsExpr::Var(inst_js),
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
                // Newtype constructor: Ctor.create (identity)
                let base = gen_qualified_ref_raw(ctx, name);
                JsExpr::Indexer(
                    Box::new(base),
                    Box::new(JsExpr::StringLit("create".to_string())),
                )
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
                            let updated = gen_record_update(ctx, inner_arg, &updates);
                            let f = gen_expr(ctx, outer_func);
                            return JsExpr::App(Box::new(f), vec![updated]);
                        }
                        return gen_record_update(ctx, func, &updates);
                    }
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

        Expr::OpParens { op, .. } => {
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
            resolve_op_ref(ctx, op)
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
        // First, check if this is a class method
        let method_qi = unqualified(qident.name);
        if let Some((class_qi, _)) = find_class_method(ctx, &method_qi) {
            if let Some(dict_expr) = find_dict_in_scope(ctx, &scope, class_qi.name) {
                return Some(JsExpr::App(Box::new(base), vec![dict_expr]));
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
    let result = try_apply_resolved_dict(ctx, qident, base.clone(), span);
    result
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
    let is_class_method = ctx.all_class_methods.contains_key(&qident.name);
    if is_class_method {
        if let Some((class_qi, _)) = ctx.all_class_methods.get(&qident.name) {
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
                    JsExpr::ModuleAccessor(js_mod.clone(), js_name)
                } else {
                    JsExpr::Var(js_name)
                }
            } else if let Some(source) = ctx.instance_sources.get(name) {
                match source {
                    None => JsExpr::Var(js_name),
                    Some(parts) => {
                        if let Some(js_mod) = ctx.import_map.get(parts) {
                            JsExpr::ModuleAccessor(js_mod.clone(), js_name)
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

/// Find class method info for a name.
fn find_class_method(ctx: &CodegenCtx, method_qi: &QualifiedIdent) -> Option<(QualifiedIdent, Vec<QualifiedIdent>)> {
    ctx.all_class_methods.get(&method_qi.name).cloned()
}

/// Find constraint class names for a function (non-class-method).
fn find_fn_constraints(ctx: &CodegenCtx, qident: &QualifiedIdent) -> Vec<Symbol> {
    // Don't apply to class methods (handled separately)
    if ctx.all_class_methods.contains_key(&qident.name) {
        return vec![];
    }
    ctx.all_fn_constraints.get(&qident.name).cloned().unwrap_or_default()
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
            None => JsExpr::Var(inst_js), // local
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

                // Push dict scope entries for constraints
                let prev_scope_len = ctx.dict_scope.borrow().len();
                if let Some(ref constraints) = constraints {
                    for (class_qi, _) in constraints {
                        let class_name_str = interner::resolve(class_qi.name).unwrap_or_default();
                        let dict_param = format!("$dict{class_name_str}");
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

    iife_body.push(JsStmt::Throw(JsExpr::App(
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
                Literal::Boolean(b) => JsExpr::Binary(
                    JsBinaryOp::StrictEq,
                    Box::new(scrutinee.clone()),
                    Box::new(JsExpr::BoolLit(*b)),
                ),
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
            JsExpr::Var(any_name_to_js(name))
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

/// Generate code for a single operator application, handling $ and # inlining.
fn gen_single_op(ctx: &CodegenCtx, left: &Expr, op: &Spanned<QualifiedIdent>, right: &Expr) -> JsExpr {
    let op_sym = op.value.name;
    let op_str = interner::resolve(op_sym).unwrap_or_default();

    // Inline $ and #
    if op_str == "$" || op_str == "apply" {
        let f = gen_expr(ctx, left);
        let x = gen_expr(ctx, right);
        return JsExpr::App(Box::new(f), vec![x]);
    }
    if op_str == "#" || op_str == "applyFlipped" {
        let x = gen_expr(ctx, left);
        let f = gen_expr(ctx, right);
        return JsExpr::App(Box::new(f), vec![x]);
    }

    let op_ref = resolve_op_ref(ctx, op);
    let l = gen_expr(ctx, left);
    let r = gen_expr(ctx, right);
    JsExpr::App(
        Box::new(JsExpr::App(Box::new(op_ref), vec![l])),
        vec![r],
    )
}

/// Apply an operator to two JS expressions, handling $ and # inlining.
fn apply_op(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>, lhs: JsExpr, rhs: JsExpr) -> JsExpr {
    let op_str = interner::resolve(op.value.name).unwrap_or_default();
    if op_str == "$" || op_str == "apply" {
        return JsExpr::App(Box::new(lhs), vec![rhs]);
    }
    if op_str == "#" || op_str == "applyFlipped" {
        return JsExpr::App(Box::new(rhs), vec![lhs]);
    }
    let op_ref = resolve_op_ref(ctx, op);
    JsExpr::App(
        Box::new(JsExpr::App(Box::new(op_ref), vec![lhs])),
        vec![rhs],
    )
}

/// Resolve an operator to its JS reference (target function + dict application).
fn resolve_op_ref(ctx: &CodegenCtx, op: &Spanned<QualifiedIdent>) -> JsExpr {
    let op_sym = op.value.name;
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
        // Resolve the target function. If name_source knows the target, use normal resolution.
        // Otherwise, use the source module from operator_targets directly.
        if ctx.local_names.contains(target_name) || ctx.name_source.contains_key(target_name) {
            let target_qi = QualifiedIdent { module: None, name: *target_name };
            gen_qualified_ref_with_span(ctx, &target_qi, Some(op.span))
        } else if let Some(parts) = source_parts {
            // Target not in name_source — resolve via operator's source module
            if let Some(js_mod) = ctx.import_map.get(parts) {
                let base = JsExpr::ModuleAccessor(js_mod.clone(), target_js);
                // Try to apply dict
                let target_qi = QualifiedIdent { module: None, name: *target_name };
                if let Some(dict_applied) = try_apply_dict(ctx, &target_qi, base.clone(), Some(op.span)) {
                    dict_applied
                } else {
                    base
                }
            } else {
                let target_qi = QualifiedIdent { module: None, name: *target_name };
                gen_qualified_ref_with_span(ctx, &target_qi, Some(op.span))
            }
        } else {
            let target_qi = QualifiedIdent { module: None, name: *target_name };
            gen_qualified_ref_with_span(ctx, &target_qi, Some(op.span))
        }
    } else {
        gen_qualified_ref_with_span(ctx, &op.value, Some(op.span))
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
