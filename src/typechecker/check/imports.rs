use std::collections::{HashMap, HashSet};

use crate::ast::{Decl, Module};
use crate::cst::{
    DataMembers,
    Export, Import, ImportList, ModuleName,
};
use crate::interner::Symbol;
use crate::names::{
    self, Qualified, ValueName, TypeName, TypeVarName, ClassName, ConstructorName,
    OpName, TypeOpName, ModuleQualifier,
};
use crate::typechecker::env::Env;
use crate::typechecker::error::TypeError;
use crate::typechecker::infer::InferCtx;
use crate::typechecker::registry::{ModuleExports, ModuleRegistry};
use crate::typechecker::types::{Scheme, Type};

use super::{
    collect_type_con_names_from_type, qualified_symbol,
    prim_exports, is_prim_module, is_prim_submodule, prim_submodule_exports,
};

// ---------------------------------------------------------------------------
// Typed-name construction helpers
// ---------------------------------------------------------------------------

/// Create an unqualified Qualified<ValueName> from a Symbol.
fn qv(sym: Symbol) -> Qualified<ValueName> {
    Qualified::unqualified(ValueName::new(sym))
}

/// Create an unqualified Qualified<TypeName> from a Symbol.
fn qt(sym: Symbol) -> Qualified<TypeName> {
    Qualified::unqualified(TypeName::new(sym))
}

/// Create an unqualified Qualified<ConstructorName> from a Symbol.
fn qc(sym: Symbol) -> Qualified<ConstructorName> {
    Qualified::unqualified(ConstructorName::new(sym))
}

/// Create an unqualified Qualified<ClassName> from a Symbol.
fn qcl(sym: Symbol) -> Qualified<ClassName> {
    Qualified::unqualified(ClassName::new(sym))
}

/// Create an unqualified Qualified<OpName> from a Symbol.
fn qop(sym: Symbol) -> Qualified<OpName> {
    Qualified::unqualified(OpName::new(sym))
}

/// Create an unqualified Qualified<TypeOpName> from a Symbol.
fn qtop(sym: Symbol) -> Qualified<TypeOpName> {
    Qualified::unqualified(TypeOpName::new(sym))
}

/// Optionally qualify a Qualified<ValueName>: if qualifier is Some, set it.
fn qualify_v(name: Qualified<ValueName>, qualifier: Option<Symbol>) -> Qualified<ValueName> {
    match qualifier {
        Some(q) => Qualified::qualified(ModuleQualifier::new(q), name.name),
        None => name,
    }
}

/// Optionally qualify a Qualified<TypeName>: if qualifier is Some, set it.
fn qualify_t(name: Qualified<TypeName>, qualifier: Option<Symbol>) -> Qualified<TypeName> {
    match qualifier {
        Some(q) => Qualified::qualified(ModuleQualifier::new(q), name.name),
        None => name,
    }
}

/// Optionally qualify a Qualified<ConstructorName>: if qualifier is Some, set it.
fn qualify_c(name: Qualified<ConstructorName>, qualifier: Option<Symbol>) -> Qualified<ConstructorName> {
    match qualifier {
        Some(q) => Qualified::qualified(ModuleQualifier::new(q), name.name),
        None => name,
    }
}

/// Optionally qualify a Qualified<OpName>: if qualifier is Some, set it.
fn qualify_op(name: Qualified<OpName>, qualifier: Option<Symbol>) -> Qualified<OpName> {
    match qualifier {
        Some(q) => Qualified::qualified(ModuleQualifier::new(q), name.name),
        None => name,
    }
}

/// Walk a kind type and qualify Con references that match exported type names.
/// Used when importing type kinds from other modules with a qualifier.
/// E.g., importing LibB's `DemoData :: DemoKind` as LibB produces `DemoData :: LibB.DemoKind`.
pub(crate) fn qualify_kind_refs(kind: &Type, qualifier: Symbol, exported_types: &HashSet<Symbol>) -> Type {
    match kind {
        Type::Con(name) => {
            // Don't qualify Prim kind names — these are built-in kinds, not module-specific types.
            let name_str = crate::interner::resolve(name.name_symbol()).unwrap_or_default();
            if matches!(name_str.as_str(), "Type" | "Constraint" | "Symbol" | "Row" | "Int") {
                return kind.clone();
            }
            if name.module.is_none() && exported_types.contains(&name.name_symbol()) {
                Type::Con(Qualified::qualified(ModuleQualifier::new(qualifier), name.name))
            } else {
                kind.clone()
            }
        }
        Type::Fun(a, b) => Type::fun(
            qualify_kind_refs(a, qualifier, exported_types),
            qualify_kind_refs(b, qualifier, exported_types),
        ),
        Type::App(a, b) => Type::app(
            qualify_kind_refs(a, qualifier, exported_types),
            qualify_kind_refs(b, qualifier, exported_types),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(qualify_kind_refs(body, qualifier, exported_types)),
        ),
        _ => kind.clone(),
    }
}

/// Strip module qualifiers from kind type constructors for export.
/// Exported kinds should use bare names so importing modules can add their own
/// qualifiers via `qualify_kind_refs`. Without this, internal import aliases
/// (e.g., `K.Subject`) would leak into exported kinds and be unresolvable by
/// downstream modules.
pub(crate) fn strip_kind_qualifiers(kind: &Type) -> Type {
    match kind {
        Type::Con(name) if name.module.is_some() => {
            Type::Con(Qualified::unqualified(name.name))
        }
        Type::Fun(a, b) => Type::fun(
            strip_kind_qualifiers(a),
            strip_kind_qualifiers(b),
        ),
        Type::App(a, b) => Type::app(
            strip_kind_qualifiers(a),
            strip_kind_qualifiers(b),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(strip_kind_qualifiers(body)),
        ),
        _ => kind.clone(),
    }
}

/// Convert a ModuleName to a single symbol (joining parts with '.').
pub(crate) fn module_name_to_symbol(module_name: &crate::cst::ModuleName) -> Symbol {
    crate::interner::intern_module_name(&module_name.parts)
}

/// Optionally qualify a name: if qualifier is Some, prefix with "Q.", otherwise return as-is.
pub(crate) fn maybe_qualify_symbol(name: Symbol, qualifier: Option<Symbol>) -> Symbol {
    match qualifier {
        Some(q) => qualified_symbol(q, name),
        None => name,
    }
}

/// Canonicalize unqualified type constructor references in an alias body.
/// For qualified imports (`import M as Q`), alias bodies may contain
/// `Type::Con(QualifiedIdent { module: None, name: "Bar" })` — unqualified
/// references to types from the source module. This function sets the module
/// qualifier to the source module's canonical name so that `try_expand_alias`
/// can find them via canonical key or canonical_to_qualifier fallback, and
/// so they won't be confused with local aliases of the same name.
pub(crate) fn canonicalize_alias_body_types(
    ty: &Type,
    source_module: Symbol,
    exported_type_names: &HashSet<TypeName>,
    exclude_name: Option<Symbol>,
) -> Type {
    match ty {
        Type::Con(q) if q.module.is_none()
            && exported_type_names.contains(&TypeName::new(q.name_symbol()))
            && exclude_name.map_or(true, |ex| ex != q.name_symbol()) => {
            Type::Con(Qualified::qualified(ModuleQualifier::new(source_module), q.name))
        }
        Type::App(f, a) => {
            Type::App(
                Box::new(canonicalize_alias_body_types(f, source_module, exported_type_names, exclude_name)),
                Box::new(canonicalize_alias_body_types(a, source_module, exported_type_names, exclude_name)),
            )
        }
        Type::Fun(a, b) => {
            Type::Fun(
                Box::new(canonicalize_alias_body_types(a, source_module, exported_type_names, exclude_name)),
                Box::new(canonicalize_alias_body_types(b, source_module, exported_type_names, exclude_name)),
            )
        }
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(canonicalize_alias_body_types(body, source_module, exported_type_names, exclude_name)))
        }
        Type::Record(fields, tail) => {
            let new_fields: Vec<_> = fields.iter()
                .map(|(label, ty)| (*label, canonicalize_alias_body_types(ty, source_module, exported_type_names, exclude_name)))
                .collect();
            let new_tail = tail.as_ref().map(|t| Box::new(canonicalize_alias_body_types(t, source_module, exported_type_names, exclude_name)));
            Type::Record(new_fields, new_tail)
        }
        _ => ty.clone(),
    }
}

type InstanceMap = HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>;

/// Look up instances for a class, falling back to unqualified name if needed.
/// Instance entries are stored under the exporting module's key (typically unqualified),
/// but constraints may reference the class through a qualified import (e.g. `Row.Nub`).
pub(crate) fn lookup_instances<'a>(
    instances: &'a InstanceMap,
    class_name: &Qualified<ClassName>,
) -> Option<&'a Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>> {
    instances.get(class_name).or_else(|| {
        if class_name.module.is_some() {
            // Qualified lookup failed — try unqualified
            instances.get(&Qualified::unqualified(class_name.name))
        } else {
            // Unqualified lookup failed — search for any qualified variant with same name
            instances.iter()
                .find(|(k, _)| k.name == class_name.name)
                .map(|(_, v)| v)
        }
    })
}

/// Process all import declarations, bringing imported names into scope.
/// Returns the set of explicitly imported type names (for scope conflict detection
/// with local type declarations).
pub(crate) fn process_imports(
    module: &Module,
    registry: &ModuleRegistry,
    env: &mut Env,
    ctx: &mut InferCtx,
    instances: &mut HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    errors: &mut Vec<TypeError>,
) -> HashSet<TypeName> {
    let mut explicitly_imported_types: HashSet<TypeName> = HashSet::new();
    // Build Prim exports once so explicit `import Prim` / `import Prim as P` resolves.
    let prim = prim_exports();

    // Track which modules' instances have already been imported to avoid redundant dedup work.
    // Each module's exports contain all transitive instances, so we only need to import
    // instances from each unique module once.
    let mut imported_instance_modules: HashSet<Symbol> = HashSet::new();

    // Pre-scan local type alias names so import processing can detect collisions.
    // This is needed because local aliases aren't registered until Pass 1, but we need
    // to know about them during import processing to qualify conflicting imported types.
    let local_type_alias_names: HashSet<TypeName> = module.decls.iter()
        .filter_map(|d| match d {
            Decl::TypeAlias { name, .. } => Some(TypeName::new(name.value)),
            _ => None,
        })
        .collect();

    // Pre-scan local data/newtype/foreign data type names so import processing can
    // avoid registering imported type aliases that collide with local data types.
    // Without this, `type Thread = { ... }` (imported alias) overwrites the local
    // `newtype Thread = T Thread.Thread` in type_aliases, causing instance heads
    // like `Show Thread` to be incorrectly alias-expanded to a record type.
    let local_data_type_names: HashSet<TypeName> = module.decls.iter()
        .filter_map(|d| match d {
            Decl::Data { name, kind_sig, is_role_decl, .. }
                if *kind_sig == crate::cst::KindSigSource::None && !is_role_decl =>
                    Some(TypeName::new(name.value)),
            Decl::Newtype { name, .. } => Some(TypeName::new(name.value)),
            Decl::ForeignData { name, .. } => Some(TypeName::new(name.value)),
            _ => None,
        })
        .collect();

    // Pre-scan all imports to collect type alias names that will be imported
    // into the unqualified namespace. This is needed so qualified imports can
    // detect name collisions with type aliases even when the alias-providing
    // import appears later in the import list. Without this, import ordering
    // affects whether defined_types qualifies value scheme type constructors,
    // causing incorrect alias expansion (e.g., `Expiry` data type in a qualified
    // import's value scheme gets alias-expanded to `{ expiresIn :: Int }` from
    // an unqualified type alias import that hasn't been processed yet).
    let all_alias_names: HashSet<TypeName> = {
        let mut names = local_type_alias_names.clone();
        for import_decl in &module.imports {
            // Only unqualified imports add aliases to the unqualified namespace
            if import_decl.qualified.is_some() {
                continue;
            }
            let prim_sub_pre;
            let module_exports_pre = if is_prim_module(&import_decl.module) {
                prim
            } else if is_prim_submodule(&import_decl.module) {
                prim_sub_pre = prim_submodule_exports(&import_decl.module);
                &prim_sub_pre
            } else {
                match registry.lookup(&import_decl.module.parts) {
                    Some(exports) => exports,
                    None => continue,
                }
            };
            match &import_decl.imports {
                None => {
                    // import M — all type aliases imported unqualified
                    for name in module_exports_pre.type_aliases.keys() {
                        names.insert(name.name);
                    }
                }
                Some(ImportList::Explicit(items)) => {
                    // import M (x, y, ...) — check which are type aliases
                    for item in items {
                        let sym = import_name(item);
                        if module_exports_pre.type_aliases.keys().any(|n| n.name_symbol() == sym) {
                            names.insert(TypeName::new(sym));
                        }
                    }
                }
                Some(ImportList::Hiding(items)) => {
                    // import M hiding (x, y) — all aliases except hidden
                    let hidden_pre: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                    for name in module_exports_pre.type_aliases.keys() {
                        if !hidden_pre.contains(&name.name_symbol()) {
                            names.insert(name.name);
                        }
                    }
                }
            }
        }
        names
    };

    // Track import origins for scope conflict detection.
    // Maps (possibly qualified) name → (origin module symbol, is_explicit).
    // A scope conflict occurs when a name is imported from two different origin modules
    // AND both imports have the same explicitness level. Explicit imports shadow open imports.
    let mut import_origins: HashMap<Symbol, (Symbol, bool)> = HashMap::new();

    for import_decl in &module.imports {
        // Handle Prim submodules (Prim.Coerce, Prim.Row, etc.) as built-in
        let prim_sub;
        let module_exports = if is_prim_module(&import_decl.module) {
            prim
        } else if is_prim_submodule(&import_decl.module) {
            prim_sub = prim_submodule_exports(&import_decl.module);
            &prim_sub
        } else {
            match registry.lookup(&import_decl.module.parts) {
                Some(exports) => exports,
                None => {
                    errors.push(TypeError::ModuleNotFound {
                        span: import_decl.span,
                        name: module_name_to_symbol(&import_decl.module),
                    });
                    continue;
                }
            }
        };

        let qualifier = import_decl.qualified.as_ref().map(module_name_to_symbol);
        let mod_sym = module_name_to_symbol(&import_decl.module);

        // Determine if this is an explicit import (import M (x)) vs open (import M)
        let is_explicit = matches!(&import_decl.imports, Some(ImportList::Explicit(_)));

        // Collect imported value names for scope conflict detection
        let imported_names: Vec<Symbol> = match (&import_decl.imports, qualifier) {
            (None, Some(q)) => {
                // import M as Q — qualified names
                module_exports
                    .values
                    .keys()
                    .map(|n| maybe_qualify_symbol(n.name_symbol(), Some(q)))
                    .collect()
            }
            (None, None) => {
                // import M — all unqualified values
                module_exports.values.keys().map(|n| n.name_symbol()).collect()
            }
            (Some(ImportList::Explicit(items)), _) => items
                .iter()
                .map(|i| maybe_qualify_symbol(import_name(i), qualifier))
                .collect(),
            (Some(ImportList::Hiding(items)), _) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                module_exports
                    .values
                    .keys()
                    .filter(|n| !hidden.contains(&n.name_symbol()))
                    .map(|n| maybe_qualify_symbol(n.name_symbol(), qualifier))
                    .collect()
            }
        };

        // Check for scope conflicts: same name from different defining modules.
        for name in &imported_names {
            // Look up the defining origin for this name (unqualified for origin lookup)
            let unqual = if qualifier.is_some() {
                // For qualified imports, extract unqualified name for origin lookup
                let name_str = crate::interner::resolve(*name).unwrap_or_default();
                if let Some(pos) = name_str.find('.') {
                    crate::interner::intern(&name_str[pos + 1..])
                } else {
                    *name
                }
            } else {
                *name
            };
            let found_origin = module_exports.value_origins.get(&ValueName::new(unqual)).copied();
            let origin = found_origin.unwrap_or(mod_sym);
            if let Some(&(existing_origin, existing_explicit)) = import_origins.get(name) {
                if existing_origin != origin {
                    if is_explicit && existing_explicit {
                        // Both explicitly import the same name from different modules → conflict
                        ctx.scope_conflicts.insert(ValueName::new(*name));
                    } else if is_explicit && !existing_explicit {
                        // Explicit import shadows the open import → replace, no conflict
                        import_origins.insert(*name, (origin, true));
                    } else if !is_explicit && existing_explicit {
                        // Existing explicit import shadows this open import → no conflict
                    } else {
                        // Both open imports from different modules → conflict
                        ctx.scope_conflicts.insert(ValueName::new(*name));
                    }
                }
            } else {
                import_origins.insert(*name, (origin, is_explicit));
            }
        }

        // Import instances once per unique module. In PureScript, type class instances are
        // globally visible — importing any item from a module imports all its instances.
        // Module-level dedup avoids redundant O(n²) per-instance comparison for reimports.
        if imported_instance_modules.insert(mod_sym) {
            for (class_name, insts) in &module_exports.instances {
                let existing = instances.entry(*class_name).or_default();
                for inst in insts {
                    if !existing.iter().any(|e| e.0 == inst.0) {
                        existing.push(inst.clone());
                    }
                }
            }
            // Import pre-computed self-referential aliases to avoid recomputing from scratch.
            ctx.state.self_referential_aliases.extend(module_exports.self_referential_aliases.iter().copied());
        }

        // Compute canonical_origins for explicit/hiding import paths: maps unqualified
        // type names to their origin module when they collide with LOCAL type aliases.
        // Use all_alias_names (not just local_type_alias_names) for consistency with
        // import_all's canonical_origins. Without this, import_item value schemes have
        // bare type names while import_all alias bodies have canonicalized names, causing
        // unification mismatches (e.g., Time vs Data.Time.Time).
        let import_canonical_origins: Option<HashMap<Symbol, Symbol>> = {
            let mut origins: HashMap<Symbol, Symbol> = HashMap::new();
            for (name, &origin) in &module_exports.type_origins {
                if all_alias_names.contains(name) {
                    origins.insert(name.symbol(), origin);
                }
            }
            if origins.is_empty() { None } else { Some(origins) }
        };

        match &import_decl.imports {
            None => {
                // import M — everything unqualified; import M as Q — everything qualified only
                import_all(Some(import_decl.module.clone()), module_exports, env, ctx, qualifier, &all_alias_names, &local_type_alias_names, &local_data_type_names);
            }
            Some(ImportList::Explicit(items)) => {
                // import M (x) — listed items unqualified
                // import M (x) as Q — listed items qualified only
                for item in items {
                    // Track explicitly imported type names (unqualified)
                    if qualifier.is_none() {
                        match item {
                            Import::Type(name, _) => {
                                explicitly_imported_types.insert(name.value);
                            }
                            Import::Class(name) => {
                                explicitly_imported_types.insert(TypeName::new(name.value.symbol()));
                            }
                            _ => {}
                        }
                    }
                    import_item(
                        &import_decl.module,
                        item,
                        module_exports,
                        env,
                        ctx,
                        instances,
                        qualifier,
                        import_decl.span,
                        errors,
                        &import_canonical_origins,
                    );
                }
                // Import type_con_arities from the source module for names referenced
                // in imported alias bodies. This ensures data type arities are known
                // for alias expansion disambiguation (e.g., `type GqlData = RemoteData GqlError`
                // where GqlError is a data type in the source module but also an alias
                // from a different qualified import in the consuming module).
                {
                    let mut alias_body_names: HashSet<Symbol> = HashSet::new();
                    for item in items {
                        let item_name = import_name(item);
                        if let Some(alias) = module_exports.type_aliases.get(&qt(item_name)) {
                            collect_type_con_names_from_type(&alias.1, &mut alias_body_names);
                        }
                    }
                    if !alias_body_names.is_empty() {
                        for (name, arity) in &module_exports.type_con_arities {
                            if alias_body_names.contains(&name.name_symbol()) {
                                ctx.type_con_arities.entry(qualify_t(*name, qualifier)).or_insert(*arity);
                            }
                        }
                    }
                }
            }
            Some(ImportList::Hiding(items)) => {
                let hidden: HashSet<Symbol> = items.iter().map(|i| import_name(i)).collect();
                import_all_except(Some(import_decl.module.clone()), module_exports, &hidden, env, ctx, instances, qualifier, &local_data_type_names, &import_canonical_origins);
            }
        }
    }

    explicitly_imported_types
}


/// Resolve import-qualifier-prefixed type constructors to canonical module names.
/// E.g., `Con(CoreResponse.Response)` → `Con(JS.Fetch.Response.Response)` when
/// `CoreResponse` maps to `JS.Fetch.Response` in the qualifier map.
pub(crate) fn resolve_type_qualifiers(ty: &Type, qualifier_map: &HashMap<Symbol, Symbol>) -> Type {
    match ty {
        Type::Con(name) => {
            if let Some(q) = name.module {
                if let Some(&canonical) = qualifier_map.get(&q.symbol()) {
                    return Type::Con(Qualified::qualified(ModuleQualifier::new(canonical), name.name));
                }
            }
            ty.clone()
        }
        Type::Fun(a, b) => Type::fun(
            resolve_type_qualifiers(a, qualifier_map),
            resolve_type_qualifiers(b, qualifier_map),
        ),
        Type::App(f, a) => Type::app(
            resolve_type_qualifiers(f, qualifier_map),
            resolve_type_qualifiers(a, qualifier_map),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(resolve_type_qualifiers(body, qualifier_map)),
        ),
        Type::Record(fields, tail) => {
            let fields = fields.iter()
                .map(|(l, t)| (*l, resolve_type_qualifiers(t, qualifier_map)))
                .collect();
            let tail = tail.as_ref()
                .map(|t| Box::new(resolve_type_qualifiers(t, qualifier_map)));
            Type::Record(fields, tail)
        }
        _ => ty.clone(),
    }
}

/// Qualify unqualified type constructor names in a type using canonical module names.
/// For each unqualified `Con(X)` that has an entry in `canonical_origins`, replace with
/// `Con(CanonicalModule.X)`. This prevents local type aliases from incorrectly expanding
/// imported type constructors that share the same name.
pub(crate) fn canonicalize_type_cons(ty: &Type, canonical_origins: &HashMap<Symbol, Symbol>) -> Type {
    match ty {
        Type::Con(name) => {
            if name.module.is_none() {
                if let Some(&origin) = canonical_origins.get(&name.name_symbol()) {
                    return Type::Con(Qualified::qualified(ModuleQualifier::new(origin), name.name));
                }
            }
            ty.clone()
        }
        Type::Fun(a, b) => Type::fun(
            canonicalize_type_cons(a, canonical_origins),
            canonicalize_type_cons(b, canonical_origins),
        ),
        Type::App(f, a) => Type::app(
            canonicalize_type_cons(f, canonical_origins),
            canonicalize_type_cons(a, canonical_origins),
        ),
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(canonicalize_type_cons(body, canonical_origins)),
        ),
        Type::Record(fields, tail) => {
            let fields = fields.iter()
                .map(|(l, t)| (*l, canonicalize_type_cons(t, canonical_origins)))
                .collect();
            let tail = tail.as_ref()
                .map(|t| Box::new(canonicalize_type_cons(t, canonical_origins)));
            Type::Record(fields, tail)
        }
        _ => ty.clone(),
    }
}

pub(crate) fn canonicalize_scheme_type_cons(scheme: &Scheme, canonical_origins: &HashMap<Symbol, Symbol>) -> Scheme {
    Scheme {
        forall_vars: scheme.forall_vars.clone(),
        ty: canonicalize_type_cons(&scheme.ty, canonical_origins),
    }
}

/// Import all names from a module's exports.
/// If `qualifier` is Some, env entries are stored with qualified keys (e.g. "Q.foo").
/// Internal maps (class_methods, data_constructors, etc.) are always unqualified.
pub(crate) fn import_all(
    from: Option<ModuleName>,
    exports: &ModuleExports,
    env: &mut Env,
    ctx: &mut InferCtx,
    qualifier: Option<Symbol>,
    all_alias_names: &HashSet<TypeName>,
    _local_type_alias_names: &HashSet<TypeName>,
    local_data_type_names: &HashSet<TypeName>,
) {
    // For qualified imports, qualify imported type constructors defined in the source
    // module to prevent local alias collisions within this module's scope.
    // E.g., `import JS.Fetch.Response as CoreResponse` qualifies `Con(Response)` to
    // `Con(CoreResponse.Response)` so local `type Response = { ... }` won't expand it.
    // IMPORTANT: only qualify types that actually collide with local type aliases,
    // otherwise instance resolution breaks (instances use unqualified names).
    // Uses all_alias_names (including imported aliases) for ordering independence.
    let defined_types: Option<(HashSet<Symbol>, Symbol)> = qualifier.and_then(|q| {
        let mod_sym = from.as_ref().map(module_name_to_symbol)?;
        let dt: HashSet<Symbol> = exports.type_origins.iter()
            .filter(|(_, &origin)| origin == mod_sym)
            .filter(|(name, _)| {
                ctx.state.type_aliases.contains_key(&Qualified::unqualified(**name))
                    || all_alias_names.contains(name)
            })
            .map(|(name, _)| name.symbol())
            .collect();
        if dt.is_empty() { None } else { Some((dt, q)) }
    });

    // Also canonicalize unqualified type names that collide with existing local aliases.
    // This handles re-exported types: `Con(Response)` from JS.Fetch (where Response
    // originates from JS.Fetch.Response) becomes `Con(JS.Fetch.Response.Response)`.
    // If the exporting module itself defines a name as a type alias, its value schemes
    // use the alias, not the data type. Don't canonicalize in that case — canonicalizing
    // would turn alias references into data type references (e.g., Time=Number into
    // Data.Time.Time, or ResponseUpdate into its qualified form).
    let canonical_origins: Option<HashMap<Symbol, Symbol>> = {
        let mut origins: HashMap<Symbol, Symbol> = HashMap::new();
        for (name, &origin) in &exports.type_origins {
            let name_sym = name.symbol();
            // If the exporting module itself has this as a type alias, its value
            // schemes use the alias meaning. Don't canonicalize.
            if exports.type_aliases.iter().any(|(k, _)| k.name_symbol() == name_sym) {
                continue;
            }
            let has_alias_collision = ctx.state.type_aliases.contains_key(&Qualified::unqualified(*name))
                || all_alias_names.contains(name);
            if !has_alias_collision {
                continue;
            }
            origins.insert(name_sym, origin);
        }
        if origins.is_empty() { None } else { Some(origins) }
    };

    // Import class method info first so we can detect conflicts.
    // For qualified imports (import M as Q), only insert under the qualified key
    // so we don't pollute the unqualified class_methods map. This prevents
    // `import Prelude as Prelude` from re-registering `top` as a class method
    // after `import Prelude hiding (top)` correctly hid it.
    for (name, info) in &exports.class_methods {
        let key = qualify_v(*name, qualifier);
        ctx.class_methods.insert(key, info.clone());
        // Populate class_method_schemes so instance expected-type lookups use the canonical
        // class type even if the method name later gets shadowed in env by another import.
        if let Some(scheme) = exports.values.get(name) {
            ctx.class_method_schemes.entry(name.name).or_insert_with(|| scheme.clone());
        }
    }
    for (name, scheme) in &exports.values {
        // Don't let a non-class value overwrite a class method's env entry.
        // E.g. Data.Function.apply must not shadow Control.Apply.apply.
        // Only applies to unqualified imports — qualified names (Q.foo) can't conflict.
        if qualifier.is_none()
            && ctx.class_methods.contains_key(name)
            && !exports.class_methods.contains_key(name)
        {
            continue;
        }
        // Apply two fixes to prevent alias expansion collisions:
        // 1. For qualified imports, qualify type cons defined in source module with qualifier
        // 2. Canonicalize type cons that collide with existing local aliases
        let mut scheme = scheme.clone();
        if let Some((dt, q)) = &defined_types {
            scheme = Scheme {
                forall_vars: scheme.forall_vars,
                ty: canonicalize_type_cons(&scheme.ty, &dt.iter().map(|&n| (n, *q)).collect()),
            };
        }
        if let Some(co) = &canonical_origins {
            scheme = canonicalize_scheme_type_cons(&scheme, co);
        }
        env.insert_scheme(ValueName::new(maybe_qualify_symbol(name.name_symbol(), qualifier)), scheme);
    }
    for (name, ctors) in &exports.data_constructors {
        ctx.data_constructors.insert(*name, ctors.clone());
        if let Some(q) = qualifier {
            ctx.data_constructors.insert(qualify_t(*name, Some(q)), ctors.clone());
        }
    }
    for (name, details) in &exports.ctor_details {
        if let Some(q) = qualifier {
            // Qualified import: store under qualified key only (e.g. M.Leaf)
            // Don't insert unqualified — qualified imports don't make names
            // available unqualified, and doing so overwrites correct entries
            // from explicit unqualified imports (e.g. Left from Data.Either).
            ctx.ctor_details.insert(qualify_c(*name, Some(q)), details.clone());
        } else {
            ctx.ctor_details.insert(*name, details.clone());
        }
    }
    // Instances are imported centrally in process_imports with module-level dedup.
    for (op, target) in &exports.type_operators {
        ctx.type_operators.insert(*op, *target);
    }
    for (op, fixity) in &exports.value_fixities {
        ctx.value_fixities.insert(op.name, *fixity);
    }
    for op in &exports.function_op_aliases {
        ctx.function_op_aliases.insert(*op);
    }
    // For constructor operators (not function aliases), also import the target
    // constructor's scheme under its target name, because Binder::Constructor
    // uses the target name (e.g. `:|` → `NonEmpty`, `:` → `Cons`).
    // Function operator targets (e.g. `$` → `apply`) are NOT imported under their
    // target names to avoid collisions (Data.Function.apply vs Control.Apply.apply).
    for (op, target) in &exports.value_operator_targets {
        if !exports.function_op_aliases.contains(op) {
            if let Some(scheme) = exports.values.get(target) {
                env.insert_scheme(ValueName::new(maybe_qualify_symbol(target.name_symbol(), qualifier)), scheme.clone());
            }
        }
    }
    for (op, target) in &exports.operator_class_targets {
        ctx.operator_class_targets.insert(qualify_op(qop(op.symbol()), qualifier), qualify_v(qv(target.symbol()), qualifier));
    }
    for name in &exports.constrained_class_methods {
        ctx.constrained_class_methods.insert(name.name);
    }
    for (name, constraints) in &exports.method_own_constraints {
        ctx.method_own_constraints.entry(name.name).or_insert_with(|| constraints.clone());
    }
    for (name, details) in &exports.method_own_constraint_details {
        ctx.method_own_constraint_details.entry(*name).or_insert_with(|| details.clone());
    }
    // For qualified imports, build the set of type names that ORIGINATE from the source
    // module. We only canonicalize these in alias bodies — re-exported types (like String,
    // Maybe from Prim) should stay unqualified to avoid OaComponents.Table.String mismatches.
    let (source_module_sym, exported_type_names) = if qualifier.is_some() {
        let mod_sym = from.as_ref().map(module_name_to_symbol);
        let mut type_names: HashSet<TypeName> = HashSet::new();
        if let Some(mod_sym) = mod_sym {
            for (name, &origin) in &exports.type_origins {
                if origin == mod_sym {
                    type_names.insert(*name);
                }
            }
        }
        (mod_sym, type_names)
    } else {
        (None, HashSet::new())
    };
    for (name, alias) in &exports.type_aliases {
        let name_sym = name.name_symbol();
        let sym_params: Vec<TypeVarName> = alias.0.clone();
        // Canonicalize alias body with canonical_origins to prevent local aliases
        // from intercepting type constructor references in imported alias bodies.
        // E.g., an alias body containing `Time` (the Data.Time data type) must not
        // be expanded by a local `type Time = Number` alias.
        let body_canonicalized = if let Some(co) = &canonical_origins {
            canonicalize_type_cons(&alias.1, co)
        } else {
            alias.1.clone()
        };
        if qualifier.is_none() {
            // Unqualified import: register under unqualified key as before.
            // Don't register if it collides with a locally-defined data/newtype name.
            let collides_with_local_data = local_data_type_names.contains(&name.name);
            if !collides_with_local_data {
                ctx.state.type_aliases.insert(Qualified::unqualified(TypeName::new(name_sym)), (sym_params.clone(), body_canonicalized.clone()));
                ctx.qualified_import_unqual_aliases.remove(&name.name);
            }
        }
        // For qualified imports, canonicalize alias body so unqualified type refs
        // from the source module use the canonical module name. This allows
        // try_expand_alias to find them via canonical_to_qualifier fallback.
        let body_for_qualified = if let Some(mod_sym) = source_module_sym {
            canonicalize_alias_body_types(&body_canonicalized, mod_sym, &exported_type_names, Some(name_sym))
        } else {
            body_canonicalized.clone()
        };
        // Store under qualified key so alias expansion can disambiguate
        // when multiple modules export the same alias name with different bodies.
        if qualifier.is_some() {
            ctx.state.type_aliases.insert(qualify_t(Qualified::unqualified(TypeName::new(name_sym)), qualifier), (sym_params.clone(), body_for_qualified.clone()));
            ctx.qualified_type_alias_names.insert(qualify_t(*name, qualifier));
        }
        // Register under canonical qualified key (origin_module.name) so alias expansion
        // works after canonicalize_type_cons qualifies type constructors to avoid
        // local alias collisions. E.g., Con("Model") canonicalized to
        // Con("AdminDashboard.Model.Model") needs to find the alias under that key.
        // Skip canonical key registration for zero-param aliases: their body often
        // references the canonical form of the same name (e.g. type X = Canon.X a b c),
        // creating a self-referential zero-arg alias under the canonical key.
        if !sym_params.is_empty() {
            if let Some(co) = &canonical_origins {
                if let Some(&origin) = co.get(&name_sym) {
                    let canonical_key = Qualified::qualified(ModuleQualifier::new(origin), TypeName::new(name_sym));
                    let body = if qualifier.is_some() { body_for_qualified.clone() } else { body_canonicalized.clone() };
                    ctx.state.type_aliases.entry(canonical_key)
                        .or_insert((sym_params.clone(), body));
                }
            }
        }
        // Also register under defined_types qualified key for qualified imports.
        if let Some((dt, q)) = &defined_types {
            if dt.contains(&name_sym) {
                let dt_key = Qualified::qualified(ModuleQualifier::new(*q), TypeName::new(name_sym));
                let body = if qualifier.is_some() { body_for_qualified.clone() } else { body_canonicalized.clone() };
                ctx.state.type_aliases.entry(dt_key)
                    .or_insert((sym_params.clone(), body));
            }
        }
    }
    for (name, arity) in &exports.type_con_arities {
        ctx.type_con_arities.insert(qualify_t(*name, qualifier), *arity);
    }
    for (name, roles) in &exports.type_roles {
        ctx.type_roles.insert(*name, roles.clone());
    }
    for name in &exports.newtype_names {
        ctx.newtype_names.insert(qualify_t(qt(name.symbol()), qualifier));
    }
    for name in &exports.partial_dischargers {
        ctx.partial_dischargers.insert(qualify_v(qv(name.symbol()), qualifier));
    }
    for (name, constraints) in &exports.signature_constraints {
        // Import Coercible and solver-class constraints for typechecking.
        // Solver-class constraints (Union, Nub, etc.) need to reach deferred_constraints
        // so Pass 2.75 can solve them. Other constraints are handled locally via
        // extract_type_signature_constraints on CST types.
        let solver_constraints: Vec<_> = constraints
            .iter()
            .filter(|(cn, _)| {
                let cn_str = crate::interner::resolve(cn.name_symbol()).unwrap_or_default();
                matches!(cn_str.as_str(),
                    "Coercible" | "Union" | "Nub"
                    | "Add" | "Mul" | "ToString" | "Compare" | "Append"
                    | "CompareSymbol" | "RowToList"
                )
            })
            .cloned()
            .collect();
        if !solver_constraints.is_empty() {
            ctx.signature_constraints
                .entry(qualify_v(*name, qualifier))
                .or_default()
                .extend(solver_constraints);
        }
        // Import ALL constraints for codegen dict resolution.
        // Preserve duplicates with same class name (e.g., two Newtype constraints
        // on `over :: Newtype t a => Newtype s b => ...`).
        if !constraints.is_empty() {
            let entry = ctx.codegen_signature_constraints
                .entry(qualify_v(*name, qualifier))
                .or_default();
            if entry.is_empty() {
                entry.extend(constraints.clone());
            }
        }
    }
    // Also register codegen_signature_constraints AND signature_constraints under operator names.
    // When `>>>` targets `composeFlipped` which has Semigroupoid constraint,
    // the operator name needs to look up those constraints too.
    for (op, target) in &exports.value_operator_targets {
        // Look up constraints under both the target name AND the operator name.
        // Re-exporting modules may store constraints under the operator name
        // (when the target function wasn't explicitly imported, only the operator was).
        let op_as_value: Qualified<ValueName> = op.map(names::op_as_value);
        let constraints = exports.signature_constraints.get(target)
            .or_else(|| exports.signature_constraints.get(&op_as_value));
        if let Some(constraints) = constraints {
            if !constraints.is_empty() {
                let op_key = qualify_v(op_as_value, qualifier);
                ctx.codegen_signature_constraints
                    .entry(op_key)
                    .or_default()
                    .extend(constraints.clone());
                // Also register in signature_constraints so that infer_var's Forall
                // branch pushes to deferred_constraints (not just codegen_deferred_constraints).
                // This ensures the constraint's unif vars participate in unification and get
                // resolved at Pass 3.
                ctx.signature_constraints
                    .entry(op_key)
                    .or_default()
                    .extend(constraints.clone());
            }
        }
    }
}

/// Import a single item from a module's exports.
/// If `qualifier` is Some, env entries are stored with qualified keys.
pub(crate) fn import_item(
    _module_name: &ModuleName,
    item: &Import,
    exports: &ModuleExports,
    env: &mut Env,
    ctx: &mut InferCtx,
    _instances: &mut HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    qualifier: Option<Symbol>,
    import_span: crate::span::Span,
    errors: &mut Vec<TypeError>,
    canonical_origins: &Option<HashMap<Symbol, Symbol>>,
) {
    match item {
        Import::Value(name_spanned) => {
            let name = name_spanned.value;
            let name_sym = name.symbol();
            let name_qv = qv(name_sym);
            let name_qop = qop(name_sym);
            if exports.values.get(&name_qv).is_none() && exports.class_methods.get(&name_qv).is_none() {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: name_sym,
                });
                return;
            }
            // Import class method info first if applicable
            if let Some(info) = exports.class_methods.get(&name_qv) {
                ctx.class_methods.insert(name_qv, info.clone());
            }
            if let Some(scheme) = exports.values.get(&name_qv) {
                // Explicit imports always win — the user specifically asked for this value.
                // Canonicalize type constructors that collide with local type aliases
                // to prevent incorrect alias expansion. E.g., if the local module defines
                // `type File = { ... }`, imported `getMediaType :: File -> String` must
                // have its `File` qualified to `Web.File.File.File` to avoid expansion.
                let scheme = if let Some(co) = canonical_origins {
                    canonicalize_scheme_type_cons(scheme, co)
                } else {
                    scheme.clone()
                };
                env.insert_scheme(ValueName::new(maybe_qualify_symbol(name_sym, qualifier)), scheme);
            }
            // Instances are imported centrally in process_imports with module-level dedup.
            // Import fixity if this is an operator
            if let Some(fixity) = exports.value_fixities.get(&name_qop) {
                ctx.value_fixities.insert(OpName::new(name_sym), *fixity);
            }
            if exports.function_op_aliases.contains(&name_qop) {
                ctx.function_op_aliases.insert(name_qop);
            }
            if let Some(target) = exports.operator_class_targets.get(&OpName::new(name_sym)) {
                ctx.operator_class_targets.insert(Qualified::unqualified(OpName::new(name_sym)), Qualified::unqualified(*target));
                // Also import the target's class method info so the class_method_lookup
                // in infer_var can resolve the constraint (e.g. <> → append → Semigroup).
                if let Some(info) = exports.class_methods.get(&qv(target.symbol())) {
                    ctx.class_methods.entry(Qualified::unqualified(*target))
                        .or_insert_with(|| info.clone());
                }
            }
            if exports.constrained_class_methods.contains(&name_qv) {
                ctx.constrained_class_methods.insert(name);
            }
            if let Some(constraints) = exports.method_own_constraints.get(&name_qv) {
                ctx.method_own_constraints.entry(name).or_insert_with(|| constraints.clone());
            }
            if let Some(details) = exports.method_own_constraint_details.get(&name) {
                ctx.method_own_constraint_details.entry(name).or_insert_with(|| details.clone());
            }
            // Import ctor_details if this is a constructor alias (e.g. `:|` for `NonEmpty`)
            if let Some(details) = exports.ctor_details.get(&qc(name_sym)) {
                ctx.ctor_details.insert(qc(name_sym), details.clone());
            }
            // Import solver-class constraints for typechecking (Coercible, Union, Nub, etc.)
            if let Some(constraints) = exports.signature_constraints.get(&name_qv) {
                // Use qualified key so infer_var can find constraints when the import
                // has a qualifier (e.g., `import Pipes.Core (...) as P`).
                let qualified_key = qualify_v(name_qv, qualifier);
                let solver_only: Vec<_> = constraints
                    .iter()
                    .filter(|(cn, _)| {
                        let cn_str = crate::interner::resolve(cn.name_symbol()).unwrap_or_default();
                        matches!(cn_str.as_str(),
                            "Coercible" | "Union" | "Nub"
                            | "Add" | "Mul" | "ToString" | "Compare" | "Append"
                            | "CompareSymbol" | "RowToList"
                        )
                    })
                    .cloned()
                    .collect();
                if !solver_only.is_empty() {
                    ctx.signature_constraints
                        .entry(qualified_key)
                        .or_default()
                        .extend(solver_only);
                }
                // Import ALL constraints for codegen dict resolution.
                // Use `if entry.is_empty()` guard to avoid duplicates when the same name
                // is imported multiple times (e.g., once unqualified and once as Exports).
                if !constraints.is_empty() {
                    let entry = ctx.codegen_signature_constraints
                        .entry(qualified_key)
                        .or_default();
                    if entry.is_empty() {
                        entry.extend(constraints.clone());
                    }
                }
            }
            // For operators, also import their target's codegen constraints under the operator name
            if let Some(target) = exports.value_operator_targets.get(&name_qop) {
                let target_as_value: Qualified<ValueName> = target.map(|v| v);
                let op_as_value: Qualified<ValueName> = name_qop.map(names::op_as_value);
                let constraints = exports.signature_constraints.get(&target_as_value)
                    .or_else(|| exports.signature_constraints.get(&op_as_value));
                if let Some(constraints) = constraints {
                    if !constraints.is_empty() {
                        let qualified_key = qualify_v(name_qv, qualifier);
                        ctx.codegen_signature_constraints
                            .entry(qualified_key)
                            .or_default()
                            .extend(constraints.clone());
                        // Also add to signature_constraints for deferred_constraints path
                        ctx.signature_constraints
                            .entry(qualified_key)
                            .or_default()
                            .extend(constraints.clone());
                    }
                }
            }
            // Import partial discharger info (functions with Partial in param position)
            if exports.partial_dischargers.contains(&name) {
                ctx.partial_dischargers
                    .insert(qualify_v(qv(name_sym), qualifier));
            }
            // Import ctor_details if the operator targets a constructor (e.g. `:` → Cons)
            // Use the TARGET name as key since Binder::Constructor uses the target name
            if let Some(target) = exports.value_operator_targets.get(&name_qop) {
                // target is Qualified<ValueName>, ctor_details keys are Qualified<ConstructorName>
                let target_ctor = target.map(names::value_as_constructor);
                if let Some(details) = exports.ctor_details.get(&target_ctor) {
                    ctx.ctor_details.insert(target_ctor, details.clone());
                }
                // For constructor operators, also import the target constructor's scheme
                // under its target name (e.g. `:|` → import `NonEmpty` constructor scheme)
                if !exports.function_op_aliases.contains(&name_qop) {
                    if let Some(scheme) = exports.values.get(target) {
                        env.insert_scheme(ValueName::new(maybe_qualify_symbol(target.name_symbol(), qualifier)), scheme.clone());
                    }
                }
            }
        }
        Import::Type(name_spanned, members) => {
            let name = name_spanned.value;
            let name_sym = name.symbol();
            let name_qt = qt(name_sym);
            if let Some(ctors) = exports.data_constructors.get(&name_qt) {
                ctx.data_constructors.insert(name_qt, ctors.clone());
                if let Some(q) = qualifier {
                    ctx.data_constructors.insert(qualify_t(name_qt, Some(q)), ctors.clone());
                }
                if let Some(arity) = exports.type_con_arities.get(&name_qt) {
                    ctx.type_con_arities.insert(name_qt, *arity);
                }
                if let Some(roles) = exports.type_roles.get(&name) {
                    ctx.type_roles.insert(name, roles.clone());
                }
                if exports.newtype_names.contains(&name) {
                    ctx.newtype_names.insert(name_qt);
                }

                let import_ctors: Vec<Qualified<ConstructorName>> = match members {
                    Some(DataMembers::All) => ctors.clone(),
                    Some(DataMembers::Explicit(listed)) => {
                        // Validate that each listed constructor actually exists
                        for ctor_name in listed {
                            if !ctors.iter().any(|c| c.name_symbol() == ctor_name.value.symbol()) {
                                errors.push(TypeError::UnknownImportDataConstructor {
                                    span: import_span,
                                    name: ctor_name.value,
                                });
                            }
                        }
                        listed.iter().map(|n| qc(n.value.symbol())).collect()
                    }
                    None => Vec::new(), // Just the type, no constructors
                };

                for ctor in &import_ctors {
                    // Look up constructor scheme using ValueName (constructors are values)
                    let ctor_as_value = ctor.map(names::constructor_as_value);
                    if let Some(scheme) = exports.values.get(&ctor_as_value) {
                        let scheme = if let Some(co) = canonical_origins {
                            canonicalize_scheme_type_cons(scheme, co)
                        } else {
                            scheme.clone()
                        };
                        env.insert_scheme(ValueName::new(maybe_qualify_symbol(ctor.name_symbol(), qualifier)), scheme);
                    }
                }
                // Import ctor_details for ALL constructors when at least some are imported,
                // so the exhaustiveness checker can resolve operator aliases.
                // e.g. `import Data.List (List(Nil), (:))` needs Cons ctor_details
                // to match `:` against `Cons` during exhaustiveness checking.
                // But DON'T import ctor_details for type-only imports (members=None),
                // as the Coercible solver uses ctor_details availability to check
                // constructor accessibility for newtype unwrapping.
                if members.is_some() {
                    for ctor in ctors {
                        if let Some(details) = exports.ctor_details.get(ctor) {
                            if let Some(q) = qualifier {
                                // Qualified import: store under qualified key only
                                ctx.ctor_details.insert(qualify_c(*ctor, Some(q)), details.clone());
                            } else {
                                ctx.ctor_details.insert(*ctor, details.clone());
                            }
                        }
                    }
                }
                // Also import the type alias if one exists with the same name
                // (kind signatures create data_constructors entries for type aliases)
                if let Some(alias) = exports.type_aliases.get(&name_qt) {
                    let sym_params: Vec<TypeVarName> = alias.0.clone();
                    if qualifier.is_none() {
                        let body = if let Some(co) = canonical_origins {
                            canonicalize_type_cons(&alias.1, co)
                        } else {
                            alias.1.clone()
                        };
                        ctx.state.type_aliases.insert(Qualified::unqualified(TypeName::new(name_sym)), (sym_params.clone(), body));
                        ctx.qualified_import_unqual_aliases.remove(&name);
                    }
                    if let Some(q) = qualifier {
                        // Canonicalize body for qualified import
                        let mod_sym = module_name_to_symbol(_module_name);
                        let mut type_names: HashSet<TypeName> = HashSet::new();
                        for (n, &origin) in &exports.type_origins {
                            if origin == mod_sym { type_names.insert(*n); }
                        }
                        let body = canonicalize_alias_body_types(&alias.1, mod_sym, &type_names, Some(name_sym));
                        ctx.state.type_aliases.insert(qualify_t(Qualified::unqualified(TypeName::new(name_sym)), qualifier), (sym_params.clone(), body.clone()));
                        ctx.qualified_type_alias_names.insert(qualify_t(name_qt, Some(q)));
                        // Register under canonical key
                        if let Some(co) = canonical_origins {
                            if let Some(&origin) = co.get(&name_sym) {
                                let canonical_key = Qualified::qualified(ModuleQualifier::new(origin), TypeName::new(name_sym));
                                ctx.state.type_aliases.entry(canonical_key)
                                    .or_insert((sym_params.clone(), body));
                            }
                        }
                    } else {
                        // Register under canonical key (unqualified import)
                        // Skip for zero-param aliases to avoid self-referential expansion loops.
                        if !sym_params.is_empty() {
                            if let Some(co) = canonical_origins {
                                if let Some(&origin) = co.get(&name_sym) {
                                    let canonical_key = Qualified::qualified(ModuleQualifier::new(origin), TypeName::new(name_sym));
                                    ctx.state.type_aliases.entry(canonical_key)
                                        .or_insert((sym_params.clone(), alias.1.clone()));
                                }
                            }
                        }
                    }
                }
            } else if let Some(alias) = exports.type_aliases.get(&name_qt) {
                // Type alias import
                let sym_params: Vec<TypeVarName> = alias.0.clone();
                if qualifier.is_none() {
                    // Canonicalize alias body to avoid collisions with local type aliases.
                    let body = if let Some(co) = canonical_origins {
                        canonicalize_type_cons(&alias.1, co)
                    } else {
                        alias.1.clone()
                    };
                    ctx.state.type_aliases.insert(Qualified::unqualified(TypeName::new(name_sym)), (sym_params.clone(), body));
                    ctx.qualified_import_unqual_aliases.remove(&name);
                }
                if qualifier.is_some() {
                    // Canonicalize body for qualified import
                    let mod_sym = module_name_to_symbol(_module_name);
                    let alias_names: HashSet<TypeName> = exports.type_aliases.keys().map(|k| k.name).collect();
                    let body = canonicalize_alias_body_types(&alias.1, mod_sym, &alias_names, Some(name_sym));
                    ctx.state.type_aliases.insert(qualify_t(Qualified::unqualified(TypeName::new(name_sym)), qualifier), (sym_params.clone(), body.clone()));
                    ctx.qualified_type_alias_names.insert(qualify_t(name_qt, qualifier));
                    // Register under canonical key (skip zero-param to avoid self-ref loops)
                    if !sym_params.is_empty() {
                        if let Some(co) = canonical_origins {
                            if let Some(&origin) = co.get(&name_sym) {
                                let canonical_key = Qualified::qualified(ModuleQualifier::new(origin), TypeName::new(name_sym));
                                ctx.state.type_aliases.entry(canonical_key)
                                    .or_insert((sym_params.clone(), body));
                            }
                        }
                    }
                } else {
                    // Register under canonical key (unqualified import, skip zero-param)
                    if !sym_params.is_empty() {
                        if let Some(co) = canonical_origins {
                            if let Some(&origin) = co.get(&name_sym) {
                                let canonical_key = Qualified::qualified(ModuleQualifier::new(origin), TypeName::new(name_sym));
                                ctx.state.type_aliases.entry(canonical_key)
                                    .or_insert((sym_params.clone(), alias.1.clone()));
                            }
                        }
                    }
                }
            } else {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: name_sym,
                });
            }
        }
        Import::Class(name_spanned) => {
            let name = name_spanned.value;
            let name_sym = name.symbol();
            let name_qcl = qcl(name_sym);
            // Check if the class exists in the exports: it may have methods,
            // instances, or be a constraint-only class (no methods, e.g. `class (A a, B a) <= C a`).
            let has_class = exports.class_methods.values().any(|(cn, _)| cn.name_symbol() == name_sym)
                || exports.instances.get(&name_qcl).is_some()
                || exports.class_param_counts.contains_key(&name_qcl);
            if !has_class {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: name_sym,
                });
                return;
            }
            for (method_name, info) in &exports.class_methods {
                if info.0.name_symbol() == name_sym {
                    ctx.class_methods
                        .insert(*method_name, info.clone());
                    if exports.constrained_class_methods.contains(method_name) {
                        ctx.constrained_class_methods.insert(method_name.name);
                    }
                    if let Some(constraints) = exports.method_own_constraints.get(method_name) {
                        ctx.method_own_constraints.entry(method_name.name).or_insert_with(|| constraints.clone());
                    }
                    if let Some(details) = exports.method_own_constraint_details.get(&method_name.name) {
                        ctx.method_own_constraint_details.entry(method_name.name).or_insert_with(|| details.clone());
                    }
                    // Also populate class_method_schemes so instance expected-type
                    // lookups can use the canonical class type even if the method
                    // name gets shadowed in env by a later value import.
                    if let Some(scheme) = exports.values.get(method_name) {
                        ctx.class_method_schemes.insert(method_name.name, scheme.clone());
                    }
                }
            }
            // Instances are imported centrally in process_imports with module-level dedup.
        }
        Import::TypeOp(name_spanned) => {
            let name = name_spanned.value;
            let name_sym = name.symbol();
            let name_qtop = qtop(name_sym);
            if let Some(target) = exports.type_operators.get(&name_qtop) {
                ctx.type_operators.insert(name_qtop, *target);
                // Import the target's type alias definition if it exists
                // target is Qualified<TypeName>; type_aliases is keyed by Qualified<TypeName>
                if let Some(alias) = exports.type_aliases.get(target) {
                    let sym_params: Vec<TypeVarName> = alias.0.clone();
                    let target_sym = target.name_symbol();
                    if qualifier.is_none() {
                        ctx.state.type_aliases.insert(Qualified::unqualified(target.name), (sym_params.clone(), alias.1.clone()));
                    } else {
                        let mod_sym = module_name_to_symbol(_module_name);
                        let mut type_names: HashSet<TypeName> = HashSet::new();
                        for (n, &origin) in &exports.type_origins {
                            if origin == mod_sym { type_names.insert(*n); }
                        }
                        let body = canonicalize_alias_body_types(&alias.1, mod_sym, &type_names, Some(target_sym));
                        ctx.state.type_aliases.insert(qualify_t(Qualified::unqualified(target.name), qualifier), (sym_params, body));
                    }
                }
            } else {
                errors.push(TypeError::UnknownImport {
                    span: import_span,
                    name: name_sym,
                });
            }
        }
    }
}

/// Import all names except those in the hidden set.
/// If `qualifier` is Some, env entries are stored with qualified keys.
pub(crate) fn import_all_except(
    from: Option<ModuleName>,
    exports: &ModuleExports,
    hidden: &HashSet<Symbol>,
    env: &mut Env,
    ctx: &mut InferCtx,
    _instances: &mut HashMap<Qualified<ClassName>, Vec<(Vec<Type>, Vec<(Qualified<ClassName>, Vec<Type>)>, Option<Symbol>)>>,
    qualifier: Option<Symbol>,
    local_data_type_names: &HashSet<TypeName>,
    canonical_origins: &Option<HashMap<Symbol, Symbol>>,
) {
    // Import class method info first so we can detect conflicts
    for (name, info) in &exports.class_methods {
        if !hidden.contains(&name.name_symbol()) {
            ctx.class_methods.insert(*name, info.clone());
        }
    }
    for (name, scheme) in &exports.values {
        if !hidden.contains(&name.name_symbol()) {
            // Don't let a non-class value overwrite a class method's env entry.
            // Only applies to unqualified imports — qualified names (Q.foo) can't conflict.
            if qualifier.is_none()
                && ctx.class_methods.contains_key(name)
                && !exports.class_methods.contains_key(name)
            {
                continue;
            }
            // Canonicalize type constructors that collide with local type aliases
            let scheme = if let Some(co) = canonical_origins {
                canonicalize_scheme_type_cons(scheme, co)
            } else {
                scheme.clone()
            };
            env.insert_scheme(ValueName::new(maybe_qualify_symbol(name.name_symbol(), qualifier)), scheme);
        }
    }
    for (name, ctors) in &exports.data_constructors {
        if !hidden.contains(&name.name_symbol()) {
            ctx.data_constructors.insert(*name, ctors.clone());
            if let Some(q) = qualifier {
                ctx.data_constructors.insert(qualify_t(*name, Some(q)), ctors.clone());
            }
            for ctor in ctors {
                if !hidden.contains(&ctor.name_symbol()) {
                    if let Some(details) = exports.ctor_details.get(ctor) {
                        if let Some(q) = qualifier {
                            ctx.ctor_details.insert(qualify_c(*ctor, Some(q)), details.clone());
                        } else {
                            ctx.ctor_details.insert(*ctor, details.clone());
                        }
                    }
                }
            }
        }
    }
    // Instances are imported centrally in process_imports with module-level dedup.
    for (op, target) in &exports.type_operators {
        if !hidden.contains(&op.name_symbol()) {
            ctx.type_operators.insert(*op, *target);
        }
    }
    for (op, fixity) in &exports.value_fixities {
        if !hidden.contains(&op.name_symbol()) {
            ctx.value_fixities.insert(op.name, *fixity);
        }
    }
    for op in &exports.function_op_aliases {
        if !hidden.contains(&op.name_symbol()) {
            ctx.function_op_aliases.insert(*op);
        }
    }
    // For constructor operators, also import the target constructor's scheme
    for (op, target) in &exports.value_operator_targets {
        if !hidden.contains(&op.name_symbol()) && !exports.function_op_aliases.contains(op) {
            if let Some(scheme) = exports.values.get(target) {
                env.insert_scheme(ValueName::new(maybe_qualify_symbol(target.name_symbol(), qualifier)), scheme.clone());
            }
        }
    }
    for (op, target) in &exports.operator_class_targets {
        if !hidden.contains(&op.symbol()) {
            ctx.operator_class_targets.insert(qualify_op(qop(op.symbol()), qualifier), qualify_v(qv(target.symbol()), qualifier));
        }
    }
    for name in &exports.constrained_class_methods {
        if !hidden.contains(&name.name_symbol()) {
            ctx.constrained_class_methods.insert(name.name);
        }
    }
    for (name, constraints) in &exports.method_own_constraints {
        if !hidden.contains(&name.name_symbol()) {
            ctx.method_own_constraints.entry(name.name).or_insert_with(|| constraints.clone());
        }
    }
    for (name, details) in &exports.method_own_constraint_details {
        if !hidden.contains(&name.symbol()) {
            ctx.method_own_constraint_details.entry(*name).or_insert_with(|| details.clone());
        }
    }
    // For qualified imports, build set of type names originating from source module.
    let (source_module_sym, exported_type_names) = if qualifier.is_some() {
        let mod_sym = from.as_ref().map(module_name_to_symbol);
        let mut type_names: HashSet<TypeName> = HashSet::new();
        if let Some(mod_sym) = mod_sym {
            for (name, &origin) in &exports.type_origins {
                if origin == mod_sym {
                    type_names.insert(*name);
                }
            }
        }
        (mod_sym, type_names)
    } else {
        (None, HashSet::new())
    };
    for (name, alias) in &exports.type_aliases {
        let name_sym = name.name_symbol();
        if !hidden.contains(&name_sym) {
            let sym_params: Vec<TypeVarName> = alias.0.clone();
            // Canonicalize alias body with canonical_origins to prevent local aliases
            // from intercepting type constructor references in imported alias bodies.
            let body_canonicalized = if let Some(co) = canonical_origins {
                canonicalize_type_cons(&alias.1, co)
            } else {
                alias.1.clone()
            };
            if qualifier.is_none() {
                // Unqualified import: register under unqualified key.
                let collides_with_local_data = local_data_type_names.contains(&name.name);
                if !collides_with_local_data {
                    ctx.state.type_aliases.insert(Qualified::unqualified(TypeName::new(name_sym)), (sym_params.clone(), body_canonicalized.clone()));
                    ctx.qualified_import_unqual_aliases.remove(&name.name);
                }
            }
            // Canonicalize alias body for qualified imports.
            let body_for_qualified = if let Some(mod_sym) = source_module_sym {
                canonicalize_alias_body_types(&body_canonicalized, mod_sym, &exported_type_names, Some(name_sym))
            } else {
                body_canonicalized.clone()
            };
            if qualifier.is_some() {
                ctx.state.type_aliases.insert(qualify_t(Qualified::unqualified(TypeName::new(name_sym)), qualifier), (sym_params.clone(), body_for_qualified.clone()));
                ctx.qualified_type_alias_names.insert(qualify_t(*name, qualifier));
            }
            // Register under canonical qualified key so alias expansion works after
            // canonicalize_type_cons qualifies type constructors.
            // Skip for zero-param aliases to avoid self-referential expansion loops.
            if !sym_params.is_empty() {
            if let Some(co) = canonical_origins {
                if let Some(&origin) = co.get(&name_sym) {
                    let canonical_key = Qualified::qualified(ModuleQualifier::new(origin), TypeName::new(name_sym));
                    let body = if qualifier.is_some() { body_for_qualified.clone() } else { body_canonicalized.clone() };
                    ctx.state.type_aliases.entry(canonical_key)
                        .or_insert((sym_params.clone(), body));
                }
            }
            }
        }
    }
    for (name, arity) in &exports.type_con_arities {
        if !hidden.contains(&name.name_symbol()) {
            ctx.type_con_arities.insert(qualify_t(*name, qualifier), *arity);
        }
    }
    // Roles, newtype info, and signature constraints are always imported (non-hideable)
    for (name, roles) in &exports.type_roles {
        ctx.type_roles.insert(*name, roles.clone());
    }
    for name in &exports.newtype_names {
        ctx.newtype_names.insert(qualify_t(qt(name.symbol()), qualifier));
    }
    for name in &exports.partial_dischargers {
        if !hidden.contains(&name.symbol()) {
            ctx.partial_dischargers
                .insert(qualify_v(qv(name.symbol()), qualifier));
        }
    }
    for (name, constraints) in &exports.signature_constraints {
        if !hidden.contains(&name.name_symbol()) {
            let solver_only: Vec<_> = constraints
                .iter()
                .filter(|(cn, _)| {
                    let cn_str = crate::interner::resolve(cn.name_symbol()).unwrap_or_default();
                    matches!(cn_str.as_str(),
                        "Coercible" | "Union" | "Nub"
                        | "Add" | "Mul" | "ToString" | "Compare" | "Append"
                        | "CompareSymbol" | "RowToList"
                    )
                })
                .cloned()
                .collect();
            if !solver_only.is_empty() {
                ctx.signature_constraints
                    .entry(qualify_v(*name, qualifier))
                    .or_default()
                    .extend(solver_only);
            }
            // Import ALL constraints for codegen dict resolution
            if !constraints.is_empty() {
                ctx.codegen_signature_constraints
                    .entry(qualify_v(*name, qualifier))
                    .or_default()
                    .extend(constraints.clone());
            }
        }
    }
    // Also register codegen_signature_constraints AND signature_constraints under operator names
    for (op, target) in &exports.value_operator_targets {
        if !hidden.contains(&op.name_symbol()) {
            let op_as_value: Qualified<ValueName> = op.map(names::op_as_value);
            let constraints = exports.signature_constraints.get(target)
                .or_else(|| exports.signature_constraints.get(&op_as_value));
            if let Some(constraints) = constraints {
                if !constraints.is_empty() {
                    let op_key = qualify_v(op_as_value, qualifier);
                    ctx.codegen_signature_constraints
                        .entry(op_key)
                        .or_default()
                        .extend(constraints.clone());
                    ctx.signature_constraints
                        .entry(op_key)
                        .or_default()
                        .extend(constraints.clone());
                }
            }
        }
    }
}

/// Get the primary symbol name from an Import item.
pub(crate) fn import_name(item: &Import) -> Symbol {
    item.name()
}

/// Determines which names from a module's exports should be re-exported,
/// based on the import declaration. In PureScript, `module X` in an export
/// list only re-exports what was actually imported from X in this module.
pub(crate) struct ImportFilter {
    /// None = import all (no filtering). Some = only these names allowed.
    values: Option<HashSet<ValueName>>,
    types: Option<HashSet<TypeName>>,
    classes: Option<HashSet<ClassName>>,
    type_ops: Option<HashSet<TypeOpName>>,
}

pub(crate) fn build_import_filter(
    import_decl: &crate::cst::ImportDecl,
    mod_exports: &ModuleExports,
) -> ImportFilter {
    match &import_decl.imports {
        None => ImportFilter {
            values: None,
            types: None,
            classes: None,
            type_ops: None,
        },
        Some(crate::cst::ImportList::Explicit(imports)) => {
            let mut values: HashSet<ValueName> = HashSet::new();
            let mut types: HashSet<TypeName> = HashSet::new();
            let mut classes: HashSet<ClassName> = HashSet::new();
            let mut type_ops: HashSet<TypeOpName> = HashSet::new();
            for imp in imports {
                match imp {
                    crate::cst::Import::Value(name) => {
                        values.insert(name.value);
                        // Importing an operator also imports its target value into the env
                        // so the typechecker can look up its type (AST desugars `1 + 2` to `add 1 2`).
                        // The AST converter gates user-visible scoping separately.
                        if let Some(target) = mod_exports.value_operator_targets.get(&qop(name.value.symbol())) {
                            values.insert(target.name);
                        }
                    }
                    crate::cst::Import::Type(name, members) => {
                        types.insert(name.value);
                        // Importing Type(..) also imports its constructors as values
                        if let Some(crate::cst::DataMembers::All) = members {
                            if let Some(ctors) = mod_exports.data_constructors.get(&qt(name.value.symbol())) {
                                for ctor in ctors {
                                    values.insert(ValueName::new(ctor.name_symbol()));
                                }
                            }
                        } else if let Some(crate::cst::DataMembers::Explicit(ctor_names)) = members
                        {
                            for ctor in ctor_names {
                                values.insert(ValueName::new(ctor.value.symbol()));
                            }
                        }
                    }
                    crate::cst::Import::Class(name) => {
                        classes.insert(name.value);
                        // Importing a class also imports all its methods
                        for (method_name, (class_name, _)) in &mod_exports.class_methods {
                            if class_name.name == name.value {
                                values.insert(method_name.name);
                            }
                        }
                    }
                    crate::cst::Import::TypeOp(name) => {
                        type_ops.insert(name.value);
                    }
                }
            }
            ImportFilter {
                values: Some(values),
                types: Some(types),
                classes: Some(classes),
                type_ops: Some(type_ops),
            }
        }
        Some(crate::cst::ImportList::Hiding(imports)) => {
            // For hiding, build exclusion sets and invert to "everything except hidden"
            let mut hidden_values: HashSet<ValueName> = HashSet::new();
            let mut hidden_types: HashSet<TypeName> = HashSet::new();
            let mut hidden_classes: HashSet<ClassName> = HashSet::new();
            let mut hidden_type_ops: HashSet<TypeOpName> = HashSet::new();
            for imp in imports {
                match imp {
                    crate::cst::Import::Value(name) => {
                        hidden_values.insert(name.value);
                    }
                    crate::cst::Import::Type(name, members) => {
                        hidden_types.insert(name.value);
                        if let Some(crate::cst::DataMembers::All) = members {
                            if let Some(ctors) = mod_exports.data_constructors.get(&qt(name.value.symbol())) {
                                for ctor in ctors {
                                    hidden_values.insert(ValueName::new(ctor.name_symbol()));
                                }
                            }
                        } else if let Some(crate::cst::DataMembers::Explicit(ctor_names)) = members
                        {
                            for ctor in ctor_names {
                                hidden_values.insert(ValueName::new(ctor.value.symbol()));
                            }
                        }
                    }
                    crate::cst::Import::Class(name) => {
                        hidden_classes.insert(name.value);
                        for (method_name, (class_name, _)) in &mod_exports.class_methods {
                            if class_name.name == name.value {
                                hidden_values.insert(method_name.name);
                            }
                        }
                    }
                    crate::cst::Import::TypeOp(name) => {
                        hidden_type_ops.insert(name.value);
                    }
                }
            }
            // Build allowed sets = everything in mod_exports minus hidden
            let values: HashSet<ValueName> = mod_exports
                .values
                .keys()
                .map(|n| n.name)
                .filter(|n| !hidden_values.contains(n))
                .collect();
            let types: HashSet<TypeName> = mod_exports
                .data_constructors
                .keys()
                .map(|n| n.name)
                .chain(mod_exports.type_aliases.keys().map(|n| n.name))
                .filter(|n| !hidden_types.contains(n))
                .collect();
            let classes: HashSet<ClassName> = mod_exports
                .class_methods
                .values()
                .map(|(c, _)| c.name)
                .filter(|n| !hidden_classes.contains(n))
                .collect();
            let type_ops: HashSet<TypeOpName> = mod_exports
                .type_operators
                .keys()
                .map(|n| n.name)
                .filter(|n| !hidden_type_ops.contains(n))
                .collect();
            ImportFilter {
                values: Some(values),
                types: Some(types),
                classes: Some(classes),
                type_ops: Some(type_ops),
            }
        }
    }
}

/// Filter a module's exports according to an explicit export list.
pub(crate) fn filter_exports(
    all: &ModuleExports,
    export_list: &crate::cst::ExportList,
    export_span: crate::span::Span,
    _local_types: &HashSet<Symbol>,
    _local_classes: &HashSet<crate::names::ClassName>,
    registry: &ModuleRegistry,
    imports: &[crate::cst::ImportDecl],
    current_module: &crate::cst::ModuleName,
    errors: &mut Vec<TypeError>,
    _scope_conflicts: &HashSet<ValueName>,
) -> ModuleExports {
    let mut result = ModuleExports::default();

    // Track the original defining module for each exported name (for conflict detection).
    // When two different re-export modules contribute the same name, it's only a conflict
    // if the names have different origins (i.e. independently defined in different modules).
    // Re-exporting the same definition through different paths is allowed (ModuleExportDupes).
    // We also track the import qualifier to distinguish ScopeConflict (same qualifier) from
    // ExportConflict (different qualifiers).
    // Each entry stores (origin_module, import_qualifier, is_locally_defined_in_source).
    // The is_locally_defined flag indicates whether the name was defined in the source module
    // (origin == source) vs. re-exported through it. Conflicts are only genuine when BOTH
    // names are locally defined in different modules. Re-exported names may trace to the same
    // definition but through different import paths, which is not a conflict.
    let mut value_origins: HashMap<Symbol, (Symbol, Option<Symbol>, bool)> = HashMap::new();
    let mut type_origins: HashMap<Symbol, (Symbol, Option<Symbol>, bool)> = HashMap::new();
    let mut class_origins: HashMap<Symbol, (Symbol, Option<Symbol>, bool)> = HashMap::new();

    for export in &export_list.exports {
        match export {
            Export::Value(name) => {
                let name_sym = name.symbol();
                let name_qv = qv(name_sym);
                let name_qop = qop(name_sym);
                let name_vn = *name;
                let name_on = OpName::new(name_sym);
                if let Some(scheme) = all.values.get(&name_qv) {
                    result.values.insert(name_qv, scheme.clone());
                }
                // Also export class method info if applicable
                if let Some(info) = all.class_methods.get(&name_qv) {
                    result.class_methods.insert(name_qv, info.clone());
                }
                // Also export fixity if applicable
                if let Some(fixity) = all.value_fixities.get(&name_qop) {
                    result.value_fixities.insert(name_qop, *fixity);
                }
                if all.function_op_aliases.contains(&name_qop) {
                    result.function_op_aliases.insert(name_qop);
                }
                if let Some(target) = all.operator_class_targets.get(&name_on) {
                    result.operator_class_targets.insert(name_on, *target);
                }
                if all.constrained_class_methods.contains(&name_qv) {
                    result.constrained_class_methods.insert(name_qv);
                }
                if let Some(constraints) = all.method_own_constraints.get(&name_qv) {
                    result.method_own_constraints.insert(name_qv, constraints.clone());
                }
                if let Some(details) = all.method_own_constraint_details.get(&name_vn) {
                    result.method_own_constraint_details.insert(name_vn, details.clone());
                }
                // Also export ctor_details if this is a constructor alias (e.g. `:|`)
                let name_qc = qc(name_sym);
                if let Some(details) = all.ctor_details.get(&name_qc) {
                    result.ctor_details.insert(name_qc, details.clone());
                }
                // Also export operator target mapping (e.g. + → add) and the target's value scheme
                if let Some(target) = all.value_operator_targets.get(&name_qop) {
                    result.value_operator_targets.insert(name_qop, target.clone());
                    // Include the target value's scheme so importers can look up its type
                    // (AST desugars `1 + 2` to `add 1 2`, which needs `add`'s type).
                    if let Some(target_scheme) = all.values.get(target) {
                        result.values.insert(*target, target_scheme.clone());
                    }
                    // Also export target's ctor_details if it's a constructor
                    let target_ctor = target.map(names::value_as_constructor);
                    if let Some(details) = all.ctor_details.get(&target_ctor) {
                        result.ctor_details.insert(target_ctor, details.clone());
                    }
                }
                // Export signature constraints for Coercible propagation
                if let Some(constraints) = all.signature_constraints.get(&name_qv) {
                    result.signature_constraints.insert(name_qv, constraints.clone());
                }
                // Export partial discharger info
                if all.partial_dischargers.contains(&name_vn) {
                    result.partial_dischargers.insert(name_vn);
                }
                // Export partial value names
                if all.partial_value_names.contains(&name_vn) {
                    result.partial_value_names.insert(name_vn);
                }
            }
            Export::Type(name, members) => {
                let name_qt = qt(name.symbol());
                let name_tn = *name;
                if let Some(ctors) = all.data_constructors.get(&name_qt) {
                    let export_ctors: Vec<Qualified<ConstructorName>> = match members {
                        Some(DataMembers::All) => ctors.clone(),
                        Some(DataMembers::Explicit(listed)) => listed.iter().map(|n| qc(n.value.symbol())).collect(),
                        None => {
                            // Don't overwrite existing constructor list with empty
                            // (handles `module X (A(..), A)` where second A has no members)
                            if !result.data_constructors.contains_key(&name_qt) {
                                result.data_constructors.insert(name_qt, Vec::new());
                            }
                            // Still need to export type aliases below
                            if let Some(alias) = all.type_aliases.get(&name_qt) {
                                result.type_aliases.insert(name_qt, alias.clone());
                            }
                            // Export type kind, arities, and roles
                            if let Some(kind) = all.type_kinds.get(&name_tn) {
                                result.type_kinds.insert(name_tn, kind.clone());
                            }
                            if let Some(arity) = all.type_con_arities.get(&name_qt) {
                                result.type_con_arities.insert(name_qt, *arity);
                            }
                            if let Some(roles) = all.type_roles.get(&name_tn) {
                                result.type_roles.insert(name_tn, roles.clone());
                            }
                            continue;
                        }
                    };

                    result.data_constructors.insert(name_qt, export_ctors.clone());

                    for ctor in &export_ctors {
                        // Constructors are values; look up scheme using ValueName
                        let ctor_as_value = ctor.map(names::constructor_as_value);
                        if let Some(scheme) = all.values.get(&ctor_as_value) {
                            result.values.insert(ctor_as_value, scheme.clone());
                        }
                        if let Some(details) = all.ctor_details.get(ctor) {
                            result.ctor_details.insert(*ctor, details.clone());
                        }
                    }
                }
                // Also export type aliases with this name
                if let Some(alias) = all.type_aliases.get(&name_qt) {
                    result.type_aliases.insert(name_qt, alias.clone());
                }
                // Also export type kind
                if let Some(kind) = all.type_kinds.get(&name_tn) {
                    result.type_kinds.insert(name_tn, kind.clone());
                }
                // Also export type con arities
                if let Some(arity) = all.type_con_arities.get(&name_qt) {
                    result.type_con_arities.insert(name_qt, *arity);
                }
                // Also export type roles
                if let Some(roles) = all.type_roles.get(&name_tn) {
                    result.type_roles.insert(name_tn, roles.clone());
                }
            }
            Export::Class(name) => {
                let name_qcl = qcl(name.symbol());
                let name_cn = *name;
                // Export class metadata (for constraint generation) but NOT methods as values.
                // In PureScript, `module M (class C) where` only exports the class —
                // methods must be listed separately: `module M (class C, methodName) where`.
                for (method_name, (class_name, tvs)) in &all.class_methods {
                    if class_name.name_symbol() == name.symbol() {
                        result
                            .class_methods
                            .insert(*method_name, (*class_name, tvs.clone()));
                        if all.constrained_class_methods.contains(method_name) {
                            result.constrained_class_methods.insert(*method_name);
                        }
                        if let Some(constraints) = all.method_own_constraints.get(method_name) {
                            result.method_own_constraints.insert(*method_name, constraints.clone());
                        }
                        if let Some(details) = all.method_own_constraint_details.get(&method_name.name) {
                            result.method_own_constraint_details.insert(method_name.name, details.clone());
                        }
                    }
                }
                // Export instances for this class
                if let Some(insts) = all.instances.get(&name_qcl) {
                    result.instances.insert(name_qcl, insts.clone());
                }
                // Export class param count (needed for orphan detection and arity checking)
                if let Some(count) = all.class_param_counts.get(&name_qcl) {
                    result.class_param_counts.insert(name_qcl, *count);
                }
                if let Some(fd) = all.class_fundeps.get(&name_cn) {
                    result.class_fundeps.insert(name_cn, fd.clone());
                }
            }
            Export::TypeOp(name) => {
                let name_qtop = qtop(name.symbol());
                if let Some(target) = all.type_operators.get(&name_qtop) {
                    result.type_operators.insert(name_qtop, *target);
                }
                if let Some(fixity) = all.type_fixities.get(&name_qtop) {
                    result.type_fixities.insert(name_qtop, *fixity);
                }
            }
            Export::Module(mod_name) => {
                // Self-re-export: `module A (module A)` exports everything
                // defined locally in A. The module doesn't import itself,
                // so we copy all items from `all` directly.
                if module_name_to_symbol(mod_name) == module_name_to_symbol(current_module) {
                    for (name, scheme) in &all.values {
                        result.values.insert(*name, scheme.clone());
                    }
                    for (name, ctors) in &all.data_constructors {
                        // Don't overwrite entries already set by explicit Export::Type
                        result.data_constructors.entry(*name).or_insert_with(|| ctors.clone());
                    }
                    for (name, details) in &all.ctor_details {
                        result.ctor_details.entry(*name).or_insert_with(|| details.clone());
                    }
                    for (name, info) in &all.class_methods {
                        result.class_methods.insert(*name, info.clone());
                    }
                    for (name, target) in &all.type_operators {
                        result.type_operators.insert(*name, *target);
                    }
                    for (name, fixity) in &all.type_fixities {
                        result.type_fixities.insert(*name, *fixity);
                    }
                    for (name, fixity) in &all.value_fixities {
                        result.value_fixities.insert(*name, *fixity);
                    }
                    for name in &all.function_op_aliases {
                        result.function_op_aliases.insert(*name);
                    }
                    for (op, target) in &all.operator_class_targets {
                        result.operator_class_targets.insert(*op, *target);
                    }
                    for (op, target) in &all.value_operator_targets {
                        result.value_operator_targets.insert(*op, target.clone());
                    }
                    for name in &all.constrained_class_methods {
                        result.constrained_class_methods.insert(*name);
                    }
                    for (name, constraints) in &all.method_own_constraints {
                        result.method_own_constraints.insert(*name, constraints.clone());
                    }
                    for (name, details) in &all.method_own_constraint_details {
                        result.method_own_constraint_details.insert(*name, details.clone());
                    }
                    for (name, alias) in &all.type_aliases {
                        result.type_aliases.insert(*name, alias.clone());
                    }
                    for (name, count) in &all.class_param_counts {
                        result.class_param_counts.insert(*name, *count);
                    }
                    for (name, fd) in &all.class_fundeps {
                        result.class_fundeps.insert(*name, fd.clone());
                    }
                    continue;
                }
                // Re-export everything from the named module.
                // `module X` in the export list matches an import whose *effective qualifier* equals X.
                // The effective qualifier is the alias if present, otherwise the module name.
                // e.g. `import Data.Foo` has effective qualifier `Data.Foo`
                // e.g. `import Data.Foo as Foo` has effective qualifier `Foo`
                // So `module Data.Foo` matches the first but NOT the second.
                let reexport_mod_sym = module_name_to_symbol(mod_name);
                for import_decl in imports {
                    let effective_qualifier = import_decl
                        .qualified
                        .as_ref()
                        .map(|q| module_name_to_symbol(q))
                        .unwrap_or_else(|| module_name_to_symbol(&import_decl.module));
                    if effective_qualifier == reexport_mod_sym {
                        // Look up from registry; also check Prim submodules
                        let prim_sub;
                        let full_exports = if is_prim_module(&import_decl.module) {
                            Some(prim_exports())
                        } else if is_prim_submodule(&import_decl.module) {
                            prim_sub = prim_submodule_exports(&import_decl.module);
                            Some(&prim_sub)
                        } else {
                            registry.lookup(&import_decl.module.parts)
                        };
                        if let Some(mod_exports) = full_exports {
                            // Resolve the actual source module for origin tracking.
                            // For Prim modules, use reexport_mod_sym directly.
                            let source_mod_sym = module_name_to_symbol(&import_decl.module);

                            // Build import filter: only names actually imported participate
                            // in conflict detection, but all items are re-exported.
                            let filter = build_import_filter(import_decl, mod_exports);

                            // The import qualifier determines whether a conflict is
                            // a ScopeConflict (same qualifier) or ExportConflict (different qualifiers).
                            let import_qual = import_decl.qualified.as_ref().map(|q| module_name_to_symbol(q));

                            // Check for conflicts: class methods
                            for (name, info) in &mod_exports.class_methods {
                                let (class_name, _) = info;
                                let cn_sym = class_name.name_symbol();
                                let imported = filter
                                    .classes
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&class_name.name));
                                if imported {
                                    let origin = mod_exports
                                        .class_origins
                                        .get(&class_name.name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = class_origins.get(&cn_sym) {
                                        if prev_origin != origin && prev_local && is_local_def {
                                            if prev_qual == import_qual {
                                                errors.push(TypeError::ScopeConflict {
                                                    span: export_span,
                                                    name: cn_sym,
                                                });
                                            } else {
                                                errors.push(TypeError::ExportConflict {
                                                    span: export_span,
                                                    name: cn_sym,
                                                });
                                            }
                                        }
                                    } else {
                                        class_origins.insert(cn_sym, (origin, import_qual, is_local_def));
                                    }
                                }
                                result.class_methods.insert(*name, info.clone());
                            }
                            for (name, scheme) in &mod_exports.values {
                                // Don't let a non-class value overwrite a class method's entry
                                if result.class_methods.contains_key(name)
                                    && !mod_exports.class_methods.contains_key(name)
                                {
                                    continue;
                                }
                                let n_sym = name.name_symbol();
                                let origin = mod_exports
                                    .value_origins
                                    .get(&name.name)
                                    .copied()
                                    .unwrap_or(source_mod_sym);
                                let imported = filter
                                    .values
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&name.name));
                                if imported {
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = value_origins.get(&n_sym) {
                                        if prev_origin != origin && prev_local && is_local_def {
                                            let both_are_class_methods =
                                                mod_exports.class_methods.contains_key(name)
                                                && result.class_methods.contains_key(name);
                                            if !both_are_class_methods {
                                                if prev_qual == import_qual {
                                                    errors.push(TypeError::ScopeConflict {
                                                        span: export_span,
                                                        name: n_sym,
                                                    });
                                                } else {
                                                    errors.push(TypeError::ExportConflict {
                                                        span: export_span,
                                                        name: n_sym,
                                                    });
                                                }
                                            }
                                        }
                                    } else {
                                        value_origins.insert(n_sym, (origin, import_qual, is_local_def));
                                    }
                                }
                                if imported {
                                    result.values.insert(*name, scheme.clone());
                                }
                            }
                            for (name, ctors) in &mod_exports.data_constructors {
                                let n_sym = name.name_symbol();
                                let imported = filter
                                    .types
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&name.name));
                                if imported {
                                    let origin = mod_exports
                                        .type_origins
                                        .get(&name.name)
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = type_origins.get(&n_sym) {
                                        if prev_origin != origin && prev_local && is_local_def {
                                            if prev_qual == import_qual {
                                                errors.push(TypeError::ScopeConflict {
                                                    span: export_span,
                                                    name: n_sym,
                                                });
                                            } else {
                                                errors.push(TypeError::ExportConflict {
                                                    span: export_span,
                                                    name: n_sym,
                                                });
                                            }
                                        }
                                    } else {
                                        type_origins.insert(n_sym, (origin, import_qual, is_local_def));
                                    }
                                }
                                // Don't overwrite data_constructors already set by an explicit
                                // Export::Type — the explicit export has the correct constructor
                                // list for the locally-defined type, while a module re-export
                                // may carry a same-named type from a different module.
                                result.data_constructors.entry(*name).or_insert_with(|| ctors.clone());
                            }
                            for (name, details) in &mod_exports.ctor_details {
                                // Don't overwrite ctor_details already set by Export::Type
                                result.ctor_details.entry(*name).or_insert_with(|| details.clone());
                            }
                            for (name, target) in &mod_exports.type_operators {
                                let n_sym = name.name_symbol();
                                let imported = filter
                                    .type_ops
                                    .as_ref()
                                    .map_or(true, |allowed| allowed.contains(&name.name));
                                if imported {
                                    let origin = mod_exports
                                        .value_origins
                                        .get(&ValueName::new(n_sym))
                                        .copied()
                                        .unwrap_or(source_mod_sym);
                                    let is_local_def = origin == source_mod_sym;
                                    if let Some(&(prev_origin, prev_qual, prev_local)) = value_origins.get(&n_sym) {
                                        if prev_origin != origin && prev_local && is_local_def {
                                            if prev_qual == import_qual {
                                                errors.push(TypeError::ScopeConflict {
                                                    span: export_span,
                                                    name: n_sym,
                                                });
                                            } else {
                                                errors.push(TypeError::ExportConflict {
                                                    span: export_span,
                                                    name: n_sym,
                                                });
                                            }
                                        }
                                    } else {
                                        value_origins.insert(n_sym, (origin, import_qual, is_local_def));
                                    }
                                }
                                result.type_operators.insert(*name, *target);
                            }
                            for (name, fixity) in &mod_exports.type_fixities {
                                result.type_fixities.insert(*name, *fixity);
                            }
                            for (name, fixity) in &mod_exports.value_fixities {
                                result.value_fixities.insert(*name, *fixity);
                            }
                            for name in &mod_exports.function_op_aliases {
                                result.function_op_aliases.insert(*name);
                            }
                            for (op, target) in &mod_exports.operator_class_targets {
                                result.operator_class_targets.insert(*op, *target);
                            }
                            for (op, target) in &mod_exports.value_operator_targets {
                                result.value_operator_targets.insert(*op, target.clone());
                            }
                            for name in &mod_exports.constrained_class_methods {
                                result.constrained_class_methods.insert(*name);
                            }
                            for (name, constraints) in &mod_exports.method_own_constraints {
                                result.method_own_constraints.insert(*name, constraints.clone());
                            }
                            for (name, alias) in &mod_exports.type_aliases {
                                // Don't overwrite locally-defined aliases with re-exported ones.
                                // E.g. `module Table (module ColFilterControls, Input, ...)` should
                                // keep Table's own `Input` (7 params) rather than overwriting it
                                // with ColFilterControls' `Input` (3 params).
                                result.type_aliases.entry(*name).or_insert_with(|| alias.clone());
                            }
                            for (name, count) in &mod_exports.class_param_counts {
                                result.class_param_counts.insert(*name, *count);
                            }
                            for (name, fd) in &mod_exports.class_fundeps {
                                result.class_fundeps.insert(*name, fd.clone());
                            }
                            for (name, kind) in &mod_exports.type_kinds {
                                // Don't overwrite existing type_kinds entries — an explicit
                                // Export::Type may have already set the correct kind (e.g.
                                // a 1-param alias kind), and a `module X` re-export from a
                                // different module may carry a data type with the same
                                // unqualified name but a different kind.
                                result.type_kinds.entry(*name).or_insert_with(|| kind.clone());
                            }
                            for (name, kind) in &mod_exports.class_type_kinds {
                                result.class_type_kinds.entry(*name).or_insert_with(|| kind.clone());
                            }
                            for (name, arity) in &mod_exports.type_con_arities {
                                result.type_con_arities.insert(*name, *arity);
                            }
                            for (name, roles) in &mod_exports.type_roles {
                                result.type_roles.insert(*name, roles.clone());
                            }
                        }
                    }
                }
            }
        }
    }

    // Always export all instances (PureScript instances are globally visible)
    for (class_name, insts) in &all.instances {
        result
            .instances
            .entry(*class_name)
            .or_default()
            .extend(insts.clone());
    }

    // Carry forward origin tracking into the result so downstream modules
    // can also detect export conflicts correctly.
    // For locally-exported names (Export::Value/Type/Class), use all's origins.
    // For re-exported names (Export::Module), use the origins we tracked.
    for (name, origin) in &all.value_origins {
        if result.values.contains_key(&qv(name.symbol())) {
            result.value_origins.entry(*name).or_insert(*origin);
        }
    }
    for (name, origin) in &all.type_origins {
        if result.data_constructors.contains_key(&qt(name.symbol())) {
            result.type_origins.entry(*name).or_insert(*origin);
        }
    }
    // Also propagate type_origins for types that appear in exported value schemes
    // but aren't in data_constructors. This covers cases like `fetchWithOptions :: ...
    // Promise Response` where Response is a foreign import data type from another module
    // that isn't directly exported as a type.
    {
        let mut scheme_type_names: HashSet<Symbol> = HashSet::new();
        for scheme in result.values.values() {
            collect_unqualified_type_cons(&scheme.ty, &mut scheme_type_names);
        }
        for name in &scheme_type_names {
            let tn = TypeName::new(*name);
            if !result.type_origins.contains_key(&tn) {
                if let Some(origin) = all.type_origins.get(&tn) {
                    result.type_origins.insert(tn, *origin);
                }
            }
        }
    }
    for (name, origin) in &all.class_origins {
        result.class_origins.entry(*name).or_insert(*origin);
    }
    // Also include origins from re-exported modules
    for (name, (origin, _, _)) in &value_origins {
        result.value_origins.entry(ValueName::new(*name)).or_insert(*origin);
    }
    for (name, (origin, _, _)) in &type_origins {
        result.type_origins.entry(TypeName::new(*name)).or_insert(*origin);
    }
    for (name, (origin, _, _)) in &class_origins {
        result.class_origins.entry(ClassName::new(*name)).or_insert(*origin);
    }

    // Role info, newtype names, and signature constraints are always propagated
    result.type_roles = all.type_roles.clone();
    result.newtype_names = all.newtype_names.clone();
    result.signature_constraints = all.signature_constraints.clone();
    result.partial_dischargers = all.partial_dischargers.clone();
    result.partial_value_names = all.partial_value_names.clone();
    result.type_con_arities = all.type_con_arities.clone();
    result.method_own_constraints = all.method_own_constraints.clone();
    result.resolved_dicts = all.resolved_dicts.clone();
    result.let_binding_constraints = all.let_binding_constraints.clone();
    result.record_update_fields = all.record_update_fields.clone();
    result.class_method_order = all.class_method_order.clone();
    result.instance_var_kinds = all.instance_var_kinds.clone();

    result
}

/// Collect unqualified type constructor names from a type.
/// Used to find type names in exported value schemes that need origin tracking.
pub(crate) fn collect_unqualified_type_cons(ty: &Type, out: &mut HashSet<Symbol>) {
    match ty {
        Type::Con(name) if name.module.is_none() => { out.insert(name.name_symbol()); }
        Type::Fun(a, b) => {
            collect_unqualified_type_cons(a, out);
            collect_unqualified_type_cons(b, out);
        }
        Type::App(f, a) => {
            collect_unqualified_type_cons(f, out);
            collect_unqualified_type_cons(a, out);
        }
        Type::Forall(_, body) => collect_unqualified_type_cons(body, out),
        Type::Record(fields, tail) => {
            for (_, t) in fields { collect_unqualified_type_cons(t, out); }
            if let Some(t) = tail { collect_unqualified_type_cons(t, out); }
        }
        _ => {}
    }
}
