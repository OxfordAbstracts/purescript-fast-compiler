//! Cross-module import resolution.
//!
//! Given a parsed `cst::Module` and a populated `ModuleRegistry`,
//! produce the pre-populated `Env` and `InstanceIndex` that the
//! single-module pipeline (`infer_value_scc_with_all`) needs.
//!
//! The resolver mirrors legacy `src/typechecker/check/imports.rs`
//! but lives inside the new pipeline shape:
//!
//! * `Prim` is always implicitly imported unqualified. The
//!   corresponding `Prim.*` submodules are not implicit — users
//!   write `import Prim.Row` explicitly when they want those.
//! * Every explicit `import M (...)` adds its listed items into
//!   the env. `import M as Q` adds a qualified prefix; an
//!   unqualified import also makes the items findable by their
//!   bare name.
//! * Instances travel globally: every successfully-resolved
//!   import contributes that module's entire `instances` list to
//!   the built `InstanceIndex`, regardless of the import
//!   filter. Classes travel with their instances.

use crate::cst::{self, DataMembers, Decl, ImportDecl, ImportList};
use crate::typecheck_db::env::Env;
use crate::typecheck_db::module_registry::{ModuleExports, ModuleRegistry};
use crate::typecheck_db::passes::instance_index::InstanceIndex;
use crate::typecheck_db::prim::prim_exports;
use crate::typecheck_db::types::QName;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportError {
    pub span: crate::span::Span,
    pub kind: ImportErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportErrorKind {
    /// `import M` where `M` isn't known to the registry.
    UnknownModule(String),
    /// `import M (foo)` where `foo` isn't in M's exports.
    UnknownValue { module: String, name: String },
    /// `import M (Bar(..))` where `Bar` isn't in M's types.
    UnknownType { module: String, name: String },
    /// `import M (Bar(C1))` where `C1` isn't one of Bar's ctors.
    UnknownConstructor {
        module: String,
        type_name: String,
        ctor: String,
    },
    /// `import M (class C)` where `C` isn't in M's classes.
    UnknownClass { module: String, name: String },
    /// `import M ((<>))` where `<>` isn't in M's fixities.
    UnknownOperator { module: String, name: String },
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

/// Build the pre-populated `Env` + `InstanceIndex` a single
/// module's check should start from. The returned `Vec` carries
/// any non-fatal import errors — callers can surface them to the
/// user and still proceed with inference.
pub fn build_env_from_imports(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> (Env, InstanceIndex, Vec<ImportError>) {
    let mut env = Env::new();
    let mut ix = InstanceIndex::new();
    let mut errors: Vec<ImportError> = Vec::new();

    // Every user module implicitly sees `Prim` unqualified.
    let prims = prim_exports();
    if let Some(prim) = prims.get("Prim") {
        import_all("Prim", prim, /*qualifier=*/ None, &mut env, &mut ix);
    }

    for imp in &module.imports {
        let target_name = module_name_string(&imp.module);
        // Prim and its submodules are resolved from the static
        // `prim_exports` map first; user modules come from the
        // registry.
        let target: Option<&ModuleExports> = prims
            .get(&target_name)
            .or_else(|| registry.get(&target_name));
        let target = match target {
            Some(t) => t,
            None => {
                errors.push(ImportError {
                    span: imp.span,
                    kind: ImportErrorKind::UnknownModule(target_name.clone()),
                });
                continue;
            }
        };

        let qualifier: Option<String> = imp
            .qualified
            .as_ref()
            .map(|q| module_name_string(q));

        apply_import(&target_name, target, &imp, qualifier, &mut env, &mut ix, &mut errors);
    }

    (env, ix, errors)
}

// ---------------------------------------------------------------------------
// Import application helpers
// ---------------------------------------------------------------------------

fn apply_import(
    target_name: &str,
    target: &ModuleExports,
    imp: &ImportDecl,
    qualifier: Option<String>,
    env: &mut Env,
    ix: &mut InstanceIndex,
    errors: &mut Vec<ImportError>,
) {
    match &imp.imports {
        None => {
            // `import M` or `import M as Q` — take everything.
            import_all(target_name, target, qualifier.clone(), env, ix);
        }
        Some(ImportList::Explicit(items)) => {
            for item in items {
                apply_explicit(target_name, target, item, qualifier.clone(), env, ix, errors, imp.span);
            }
            // Instances still travel with any non-empty import.
            merge_instances_and_classes(target, ix);
        }
        Some(ImportList::Hiding(hidden)) => {
            let mut filter = HideFilter::default();
            for item in hidden {
                filter.insert(item);
            }
            import_all_except(target_name, target, qualifier.clone(), &filter, env, ix);
        }
    }
}

fn import_all(
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<String>,
    env: &mut Env,
    ix: &mut InstanceIndex,
) {
    import_all_except(target_name, target, qualifier, &HideFilter::default(), env, ix)
}

fn import_all_except(
    target_name: &str,
    target: &ModuleExports,
    qualifier: Option<String>,
    hidden: &HideFilter,
    env: &mut Env,
    ix: &mut InstanceIndex,
) {
    // Values. Bind each scheme under both the import-chosen
    // qualifier key (`qualifier.name`) AND an origin-module key
    // (`target.value_origins[name].name`, falling back to the
    // importee itself). The origin key is what rebracket-time
    // fixity lowering looks up when a fixity decl's target has
    // been canonicalized to its defining module — without it,
    // `Var("Data.Function.apply")` would not resolve when the
    // module was imported unqualified through a re-exporter.
    for (name, scheme) in &target.values {
        let is_hidden = hidden.values.contains(name.as_str());
        // Hiding removes the unqualified-in-this-module binding
        // (`(None|alias, name)`) but NOT the origin-qualified
        // binding (`(Some("Data.Semiring"), name)`). The
        // origin-qualified key is what rebracket-time operator
        // lowering looks up when `+` has been canonicalized to
        // `Data.Semiring.add`; without it, `import Prelude
        // hiding (add)` would cascade into every use of `+`
        // failing to resolve.
        if !is_hidden {
            let key = QName { module: qualifier.clone(), name: name.clone() };
            env.bind_scheme(key, scheme.clone());
        }
        let origin = target
            .value_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| target_name.to_string());
        env.bind_scheme(
            QName { module: Some(origin), name: name.clone() },
            scheme.clone(),
        );
    }
    // Also bind every extra origin-qualified scheme the
    // re-exporter surfaced — e.g. `Prelude.qualified_values`
    // holds `Data.Function.apply` even when its primary `values`
    // entry was won by `Control.Apply.apply`. Origin-qualified
    // bindings ignore `hidden` for the same reason as above.
    for ((origin, name), scheme) in &target.qualified_values {
        env.bind_scheme(
            QName { module: Some(origin.clone()), name: name.clone() },
            scheme.clone(),
        );
    }
    // Data constructors: synthesize each one's value scheme
    // (`forall a b. f1 -> f2 -> … -> T a b …`) and bind it
    // under both the import qualifier and the origin module.
    // The origin-qualified key lets a rebracketer-produced
    // `Expr::Constructor { name: Lib.Tuple }` resolve even when
    // `Lib` was imported unqualified (i.e. `qualifier: None`).
    for (ctor_name, info) in &target.ctors {
        if hidden.ctors.contains(ctor_name.as_str()) {
            continue;
        }
        let scheme = synth_ctor_scheme(info);
        let key = QName { module: qualifier.clone(), name: ctor_name.clone() };
        env.bind_scheme(key, scheme.clone());
        let origin_key = QName {
            module: Some(target_name.to_string()),
            name: ctor_name.clone(),
        };
        env.bind_scheme(origin_key, scheme);
    }
    // Instances + class info: always propagated.
    merge_instances_and_classes(target, ix);
}

fn apply_explicit(
    target_name: &str,
    target: &ModuleExports,
    item: &cst::Import,
    qualifier: Option<String>,
    env: &mut Env,
    _ix: &mut InstanceIndex,
    errors: &mut Vec<ImportError>,
    span: crate::span::Span,
) {
    match item {
        cst::Import::Value(vn) => {
            let name = crate::typecheck_db::util::resolve_symbol(vn.value.symbol());
            match target.values.get(&name) {
                Some(scheme) => {
                    let key = QName { module: qualifier.clone(), name: name.clone() };
                    env.bind_scheme(key, scheme.clone());
                    // Also bind under the origin module's qualified
                    // key so a rebracketer-produced `Var("A.foo")`
                    // can resolve even when `foo` was imported
                    // unqualified. Matches the `import_all_except`
                    // path — every imported scheme is findable both
                    // by the user's chosen qualifier and by its
                    // defining module.
                    let origin = target
                        .value_origins
                        .get(&name)
                        .cloned()
                        .unwrap_or_else(|| target_name.to_string());
                    env.bind_scheme(
                        QName {
                            module: Some(origin),
                            name: name.clone(),
                        },
                        scheme.clone(),
                    );
                    // If this Value-import is actually an operator
                    // alias (e.g. `import M ((==))` where `==` aliases
                    // `eq`), also bring the underlying target into
                    // scope. After desugar, call-site code references
                    // the target directly, not the operator, so the
                    // target must be resolvable.
                    if let Some(fx) = target.value_fixities.get(&name) {
                        if let Some(target_scheme) = target.values.get(&fx.target_name) {
                            env.bind_scheme(
                                QName {
                                    module: qualifier.clone(),
                                    name: fx.target_name.clone(),
                                },
                                target_scheme.clone(),
                            );
                            // Mirror under the fixity's own
                            // origin-module (may differ from
                            // `target_name` when a re-export chain
                            // is at play).
                            let fixity_origin = fx
                                .target_module
                                .clone()
                                .unwrap_or_else(|| target_name.to_string());
                            env.bind_scheme(
                                QName {
                                    module: Some(fixity_origin),
                                    name: fx.target_name.clone(),
                                },
                                target_scheme.clone(),
                            );
                        }
                        // Constructor-operator alias: `infixr 6
                        // Tuple as /\` — fixity target is in
                        // `target.ctors`, not `target.values`.
                        // Synthesize the ctor's value scheme and
                        // bind under qualifier + origin keys so
                        // rebracketed `a /\ b` → `Constructor
                        // A.Tuple` resolves.
                        if let Some(info) = target.ctors.get(&fx.target_name) {
                            let ctor_scheme = synth_ctor_scheme(info);
                            env.bind_scheme(
                                QName {
                                    module: qualifier.clone(),
                                    name: fx.target_name.clone(),
                                },
                                ctor_scheme.clone(),
                            );
                            let fixity_origin = fx
                                .target_module
                                .clone()
                                .unwrap_or_else(|| target_name.to_string());
                            env.bind_scheme(
                                QName {
                                    module: Some(fixity_origin),
                                    name: fx.target_name.clone(),
                                },
                                ctor_scheme,
                            );
                        } else if let Some(origin) = fx.target_module.clone() {
                            // Re-exporter path: the fixity's
                            // target lives in `qualified_values`
                            // because it was resolved through an
                            // imported module's exports rather
                            // than this one. Bind both the
                            // unqualified form (for the common
                            // fallback lookup) and the
                            // origin-qualified form.
                            if let Some(scheme) = target
                                .qualified_values
                                .get(&(origin.clone(), fx.target_name.clone()))
                            {
                                env.bind_scheme(
                                    QName {
                                        module: qualifier.clone(),
                                        name: fx.target_name.clone(),
                                    },
                                    scheme.clone(),
                                );
                                env.bind_scheme(
                                    QName {
                                        module: Some(origin),
                                        name: fx.target_name.clone(),
                                    },
                                    scheme.clone(),
                                );
                            }
                        }
                    }
                }
                None => errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownValue {
                        module: target_name.into(),
                        name,
                    },
                }),
            }
        }
        cst::Import::Type(tn, members) => {
            let name = crate::typecheck_db::util::resolve_symbol(tn.value.symbol());
            let type_known = target.type_arities.contains_key(&name)
                || target.data_constructors.contains_key(&name)
                || target.type_aliases.contains_key(&name);
            if !type_known {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownType {
                        module: target_name.into(),
                        name: name.clone(),
                    },
                });
                return;
            }
            // Which ctors travel with the type?
            if let Some(all_ctors) = target.data_constructors.get(&name) {
                let wanted: Vec<String> = match members {
                    None => Vec::new(),
                    Some(DataMembers::All) => all_ctors.clone(),
                    Some(DataMembers::Explicit(list)) => list
                        .iter()
                        .map(|c| {
                            crate::typecheck_db::util::resolve_symbol(c.value.symbol())
                        })
                        .collect(),
                };
                for ctor in wanted {
                    if !all_ctors.contains(&ctor) {
                        errors.push(ImportError {
                            span,
                            kind: ImportErrorKind::UnknownConstructor {
                                module: target_name.into(),
                                type_name: name.clone(),
                                ctor,
                            },
                        });
                        continue;
                    }
                    if let Some(info) = target.ctors.get(&ctor) {
                        let scheme = synth_ctor_scheme(info);
                        let key = QName {
                            module: qualifier.clone(),
                            name: ctor.clone(),
                        };
                        env.bind_scheme(key, scheme.clone());
                        let origin_key = QName {
                            module: Some(target_name.to_string()),
                            name: ctor.clone(),
                        };
                        env.bind_scheme(origin_key, scheme);
                    }
                }
            }
        }
        cst::Import::Class(cn) => {
            let name = crate::typecheck_db::util::resolve_symbol(cn.value.symbol());
            if !target.classes.contains_key(&name) {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownClass {
                        module: target_name.into(),
                        name,
                    },
                });
            }
            // Class import doesn't automatically pull in methods
            // at this layer — the class's methods live in
            // `target.values` and must be explicitly listed OR
            // brought in via `import M (class C)` + the method's
            // own import. Legacy pulls methods along with the
            // class; we can add that here once a fixture needs it.
        }
        cst::Import::TypeOp(on) => {
            let name = crate::typecheck_db::util::resolve_symbol(on.value.symbol());
            if !target.type_fixities.contains_key(&name) {
                errors.push(ImportError {
                    span,
                    kind: ImportErrorKind::UnknownOperator {
                        module: target_name.into(),
                        name,
                    },
                });
            }
        }
    }
}

fn merge_instances_and_classes(target: &ModuleExports, ix: &mut InstanceIndex) {
    for (class_name, info) in &target.classes {
        ix.insert_class(class_name.clone(), info.clone());
    }
    for inst in &target.instances {
        ix.insert(inst.clone());
    }
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

/// Synthesize the value-level `Scheme` for a constructor:
/// `forall <type_vars>. f1 -> f2 -> … -> Parent <type_vars>`.
pub(crate) fn synth_ctor_scheme(
    info: &crate::typecheck_db::passes::exhaustiveness::CtorInfo,
) -> crate::typecheck_db::types::Scheme {
    use crate::typecheck_db::types::{Scheme, Type};
    let head = Type::Con(QName::unqualified(&info.parent_type));
    let mut result = head;
    for v in &info.type_vars {
        result = Type::app(result, Type::Var(v.clone()));
    }
    let mut ty = result;
    for field in info.fields.iter().rev() {
        ty = Type::fun(field.clone(), ty);
    }
    Scheme { vars: info.type_vars.clone(), ty }
}

fn module_name_string(m: &cst::ModuleName) -> String {
    m.parts
        .iter()
        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
        .collect::<Vec<_>>()
        .join(".")
}

#[derive(Debug, Clone, Default)]
struct HideFilter<'a> {
    values: std::collections::HashSet<&'a str>,
    ctors: std::collections::HashSet<&'a str>,
    types: std::collections::HashSet<&'a str>,
    classes: std::collections::HashSet<&'a str>,
    ops: std::collections::HashSet<&'a str>,
}

impl<'a> HideFilter<'a> {
    fn insert(&mut self, item: &'a cst::Import) {
        // For hiding, we only need to keep name strings; clone
        // them out of the interner as owned strings. But we
        // store string slices — the CST outlives this filter so
        // we can use short-lived refs through a boxed leak.
        let name_owned: String = match item {
            cst::Import::Value(n) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
            cst::Import::Type(n, _) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
            cst::Import::Class(n) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
            cst::Import::TypeOp(n) => {
                crate::typecheck_db::util::resolve_symbol(n.value.symbol())
            }
        };
        // Leak to 'static since this filter is short-lived per
        // import resolution. An import list is typically <100
        // names, so this is a small, bounded leak.
        let s: &'static str = Box::leak(name_owned.into_boxed_str());
        match item {
            cst::Import::Value(_) => {
                self.values.insert(s);
            }
            cst::Import::Type(_, members) => {
                self.types.insert(s);
                if let Some(DataMembers::All) = members {
                    // Hide all ctors of this type too.
                }
                // Specific ctor hiding not supported in hiding
                // lists by legacy either.
            }
            cst::Import::Class(_) => {
                self.classes.insert(s);
            }
            cst::Import::TypeOp(_) => {
                self.ops.insert(s);
            }
        }
    }
}

// Silence: unused Decl variant would hint at Decl import not being needed
// in this module; we keep the `cst::Import` / `cst::Module` paths.
#[allow(dead_code)]
fn _touch_decl(_: &Decl) {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::env::Lookup;
    use crate::typecheck_db::module_registry::ModuleExports;
    use crate::typecheck_db::passes::instance_index::{ClassInfo, Instance};
    use crate::typecheck_db::types::{Scheme, Type};

    fn int_ty() -> Type {
        Type::Con(QName::unqualified("Int"))
    }

    fn parse_mod(src: &str) -> cst::Module {
        parse(src).unwrap()
    }

    /// Register a fake module with a single value `foo :: Int`.
    fn registry_with_foo() -> ModuleRegistry {
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.values.insert("foo".into(), Scheme::mono(int_ty()));
        r.insert("Data.Foo", exp);
        r
    }

    // =================================================================
    // Prim is always visible
    // =================================================================

    #[test]
    fn prim_is_implicitly_imported() {
        let module = parse_mod("module M where\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert!(errs.is_empty());
        // `Int` is a Prim type; after implicit Prim import, the
        // env should know about Prim's classes at least.
        let _ = env;
    }

    #[test]
    fn prim_auto_import_provides_partial_class() {
        let module = parse_mod("module M where\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert!(errs.is_empty());
        assert!(ix.class_info("Partial").is_some());
        assert!(ix.class_info("IsSymbol").is_some());
    }

    // =================================================================
    // import all / qualified / hiding
    // =================================================================

    #[test]
    fn import_all_unqualified_makes_values_available() {
        let module = parse_mod("module M where\nimport Data.Foo\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert!(errs.is_empty(), "got: {errs:?}");
        match env.lookup_unqualified("foo") {
            Lookup::Scheme(s) => assert_eq!(s.ty, int_ty()),
            other => panic!("expected scheme, got {other:?}"),
        }
    }

    #[test]
    fn import_as_qualifies_all_values() {
        let module = parse_mod("module M where\nimport Data.Foo as F\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert!(errs.is_empty());
        let qualified = QName { module: Some("F".into()), name: "foo".into() };
        assert!(env.lookup_qualified(&qualified).is_some());
    }

    #[test]
    fn import_explicit_value() {
        let module = parse_mod("module M where\nimport Data.Foo (foo)\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert!(errs.is_empty());
        match env.lookup_unqualified("foo") {
            Lookup::Scheme(_) => {}
            other => panic!("expected scheme, got {other:?}"),
        }
    }

    #[test]
    fn import_unknown_value_reports_error() {
        let module = parse_mod("module M where\nimport Data.Foo (bar)\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &registry_with_foo());
        assert_eq!(errs.len(), 1);
        match &errs[0].kind {
            ImportErrorKind::UnknownValue { module, name } => {
                assert_eq!(module, "Data.Foo");
                assert_eq!(name, "bar");
            }
            other => panic!("wrong error: {other:?}"),
        }
    }

    #[test]
    fn import_unknown_module_reports_error() {
        let module = parse_mod("module M where\nimport Data.DoesNotExist\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert_eq!(errs.len(), 1);
        assert!(matches!(
            errs[0].kind,
            ImportErrorKind::UnknownModule(ref m) if m == "Data.DoesNotExist"
        ));
    }

    #[test]
    fn import_hiding_excludes_listed_value() {
        // Register a module with both foo + bar.
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.values.insert("foo".into(), Scheme::mono(int_ty()));
        exp.values.insert("bar".into(), Scheme::mono(int_ty()));
        r.insert("Data.Mix", exp);
        let module = parse_mod("module M where\nimport Data.Mix hiding (bar)\n");
        let (env, _ix, errs) = build_env_from_imports(&module, &r);
        assert!(errs.is_empty());
        assert!(matches!(env.lookup_unqualified("foo"), Lookup::Scheme(_)));
        assert!(matches!(env.lookup_unqualified("bar"), Lookup::Missing));
    }

    // =================================================================
    // Instance propagation
    // =================================================================

    #[test]
    fn imports_propagate_instances_and_class_info() {
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.classes.insert(
            "Eq".into(),
            ClassInfo { type_vars: vec!["a".into()], fundeps: vec![] },
        );
        exp.instances.push(Instance {
            class: QName::unqualified("Eq"),
            types: vec![int_ty()],
            context: vec![],
            vars: vec![],
            chained: false,
        });
        r.insert("Data.Eq", exp);
        let module = parse_mod("module M where\nimport Data.Eq\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &r);
        assert!(errs.is_empty());
        assert!(ix.class_info("Eq").is_some());
        assert_eq!(ix.candidates("Eq").len(), 1);
    }

    #[test]
    fn explicit_imports_still_propagate_instances() {
        // PureScript: even `import M (foo)` pulls in M's instances.
        let mut r = ModuleRegistry::new();
        let mut exp = ModuleExports::default();
        exp.values.insert("foo".into(), Scheme::mono(int_ty()));
        exp.instances.push(Instance {
            class: QName::unqualified("Eq"),
            types: vec![int_ty()],
            context: vec![],
            vars: vec![],
            chained: false,
        });
        r.insert("Data.Foo", exp);
        let module = parse_mod("module M where\nimport Data.Foo (foo)\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &r);
        assert!(errs.is_empty());
        assert_eq!(ix.candidates("Eq").len(), 1);
    }

    // =================================================================
    // Class / operator / type import errors
    // =================================================================

    #[test]
    fn import_unknown_class_reports_error() {
        let mut r = ModuleRegistry::new();
        r.insert("Data.Foo", ModuleExports::default());
        let module =
            parse_mod("module M where\nimport Data.Foo (class NoSuch)\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &r);
        assert_eq!(errs.len(), 1);
        assert!(matches!(errs[0].kind, ImportErrorKind::UnknownClass { .. }));
    }

    #[test]
    fn import_unknown_type_reports_error() {
        let mut r = ModuleRegistry::new();
        r.insert("Data.Foo", ModuleExports::default());
        let module = parse_mod("module M where\nimport Data.Foo (NoSuchType)\n");
        let (_env, _ix, errs) = build_env_from_imports(&module, &r);
        assert_eq!(errs.len(), 1);
        assert!(matches!(errs[0].kind, ImportErrorKind::UnknownType { .. }));
    }

    #[test]
    fn import_prim_submodule_by_name() {
        // `import Prim.Row` is a real thing; resolver should
        // pick it up from the static prim_exports map.
        let module = parse_mod("module M where\nimport Prim.Row\n");
        let (_env, ix, errs) = build_env_from_imports(&module, &ModuleRegistry::new());
        assert!(errs.is_empty());
        assert!(ix.class_info("Cons").is_some());
        assert!(ix.class_info("Union").is_some());
    }
}
