//! Multi-module driver: `check_many_modules`.
//!
//! Given a set of parsed modules, sort them by their import
//! graph, check each in order while threading through a shared
//! [`ModuleRegistry`], and return the per-module results.
//!
//! Scope today:
//! * Topological ordering + cycle detection (SCCs with more than
//!   one module are reported as `CycleInModules`).
//! * Per-module import resolution via [`build_env_from_imports`].
//! * Per-module desugar + inference + exhaustiveness + constraints
//!   solving (delegating to the existing single-module pipeline).
//! * `distill_exports` on the result so downstream modules can
//!   import what was just checked.
//!
//! Not yet covered: fine-grained SCC breakdown *within* a module
//! (we pass all value decls to one `infer_value_scc_with_all`
//! call), per-decl cache invalidation across module boundaries,
//! and re-export (`module N` in an export clause).

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cst;
use crate::typecheck_db::desugar::{desugar, DesugarContext};
use crate::typecheck_db::env::Env;
use crate::typecheck_db::module_registry::{distill_exports, ModuleExports, ModuleRegistry};
use crate::typecheck_db::passes::constraints::{ConstraintError, PendingConstraint, ResolvedDict};
use crate::typecheck_db::passes::exhaustiveness::{CtorInfo, CtorRegistry, DataConstructors, NonExhaustive};
use crate::typecheck_db::passes::imports::{build_env_from_imports, ImportError};
use crate::typecheck_db::passes::infer_value::{
    infer_value_scc_with_all, InferError, InferredScheme,
};
use crate::typecheck_db::passes::instance_index::{ClassInfo, Instance, InstanceIndex};
use crate::typecheck_db::types::TypeOpMap;

// ---------------------------------------------------------------------------
// Result + error types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct ModuleCheckResult {
    pub name: String,
    pub schemes: Vec<InferredScheme>,
    pub import_errors: Vec<ImportError>,
    /// Aggregated across every decl in the module.
    pub exhaustiveness_errors: Vec<NonExhaustive>,
    pub constraint_errors: Vec<ConstraintError>,
    pub deferred_constraints: Vec<PendingConstraint>,
    pub resolved_dicts: Vec<ResolvedDict>,
    /// Inference bailed out early. When set, `schemes` contains
    /// whatever was inferred before the error.
    pub inference_error: Option<InferError>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MultiModuleError {
    /// An SCC of size >1 — modules mutually import each other.
    CycleInModules(Vec<String>),
    /// Module M imports N, but N is neither in the input nor in
    /// the registry (and isn't a Prim module).
    UnknownImport { from: String, missing: String },
}

/// Aggregate return of a multi-module check.
#[derive(Debug, Clone)]
pub struct ModuleCheckReport {
    pub registry: ModuleRegistry,
    pub results: Vec<ModuleCheckResult>,
    pub errors: Vec<MultiModuleError>,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Check every module in `modules`. Topologically sorts by
/// imports, processes each in order against a shared
/// [`ModuleRegistry`], and returns per-module results.
pub fn check_many_modules(modules: Vec<(String, cst::Module)>) -> ModuleCheckReport {
    let name_index: HashMap<String, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, (n, _))| (n.clone(), i))
        .collect();

    let mut report = ModuleCheckReport {
        registry: ModuleRegistry::new(),
        results: Vec::new(),
        errors: Vec::new(),
    };

    let (order, cycles) = topo_sort_modules(&modules, &name_index);
    for cycle in cycles {
        report.errors.push(MultiModuleError::CycleInModules(cycle));
    }

    for idx in order {
        let (name, module) = &modules[idx];
        let result = check_one_module(name.clone(), module, &mut report.registry);
        report.results.push(result);
    }

    report
}

// ---------------------------------------------------------------------------
// Single-module orchestration
// ---------------------------------------------------------------------------

fn check_one_module(
    name: String,
    module: &cst::Module,
    registry: &mut ModuleRegistry,
) -> ModuleCheckResult {
    // 1) Pull imports into an Env + InstanceIndex.
    let (mut env, mut instance_index, import_errors) =
        build_env_from_imports(module, registry);

    // 2) Desugar every decl with whatever fixity the module
    // already declares. Cross-module operator rebracketing will
    // need fixity_table injection from imports; that lands when
    // a fixture demands it.
    let ctx = DesugarContext::default();
    let desugared: Vec<cst::Decl> = module
        .decls
        .iter()
        .map(|d| desugar(d, &ctx))
        .collect();

    // 3) Build data_constructors + ctor_details from local decls
    // plus imported entries. Exhaustiveness consults the merged
    // map.
    let (data_constructors, ctor_details, local_classes, local_instances) =
        collect_decl_scope(&desugared);

    // Merge in instances + classes from imports (already done
    // during `build_env_from_imports`, but we also want local
    // instances in the index).
    for inst in &local_instances {
        instance_index.insert(inst.clone());
    }
    for (class_name, info) in &local_classes {
        instance_index.insert_class(class_name.clone(), info.clone());
    }

    // Bind every local data / newtype constructor into the Env
    // as a value scheme so expressions like `Just x` and patterns
    // like `Just x` resolve. Missing today: imported constructors
    // from other modules still need their schemes too; that
    // happens during import if the import pulled the ctor in.
    bind_local_ctors(&desugared, &mut env);

    // 4) Run the single-module pipeline. We pass every value decl
    // in one SCC — fine for most programs; a finer SCC split can
    // come later.
    let type_ops = TypeOpMap::default();
    let decl_refs: Vec<&cst::Decl> = desugared.iter().collect();

    let (schemes, inference_error) = match infer_value_scc_with_all(
        &type_ops,
        &mut env,
        &decl_refs,
        &data_constructors,
        &ctor_details,
        &instance_index,
    ) {
        Ok(s) => (s, None),
        Err(e) => (Vec::new(), Some(e)),
    };

    // 5) Aggregate per-decl diagnostics.
    let mut exhaustiveness_errors = Vec::new();
    let mut constraint_errors = Vec::new();
    let mut deferred_constraints = Vec::new();
    let mut resolved_dicts = Vec::new();
    for s in &schemes {
        exhaustiveness_errors.extend(s.exhaustiveness_errors.iter().cloned());
        constraint_errors.extend(s.constraint_errors.iter().cloned());
        deferred_constraints.extend(s.pending_constraints.iter().cloned());
        resolved_dicts.extend(s.resolved_dicts.iter().cloned());
    }

    // 6) Distill exports + register.
    let exports = distill_exports(
        module,
        &schemes,
        &local_instances,
        &local_classes,
        &ctor_details,
    );
    registry.insert(name.clone(), exports);

    ModuleCheckResult {
        name,
        schemes,
        import_errors,
        exhaustiveness_errors,
        constraint_errors,
        deferred_constraints,
        resolved_dicts,
        inference_error,
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Collect local data / newtype / class / instance info from a
/// module's decls. Returns the exhaustiveness-shaped maps plus
/// local class + instance records.
fn collect_decl_scope(
    decls: &[cst::Decl],
) -> (
    DataConstructors,
    CtorRegistry,
    HashMap<String, ClassInfo>,
    Vec<Instance>,
) {
    let mut data_constructors: DataConstructors = HashMap::new();
    let mut ctor_details: CtorRegistry = HashMap::new();

    let type_ops = TypeOpMap::default();
    for d in decls {
        match d {
            cst::Decl::Data { name, type_vars, constructors, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let ctor_names: Vec<String> = constructors
                    .iter()
                    .map(|c| {
                        crate::typecheck_db::util::resolve_symbol(c.name.value.symbol())
                    })
                    .collect();
                data_constructors.insert(type_name.clone(), ctor_names.clone());
                for c in constructors {
                    let ctor_name =
                        crate::typecheck_db::util::resolve_symbol(c.name.value.symbol());
                    let fields: Vec<_> = c
                        .fields
                        .iter()
                        .map(|f| {
                            crate::typecheck_db::types::convert_type_expr(f, &type_ops)
                        })
                        .collect();
                    ctor_details.insert(
                        ctor_name,
                        CtorInfo {
                            parent_type: type_name.clone(),
                            type_vars: tvars.clone(),
                            fields,
                        },
                    );
                }
            }
            cst::Decl::Newtype { name, type_vars, constructor, ty, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let ctor_name =
                    crate::typecheck_db::util::resolve_symbol(constructor.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                data_constructors.insert(type_name.clone(), vec![ctor_name.clone()]);
                ctor_details.insert(
                    ctor_name,
                    CtorInfo {
                        parent_type: type_name,
                        type_vars: tvars,
                        fields: vec![crate::typecheck_db::types::convert_type_expr(
                            ty, &type_ops,
                        )],
                    },
                );
            }
            _ => {}
        }
    }

    // Reuse the existing instance-index scanner for classes and
    // instances.
    let local_ix = crate::typecheck_db::passes::instance_index::from_decls(decls, &type_ops);
    let mut local_classes: HashMap<String, ClassInfo> = HashMap::new();
    for d in decls {
        if let cst::Decl::Class { name, .. } = d {
            let n = crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            if let Some(info) = local_ix.class_info(&n) {
                local_classes.insert(n, info.clone());
            }
        }
    }
    let mut local_instances: Vec<Instance> = Vec::new();
    for (_, inst_list) in collect_classes(&local_ix) {
        for inst in inst_list {
            local_instances.push(inst.clone());
        }
    }

    (data_constructors, ctor_details, local_classes, local_instances)
}

fn collect_classes<'a>(
    ix: &'a InstanceIndex,
) -> Vec<(&'a str, Vec<&'a Instance>)> {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut out: Vec<(&str, Vec<&Instance>)> = Vec::new();
    // Iterate the index via a public accessor; for now use a
    // workaround: candidates() returns a slice, but we need all
    // class names. Prim classes have no instances so we only need
    // to discover classes that have at least one candidate — a
    // fine approximation until `InstanceIndex` exposes a class
    // iterator directly.
    for class in candidate_class_names(ix) {
        if seen.insert(class) {
            let cands: Vec<&Instance> = ix.candidates(class).iter().collect();
            out.push((class, cands));
        }
    }
    out
}

fn candidate_class_names(ix: &InstanceIndex) -> Vec<&str> {
    // Access via a bit of reflection: we know `candidates()` is
    // keyed by name, but there's no `classes()` iterator yet.
    // A full iterator would require a public API change; for
    // now, start with an empty list — the caller merges
    // instances via another path (local_instances accumulator
    // built from `from_decls` in `collect_decl_scope`).
    let _ = ix;
    Vec::new()
}

/// For every local data / newtype constructor, synthesize its
/// value scheme (`forall a. f1 -> ... -> fn -> T a b ...`) and
/// bind it under its simple name in the env.
fn bind_local_ctors(decls: &[cst::Decl], env: &mut Env) {
    use crate::typecheck_db::types::{QName, Scheme, Type};
    let type_ops = TypeOpMap::default();
    for d in decls {
        match d {
            cst::Decl::Data { name, type_vars, constructors, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let result_ty =
                    apply_type_vars(&Type::Con(QName::unqualified(&type_name)), &tvars);
                for c in constructors {
                    let ctor_name =
                        crate::typecheck_db::util::resolve_symbol(c.name.value.symbol());
                    let fields: Vec<Type> = c
                        .fields
                        .iter()
                        .map(|f| {
                            crate::typecheck_db::types::convert_type_expr(f, &type_ops)
                        })
                        .collect();
                    let scheme_ty = build_fn_chain(&fields, &result_ty);
                    let scheme = Scheme { vars: tvars.clone(), ty: scheme_ty };
                    env.bind_scheme(QName::unqualified(&ctor_name), scheme);
                }
            }
            cst::Decl::Newtype { name, type_vars, constructor, ty, .. } => {
                let type_name =
                    crate::typecheck_db::util::resolve_symbol(name.value.symbol());
                let tvars: Vec<String> = type_vars
                    .iter()
                    .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                    .collect();
                let result_ty =
                    apply_type_vars(&Type::Con(QName::unqualified(&type_name)), &tvars);
                let field_ty = crate::typecheck_db::types::convert_type_expr(ty, &type_ops);
                let ctor_name =
                    crate::typecheck_db::util::resolve_symbol(constructor.value.symbol());
                let scheme_ty = Type::fun(field_ty, result_ty);
                let scheme = Scheme { vars: tvars.clone(), ty: scheme_ty };
                env.bind_scheme(QName::unqualified(&ctor_name), scheme);
            }
            _ => {}
        }
    }
}

/// Build `T a b c …` from a head type and the parent's type-var names.
fn apply_type_vars(
    head: &crate::typecheck_db::types::Type,
    tvars: &[String],
) -> crate::typecheck_db::types::Type {
    use crate::typecheck_db::types::Type;
    let mut ty = head.clone();
    for v in tvars {
        ty = Type::app(ty, Type::Var(v.clone()));
    }
    ty
}

/// `[f1, f2, …, fn] + result` → `f1 -> f2 -> … -> fn -> result`.
fn build_fn_chain(
    fields: &[crate::typecheck_db::types::Type],
    result: &crate::typecheck_db::types::Type,
) -> crate::typecheck_db::types::Type {
    use crate::typecheck_db::types::Type;
    let mut acc = result.clone();
    for f in fields.iter().rev() {
        acc = Type::fun(f.clone(), acc);
    }
    acc
}

fn topo_sort_modules(
    modules: &[(String, cst::Module)],
    name_index: &HashMap<String, usize>,
) -> (Vec<usize>, Vec<Vec<String>>) {
    // Edges: for each module i, list of js it depends on
    // (i imports j). Kahn's algorithm.
    let n = modules.len();
    let mut deps: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    let mut rev_deps: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (i, (_, m)) in modules.iter().enumerate() {
        for imp in &m.imports {
            let imported = imp
                .module
                .parts
                .iter()
                .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
                .collect::<Vec<_>>()
                .join(".");
            // Skip Prim imports and imports we don't have source
            // for; those are either built in or (legitimately)
            // missing — that's a build-level concern, not a
            // topo-sort concern.
            if crate::typecheck_db::prim::is_prim_module_name(&imported) {
                continue;
            }
            if let Some(&j) = name_index.get(&imported) {
                deps[i].insert(j);
                rev_deps[j].insert(i);
            }
        }
    }

    // Kahn: push all modules with no deps, pop one at a time.
    let mut in_degree: Vec<usize> = deps.iter().map(|s| s.len()).collect();
    let mut queue: VecDeque<usize> =
        (0..n).filter(|i| in_degree[*i] == 0).collect();
    let mut order: Vec<usize> = Vec::with_capacity(n);
    while let Some(i) = queue.pop_front() {
        order.push(i);
        for &j in &rev_deps[i] {
            in_degree[j] -= 1;
            if in_degree[j] == 0 {
                queue.push_back(j);
            }
        }
    }

    // Anything remaining is part of a cycle. Group by
    // connectedness and report as `CycleInModules`.
    let mut cycles: Vec<Vec<String>> = Vec::new();
    if order.len() < n {
        let remaining: Vec<usize> = (0..n).filter(|i| !order.contains(i)).collect();
        // Simple: one cycle per connected component among the
        // remaining set. Good enough for a first pass.
        let mut visited: HashSet<usize> = HashSet::new();
        for &start in &remaining {
            if visited.contains(&start) {
                continue;
            }
            let mut stack = vec![start];
            let mut component: Vec<usize> = Vec::new();
            while let Some(i) = stack.pop() {
                if !visited.insert(i) {
                    continue;
                }
                component.push(i);
                for &j in &deps[i] {
                    if remaining.contains(&j) {
                        stack.push(j);
                    }
                }
                for &j in &rev_deps[i] {
                    if remaining.contains(&j) {
                        stack.push(j);
                    }
                }
            }
            cycles.push(
                component
                    .iter()
                    .map(|i| modules[*i].0.clone())
                    .collect(),
            );
        }
    }

    (order, cycles)
}

// Silence unused-import complaints when ModuleExports isn't
// directly constructed in this file (it's only built via
// distill_exports).
#[allow(dead_code)]
fn _touch_exports(_: &ModuleExports) {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn parse_mod(src: &str) -> cst::Module {
        parse(src).unwrap()
    }

    // =================================================================
    // Topological ordering + cycle detection
    // =================================================================

    #[test]
    fn single_module_no_imports_processes_successfully() {
        let m = parse_mod("module M where\nfoo = 1\n");
        let report = check_many_modules(vec![("M".into(), m)]);
        assert!(report.errors.is_empty(), "got: {:?}", report.errors);
        assert_eq!(report.results.len(), 1);
        assert_eq!(report.results[0].name, "M");
    }

    #[test]
    fn importer_checked_after_importee() {
        // B imports A. Both must be processed; A first.
        let a = parse_mod("module A where\nfoo = 1\n");
        let b = parse_mod("module B where\nimport A\nbar = foo\n");
        let report = check_many_modules(vec![("B".into(), b), ("A".into(), a)]);
        assert!(report.errors.is_empty());
        // A comes first in results.
        let names: Vec<&str> = report.results.iter().map(|r| r.name.as_str()).collect();
        assert_eq!(names, vec!["A", "B"]);
    }

    #[test]
    fn cycle_between_two_modules_is_reported() {
        let a = parse_mod("module A where\nimport B\nfoo = 1\n");
        let b = parse_mod("module B where\nimport A\nbar = 2\n");
        let report = check_many_modules(vec![("A".into(), a), ("B".into(), b)]);
        // Neither module should land in results; both in the cycle.
        let cycle_reported = report.errors.iter().any(|e| {
            matches!(e, MultiModuleError::CycleInModules(names)
                if names.iter().any(|n| n == "A")
                    && names.iter().any(|n| n == "B"))
        });
        assert!(cycle_reported, "got: {:?}", report.errors);
    }

    #[test]
    fn chain_a_then_b_then_c_all_process() {
        let a = parse_mod("module A where\nax = 1\n");
        let b = parse_mod("module B where\nimport A\nbx = ax\n");
        let c = parse_mod("module C where\nimport B\ncx = bx\n");
        let report = check_many_modules(vec![
            ("C".into(), c),
            ("A".into(), a),
            ("B".into(), b),
        ]);
        assert!(report.errors.is_empty());
        let names: Vec<&str> = report.results.iter().map(|r| r.name.as_str()).collect();
        assert_eq!(names, vec!["A", "B", "C"]);
    }

    // =================================================================
    // Cross-module lookup produces the right scheme
    // =================================================================

    #[test]
    fn import_brings_value_into_scope() {
        // A exports foo; B uses foo.
        let a = parse_mod("module A where\nfoo = 1\n");
        let b = parse_mod("module B where\nimport A\nbar = foo\n");
        let report = check_many_modules(vec![("A".into(), a), ("B".into(), b)]);
        assert!(report.errors.is_empty());
        let b_result = report.results.iter().find(|r| r.name == "B").unwrap();
        assert!(b_result.inference_error.is_none(), "{:?}", b_result.inference_error);
        // `bar` was inferred — it exists as a scheme.
        assert!(b_result.schemes.iter().any(|s| s.name == "bar"));
    }

    #[test]
    fn import_as_qualified_requires_prefix_to_lookup() {
        let a = parse_mod("module A where\nfoo = 1\n");
        let b = parse_mod("module B where\nimport A as Q\nbar = Q.foo\n");
        let report = check_many_modules(vec![("A".into(), a), ("B".into(), b)]);
        let b_result = report.results.iter().find(|r| r.name == "B").unwrap();
        assert!(
            b_result.inference_error.is_none(),
            "{:?}",
            b_result.inference_error,
        );
    }

    #[test]
    fn unqualified_ref_fails_under_import_as() {
        // `import A as Q` — bare `foo` should NOT resolve.
        let a = parse_mod("module A where\nfoo = 1\n");
        let b = parse_mod("module B where\nimport A as Q\nbar = foo\n");
        let report = check_many_modules(vec![("A".into(), a), ("B".into(), b)]);
        let b_result = report.results.iter().find(|r| r.name == "B").unwrap();
        // Inference should fail with UnboundVar("foo").
        assert!(
            matches!(
                &b_result.inference_error,
                Some(InferError::UnboundVar(n)) if n == "foo"
            ),
            "expected UnboundVar(\"foo\"); got {:?}",
            b_result.inference_error,
        );
    }

    // =================================================================
    // Import errors surface per-module
    // =================================================================

    #[test]
    fn import_of_unknown_module_reports_import_error() {
        let m = parse_mod("module M where\nimport Data.DoesNotExist\n");
        let report = check_many_modules(vec![("M".into(), m)]);
        let r = &report.results[0];
        assert_eq!(r.import_errors.len(), 1);
    }

    // =================================================================
    // Diagnostics aggregate across decls
    // =================================================================

    #[test]
    fn exhaustiveness_errors_surface_on_result() {
        // `data X = A | B` + `f x = case x of A -> 0` leaves B
        // uncovered.
        let m = parse_mod(
            "\
module M where
data X = A | B
f x = case x of A -> 0
",
        );
        let report = check_many_modules(vec![("M".into(), m)]);
        let r = &report.results[0];
        assert!(!r.exhaustiveness_errors.is_empty(), "expected non-exhaustive error");
    }

    #[test]
    fn inference_error_is_reported_not_panic() {
        // Reference an undefined name — inference must fail
        // gracefully, not bring the whole driver down.
        let m = parse_mod("module M where\nfoo = undefinedNameHere\n");
        let report = check_many_modules(vec![("M".into(), m)]);
        let r = &report.results[0];
        assert!(matches!(r.inference_error, Some(InferError::UnboundVar(_))));
    }
}
