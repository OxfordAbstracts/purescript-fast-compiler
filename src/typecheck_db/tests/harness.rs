//! Test-harness helpers shared by every e2e test.
//!
//! Keeps test bodies small: a typical passing test is
//!
//! ```ignore
//! #[test]
//! fn my_feature() {
//!     assert_typechecks(include_str!("fixtures/single_succeeds/my_feature.purs"));
//! }
//! ```
//!
//! Failing tests get a richer shape that lets each case narrow
//! in on the expected diagnostic.

use crate::cst;
use crate::parser::parse;
use crate::typecheck_db::driver::{CacheOutcome, TypecheckDb};
use crate::typecheck_db::driver_multi::{
    check_many_modules, check_many_modules_with_db, ModuleCheckReport, ModuleCheckResult,
    ModuleInput, MultiModuleError,
};

// ---------------------------------------------------------------------------
// Parsing + module-name extraction
// ---------------------------------------------------------------------------

/// Parse a single PureScript source. Panics with the file's
/// first 80 chars on a parse error — e2e tests aren't supposed
/// to fail at parse time, so this being a hard stop is correct.
pub fn parse_source(src: &str) -> cst::Module {
    parse(src).unwrap_or_else(|e| {
        let preview: String = src.chars().take(80).collect();
        panic!("parse error: {e:?}\n  source starts: {preview:?}");
    })
}

/// Extract the canonical module name from a parsed module
/// (e.g. `"Data.Maybe"` from `module Data.Maybe where …`).
pub fn module_name(m: &cst::Module) -> String {
    m.name
        .value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
}

// ---------------------------------------------------------------------------
// High-level asserts
// ---------------------------------------------------------------------------

/// Parse one source and expect `check_many_modules` to report
/// zero errors, imports, exhaustiveness findings, constraint
/// problems, or cycles. The first offending item is printed so
/// the failure message points directly at the bug.
pub fn assert_typechecks(src: &str) {
    let module = parse_source(src);
    let name = module_name(&module);
    let report = check_many_modules(vec![ModuleInput::new(name, src, module)]);
    assert_report_clean(&report);
}

/// Multi-source variant. All sources are parsed, each gets
/// checked in the driver's topo order, and the whole report
/// must be clean.
pub fn assert_typechecks_multi(sources: &[&str]) {
    let mut parsed: Vec<ModuleInput> = Vec::with_capacity(sources.len());
    for src in sources {
        let m = parse_source(src);
        parsed.push(ModuleInput::new(module_name(&m), *src, m));
    }
    let report = check_many_modules(parsed);
    assert_report_clean(&report);
}

fn assert_report_clean(report: &ModuleCheckReport) {
    // Driver-level errors first — a cycle or missing module
    // means subsequent module results can't be trusted.
    for err in &report.errors {
        panic!("driver error: {err:?}");
    }
    for result in &report.results {
        if let Some(err) = &result.inference_error {
            panic!("{}: inference error {err:?}", result.name);
        }
        if let Some(ie) = result.import_errors.first() {
            panic!(
                "{}: import error {:?} at span {:?}",
                result.name, ie.kind, ie.span,
            );
        }
        if let Some(ne) = result.exhaustiveness_errors.first() {
            panic!(
                "{}: non-exhaustive {} — missing {:?}",
                result.name, ne.type_name, ne.missing,
            );
        }
        if let Some(ce) = result.constraint_errors.first() {
            panic!(
                "{}: constraint {:?} on {} args={:?} span={:?}",
                result.name,
                ce.kind,
                ce.constraint.class.name,
                ce.constraint.args,
                ce.span,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Failure assertions: drive the pipeline and hand back the report
// so the caller can inspect the exact diagnostic.
// ---------------------------------------------------------------------------

/// Parse + check a single source and return the result unchanged.
/// Tests then make pinpoint claims about which diagnostic fired
/// rather than just "something went wrong".
pub fn check_single(src: &str) -> ModuleCheckResult {
    let module = parse_source(src);
    let name = module_name(&module);
    let mut report = check_many_modules(vec![ModuleInput::new(name, src, module)]);
    assert_eq!(
        report.results.len(),
        1,
        "expected one module result, got {}",
        report.results.len(),
    );
    report.results.remove(0)
}

/// Multi-source variant that returns the whole report, cycles and
/// all — `failures::` tests use this to assert on driver-level
/// errors like module cycles.
pub fn check_multi(sources: &[&str]) -> ModuleCheckReport {
    let mut parsed: Vec<ModuleInput> = Vec::with_capacity(sources.len());
    for src in sources {
        let m = parse_source(src);
        parsed.push(ModuleInput::new(module_name(&m), *src, m));
    }
    check_many_modules(parsed)
}

/// Incremental helper: parse `sources` and drive them through the
/// supplied `db`. Call twice with the same db to observe cache-hit
/// behavior.
pub fn run_with_shared_db(
    db: &mut TypecheckDb,
    sources: &[(&str, &str)],
) -> ModuleCheckReport {
    let mut parsed: Vec<ModuleInput> = Vec::with_capacity(sources.len());
    for (name, src) in sources {
        let m = parse_source(src);
        parsed.push(ModuleInput::new(name.to_string(), *src, m));
    }
    check_many_modules_with_db(db, parsed)
}

/// Convenience: pluck a specific `(module, decl)` cache outcome out
/// of a report. Panics if the module or decl isn't present, so
/// tests fail fast on a typo instead of silently returning `None`.
pub fn outcome_of(
    report: &ModuleCheckReport,
    module: &str,
    decl: &str,
) -> CacheOutcome {
    let result = report
        .results
        .iter()
        .find(|r| r.name == module)
        .unwrap_or_else(|| {
            panic!(
                "module {module:?} not in report; modules present: {:?}",
                report.results.iter().map(|r| &r.name).collect::<Vec<_>>()
            )
        });
    *result
        .decl_outcomes
        .get(decl)
        .unwrap_or_else(|| {
            panic!(
                "decl {decl:?} not in {module:?} decl_outcomes; present: {:?}",
                result.decl_outcomes.keys().collect::<Vec<_>>()
            )
        })
}

// Silence unused-import noise when a sub-module only uses one of
// the helpers.
#[allow(dead_code)]
pub fn _touch_multi_err(_: &MultiModuleError) {}
