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
use crate::typecheck_db::driver_multi::{
    check_many_modules, ModuleCheckReport, ModuleCheckResult, MultiModuleError,
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
    let report = check_many_modules(vec![(name, module)]);
    assert_report_clean(&report);
}

/// Multi-source variant. All sources are parsed, each gets
/// checked in the driver's topo order, and the whole report
/// must be clean.
pub fn assert_typechecks_multi(sources: &[&str]) {
    let mut parsed: Vec<(String, cst::Module)> = Vec::with_capacity(sources.len());
    for src in sources {
        let m = parse_source(src);
        parsed.push((module_name(&m), m));
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
                "{}: constraint {:?} on {}",
                result.name, ce.kind, ce.constraint.class.name,
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
    let mut report = check_many_modules(vec![(name, module)]);
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
    let mut parsed: Vec<(String, cst::Module)> = Vec::with_capacity(sources.len());
    for src in sources {
        let m = parse_source(src);
        parsed.push((module_name(&m), m));
    }
    check_many_modules(parsed)
}

// Silence unused-import noise when a sub-module only uses one of
// the helpers.
#[allow(dead_code)]
pub fn _touch_multi_err(_: &MultiModuleError) {}
