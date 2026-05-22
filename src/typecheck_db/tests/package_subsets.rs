//! Subset acceptance tests over the package fixture corpus.
//!
//! `all_packages_typecheck` runs the entire 4859-module set
//! (~2 minutes release) which is too coarse for fast iteration.
//! These tests each pick an anchor module and check its full
//! transitive import closure — every closure stays under 500
//! modules, so each test exercises a meaningful slice in a few
//! seconds without duplicating the full sweep.
//!
//! Anchors were chosen for diversity: different package families
//! (Halogen, Deku, Lumi, Web.GPU, …) plus a few tiny leaves so
//! breakages in core libraries surface immediately.

use crate::typecheck_db::driver_multi::{check_many_modules, ModuleInput};
use crate::typecheck_db::test_support::{
    package_modules_by_name, transitive_closure_of,
};

/// Run the transitive closure of `anchor` through the driver and
/// assert the report is clean. Panics with a precise diagnostic
/// at the first failing module / driver error so the caller can
/// jump straight to the bug.
fn check_closure(anchor: &str, max_size: usize) {
    let pkgs = package_modules_by_name();
    assert!(
        pkgs.contains_key(anchor),
        "anchor module {anchor:?} not found in packages",
    );
    let closure = transitive_closure_of(anchor, &pkgs);
    assert!(
        closure.len() <= max_size,
        "{anchor}: closure has {} modules — exceeds budget of {max_size}",
        closure.len(),
    );
    let report = check_many_modules(closure);
    for err in &report.errors {
        panic!("{anchor}: driver error {err:?}");
    }
    for result in &report.results {
        if let Some(err) = &result.inference_error {
            panic!("{anchor}: {}: inference {err:?}", result.name);
        }
        if let Some(ie) = result.import_errors.first() {
            panic!(
                "{anchor}: {}: import {:?} at span {:?}",
                result.name, ie.kind, ie.span,
            );
        }
        if let Some(ce) = result.constraint_errors.first() {
            panic!(
                "{anchor}: {}: constraint {:?} on {} args={:?} span={:?}",
                result.name,
                ce.kind,
                ce.constraint.class.name,
                ce.constraint.args,
                ce.span,
            );
        }
        if let Some(ke) = result.kind_errors.first() {
            panic!("{anchor}: {}: kind {:?}", result.name, ke.kind);
        }
        if let Some(ce) = result.coercible_errors.first() {
            panic!("{anchor}: {}: coercible {:?}", result.name, ce.kind);
        }
        if let Some(ve) = result.validation_errors.first() {
            panic!("{anchor}: {}: validation {:?}", result.name, ve.kind);
        }
        // Non-exhaustive patterns are warnings in the reference
        // compiler — `all_packages_typecheck` and `build_from_sources`
        // both skip them here.
    }
}

// ---------------------------------------------------------------------------
// Tiny closures (≤ 25 modules) — fast smoke tests over core libraries.
// Any of these failing means something deeply load-bearing broke.
// ---------------------------------------------------------------------------

#[test]
fn subset_control_applicative() {
    check_closure("Control.Applicative", 25);
}

#[test]
fn subset_data_monoid_generic() {
    check_closure("Data.Monoid.Generic", 25);
}

// ---------------------------------------------------------------------------
// Small closures (25-100 modules) — exercise common feature combinations.
// ---------------------------------------------------------------------------

#[test]
fn subset_type_data_peano() {
    check_closure("Type.Data.Peano", 50);
}

#[test]
fn subset_data_const() {
    check_closure("Data.Const", 60);
}

#[test]
fn subset_affjax_request_header() {
    check_closure("Affjax.RequestHeader", 60);
}

// ---------------------------------------------------------------------------
// Medium closures (100-300 modules) — bulk diverse coverage.
// ---------------------------------------------------------------------------

#[test]
fn subset_uri() {
    check_closure("URI", 250);
}

#[test]
fn subset_marked() {
    check_closure("Marked", 300);
}

#[test]
fn subset_pipes_postgres() {
    check_closure("Pipes.Postgres", 300);
}

#[test]
fn subset_httpurple() {
    check_closure("HTTPurple", 300);
}

#[test]
fn subset_webb_afflist() {
    check_closure("Webb.AffList", 300);
}

// ---------------------------------------------------------------------------
// Large closures (300-500 modules) — cover wide package subtrees.
// Still well under the full-sweep size, so failures stay localized.
// ---------------------------------------------------------------------------

#[test]
fn subset_yoga_react_dom() {
    check_closure("Yoga.React.DOM", 350);
}

#[test]
fn subset_web_gpu_navigator() {
    check_closure("Web.GPU.Navigator", 450);
}

#[test]
fn subset_lumi_components_styles() {
    check_closure("Lumi.Components.Styles", 500);
}

#[test]
fn subset_halogen_xshell_commandline() {
    check_closure("Halogen.XShell.CommandLine", 500);
}
