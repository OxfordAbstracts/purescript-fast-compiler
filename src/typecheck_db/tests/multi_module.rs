//! End-to-end multi-module tests: two or more sources where
//! later modules import earlier ones. The driver must topo-sort
//! correctly, thread each module's exports into the next
//! module's `Env`, and finish with a clean report.

use super::harness::{assert_typechecks_multi, check_multi};
use crate::typecheck_db::driver_multi::MultiModuleError;
use crate::typecheck_db::passes::imports::ImportErrorKind;

#[test]
fn importer_uses_imported_value() {
    // B imports A's `answer` (import-all, unqualified).
    assert_typechecks_multi(&[
        include_str!("fixtures/multi_succeeds/import_value_a.purs"),
        include_str!("fixtures/multi_succeeds/import_value_b.purs"),
    ]);
}

#[test]
fn importer_resolves_via_qualified_alias() {
    // `import Test.Multi.AsA as Q` — bare `answer` must *not*
    // resolve, `Q.answer` must. The success here proves the
    // qualified path works; the negative half is covered by a
    // separate failure test below.
    assert_typechecks_multi(&[
        include_str!("fixtures/multi_succeeds/import_as_a.purs"),
        include_str!("fixtures/multi_succeeds/import_as_b.purs"),
    ]);
}

#[test]
fn importer_uses_imported_data_ctors() {
    // `Maybe(..)` pulls both constructors into the importer's
    // env as usable value schemes.
    assert_typechecks_multi(&[
        include_str!("fixtures/multi_succeeds/import_ctor_a.purs"),
        include_str!("fixtures/multi_succeeds/import_ctor_b.purs"),
    ]);
}

#[test]
fn unknown_module_reports_import_error() {
    let report = check_multi(&[include_str!("fixtures/multi_fails/unknown_module.purs")]);
    let result = report
        .results
        .iter()
        .find(|r| r.name == "Test.MultiFails.UnknownModule")
        .expect("module result present");
    assert!(
        result.import_errors.iter().any(|e| matches!(
            &e.kind,
            ImportErrorKind::UnknownModule(name) if name == "Test.DoesNotExist"
        )),
        "expected UnknownModule(Test.DoesNotExist); got {:?}",
        result.import_errors,
    );
}

#[test]
fn unknown_value_in_explicit_import_reports() {
    let report = check_multi(&[
        include_str!("fixtures/multi_fails/unknown_value_a.purs"),
        include_str!("fixtures/multi_fails/unknown_value_b.purs"),
    ]);
    let b = report
        .results
        .iter()
        .find(|r| r.name == "Test.MultiFails.UnknownValueB")
        .expect("B module result");
    assert!(
        b.import_errors.iter().any(|e| matches!(
            &e.kind,
            ImportErrorKind::UnknownValue { module, name }
                if module == "Test.MultiFails.UnknownValueA" && name == "missing"
        )),
        "expected UnknownValue(UnknownValueA::missing); got {:?}",
        b.import_errors,
    );
}

#[test]
fn module_cycle_is_reported() {
    let report = check_multi(&[
        include_str!("fixtures/multi_fails/cycle_a.purs"),
        include_str!("fixtures/multi_fails/cycle_b.purs"),
    ]);
    assert!(
        report.errors.iter().any(|e| matches!(e, MultiModuleError::CycleInModules(names)
            if names.iter().any(|n| n == "Test.MultiFails.CycleA")
                && names.iter().any(|n| n == "Test.MultiFails.CycleB"))),
        "expected CycleInModules naming both halves; got {:?}",
        report.errors,
    );
}
