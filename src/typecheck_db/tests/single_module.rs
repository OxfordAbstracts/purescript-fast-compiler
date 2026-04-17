//! Single-module e2e tests that should typecheck cleanly.
//!
//! Each test names the feature(s) the fixture exercises. The
//! fixture is a real PureScript source in `fixtures/`. The
//! expectation is always the same: zero errors end-to-end.
//! Failure paths live in [`crate::typecheck_db::tests::failures`].

use super::harness::assert_typechecks;

#[test]
fn literals_and_lambda() {
    // Int / Number / String / Char / Boolean literals + `identity`
    // + two-arg `const`.
    assert_typechecks(include_str!("fixtures/single_succeeds/literals_and_lambda.purs"));
}

#[test]
fn let_and_if() {
    // Nested `let` bindings + if-then-else branch unification.
    assert_typechecks(include_str!("fixtures/single_succeeds/let_and_if.purs"));
}

#[test]
fn data_and_case() {
    // ADT declaration + exhaustive case + multi-equation merge
    // + single-field nested constructor recursion.
    assert_typechecks(include_str!("fixtures/single_succeeds/data_and_case.purs"));
}

#[test]
fn newtype_round_trip() {
    // Newtype constructor at value and pattern sites.
    assert_typechecks(include_str!("fixtures/single_succeeds/newtype.purs"));
}

#[test]
fn records() {
    // Closed record literal, open-row field access, record
    // update, pun syntax.
    assert_typechecks(include_str!("fixtures/single_succeeds/records.purs"));
}

#[test]
fn arrays() {
    // Array literal, empty-array polymorphism, array pattern.
    assert_typechecks(include_str!("fixtures/single_succeeds/arrays.purs"));
}

#[test]
fn class_and_instance() {
    // Single-class definition, one-constructor ADT, instance
    // discharged by the Phase B solver on call-site `show Happy`.
    assert_typechecks(include_str!("fixtures/single_succeeds/class_and_instance.purs"));
}

#[test]
fn instance_context_recursive_solving() {
    // `instance Eq a => Eq (Maybe a)` + `instance Eq Int` —
    // the Phase C fixed-point loop must discharge the outer
    // `Eq (Maybe Int)` and the inner `Eq Int` together.
    assert_typechecks(include_str!("fixtures/single_succeeds/instance_context.purs"));
}

#[test]
fn where_clause_bindings() {
    // `where` clauses are lowered into a synthetic `let` around
    // the body so the clause's names are visible during
    // inference.
    assert_typechecks(include_str!("fixtures/single_succeeds/where_clause.purs"));
}
