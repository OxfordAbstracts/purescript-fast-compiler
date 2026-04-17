//! Single-module tests whose job is to fail, with specific
//! expected diagnostics. Each case picks one error class the
//! checker must catch for the right reason.

use super::harness::check_single;
use crate::typecheck_db::passes::constraints::ConstraintErrorKind;
use crate::typecheck_db::passes::infer_value::InferError;

#[test]
fn unbound_var_reported() {
    let r = check_single(include_str!("fixtures/single_fails/unbound_var.purs"));
    assert!(
        matches!(&r.inference_error, Some(InferError::UnboundVar(n)) if n == "missingThing"),
        "expected UnboundVar(\"missingThing\"); got {:?}",
        r.inference_error,
    );
}

#[test]
fn wrong_type_annotation_fails_unification() {
    // `bad :: Int` + `bad = "string"` — annotation forces Int
    // but body is String, so unification mismatches.
    let r = check_single(include_str!("fixtures/single_fails/wrong_type.purs"));
    assert!(
        matches!(&r.inference_error, Some(InferError::Unify(_))),
        "expected Unify mismatch; got {:?}",
        r.inference_error,
    );
}

#[test]
fn non_exhaustive_case_reported() {
    let r = check_single(include_str!("fixtures/single_fails/non_exhaustive.purs"));
    assert!(
        r.exhaustiveness_errors
            .iter()
            .any(|e| e.type_name == "Maybe" && e.missing.iter().any(|m| m == "Just")),
        "expected non-exhaustive Maybe missing Just; got {:?}",
        r.exhaustiveness_errors,
    );
}

#[test]
fn missing_instance_reported() {
    let r = check_single(include_str!("fixtures/single_fails/missing_instance.purs"));
    assert!(
        r.constraint_errors.iter().any(|e| e.kind
            == ConstraintErrorKind::NoInstanceFound
            && e.constraint.class.name == "Show"),
        "expected NoInstanceFound for Show; got {:?}",
        r.constraint_errors,
    );
}

#[test]
fn unbound_constructor_reported() {
    let r = check_single(include_str!("fixtures/single_fails/unbound_constructor.purs"));
    assert!(
        matches!(
            &r.inference_error,
            Some(InferError::UnboundConstructor(n)) if n.contains("Zebra")
        ),
        "expected UnboundConstructor(Zebra); got {:?}",
        r.inference_error,
    );
}
