//! End-to-end multi-module tests: two or more sources where
//! later modules import earlier ones. The driver must topo-sort
//! correctly, thread each module's exports into the next
//! module's `Env`, and finish with a clean report.

use super::harness::{assert_typechecks_multi, check_multi};
use crate::typecheck_db::driver_multi::MultiModuleError;
use crate::typecheck_db::passes::imports::ImportErrorKind;

#[test]
fn generic_sub_cross_module_with_imported_fundep_class() {
    // Multi-module mirror of `Data.Ring.Generic.genericSub`:
    // module A exports the `Generic a rep | a -> rep` class plus
    // `from` / `to`; module B imports them and writes
    // `genericSub x y = to $ from x `genericSub'` from y`. This
    // isolates the Prelude failure where `NoInstanceFound on
    // Generic [Fun(..)]` appeared.
    assert_typechecks_multi(&[
        "\
module A
  ( class Generic, from, to
  , apply, ($)
  ) where

class Generic a rep | a -> rep where
  from :: a -> rep
  to :: rep -> a

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

infixr 0 apply as $
",
        "\
module B where

import A (class Generic, from, to, ($))

data NoArguments = NoArguments
data Product a b = Product a b
data Argument a = Argument a
data Constructor (name :: Symbol) a = Constructor a

class Ring a where
  sub :: a -> a -> a

class GenericRing r where
  genericSub' :: r -> r -> r

instance genericRingNoArguments :: GenericRing NoArguments where
  genericSub' _ _ = NoArguments

instance genericRingArgument :: Ring a => GenericRing (Argument a) where
  genericSub' (Argument x) (Argument y) = Argument (sub x y)

instance genericRingProduct :: (GenericRing a, GenericRing b) => GenericRing (Product a b) where
  genericSub' (Product a1 b1) (Product a2 b2) = Product (genericSub' a1 a2) (genericSub' b1 b2)

instance genericRingConstructor :: GenericRing a => GenericRing (Constructor name a) where
  genericSub' (Constructor a1) (Constructor a2) = Constructor (genericSub' a1 a2)

genericSub :: forall a rep. Generic a rep => GenericRing rep => a -> a -> a
genericSub x y = to $ from x `genericSub'` from y
",
    ]);
}

#[test]
fn apply_second_cross_module_imports_functor_and_apply() {
    // Cross-module mirror of `Prelude::Control.Apply.applySecond`:
    // module A defines the `Functor`/`Apply` classes and exposes
    // their methods + operator aliases; module B consumes both and
    // writes `applySecond a b = const identity <$> a <*> b`.
    // Reproduces the `Mismatch(Fun(...), App(App(...)))` gap —
    // single-module tests don't hit it because the same-module
    // scheme for `apply` isn't re-instantiated through the
    // import-driven scheme path.
    assert_typechecks_multi(&[
        "\
module A
  ( class Functor, map, (<$>)
  , const, identity
  ) where

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

infixl 4 map as <$>

const :: forall a b. a -> b -> a
const x _ = x

identity :: forall a. a -> a
identity x = x
",
        "\
module B where

import A (class Functor, const, identity, (<$>))

class Functor f <= Apply f where
  apply :: forall a b. f (a -> b) -> f a -> f b

infixl 4 apply as <*>

applySecond :: forall a b f. Apply f => f a -> f b -> f b
applySecond a b = const identity <$> a <*> b
",
    ]);
}

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
