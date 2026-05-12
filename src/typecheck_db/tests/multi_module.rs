//! End-to-end multi-module tests: two or more sources where
//! later modules import earlier ones. The driver must topo-sort
//! correctly, thread each module's exports into the next
//! module's `Env`, and finish with a clean report.

use super::harness::{assert_typechecks_multi, check_multi};
use crate::typecheck_db::driver_multi::MultiModuleError;
use crate::typecheck_db::passes::imports::ImportErrorKind;

#[test]
#[ignore = "diagnostic — Eq instance body calls show + == on String"]
fn diag_eq_instance_body_show_eq() {
    // Reproducer for Node.FS.Constants::eqFileFlags's
    // `eq x y = show x == show y` pattern. Inside an `Eq T`
    // instance method, references to `==` (which desugars to the
    // class method `eq`) should resolve to the polymorphic class
    // method, not be shadowed by the instance method's own
    // specialised scheme.
    assert_typechecks_multi(&[
        "\
module ShowEq where

class Show a where
  show :: a -> String

class Eq a where
  eq :: a -> a -> Boolean

infix 4 eq as ==

foreign import data String :: Type
data Boolean = TT | FF

instance Eq String where
  eq = eqStringImpl

foreign import eqStringImpl :: String -> String -> Boolean

instance Show String where
  show s = s
",
        "\
module Main where

import ShowEq (class Eq, class Show, eq, show, (==), String, Boolean)

data Color = Red | Green | Blue

instance Show Color where
  show Red = \"Red\"
  show Green = \"Green\"
  show Blue = \"Blue\"

instance Eq Color where
  eq x y = show x == show y
",
    ]);
}

#[test]
#[ignore = "diagnostic — MonadThrow Error Effect re-import chain"]
fn diag_monad_throw_effect_re_imported() {
    // Closer mirror of Webb.Monad.Prelude::expectM: `throwString`
    // is in a separate module that imports its `Error` from one
    // module and its `MonadThrow` class + instance from another.
    // The consumer (Main) imports `throwString` AND `Effect` /
    // `liftEffect`; the use site forces `m := Effect`, requiring
    // `MonadThrow Error Effect` to discharge through both chains.
    assert_typechecks_multi(&[
        "\
module Exception where

foreign import data Error :: Type
foreign import error :: String -> Error
",
        "\
module Eff where

foreign import data Effect :: Type -> Type
",
        "\
module MonadErr where

import Exception (Error)
import Eff (Effect)

class MonadThrow e m where
  throwError :: forall a. e -> m a

instance monadThrowEffect :: MonadThrow Error Effect where
  throwError = throwErrorImpl

foreign import throwErrorImpl :: forall a. Error -> Effect a
",
        "\
module Helpers where

import Exception (Error, error)
import MonadErr (class MonadThrow, throwError)

throwString :: forall a m. MonadThrow Error m => String -> m a
throwString s = throwError (error s)
",
        "\
module Main where

import Eff (Effect)
import Helpers (throwString)

doThrow :: Effect Unit
doThrow = throwString \"oh no\"

data Unit = Unit
",
    ]);
}

#[test]
#[ignore = "diagnostic — MonadThrow Error Effect discharge"]
fn diag_monad_throw_effect_discharges() {
    // Reproduces the MonadThrow NoInstanceFound cluster (19
    // modules) — `expectM`-style helpers that call
    // `liftEffect (throwError err)` against a `MonadThrow Error
    // Effect` instance defined in a sibling module.
    assert_typechecks_multi(&[
        "\
module Err where

foreign import data Error :: Type

class MonadThrow e m where
  throwError :: forall a. e -> m a

foreign import data Effect :: Type -> Type

instance monadThrowEffect :: MonadThrow Error Effect where
  throwError = throwErrorImpl

foreign import throwErrorImpl :: forall a. Error -> Effect a

foreign import error :: String -> Error

throwString :: forall a m. MonadThrow Error m => String -> m a
throwString s = throwError (error s)
",
        "\
module Main where

import Err (Effect, Error, MonadThrow, throwString)

doThrow :: Effect Unit
doThrow = throwString \"oh no\"

data Unit = Unit
",
    ]);
}

#[test]
fn compose_polymorphic_record_via_imported_class() {
    // Reproducer for the Next.Router compose-direction bug: the
    // failing usage `event "x" <<< mkEffectFn1` against a sig
    // `forall r. ({ cancelled :: Boolean | r } -> Effect Unit) ->
    // Effect (Effect Unit)`.
    assert_typechecks_multi(&[
        "\
module Semi where

class Semigroupoid a where
  compose :: forall b c d. a c d -> a b c -> a b d

instance semigroupoidFn :: Semigroupoid (->) where
  compose f g x = f (g x)

infixr 9 compose as <<<
",
        "\
module Eff where

foreign import data Effect :: Type -> Type
foreign import data EffectFn1 :: Type -> Type -> Type

foreign import mkEffectFn1 :: forall a r. (a -> Effect r) -> EffectFn1 a r
",
        "\
module Main where

import Semi (compose, (<<<))
import Eff (Effect, EffectFn1, mkEffectFn1)

data Unit = Unit
data Boolean = TT | FF

foreign import event :: forall a. String -> a -> Effect (Effect Unit)

routeChangeError
  :: forall r. ({ cancelled :: Boolean | r } -> Effect Unit) -> Effect (Effect Unit)
routeChangeError = event \"rce\" <<< mkEffectFn1
",
    ]);
}

#[test]
fn imported_alias_in_constrained_higher_order_sig() {
    // Mirrors `mapAccumL :: Traversable f => (s -> a -> Accum s b)
    // -> s -> f a -> Accum s (f b)` — a cross-module alias used
    // inside a constrained, higher-order signature, with a sibling
    // decl (`scanl`) that passes a record literal where `Accum s b`
    // is expected.
    assert_typechecks_multi(&[
        "\
module AccumLib (Accum) where

type Accum s a = { accum :: s, value :: a }
",
        "\
module Main where

import AccumLib (Accum)

class Foldable f where
  foldr :: forall a b. (a -> b -> b) -> b -> f a -> b

mapAccumL
  :: forall a b f s. Foldable f
  => (s -> a -> Accum s b)
  -> s
  -> f a
  -> Accum s Int
mapAccumL _ s _ = { accum: s, value: 0 }

scanl :: forall a b f. Foldable f => (b -> a -> b) -> b -> f a -> Int
scanl f b0 xs = (mapAccumL (\\b a -> let b' = f b a in { accum: b', value: b' }) b0 xs).value
",
    ]);
}

#[test]
fn imported_alias_expands_to_record_at_call_site() {
    assert_typechecks_multi(&[
        "\
module AccumLib (Accum) where

type Accum s a = { accum :: s, value :: a }
",
        "\
module Main where

import AccumLib (Accum)

mk :: Int -> Accum Int Int
mk x = { accum: x, value: x }

useIt :: forall s. (Int -> Accum s Int) -> Int -> s
useIt f x = (f x).accum
",
    ]);
}

#[test]
fn prelude_style_generic_via_reexport_chain() {
    // Multi-module mirror of Prelude's failing path: `F` defines
    // `apply` + `$`, `Rep` defines the `Generic a rep | a -> rep`
    // class, `P` re-exports both via `module ...` clauses, and
    // consumer `G` imports `P` unqualified. Without tracking the
    // origin of re-exported values, `$` rewrites to
    // `Var("F.apply")` but the env only has `(None, "apply")`
    // / `(Some("P"), "apply")`, producing an UnboundVar surprise
    // that matched the real Prelude regression.
    assert_typechecks_multi(&[
        "\
module F
  ( apply, ($)
  ) where

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

infixr 0 apply as $
",
        "\
module Rep
  ( class Generic, from, to
  ) where

class Generic a rep | a -> rep where
  from :: a -> rep
  to :: rep -> a
",
        "\
module P
  ( module F
  , module Rep
  ) where

import F
import Rep
",
        "\
module G where

import P

class GR r where
  gsub' :: r -> r -> r

gsub :: forall a rep. Generic a rep => GR rep => a -> a -> a
gsub x y = to $ from x `gsub'` from y
",
    ]);
}

#[test]
fn reexport_preserves_fixity_target_origin() {
    // Mirror the Prelude re-export chain that triggered
    // `UnboundVar("Data.Function.apply")`: module `F` defines
    // `apply` and `($)` with `$` aliased to `apply`; module `P`
    // only re-exports `F` via a `module F` clause; module `U`
    // imports `P` and uses `$`. With fixity-target
    // canonicalization, `$` lowers to `Var("F.apply")` — so the
    // env populated from `P`'s re-exports must bind `F.apply`.
    assert_typechecks_multi(&[
        "\
module F
  ( apply, ($)
  ) where

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

infixr 0 apply as $
",
        "\
module P (module F) where

import F
",
        "\
module U where

import P

id :: forall a. a -> a
id x = x

use :: Int
use = id $ 1
",
    ]);
}

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
