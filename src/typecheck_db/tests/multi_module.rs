//! End-to-end multi-module tests: two or more sources where
//! later modules import earlier ones. The driver must topo-sort
//! correctly, thread each module's exports into the next
//! module's `Env`, and finish with a clean report.

use super::harness::{assert_typechecks_multi, check_multi};
use crate::typecheck_db::driver_multi::MultiModuleError;
use crate::typecheck_db::passes::imports::ImportErrorKind;

#[test]
#[ignore = "diagnostic — alias-name vs locally-imported newtype collision"]
fn diag_state_alias_collision() {
    // Marionette.Controllers.Monadic imports `Marionette.Types.State`
    // (a newtype) and `Control.Monad.State (class MonadState)` (NOT
    // the alias). The body's `state` value has the imported newtype
    // type. Our typechecker has occasionally conflated this with
    // the `Control.Monad.State` alias `type State s = StateT s
    // Identity`, producing `State` vs `StateT _` mismatches.
    assert_typechecks_multi(&[
        "\
module StateT where

foreign import data StateT :: Type -> (Type -> Type) -> Type -> Type
foreign import data Identity :: Type -> Type

type State s = StateT s Identity

class MonadState s m where
  getState :: m s
",
        "\
module MyState where

newtype State s m = State (s -> m s)
",
        "\
module Main where

import StateT (class MonadState)
import MyState (State)

foreign import data Aff :: Type -> Type

useState :: forall sta. State sta Aff -> Aff Unit
useState _ = pureAff

foreign import pureAff :: forall a. Aff a
data Unit = Unit
",
    ]);
}

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

// ---------------------------------------------------------------------------
// MREs for the Halogen "ambiguous re-exported ctor" issue
// ---------------------------------------------------------------------------
//
// `Halogen.Query.Input` defines `data Input action = ... | Action action`
// (1-arg `Action`). `Halogen.Query.HalogenQ` defines `data HalogenQ q a i b
// = ... | Action a b ...` (2-arg `Action`). `Halogen.Query` re-exports BOTH
// via `module Halogen.Query.Input` + `module Halogen.Query.HalogenQ`, and
// `Halogen` re-exports `Halogen.Query`. Downstream code (e.g.
// `Halogen.Hooks.Internal.Eval`) writes `H.Action act a` — two arguments,
// matching `HalogenQ.Action`. The compiler must:
//   - filter re-exports by the importing module's actual import list (so
//     `Halogen.Query`'s `module M` clauses re-export only the names this
//     module pulled in from M), and
//   - if both candidates survive filtering, choose the one whose arity
//     matches the use site (or carry both and disambiguate at use).
//
// The MREs below strip the situation down to its essentials.

/// Mirrors Halogen.Query's actual imports: `Input` is brought in
/// only via `(RefLabel(..))` while `HalogenQ` is brought in via
/// `(HalogenQ(..))`. The `module Halogen.Query.Input` re-export
/// should re-export ONLY the names Halogen.Query pulled from Input
/// (RefLabel + its ctors) — Action from Input must NOT leak. Then
/// `module Halogen.Query.HalogenQ` re-exports HalogenQ + Action.
/// Downstream `H.Action act a` resolves unambiguously to
/// HalogenQ.Action (2-arg).
#[test]
fn diag_reexport_ctor_arity_disambig() {
    assert_typechecks_multi(&[
        "\
module A where

data RefLabel = RefLabel
data Input action = RefUpdate | Action action
",
        "\
module B where

data HalogenQ q a = Initialize a | Receive q a | Action q a
",
        "\
module M
  ( module A
  , module B
  ) where

import A (RefLabel(..))
import B (HalogenQ(..))
",
        "\
module Main where

import M (HalogenQ(..))

data Foo = Foo
data Bar = Bar

useAction :: Foo -> Bar -> HalogenQ Foo Bar
useAction f b = Action f b
",
    ]);
}

/// Same scenario but the user qualifies the import (`import M as H`)
/// and writes `H.Action f b`. The qualified-resolution path must pick
/// the arity-2 ctor.
#[test]
fn diag_reexport_ctor_qualified_arity_disambig() {
    assert_typechecks_multi(&[
        "\
module A where

data RefLabel = RefLabel
data Input action = RefUpdate | Action action
",
        "\
module B where

data HalogenQ q a = Initialize a | Receive q a | Action q a
",
        "\
module M
  ( module A
  , module B
  ) where

import A (RefLabel(..))
import B (HalogenQ(..))
",
        "\
module Main where

import M as H

data Foo = Foo
data Bar = Bar

useAction :: Foo -> Bar -> H.HalogenQ Foo Bar
useAction f b = H.Action f b
",
    ]);
}

/// Layered re-export, mirroring `Halogen` → `Halogen.Query` →
/// (`Halogen.Query.Input`, `Halogen.Query.HalogenQ`). The deeper
/// re-export chain is where the original compiler propagates only
/// the names actually imported via the explicit lists.
#[test]
fn diag_reexport_ctor_layered_chain() {
    assert_typechecks_multi(&[
        "\
module Halogen.Query.Input where

data RefLabel = RefLabel
data Input action = RefUpdate | Action action
",
        "\
module Halogen.Query.HalogenQ where

data HalogenQ q a = Initialize a | Receive q a | Action q a
",
        "\
module Halogen.Query
  ( module Halogen.Query.Input
  , module Halogen.Query.HalogenQ
  ) where

import Halogen.Query.Input (RefLabel(..))
import Halogen.Query.HalogenQ (HalogenQ(..))
",
        "\
module Halogen
  ( module Halogen.Query
  ) where

import Halogen.Query
",
        "\
module Main where

import Halogen as H

data Foo = Foo
data Bar = Bar

useAction :: Foo -> Bar -> H.HalogenQ Foo Bar
useAction f b = H.Action f b
",
    ]);
}

/// Closer mirror of the real Halogen surface: Halogen.Query exports
/// `module Halogen.Query.Input`, `module Halogen.Query.HalogenM`,
/// and `module Halogen.Query.HalogenQ`; the HalogenM submodule
/// adds extra fixtures (its own data type with its own ctors).
/// `Halogen` re-exports `module Halogen.Query` with an explicit
/// list. Downstream `H.Action` must still resolve to HalogenQ.Action.
#[test]
fn diag_reexport_ctor_layered_with_halogenm() {
    assert_typechecks_multi(&[
        "\
module Halogen.Query.Input where

data RefLabel = RefLabel
data Input action = RefUpdate | Action action
",
        "\
module Halogen.Query.HalogenQ where

data HalogenQ q a = Initialize a | Receive q a | Action q a
",
        "\
module Halogen.Query.HalogenM where

data HalogenF state action a = State | Other action a
data HalogenM state action a = MkHalogenM a
",
        "\
module Halogen.Query
  ( module Halogen.Query.Input
  , module Halogen.Query.HalogenM
  , module Halogen.Query.HalogenQ
  ) where

import Halogen.Query.HalogenM (HalogenF(..), HalogenM(..))
import Halogen.Query.HalogenQ (HalogenQ(..))
import Halogen.Query.Input (RefLabel(..))
",
        "\
module Halogen
  ( module Halogen.Query
  ) where

import Halogen.Query (HalogenF(..), HalogenM(..), HalogenQ(..), RefLabel(..))
",
        "\
module Main where

import Halogen as H

useAction :: forall q a. q -> a -> H.HalogenQ q a
useAction f b = H.Action f b

handle :: forall q a. H.HalogenQ q a -> a
handle = case _ of
  H.Initialize a -> a
  H.Receive _ a -> a
  H.Action _ a -> a
",
    ]);
}

/// Nullary capability class — declared with no type args, no
/// instances, used purely as a propagating constraint marker
/// (`withCap :: forall a. (Cap => a) -> a` discharges locally).
/// The OA application uses ~10 of these (`PublicEventAuth`,
/// `AttendeeAuth`, `AdminAuth`, …) and 108/185 build-from-sources
/// failures pivot on them.
///
/// Expected: `bar :: MyCap => Int` propagates `MyCap` to its
/// inferred scheme. Calling `foo` (which also has `MyCap =>`)
/// from inside `bar`'s body should be discharged via the sig-
/// origin given, NOT trigger `NoInstanceFound`.
#[test]
fn diag_nullary_capability_class() {
    assert_typechecks_multi(&[
        "\
module Cap where

class MyCap
",
        "\
module Main where

import Cap (class MyCap)

foo :: MyCap => Int -> Int
foo x = x

bar :: MyCap => Int
bar = foo 1
",
    ]);
}

/// `Data.Vec` / `Data.Matrix.Reps`-shape: a use of `Succ s s'`
/// in a sig pulls in `DivMod10 x xi xl` as a sub-constraint via
/// the `typelevelSucc` instance's context. With concrete first
/// arg (e.g. `Succ D2 ?`), the chain should pick the matching
/// `divMod10D2D0 :: DivMod10 D2 D0 D2` candidate by fundep
/// `x -> i l`. Our solver was reporting `NoInstanceFound`
/// because it failed to discharge the chain — fundep-driven
/// candidate dispatch lost a beat somewhere along the recursion.
#[test]
fn diag_divmod10_succ_chain() {
    assert_typechecks_multi(&[
        "\
module Tl where

foreign import data D0 :: Type
foreign import data D1 :: Type
foreign import data D2 :: Type

class DivMod10 x i l | i l -> x, x -> i l

instance d0d0 :: DivMod10 D0 D0 D0
else instance d1d0 :: DivMod10 D1 D0 D1
else instance d2d0 :: DivMod10 D2 D0 D2

class SuccP xi xl yi yl | xi xl -> yi yl

instance sd0 :: SuccP xi D0 xi D1
else instance sd1 :: SuccP xi D1 xi D2

class Succ x y | x -> y, y -> x

instance succ ::
  ( DivMod10 x xi xl
  , SuccP xi xl yi yl
  , DivMod10 y yi yl
  ) => Succ x y
",
        "\
module Main where

import Tl (class Succ, D1, D2)

foreign import data Proxy :: forall k. k -> Type

next :: forall s s'. Succ s s' => Proxy s -> Proxy s'
next _ = mkProxy

foreign import mkProxy :: forall k (a :: k). Proxy a

useIt :: Proxy D2 -> Proxy D1
useIt p = next p

mk :: Proxy D2
mk = mkProxy
",
    ]);
}

/// Full Data.Matrix.Reps-shape: all 10 digit DivMod10 + SuccP
/// instances, plus the Pos / IsZero / Failure machinery, with
/// the multi-digit `:*` rep — exercises the same instance index
/// the real package uses. Final shape that fails:
/// `matrix21 x11 x21 = emptyRow \\ row1 x11 \\ row1 x21`
/// requires `Add D1 D1 D2` which expands to `Succ D1 D2` and
/// downstream DivMod10 / SuccP discharges.
#[test]
fn diag_typelevel_full_matrix() {
    assert_typechecks_multi(&[
        "\
module Tl where

foreign import data D0 :: Type
foreign import data D1 :: Type
foreign import data D2 :: Type
foreign import data D3 :: Type
foreign import data D4 :: Type
foreign import data D5 :: Type
foreign import data D6 :: Type
foreign import data D7 :: Type
foreign import data D8 :: Type
foreign import data D9 :: Type

foreign import data False :: Type
foreign import data True :: Type
foreign import data Tuple :: Type -> Type -> Type

class Failure t

class Nat x
instance natD0 :: Nat D0
instance natD1 :: Nat D1
instance natD2 :: Nat D2

class Pos x
instance posD1 :: Pos D1
instance posD2 :: Pos D2

class IsZero x b | x -> b
instance izD0 :: IsZero D0 True
else instance izOther :: IsZero x False

foreign import data PredecessorOfZeroError :: Type -> Type

class DivMod10 x i l | i l -> x, x -> i l

instance d0d0 :: DivMod10 D0 D0 D0
else instance d1d0 :: DivMod10 D1 D0 D1
else instance d2d0 :: DivMod10 D2 D0 D2
else instance d3d0 :: DivMod10 D3 D0 D3

class SuccP xh xl yh yl yz | xh xl -> yh yl yz, yh yl yz -> xh xl

instance spFail :: Failure (PredecessorOfZeroError x) => SuccP (Tuple x x) (Tuple x x) D0 D0 True
else instance spD0 :: SuccP xi D0 xi D1 False
else instance spD1 :: SuccP xi D1 xi D2 False
else instance spD2 :: SuccP xi D2 xi D3 False
else instance spD3 :: SuccP xi D3 xi D4 False

class Succ x y | x -> y, y -> x

instance succRel ::
  ( Pos y
  , IsZero y yz
  , DivMod10 x xi xl
  , SuccP xi xl yi yl yz
  , DivMod10 y yi yl
  ) => Succ x y

class AddP x y z | x y -> z, z x -> y

instance addPD0 :: Nat y => AddP D0 y y
else instance addPD1 :: Succ y z => AddP D1 y z
else instance addPD2 :: (Succ z z', AddP D1 y z) => AddP D2 y z'
else instance addPMulti ::
  ( Pos (Tuple xi xl)
  , Nat z
  , AddP xi yi zi
  , DivMod10 y yi yl
  , AddP xl (Tuple zi yl) z
  ) =>
  AddP (Tuple xi xl) y z

class Add x y z | x y -> z, z x -> y, z y -> x
instance addRel :: (AddP x y z, AddP y x z) => Add x y z
",
        "\
module Main where

import Tl

foreign import data Matrix :: Type -> Type -> Type -> Type

emptyRow :: forall a w. Nat w => Matrix D0 w a
emptyRow = mkMatrix

foreign import mkMatrix :: forall h w a. Matrix h w a

row1 :: forall a. a -> Matrix D1 D1 a
row1 _ = mkMatrix

concatV :: forall h1 h2 h w a. Add h1 h2 h => Nat w => Matrix h1 w a -> Matrix h2 w a -> Matrix h w a
concatV _ _ = mkMatrix

infixr 3 concatV as \\\\

matrix21 :: forall a. a -> a -> Matrix D2 D1 a
matrix21 x11 x21 = emptyRow \\\\ row1 x11 \\\\ row1 x21
",
    ]);
}

/// Smaller arithmetic MRE used to verify the basic chain works.
#[test]
fn diag_typelevel_arithmetic_chain() {
    assert_typechecks_multi(&[
        "\
module Tl where

foreign import data D0 :: Type
foreign import data D1 :: Type
foreign import data D2 :: Type
foreign import data D3 :: Type

class Nat x
instance natD0 :: Nat D0
instance natD1 :: Nat D1
instance natD2 :: Nat D2
instance natD3 :: Nat D3

class DivMod10 x i l | i l -> x, x -> i l

instance d0d0 :: DivMod10 D0 D0 D0
else instance d1d0 :: DivMod10 D1 D0 D1
else instance d2d0 :: DivMod10 D2 D0 D2
else instance d3d0 :: DivMod10 D3 D0 D3

class SuccP xh xl yh yl yz | xh xl -> yh yl yz, yh yl yz -> xh xl

instance sd0 :: SuccP xi D0 xi D1 False
else instance sd1 :: SuccP xi D1 xi D2 False
else instance sd2 :: SuccP xi D2 xi D3 False

foreign import data False :: Type

class Succ x y | x -> y, y -> x

instance succRel ::
  ( DivMod10 x xi xl
  , SuccP xi xl yi yl yz
  , DivMod10 y yi yl
  ) => Succ x y

class AddP x y z | x y -> z, z x -> y

instance addPD0 :: Nat y => AddP D0 y y
else instance addPD1 :: Succ y z => AddP D1 y z

class Add x y z | x y -> z, z x -> y, z y -> x
instance addRel :: (AddP x y z, AddP y x z) => Add x y z
",
        "\
module Main where

import Tl

foreign import data Vec :: Type -> Type -> Type
foreign import data Matrix :: Type -> Type -> Type -> Type

emptyRow :: forall a w. Nat w => Matrix D0 w a
emptyRow = mkMatrix

foreign import mkMatrix :: forall h w a. Matrix h w a

row1 :: forall a. a -> Matrix D1 D1 a
row1 _ = mkMatrix

concatV :: forall h1 h2 h w a. Add h1 h2 h => Nat w => Matrix h1 w a -> Matrix h2 w a -> Matrix h w a
concatV _ _ = mkMatrix

infixr 3 concatV as \\\\

matrix21 :: forall a. a -> a -> Matrix D2 D1 a
matrix21 x11 x21 = emptyRow \\\\ row1 x11 \\\\ row1 x21
",
    ]);
}

#[test]
fn diag_recursive_fundep_class_with_lacks() {
    assert_typechecks_multi(&[
        "\
module Tl where

foreign import data Nil :: Type
foreign import data Cons :: Type -> Type -> Type

class UseFocusedFields list out | list -> out

instance nilUFF :: UseFocusedFields Nil base

instance consUFF ::
  ( UseFocusedFields tail out'
  ) => UseFocusedFields (Cons label tail) base
",
        "\
module Main where

import Tl (class UseFocusedFields, Nil, Cons)

foreign import data Lbl :: Type
foreign import data Anything :: Type
foreign import data Int :: Type
foreign import one :: forall a. a

useIt :: forall list out. UseFocusedFields list out => list -> out
useIt _ = useIt' (one :: Int)

foreign import useIt' :: forall a b. a -> b

go :: Anything
go = useIt (one :: Cons Lbl (Cons Lbl Nil))
",
    ]);
}

/// Real-shape regression for `case _ of` with the layered re-export.
/// Mirrors Halogen.Hooks.Internal.Eval's `mkEval inputEq … = case _ of
/// H.Initialize a -> …; H.Action act a -> …`. The case-sugar `_`
/// desugars to a fresh lambda binder; pattern matches against
/// `H.Initialize` and `H.Action` MUST pin the scrutinee to
/// `HalogenQ`, not `Input`.
#[test]
fn diag_reexport_ctor_case_pattern_disambig() {
    assert_typechecks_multi(&[
        "\
module Halogen.Query.Input where

data RefLabel = RefLabel
data Input action = RefUpdate | Action action
",
        "\
module Halogen.Query.HalogenQ where

data HalogenQ q a = Initialize a | Receive q a | Action q a
",
        "\
module Halogen
  ( module Halogen.Query.Input
  , module Halogen.Query.HalogenQ
  ) where

import Halogen.Query.Input (RefLabel(..))
import Halogen.Query.HalogenQ (HalogenQ(..))
",
        "\
module Main where

import Halogen as H

handle :: forall q a. H.HalogenQ q a -> a
handle = case _ of
  H.Initialize a -> a
  H.Receive _ a -> a
  H.Action _ a -> a
",
    ]);
}
