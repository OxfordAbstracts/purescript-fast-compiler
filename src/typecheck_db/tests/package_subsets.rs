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

/// Typecheck synthetic module SOURCES against the real package
/// fixtures (Prelude, Aff, …). Each source is parsed and inserted
/// into the package map under its own module name; the LAST
/// source's transitive closure (real library code + all synthetic
/// modules it imports) is run through the driver. Panics on any
/// synthetic module's first error. Use to reproduce
/// application-shaped failures without needing the whole OA corpus.
fn check_synthetic_modules(sources: &[&str]) {
    let mut pkgs = package_modules_by_name();
    let mut names: Vec<String> = Vec::new();
    for source in sources {
        let module = crate::parser::parse(source).expect("synthetic module parses");
        let name = crate::typecheck_db::test_support::module_name_of(&module);
        names.push(name.clone());
        pkgs.insert(
            name.clone(),
            ModuleInput::new(name, source.to_string(), module),
        );
    }
    let target = names.last().expect("at least one source").clone();
    let closure = transitive_closure_of(&target, &pkgs);
    eprintln!("[synthetic] {target}: closure {} modules", closure.len());
    let report = check_many_modules(closure);
    for err in &report.errors {
        panic!("{target}: driver error {err:?}");
    }
    for result in &report.results {
        if !names.contains(&result.name) {
            continue;
        }
        if let Some(err) = &result.inference_error {
            panic!("{}: inference {err:?}", result.name);
        }
        if let Some(ce) = result.constraint_errors.first() {
            panic!(
                "{}: constraint {:?} on {} args={:?} span={:?}",
                result.name, ce.kind, ce.constraint.class.name, ce.constraint.args, ce.span,
            );
        }
        if let Some(ie) = result.import_errors.first() {
            panic!("{}: import {:?} at span {:?}", result.name, ie.kind, ie.span);
        }
    }
}

/// Single-module convenience wrapper over [`check_synthetic_modules`].
fn check_synthetic_module(source: &str) {
    check_synthetic_modules(&[source]);
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

// ---------------------------------------------------------------------------
// Synthetic application-shaped repros.
// ---------------------------------------------------------------------------

/// Repro candidate for the EventPage.Update / Components.Dialog.
/// Symposium `Mismatch(Maybe, Aff)` cluster. A big `case` whose arms
/// build `{ newState, effects :: Array (Aff (Maybe msg)) }` records
/// using the application's idioms:
///   * generic first arm via a `noEffects` helper,
///   * `# effects [ handleError "…" <=< try $ someAff … ]`
///     (Kleisli-composed error handler over `try`),
///   * `liftEffect … *> pure Nothing`,
///   * `Nothing <$ do liftEffect …`,
///   * an Aff do-block ending `pure Nothing`.
#[test]
fn synthetic_effmodel_case_arms() {
    check_synthetic_module(
        r#"module Test.Synthetic.EffModelArms where

import Prelude

import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, try)
import Effect.Class (liftEffect)

type UpdateResult st msg = { newState :: st, effects :: Array (Aff (Maybe msg)) }

data Msg = A | B | C | D | E

noEffects :: forall st msg. st -> UpdateResult st msg
noEffects st = { newState: st, effects: [] }

someEffect :: Effect Unit
someEffect = pure unit

someAff :: Int -> Aff Int
someAff = pure

update :: Msg -> Int -> UpdateResult Int Msg
update msg state = case msg of
  A -> noEffects state

  B ->
    noEffects state
      # effects [ handleError "failed" <=< try $ someAff 1 ]

  C ->
    { newState: state
    , effects: [ liftEffect someEffect *> pure Nothing ]
    }

  D ->
    { newState: state
    , effects: [ Nothing <$ do liftEffect someEffect ]
    }

  E ->
    { newState: state
    , effects:
        [ do
            void $ someAff 2
            pure Nothing
        ]
    }

  where

  effects :: Array (Aff (Maybe Msg)) -> UpdateResult Int Msg -> UpdateResult Int Msg
  effects effs result = result { effects = result.effects <> effs }

  handleError :: forall a b. String -> Either a b -> Aff (Maybe Msg)
  handleError errorMsg res =
    case lmap (const errorMsg) res of
      Left _ -> pure $ Just A
      Right _ -> pure Nothing
"#,
    );
}

/// Minimal repro of the DrPayPalCreateOrder `Mismatch(Record([],
/// None), Record([(field), …], open))` failure, isolated by
/// bisecting `existingOrderItems`. A `let`-bound, WILDCARD-annotated
/// polymorphic helper
///
///   hasField = any (_.status >>> eq A) :: forall a. Array { status :: _ | a } -> Boolean
///
/// applied to TWO arrays whose element records have DIFFERENT field
/// sets (`tickets` vs `addons`). The `{ status :: _ | a }`
/// annotation carries both a row var `a` AND a wildcard `_`; each
/// application must instantiate them FRESH. The bug pinned the
/// shared wildcard/row across both call sites, collapsing one
/// element type to the empty record.
#[test]
fn synthetic_wildcard_row_annotation_two_uses() {
    check_synthetic_module(
        r#"module Test.Synthetic.WildcardRowAnn where

import Prelude

import Data.Array (any, concatMap, filter)
import Effect (Effect)

data Status = Refund | Unpaid

derive instance Eq Status

type Detail =
  { attendee_tickets :: Array { status :: Status, ticket_name :: String, price :: Int }
  , attendee_addons :: Array { status :: Status, addon_name :: String, addon_id :: Int }
  }

fetch :: Effect Detail
fetch = pure
  { attendee_tickets: []
  , attendee_addons: []
  }

go :: Effect Boolean
go = do
  { attendee_tickets, attendee_addons } <- fetch
  let
    tickets = filter (_.status >>> (eq Refund || eq Unpaid)) attendee_tickets
    addons = filter (_.status >>> (eq Refund || eq Unpaid)) attendee_addons
    hasRefundField = any (_.status >>> eq Refund) :: forall a. Array { status :: _ | a } -> Boolean
    hasRefund = hasRefundField tickets || hasRefundField addons
  pure hasRefund
"#,
    );
}

/// Minimal repro of the EventPage.Update / Components.Dialog.
/// Symposium `Mismatch(Maybe, Aff)` failures, isolated by bisecting
/// the real module: an `Array (Aff (Maybe msg))` element of shape
///
///   Nothing <$ do
///     liftEffect $ polyEffectFn $ arg
///
/// where `polyEffectFn :: MonadEffect m => … -> m Unit` is
/// POLYMORPHIC in its monad (the real one is
/// `OaBrowserGlobal.upgradeOpenData`). With a concrete
/// `Effect Unit` argument the same shape typechecks; the
/// polymorphic version mis-pins the `<$` functor to `Maybe`
/// (from `Nothing`) instead of `Aff`.
#[test]
fn synthetic_voidright_poly_lifteffect() {
    check_synthetic_module(
        r#"module Test.Synthetic.VoidRightPoly where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)

upgrade :: forall m. MonadEffect m => Int -> m Unit
upgrade _ = liftEffect (pure unit)

effects :: Array (Aff (Maybe Int))
effects =
  [ Nothing <$ do
      liftEffect $ upgrade $ 1
  ]
"#,
    );
}

/// Two-module variant of `synthetic_effmodel_case_arms`, closer to
/// the real EventPage.Update shape:
///   * `init` lives in a SEPARATE module (its scheme travels via
///     ModuleExports, like AdminDashboard.Pages.EventPage.Model),
///   * 3-arg `update msg state pageModel@{ ui }` with an as-pattern
///     record binder,
///   * `let selectedStage = … in case msg of …` wrapper,
///   * a record-pattern do-bind `{ loadable } <- init …` from the
///     imported Aff function,
///   * where-helpers (`updateStage`, `setUi`, `effects`,
///     `handleError`) closing over the outer binders.
#[test]
fn synthetic_effmodel_two_module() {
    check_synthetic_modules(&[
        r#"module Test.Synthetic.PageModel where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

type PageUi = { expandStageSelection :: Boolean, error :: Maybe String }

type PageModel = { loadable :: Int, ui :: PageUi }

type ModelExt r = { stageId :: Int, eventId :: Int | r }

init :: forall r. ModelExt r -> Aff PageModel
init model = pure
  { loadable: model.stageId
  , ui: { expandStageSelection: false, error: Nothing }
  }
"#,
        r#"module Test.Synthetic.PageUpdate where

import Prelude

import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, try)
import Effect.Class (liftEffect)
import Test.Synthetic.PageModel (PageModel, PageUi, init)

type Model = { stageId :: Int, eventId :: Int, firstStage :: Stage }

type Stage = { stage_id :: Int, reviews_open :: Boolean }

type UpdateResult model pageModel msg =
  { newState :: model
  , newPageState :: pageModel
  , effects :: Array (Aff (Maybe msg))
  }

data Msg
  = Nav
  | ToggleExpand
  | FailedRequest String PageModel
  | ToggleReviews
  | SetStageId Int
  | ReloadPage Int
  | Copy String

type UpdateResult_ = UpdateResult Model PageModel Msg

noEffects :: forall model pageModel msg. model -> pageModel -> UpdateResult model pageModel msg
noEffects st pm = { newState: st, newPageState: pm, effects: [] }

getStage :: Model -> Stage
getStage model = model.firstStage

adminUpdateStage :: Int -> Int -> Boolean -> Aff Int
adminUpdateStage _ _ _ = pure 0

copyToClipboard :: String -> Effect Unit
copyToClipboard _ = pure unit

update :: Msg -> Model -> PageModel -> UpdateResult_
update msg state pageModel@{ ui } =
  let
    selectedStage = getStage state
  in
    case msg of
      Nav ->
        noEffects state pageModel

      ToggleExpand ->
        setUi $ ui { expandStageSelection = not ui.expandStageSelection }

      FailedRequest errorString newPageModel@{ ui: newUi } ->
        noEffects state $ newPageModel { ui = newUi { error = Just errorString } }

      ToggleReviews ->
        updateStage (\stage -> stage { reviews_open = not stage.reviews_open })
          # effects
              [ handleError "Failed to update submission review status" <=< try
                  $ adminUpdateStage state.eventId selectedStage.stage_id
                  $ not selectedStage.reviews_open
              ]

      SetStageId stageId ->
        { newState: state { stageId = stageId }
        , newPageState: pageModel { ui = pageModel.ui { expandStageSelection = false } }
        , effects:
            [ do
                { loadable } <- init $ state { stageId = stageId }
                pure $ Just $ ReloadPage loadable
            ]
        }

      ReloadPage loaded ->
        { newState: state
        , newPageState: pageModel { loadable = loaded }
        , effects: []
        }

      Copy str ->
        { newState: state
        , newPageState: pageModel
        , effects: [ liftEffect (copyToClipboard str) *> pure Nothing ]
        }

  where

  updateStage :: (Stage -> Stage) -> UpdateResult_
  updateStage f = noEffects (state { firstStage = f state.firstStage }) pageModel

  setUi :: PageUi -> UpdateResult_
  setUi newUi = noEffects state (pageModel { ui = newUi })

  effects :: Array (Aff (Maybe Msg)) -> UpdateResult_ -> UpdateResult_
  effects effs result = result { effects = result.effects <> effs }

  handleError :: forall a b. String -> Either a b -> Aff (Maybe Msg)
  handleError errorMsg res =
    case lmap (const errorMsg) res of
      Left s -> pure $ Just $ FailedRequest s pageModel
      Right _ -> pure Nothing
"#,
    ]);
}
