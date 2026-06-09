module Test.Multi.ParallelInitA where

import Test.Multi.ParallelPrelude

-- Mirrors AdminDashboard.Pages.SoaaControls.Model:
--   type PageModel = { 10 modal fields :: Boolean }
--   init :: forall a. ModelExt a -> Aff PageModel

type ModelExt a = { eventId :: Int | a }

type PageModel =
  { statusModal :: Boolean
  , currencyModal :: Boolean
  , programFeatureModal :: Boolean
  , symposiumFeatureModal :: Boolean
  , registrationFeatureModal :: Boolean
  , confirmMakeFreeModal :: Boolean
  , show_presenter_emails_in_vc :: Boolean
  , has_new_auth :: Boolean
  , has_some_subs_attached_to_symposia :: Boolean
  , use_session_v2 :: Boolean
  }

init :: forall a. ModelExt a -> Aff PageModel
init _ = Aff
