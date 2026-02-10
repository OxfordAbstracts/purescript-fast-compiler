module MVC.Types
  ( UI
  , uiFromView
  ) where

import Prelude

type UI srf msg sta =
  { init :: sta
  , update :: msg -> sta -> sta
  , view :: sta -> srf msg
  }

uiFromView :: forall srf msg. srf msg -> UI srf msg Unit
uiFromView srf =
  { init: unit
  , update: \_ -> identity
  , view: \_ -> srf
  }