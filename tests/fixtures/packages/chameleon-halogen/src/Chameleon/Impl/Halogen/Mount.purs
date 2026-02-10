module Chameleon.Impl.Halogen.Mount where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Halogen (liftEffect)
import Halogen as H
import Halogen as Halogen
import Halogen.VDom.Driver as HalogenVDOM
import Chameleon.Impl.Halogen.Html (HalogenHtml, runHalogenHtml)
import Web.HTML (HTMLElement)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

type UI html msg sta =
  { view :: sta -> html msg
  , update :: msg -> sta -> sta
  , init :: sta
  }

--------------------------------------------------------------------------------
-- Halogen Component
--------------------------------------------------------------------------------

uiToHalogenComponent :: forall q i o msg sta. { onStateChange :: sta -> Effect Unit } -> UI HalogenHtml msg sta -> Halogen.Component q i o Aff
uiToHalogenComponent { onStateChange } ui =
  H.mkComponent
    { initialState
    , render
    , eval: H.mkEval $ H.defaultEval { handleAction = handleAction }
    }
  where
  initialState _ = ui.init

  render state =
    runHalogenHtml $ ui.view state

  handleAction msg = do
    state <- H.modify $ ui.update msg
    liftEffect $ onStateChange state

--------------------------------------------------------------------------------
-- Mounting
--------------------------------------------------------------------------------

uiMountAtId :: forall q o. String -> Halogen.Component q Unit o Aff -> Effect Unit
uiMountAtId id comp = launchAff_ do
  rootElem <- liftEffect $ elemById id
  _ <- HalogenVDOM.runUI comp unit rootElem
  pure unit

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

foreign import elemById :: String -> Effect HTMLElement