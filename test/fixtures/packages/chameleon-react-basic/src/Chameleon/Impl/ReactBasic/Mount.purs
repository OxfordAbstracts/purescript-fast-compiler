module Chameleon.Impl.ReactBasic.Mount where

import Prelude

import Effect (Effect)
import React.Basic.DOM.Client as ReactBasicDOM
import React.Basic.Hooks (useEffectAlways, (/\))
import React.Basic.Hooks as React
import Chameleon.Impl.ReactBasic.Html (ReactHtml, defaultConfig, runReactHtml)
import Web.DOM as DOM

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

type UI html msg sta =
  { view :: sta -> html msg
  , update :: msg -> sta -> sta
  , init :: sta
  }

--------------------------------------------------------------------------------
-- React Component
--------------------------------------------------------------------------------

uiToReactComponent
  :: forall msg sta
   . { onStateChange :: sta -> Effect Unit }
  -> UI ReactHtml msg sta
  -> React.Component {} -- {setState :: sta -> Effect Unit}
uiToReactComponent { onStateChange } ui = do
  React.component "Root" \_props -> React.do

    state /\ setState <- React.useState $ ui.init

    useEffectAlways do
      onStateChange state
      pure $ pure unit

    let
      handler :: msg -> Effect Unit
      handler msg = do
        setState $ ui.update msg

    pure
      $ runReactHtml { handler } defaultConfig
      $ ui.view state

--------------------------------------------------------------------------------
-- Mounting
--------------------------------------------------------------------------------

mountAtId :: String -> React.Component {} -> Effect Unit
mountAtId id comp = do
  rootElem <- elemById id
  app <- comp
  reactRoot <- ReactBasicDOM.createRoot rootElem
  ReactBasicDOM.renderRoot reactRoot (app {})

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

foreign import elemById :: String -> Effect DOM.Element