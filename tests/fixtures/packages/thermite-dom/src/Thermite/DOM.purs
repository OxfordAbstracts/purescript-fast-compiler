module Thermite.DOM where

import Thermite (WithChildren, Spec, createClass)
import Prelude (Unit, bind, (>>=), (<<<))
import React (class ReactPropFields, ReactClass, ReactElement, createElement)
import ReactDOM (render)
import Effect (Effect)
import Data.Traversable (traverse_)
import Web.HTML (window) as Web
import Web.HTML.HTMLDocument (body) as Web
import Web.HTML.HTMLElement (toElement) as Web
import Web.HTML.Window (document) as Web



-- | A default implementation of `main` which renders a component to the
-- | document body.
defaultMain
  :: forall state props given action
   . ReactPropFields props given
  => Spec { | state } (WithChildren props) action
  -> (WithChildren props -> { | state }) -- ^ Initial State
  -> String -- ^ Component Name
  -> { | given } -- ^ Read-Only Props
  -> Effect Unit
defaultMain spec initialState name props = do
  let component :: ReactClass (WithChildren props)
      component = createClass spec initialState name
      element :: ReactElement
      element = createElement component props []
  mContainer <- Web.window >>= Web.document >>= Web.body
  traverse_ (render element <<< Web.toElement) mContainer
