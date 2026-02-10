module VISX.Interaction.Zoom where

import Prelude
import Effect (Effect)
import Effect.Uncurried (EffectFn1)
import Prim.Row (class Union)
import React.Basic (JSX)
import React.Basic.Events (EventHandler)
import React.Basic.Hooks (ReactComponent)

foreign import zoomImpl ∷ ∀ r. ReactComponent { | r }

type ZoomProps =
  ( width ∷ Number
  , height ∷ Number
  , scaleXMin ∷ Number
  , scaleXMax ∷ Number
  , scaleYMin ∷ Number
  , scaleYMax ∷ Number
  , transformMatrix ∷ TransformMatrix
  , children ∷ ZoomInput -> JSX
  )

type ZoomInput =
  { isDragging ∷ Boolean
  , toString ∷ Effect String
  , toStringInvert ∷ Effect String
  , dragStart ∷ EventHandler
  , dragMove ∷ EventHandler
  , dragEnd ∷ EventHandler
  , scale ∷ EffectFn1 { scaleX ∷ Number, scaleY ∷ Number, point ∷ { x ∷ Number, y ∷ Number } } Unit
  }

type TransformMatrix =
  { scaleX ∷ Number
  , scaleY ∷ Number
  , translateX ∷ Number
  , translateY ∷ Number
  , skewX ∷ Number
  , skewY ∷ Number
  }

zoom ∷ ∀ attrs attrs_. Union attrs attrs_ ZoomProps => ReactComponent { | attrs }
zoom = zoomImpl
