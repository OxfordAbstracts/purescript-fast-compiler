-- [TODO] Specify props
module VISX.Util.SVG.Gradient
  ( LinearGradientProps
  , LinearGradientRequiredProps
  , gradientDarkgreenGreen
  , gradientLightgreenGreen
  , gradientOrangeRed
  , gradientPinkBlue
  , gradientPinkRed
  , gradientPurpleOrange
  , gradientPurpleRed
  , gradientPurpleTeal
  , gradientSteelPurple
  , gradientTealBlue
  , linearGradient
  , radialGradient
  ) where

import Prim.Row (class Union)
import React.Basic (ReactComponent)

type LinearGradientRequiredProps r
  = ( id ∷ String, from ∷ String, to ∷ String | r )
type LinearGradientProps
  = LinearGradientRequiredProps ( rotate ∷ String )

foreign import linearGradientImpl ∷ ∀ a. ReactComponent a
linearGradient ∷ ∀ attrs attrs_. Union attrs attrs_ LinearGradientProps ⇒ ReactComponent { | LinearGradientRequiredProps attrs }
linearGradient = linearGradientImpl

foreign import radialGradient ∷ ∀ a. ReactComponent { id ∷ String, rotate ∷ String, from ∷ String, to ∷ String | a }
foreign import gradientDarkgreenGreen ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientLightgreenGreen ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientOrangeRed ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientPinkBlue ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientPinkRed ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientPurpleOrange ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientPurpleRed ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientPurpleTeal ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientSteelPurple ∷ ∀ a. ReactComponent { id ∷ String | a }
foreign import gradientTealBlue ∷ ∀ a. ReactComponent { id ∷ String | a }
