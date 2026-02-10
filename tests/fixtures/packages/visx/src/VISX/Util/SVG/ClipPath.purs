module VISX.Util.SVG.ClipPath where

import Prelude
import Prim.Row (class Union)
import React.Basic.Hooks (ReactComponent)

foreign import rectClipPathImpl ∷ ∀ r. ReactComponent { | r }

type RectClipPathProps =
  ()

rectClipPath ∷ ∀ attrs attrs_. Union attrs attrs_ RectClipPathProps => ReactComponent { | attrs }
rectClipPath = rectClipPathImpl

foreign import circleClipPathImpl ∷ ∀ r. ReactComponent { | r }

type CircleClipPathProps =
  ()

circleClipPath ∷ ∀ attrs attrs_. Union attrs attrs_ CircleClipPathProps => ReactComponent { | attrs }
circleClipPath = circleClipPathImpl
