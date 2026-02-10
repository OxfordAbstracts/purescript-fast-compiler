module XTerm.Decoration.OverviewRuler
  ( OverviewRuler
  , setColor
  , setPosition
  ) where

import Color (Color, toHexString)
import Data.Unit (Unit)
import Effect (Effect)
import XTerm.Decoration.Options (Position, positionString)

data OverviewRuler

foreign import _setColor :: OverviewRuler -> String -> Effect Unit
foreign import _setPosition :: OverviewRuler -> String -> Effect Unit

setColor :: OverviewRuler -> Color -> Effect Unit
setColor o c = _setColor o (toHexString c)

setPosition :: OverviewRuler -> Position -> Effect Unit
setPosition o p = _setPosition o (positionString p)
