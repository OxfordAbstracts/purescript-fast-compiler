module VISX.Util.SVG.Pattern
  ( pattern
  , PatternProps
  , circles
  , lines
  , PatternOrientation
  , horizontal
  , vertical
  , diagonal
  , diagonalLeftToRight
  ) where

import Prim.Row (class Union)
import React.Basic (JSX, ReactComponent)
import Unsafe.Coerce (unsafeCoerce)

-- Pattern
type PatternProps
  = ( id ∷ String
    , width ∷ Number
    , height ∷ Number
    , children ∷ Array JSX
    )
foreign import pattern ∷ ReactComponent { | PatternProps }

-- Circles
type CirclesProps
  = ( height ∷ Number
    , width ∷ Number
    , id ∷ String
    , background ∷ String
    , className ∷ String
    , complement ∷ Boolean -- Whether to fill in circles within the pattern gaps to increase pattern density.
    , fill ∷ String
    , radius ∷ Number -- Radius of the pattern circles (defaults to 2)
    , stroke ∷ String
    , strokeDasharray ∷ String
    , strokeWidth ∷ String
    )
circles ∷ ∀ attrs attrs_. Union attrs attrs_ CirclesProps ⇒ ReactComponent { height ∷ Number, width ∷ Number, id ∷ String | attrs }
circles = patternCirclesImpl
foreign import patternCirclesImpl ∷ ∀ r. ReactComponent { | r }

-- Lines
type LinesProps
  = ( height ∷ Number
    , width ∷ Number
    , id ∷ String
    , background ∷ String
    , className ∷ String
    , orientation ∷ Array PatternOrientation -- | Array of orientations to render (can mix multiple).
    , shapeRendering ∷ String --| Whether to fill in lines within the pattern gaps to increase pattern density.
    , stroke ∷ String
    , strokeDasharray ∷ String
    , strokeLinecap ∷ String
    , strokeWidth ∷ String
    )
lines ∷ ∀ attrs attrs_. Union attrs attrs_ LinesProps ⇒ ReactComponent { height ∷ Number, width ∷ Number, id ∷ String | attrs }
lines = patternLinesImpl
foreign import patternLinesImpl ∷ ∀ r. ReactComponent { | r }

-- Additional types
foreign import data PatternOrientation ∷ Type
horizontal ∷ PatternOrientation
horizontal = unsafeCoerce "horizontal"
vertical ∷ PatternOrientation
vertical = unsafeCoerce "vertical"
diagonal ∷ PatternOrientation
diagonal = unsafeCoerce "diagonal"
diagonalLeftToRight ∷ PatternOrientation
diagonalLeftToRight = unsafeCoerce "diagonalLeftToRight"
