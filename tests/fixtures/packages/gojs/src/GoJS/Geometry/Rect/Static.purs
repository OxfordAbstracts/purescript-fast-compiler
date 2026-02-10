module GoJS.Geometry.Rect.Static where

import GoJS.Geometry.Types (Rect_)
import GoJS.Unsafe (callStaticPure1, callStaticPure7)

-- Optional arguments: w: number, h: number
contains_ :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Boolean
contains_ = callStaticPure7 "Rect" "contains"

intersects_ :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Boolean
intersects_ = callStaticPure7 "Rect" "intersects"

intersectsLineSegment_ :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Boolean
intersectsLineSegment_ = callStaticPure7 "Rect" "intersectsLineSegment"

parse_ :: String -> Rect_
parse_ = callStaticPure1 "Rect" "parse"

stringify_ :: Rect_ -> String
stringify_ = callStaticPure1 "Rect" "stringify"