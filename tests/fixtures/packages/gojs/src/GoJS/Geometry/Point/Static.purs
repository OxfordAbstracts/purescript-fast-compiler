module GoJS.Geometry.Point.Static where

import GoJS.Geometry.Types (Point_)
import GoJS.Unsafe (callStaticPure1, callStaticPure3, callStaticPure4, callStaticPure5, callStaticPure7)

-- Pure static methods
direction_ :: Number -> Number -> Number -> Number ->  Number
direction_ = callStaticPure4 "Point" "direction"

distanceLineSegmentSquared_ :: Number -> Number -> Number -> Number -> Number -> Number ->  Number
distanceLineSegmentSquared_ = callStaticPure5 "Point" "distanceLineSegmentSquared"

distanceSquared_ :: Number -> Number -> Number -> Number ->  Number
distanceSquared_ = callStaticPure3 "Point" "distanceSquared"

intersectingLineSegments_ :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number ->  Boolean
intersectingLineSegments_ = callStaticPure7 "Point" "intersectingLineSegments"

parse_ :: String -> Point_
parse_ = callStaticPure1 "Point" "parse"

stringify_ :: Point_ -> String
stringify_ = callStaticPure1 "Point" "stringify"