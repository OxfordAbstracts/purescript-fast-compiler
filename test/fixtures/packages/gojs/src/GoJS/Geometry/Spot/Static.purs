module GoJS.Geometry.Spot.Static where

import GoJS.Geometry.Types (Spot_)
import GoJS.Unsafe (callStaticPure1)

parse_ :: String -> Spot_
parse_ = callStaticPure1 "Spot" "parse"

stringify_ :: Spot_ -> String
stringify_ = callStaticPure1 "Spot" "stringify"