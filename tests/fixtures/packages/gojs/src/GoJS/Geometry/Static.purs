module GoJS.Geometry.Static where

import GoJS.Geometry.Types (Geometry_)
import GoJS.Unsafe (callStaticPure1)

fillPath_ :: String -> String
fillPath_ = callStaticPure1 "Geometry" "fillPath"

-- Optional parameters excluded: filled: boolean
parse_ :: String -> Geometry_
parse_ = callStaticPure1 "Geometry" "parse"

stringify_ :: Geometry_ -> String
stringify_ = callStaticPure1 "Geometry" "stringify"
