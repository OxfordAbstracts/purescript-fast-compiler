module GoJS.Geometry.Size.Static where

import GoJS.Geometry.Types (Size_)
import GoJS.Unsafe (callStaticPure1)

parse_ :: String -> Size_
parse_ = callStaticPure1 "Size" "parse"

stringify_ :: Size_ -> String
stringify_ = callStaticPure1 "Size" "stringify"