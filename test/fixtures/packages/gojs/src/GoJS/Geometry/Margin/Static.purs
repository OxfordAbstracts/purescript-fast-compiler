module GoJS.Geometry.Margin.Static where

import GoJS.Geometry.Types (Margin_)
import GoJS.Unsafe (callStaticPure1)

parse_ :: String -> Margin_
parse_ = callStaticPure1 "Margin" "parse"

stringify_ :: Margin_ -> String
stringify_ = callStaticPure1 "Margin" "stringify"