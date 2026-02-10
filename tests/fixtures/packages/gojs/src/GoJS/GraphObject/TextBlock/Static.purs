module GoJS.GraphObject.TextBlock.Static where

import Prelude

import Data.Function.Uncurried (Fn2)
import Effect (Effect)
import GoJS.GraphObject.Types (TextBlock_)
import GoJS.Unsafe (callStatic0, callStatic1)

-- Baseline and Underline behaviors are normally null, but I believe they
-- still are treated as functions.
getBaseline_ :: Effect (Fn2 TextBlock_ Number Number)
getBaseline_ = callStatic0 "TextBlock" "getBaseline"

getUnderline_ :: Effect (Fn2 TextBlock_ Number Number)
getUnderline_ = callStatic0 "TextBlock" "getUnderline"

setBaseline_ :: (Fn2 TextBlock_ Number Number) -> Effect Unit
setBaseline_ = callStatic1 "TextBlock" "setBaseline"

setUnderline_ :: (Fn2 TextBlock_ Number Number) -> Effect Unit
setUnderline_ = callStatic1 "TextBlock" "setUnderline"