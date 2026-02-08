module GoJS.Geometry.Margin.Methods where

import Effect (Effect)
import GoJS.Geometry.Types (Margin_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe4)

copy_ :: Margin_ -> Effect Margin_
copy_ = callUnsafe0 "copy"

equalTo_ :: Number -> Number -> Number -> Number -> Margin_ -> Effect Boolean
equalTo_ = callUnsafe4 "equalTo"

equals_ :: Margin_ -> Margin_ -> Effect Boolean
equals_ = callUnsafe1 "equals"

isReal_ :: Margin_ -> Effect Boolean
isReal_ = callUnsafe0 "isReal"

set_ :: Margin_ -> Margin_ -> Effect Margin_
set_ = callUnsafe1 "set"

setTo_ :: Number -> Number -> Number -> Number -> Margin_ -> Effect Margin_
setTo_ = callUnsafe4 "setTo"