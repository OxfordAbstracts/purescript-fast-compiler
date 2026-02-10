module GoJS.Geometry.Size.Methods where

import Effect (Effect)
import GoJS.Geometry.Types (Size_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2)

copy_ :: Size_ -> Effect Size_
copy_ = callUnsafe0 "copy"

equalTo_ :: Number -> Number -> Size_ -> Effect Boolean
equalTo_ = callUnsafe2 "equalTo"

equals_ :: Size_ -> Size_ -> Effect Boolean
equals_ = callUnsafe1 "equals"

inflate_ :: Number -> Number -> Size_ -> Effect Size_
inflate_ = callUnsafe2 "inflate"

isReal_ :: Size_ -> Effect Boolean
isReal_ = callUnsafe0 "isReal"

set_ :: Size_ -> Size_ -> Effect Size_
set_ = callUnsafe1 "set"

setTo_ :: Number -> Number -> Size_ -> Effect Size_
setTo_ = callUnsafe2 "setTo"