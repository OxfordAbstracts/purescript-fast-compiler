module GoJS.Geometry.Rect.Methods where

import Effect (Effect)
import GoJS.Geometry.Types (Margin_, Point_, Rect_, Size_, Spot_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2, callUnsafe4)

addMargin_ :: Margin_ -> Rect_ -> Effect Rect_
addMargin_ = callUnsafe1 "addMargin"

-- Optional parameters: w: number, h: number
contains_ :: Number -> Number -> Number -> Number -> Rect_ -> Effect Boolean
contains_ = callUnsafe4 "contains"

containsPoint_ :: Number -> Number -> Rect_ -> Effect Boolean
containsPoint_ = callUnsafe2 "containsPoint"

containsRect_ :: Number -> Number -> Number -> Number -> Rect_ -> Effect Boolean
containsRect_ = callUnsafe4 "containsRect"

copy_ :: Rect_ -> Effect Rect_
copy_ = callUnsafe0 "copy"

equalTo_ :: Rect_ -> Rect_ -> Effect Boolean
equalTo_ = callUnsafe1 "equalTo"

equals_ :: Rect_ -> Rect_ -> Effect Boolean
equals_ = callUnsafe1 "equals"

grow_ :: Number -> Number -> Rect_ -> Effect Rect_
grow_ = callUnsafe2 "grow"

inflate_ :: Number -> Number -> Rect_ -> Effect Rect_
inflate_ = callUnsafe2 "inflate"

intersect_ :: Number -> Number -> Number -> Number -> Rect_ -> Effect Rect_
intersect_ = callUnsafe4 "intersect"

intersectRect_ :: Rect_ -> Rect_ -> Effect Rect_
intersectRect_ = callUnsafe1 "intersectRect"

intersects_ :: Number -> Number -> Number -> Number -> Rect_ -> Effect Boolean
intersects_ = callUnsafe4 "intersects"

intersectsRect_ :: Rect_ -> Rect_ -> Effect Boolean
intersectsRect_ = callUnsafe1 "intersectsRect"

isEmpty_ :: Rect_ -> Effect Boolean
isEmpty_ = callUnsafe0 "isEmpty"

isReal_ :: Rect_ -> Effect Boolean
isReal_ = callUnsafe0 "isReal"

offset_ :: Number -> Number -> Rect_ -> Effect Rect_
offset_ = callUnsafe2 "offset"

set_ :: Number -> Number -> Number -> Number -> Rect_ -> Effect Rect_
set_ = callUnsafe4 "set"

setPoint_ :: Point_ -> Rect_ -> Effect Rect_
setPoint_ = callUnsafe1 "setPoint"

setSize_ :: Size_ -> Rect_ -> Effect Rect_
setSize_ = callUnsafe1 "setSize"

setSpot_ :: Spot_ -> Rect_ -> Effect Rect_
setSpot_ = callUnsafe1 "setSpot"

setTo_ :: Rect_ -> Rect_ -> Effect Rect_
setTo_ = callUnsafe1 "setTo"

subtractMargin_ :: Margin_ -> Rect_ -> Effect Rect_
subtractMargin_ = callUnsafe1 "subtractMargin"

-- Optional arguments: w: number, h: number
union_ :: Number -> Number -> Number -> Number -> Rect_ -> Effect Rect_
union_ = callUnsafe4 "union"

unionPoint_ :: Point_ -> Rect_ -> Effect Rect_
unionPoint_ = callUnsafe1 "unionPoint"

unionRect_ :: Rect_ -> Rect_ -> Effect Rect_
unionRect_ = callUnsafe1 "unionRect"