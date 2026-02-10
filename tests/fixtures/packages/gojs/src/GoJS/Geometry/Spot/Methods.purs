module GoJS.Geometry.Spot.Methods where

import Effect (Effect)
import GoJS.Geometry.Types (Spot_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe4)

copy_ :: Spot_ -> Effect Spot_
copy_ = callUnsafe0 "copy"

equals_ :: Spot_ -> Spot_ -> Effect Boolean
equals_ = callUnsafe1 "equals"

includesSide_ :: Spot_ -> Spot_ -> Effect Boolean
includesSide_ = callUnsafe1 "includesSide"

isDefault_ :: Spot_ -> Effect Boolean
isDefault_ = callUnsafe0 "isDefault"

isNoSpot_ :: Spot_ -> Effect Boolean
isNoSpot_ = callUnsafe0 "isNoSpot"

isNone_ :: Spot_ -> Effect Boolean
isNone_ = callUnsafe0 "isNone"

isSide_ :: Spot_ -> Effect Boolean
isSide_ = callUnsafe0 "isSide"

isSpot_ :: Spot_ -> Effect Boolean
isSpot_ = callUnsafe0 "isSpot"

opposite_ :: Spot_ -> Effect Spot_
opposite_ = callUnsafe0 "opposite"

set_ :: Spot_ -> Spot_ -> Effect Spot_
set_ = callUnsafe1 "set"

setTo_ :: Number -> Number -> Number -> Number -> Spot_ -> Effect Spot_
setTo_ = callUnsafe4 "setTo"