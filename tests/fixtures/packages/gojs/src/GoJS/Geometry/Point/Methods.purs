module GoJS.Geometry.Point.Methods where

import Effect (Effect)
import GoJS.Geometry.Types (Point_, Rect_, Spot_)
import GoJS.Unsafe

add_ :: Point_ -> Point_ -> Effect Point_
add_ = callUnsafe1 "add"

compareWithLineSegment_ :: Point_ -> Point_ -> Point_ -> Effect Number
compareWithLineSegment_ = callUnsafe2 "compareWithLineSegment"

equals_ :: Point_ -> Point_ -> Effect Boolean
equals_ = callUnsafe1 "equals"

equalTo_ :: Point_ -> Point_ -> Effect Boolean
equalTo_ = callUnsafe1 "equalTo"

isReal_ :: Point_ -> Effect Boolean
isReal_ = callUnsafe0 "isReal"

normalize_ :: Point_ -> Effect Point_
normalize_ = callUnsafe0 "normalize"

offset_ :: Number -> Number -> Point_ -> Effect Point_
offset_ = callUnsafe2 "offset"

projectOntoLineSegment_ :: Point_ -> Point_ -> Point_ -> Effect Point_
projectOntoLineSegment_ = callUnsafe2 "projectOntoLineSegment"

projectOntoLineSegmentPoint_ :: Point_ -> Point_ -> Point_ -> Point_ -> Effect Point_
projectOntoLineSegmentPoint_ = callUnsafe3 "projectOntoLineSegmentPoint"

rotate_ :: Number -> Point_ -> Effect Point_
rotate_ = callUnsafe1 "rotate"

scale_ :: Number -> Number -> Point_ -> Effect Point_
scale_ = callUnsafe2 "scale"

set_ :: Number -> Number -> Point_ -> Effect Point_
set_ = callUnsafe2 "set"

setRectSpot_ :: Rect_ -> Spot_ -> Point_ -> Effect Point_
setRectSpot_ = callUnsafe2 "setRectSpot"

setSpot_ :: Spot_ -> Point_ -> Effect Point_
setSpot_ = callUnsafe1 "setSpot"

setTo_ :: Point_ -> Point_ -> Effect Point_
setTo_ = callUnsafe1 "setTo"

snapToGrid_ :: Point_ -> Number -> Number -> Effect Point_
snapToGrid_ = callUnsafe2 "snapToGrid"

snapToGridPoint_ :: Point_ -> Number -> Number -> Point_ -> Effect Point_
snapToGridPoint_ = callUnsafe3 "snapToGridPoint"

subtract_ :: Point_ -> Point_ -> Effect Point_
subtract_ = callUnsafe1 "subtract"
