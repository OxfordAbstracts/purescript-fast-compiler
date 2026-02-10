module GoJS.GraphObject.Panel.Part.Link.Methods where

import Prelude

import Effect (Effect)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Geometry_, Point_, Spot_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, Link_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2, callUnsafe4, callUnsafe6, callUnsafe8)

addPoint_ :: Point_ -> Link_ -> Effect Unit
addPoint_ = callUnsafe1 "addPoint"

canRelinkFrom_ :: Link_ -> Effect Boolean
canRelinkFrom_ = callUnsafe0 "canRelinkFrom"

canRelinkTo_ :: Link_ -> Effect Boolean
canRelinkTo_ = callUnsafe0 "canRelinkTo"

clearPoints_ :: Link_ -> Effect Unit
clearPoints_ = callUnsafe0 "clearPoints"

computeAdjusting_ :: Link_ -> Effect EnumValue_
computeAdjusting_ = callUnsafe0 "computeAdjusting"

computeCurve_ :: Link_ -> Effect EnumValue_
computeCurve_ = callUnsafe0 "computeCurve"

computeCurviness_ :: Link_ -> Effect Number
computeCurviness_ = callUnsafe0 "computeCurviness"

computeEndSegmentLength_ :: forall n g. IsNode n => IsGraphObject g => n -> g -> Spot_ -> Boolean -> Link_ -> Effect Number
computeEndSegmentLength_ = callUnsafe4 "computeEndSegmentLength"

computeOtherPoint_ :: forall n g. IsNode n => IsGraphObject g => n -> g -> Link_ -> Effect Point_
computeOtherPoint_ = callUnsafe2 "computeOtherPoint"

computePoints_ :: Link_ -> Effect Boolean
computePoints_ = callUnsafe0 "computePoints"

computeSpacing_ :: Link_ -> Effect Number
computeSpacing_ = callUnsafe0 "computeSpacing"

-- Optional parameters: port: GraphObject
computeSpot_ :: forall g. IsGraphObject g => Boolean -> g -> Link_ -> Effect Spot_
computeSpot_ = callUnsafe2 "computeSpot"

computeThickness_ :: Link_ -> Effect Number
computeThickness_ = callUnsafe0 "computeThickness"

findClosestSegment_ :: Point_ -> Link_ -> Effect Number
findClosestSegment_ = callUnsafe1 "findClosestSegment"

getLinkDirection_ :: forall n1 g1 n2 g2. IsNode n1 => IsGraphObject g1 => IsNode n2 => IsGraphObject g2 => n1 -> g1 -> Point_ -> Spot_ -> Boolean -> Boolean -> n2 -> g2 -> Link_ -> Effect Number
getLinkDirection_ = callUnsafe8 "getLinkDirection"

-- Optional parameters: point: Point
getLinkPoint_ :: forall n g. IsNode n => IsGraphObject g => n -> g -> Spot_ -> Boolean -> Boolean -> n -> g -> Point_ -> Link_ -> Effect Point_
getLinkPoint_ = callUnsafe8 "getLinkPoint"

-- Optional parameters: point: Point
getLinkPointFromPoint_ :: forall n g. IsNode n => IsGraphObject g => n -> g -> Point_ -> Point_ -> Boolean -> Point_ -> Link_ -> Effect Point_
getLinkPointFromPoint_ = callUnsafe6 "getLinkPointFromPoint"

getOtherNode_ :: forall n1 @n2. IsNode n1 => IsNode n2 => n1 -> Link_ -> Effect n2
getOtherNode_ = callUnsafe1 "getOtherNode"

getOtherPort_ :: forall g1 @g2. IsGraphObject g1 => IsGraphObject g2 => g1 -> Link_ -> Effect g2
getOtherPort_ = callUnsafe1 "getOtherPort"

getPoint_ :: Number -> Link_ -> Effect Point_
getPoint_ = callUnsafe1 "getPoint"

hasCurviness_ :: Link_ -> Effect Boolean
hasCurviness_ = callUnsafe0 "hasCurviness"

insertPoint_ :: Number -> Point_ -> Link_ -> Effect Unit
insertPoint_ = callUnsafe2 "insertPoint"

invalidateRoute_ :: Link_ -> Effect Unit
invalidateRoute_ = callUnsafe0 "invalidateRoute"

makeGeometry_ :: Link_ -> Effect Geometry_
makeGeometry_ = callUnsafe0 "makeGeometry"

-- Optional parameters: useLocation: boolean
move_ :: Point_ -> Boolean -> Link_ -> Effect Unit
move_ = callUnsafe2 "move"

removePoint_ :: Number -> Link_ -> Effect Unit
removePoint_ = callUnsafe1 "removePoint"

setPoint_ :: Number -> Point_ -> Link_ -> Effect Unit
setPoint_ = callUnsafe2 "setPoint"

updateRoute_ :: Link_ -> Effect Unit
updateRoute_ = callUnsafe0 "updateRoute"
