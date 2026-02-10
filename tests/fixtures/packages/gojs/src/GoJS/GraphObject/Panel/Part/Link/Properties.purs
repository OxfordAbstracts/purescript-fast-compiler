module GoJS.GraphObject.Panel.Part.Link.Properties where


import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn3)
import GoJS.Collection (Iterator_, List_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Geometry_, Point_, Rect_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, Link_, Node_, Shape_)
import GoJS.Unsafe (getUnsafe)

_adjusting :: Link_ -> EnumValue_
_adjusting = getUnsafe [ "adjusting" ]

_corner :: Link_ -> Number
_corner = getUnsafe [ "corner" ]

_curve :: Link_ -> EnumValue_
_curve = getUnsafe [ "curve" ]

_curviness :: Link_ -> Number
_curviness = getUnsafe [ "curviness" ]

_fromNode :: forall @n. IsNode n => Link_ -> Maybe n
_fromNode = toMaybe <<< getUnsafe [ "fromNode" ]

-- Read-only
_fromPort :: forall @g. IsGraphObject g => Link_ -> Maybe g
_fromPort = toMaybe <<< getUnsafe [ "fromPort" ]

_fromPortChanged :: forall g1 g2. IsGraphObject g1 => IsGraphObject g2 => Link_ -> Maybe (EffectFn3 Link_ g1 g2 Unit)
_fromPortChanged = toMaybe <<< getUnsafe [ "fromPortChanged" ]

_fromPortId :: Link_ -> String
_fromPortId = getUnsafe [ "fromPortId" ]

-- Read-only
_geometry :: Link_ -> Geometry_
_geometry = getUnsafe [ "geometry" ]

-- Read-only
_isLabeledLink :: Link_ -> Boolean
_isLabeledLink = getUnsafe [ "isLabeledLink" ]

-- Read-only
_isOrthogonal :: Link_ -> Boolean
_isOrthogonal = getUnsafe [ "isOrthogonal" ]

_isTreeLink :: Link_ -> Boolean
_isTreeLink = getUnsafe [ "isTreeLink" ]

-- Read-only
_labelNodes :: Link_ -> Iterator_ Node_
_labelNodes = getUnsafe [ "labelNodes" ]

-- Read-only
_midAngle :: Link_ -> Number
_midAngle = getUnsafe [ "midAngle" ]

-- Read-only
_midPoint :: Link_ -> Point_
_midPoint = getUnsafe [ "midPoint" ]

-- Read-only
_path :: Link_ -> Shape_
_path = getUnsafe [ "path" ]

_points :: Link_ -> List_ Point_
_points = getUnsafe [ "points" ]

-- Read-only
_pointsCount :: Link_ -> Number
_pointsCount = getUnsafe [ "pointsCount" ]

_relinkableFrom :: Link_ -> Boolean
_relinkableFrom = getUnsafe [ "relinkableFrom" ]

_relinkableTo :: Link_ -> Boolean
_relinkableTo = getUnsafe [ "relinkableTo" ]

_resegmentable :: Link_ -> Boolean
_resegmentable = getUnsafe [ "resegmentable" ]

-- Read-only
_routeBounds :: Link_ -> Rect_
_routeBounds = getUnsafe [ "routeBounds" ]

_routing :: Link_ -> EnumValue_
_routing = getUnsafe [ "routing" ]

_smoothness :: Link_ -> Number
_smoothness = getUnsafe [ "smoothness" ]

_toNode :: forall @n. IsNode n => Link_ -> Maybe n
_toNode = toMaybe <<< getUnsafe [ "toNode" ]

-- Read-only
_toPort :: forall @g. IsGraphObject g => Link_ -> Maybe g
_toPort = toMaybe <<< getUnsafe [ "toPort" ]

_toPortChanged :: forall g1 g2. IsGraphObject g1 => IsGraphObject g2 => Link_ -> Maybe (EffectFn3 Link_ g1 g2 Unit)
_toPortChanged = toMaybe <<< getUnsafe [ "toPortChanged" ]

_toPortId :: Link_ -> String
_toPortId = getUnsafe [ "toPortId" ]
