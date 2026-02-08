module GoJS.GraphObject.Shape.Properties where

import Prelude

import Data.Function.Uncurried (Fn2)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Geometry_, Rect_, Spot_)
import GoJS.GraphObject.Types (class IsGraphObject, Shape_)
import GoJS.Unsafe (getUnsafe)

_figure :: Shape_ -> String
_figure = getUnsafe [ "figure" ]

_fill :: Shape_ -> String
_fill = getUnsafe [ "fill" ]

_fromArrow :: Shape_ -> String
_fromArrow = getUnsafe [ "fromArrow" ]

_geometry :: Shape_ -> Geometry_
_geometry = getUnsafe [ "geometry" ]

_geometryStretch :: Shape_ -> EnumValue_
_geometryStretch = getUnsafe [ "geometryStretch" ]

_geometryString :: Shape_ -> String
_geometryString = getUnsafe [ "geometryString" ]

_graduatedEnd :: Shape_ -> Number
_graduatedEnd = getUnsafe [ "graduatedEnd" ]

_graduatedSkip :: Shape_ -> Maybe (Fn2 Number Shape_ Boolean)
_graduatedSkip = toMaybe <<< getUnsafe [ "graduatedSkip" ]

_graduatedStart :: Shape_ -> Number
_graduatedStart = getUnsafe [ "graduatedStart" ]

_interval :: Shape_ -> Number
_interval = getUnsafe [ "interval" ]

_isGeometryPositioned :: Shape_ -> Boolean
_isGeometryPositioned = getUnsafe [ "isGeometryPositioned" ]

_naturalBounds :: Shape_ -> Rect_
_naturalBounds = getUnsafe [ "naturalBounds" ]

_parameter1 :: Shape_ -> Number
_parameter1 = getUnsafe [ "parameter1" ]

_parameter2 :: Shape_ -> Number
_parameter2 = getUnsafe [ "parameter2" ]

_pathPattern :: forall @g. IsGraphObject g => Shape_ -> Maybe g
_pathPattern = toMaybe <<< getUnsafe [ "pathPattern" ]

_spot1 :: Shape_ -> Spot_
_spot1 = getUnsafe [ "spot1" ]

_spot2 :: Shape_ -> Spot_
_spot2 = getUnsafe [ "spot2" ]

_stroke :: Shape_ -> String
_stroke = getUnsafe [ "stroke" ]

_strokeCap :: Shape_ -> String
_strokeCap = getUnsafe [ "strokeCap" ]

_strokeDashArray :: Shape_ -> Array Number
_strokeDashArray = getUnsafe [ "strokeDashArray" ]

_strokeDashOffset :: Shape_ -> Number
_strokeDashOffset = getUnsafe [ "strokeDashOffset" ]

_strokeJoin :: Shape_ -> String
_strokeJoin = getUnsafe [ "strokeJoin" ]

_strokeMiterLimit :: Shape_ -> Number
_strokeMiterLimit = getUnsafe [ "strokeMiterLimit" ]

_strokeWidth :: Shape_ -> Number
_strokeWidth = getUnsafe [ "strokeWidth" ]

_toArrow :: Shape_ -> String
_toArrow = getUnsafe [ "toArrow" ]
