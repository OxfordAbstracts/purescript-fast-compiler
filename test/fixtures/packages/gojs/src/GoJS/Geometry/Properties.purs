module GoJS.Geometry.Properties where


import GoJS.Geometry.Types (Geometry_, PathFigure_, Rect_, Spot_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Unsafe (getUnsafe)
import GoJS.Collection (List_)

-- Read-only
_bounds :: Geometry_ -> Rect_
_bounds = getUnsafe [ "bounds" ]

_defaultStretch :: Geometry_ -> EnumValue_
_defaultStretch = getUnsafe [ "defaultStretch" ]

_endX :: Geometry_ -> Number
_endX = getUnsafe [ "endX" ]

_endY :: Geometry_ -> Number
_endY = getUnsafe [ "endY" ]

_figures :: Geometry_ -> List_ PathFigure_
_figures = getUnsafe [ "figures" ]

_spot1 :: Geometry_ -> Spot_
_spot1 = getUnsafe [ "spot1" ]

_spot2 :: Geometry_ -> Spot_
_spot2 = getUnsafe [ "spot2" ]

_startX :: Geometry_ -> Number
_startX = getUnsafe [ "startX" ]

_startY :: Geometry_ -> Number
_startY = getUnsafe [ "startY" ]

_type :: Geometry_ -> EnumValue_
_type = getUnsafe [ "type" ]