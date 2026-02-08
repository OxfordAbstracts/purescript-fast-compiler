module GoJS.Layout.CircularLayout.Properties where

import Data.Function.Uncurried (Fn2)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Point_)
import GoJS.Layout.Types (CircularLayout_, CircularVertex_)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_actualCenter :: CircularLayout_ -> Point_
_actualCenter = getUnsafe [ "actualCenter" ]

-- Read-only
_actualSpacing :: CircularLayout_ -> Number
_actualSpacing = getUnsafe [ "actualSpacing" ]

-- Read-only
_actualXRadius :: CircularLayout_ -> Number
_actualXRadius = getUnsafe [ "actualXRadius" ]

-- Read-only
_actualYRadius :: CircularLayout_ -> Number
_actualYRadius = getUnsafe [ "actualYRadius" ]

_aspectRatio :: CircularLayout_ -> Number
_aspectRatio = getUnsafe [ "aspectRatio" ]

_comparer :: CircularLayout_ -> Fn2 CircularVertex_ CircularVertex_ Number
_comparer = getUnsafe [ "comparer" ]

_direction :: CircularLayout_ -> EnumValue_
_direction = getUnsafe [ "direction" ]

_directionCircular :: CircularLayout_ -> EnumValue_
_directionCircular = getUnsafe [ "directionCircular" ]

_nodeDiameterFormula :: CircularLayout_ -> EnumValue_
_nodeDiameterFormula = getUnsafe [ "nodeDiameterFormula" ]

_radius :: CircularLayout_ -> Number
_radius = getUnsafe [ "radius" ]

_sorting :: CircularLayout_ -> EnumValue_
_sorting = getUnsafe [ "sorting" ]

_spacing :: CircularLayout_ -> Number
_spacing = getUnsafe [ "spacing" ]

_startAngle :: CircularLayout_ -> Number
_startAngle = getUnsafe [ "startAngle" ]

_sweepAngle :: CircularLayout_ -> Number
_sweepAngle = getUnsafe [ "sweepAngle" ]