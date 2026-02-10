module GoJS.Geometry.PathSegment.Properties where

import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (PathSegment_)
import GoJS.Unsafe (getUnsafe)

_centerX :: PathSegment_ -> Number
_centerX = getUnsafe [ "centerX" ]

_centerY :: PathSegment_ -> Number
_centerY = getUnsafe [ "centerY" ]

_endX :: PathSegment_ -> Number
_endX = getUnsafe [ "endX" ]

_endY :: PathSegment_ -> Number
_endY = getUnsafe [ "endY" ]

_isClockwiseArc :: PathSegment_ -> Boolean
_isClockwiseArc = getUnsafe [ "isClockwiseArc" ]

_isClosed :: PathSegment_ -> Boolean
_isClosed = getUnsafe [ "isClosed" ]

_isLargeArc :: PathSegment_ -> Boolean
_isLargeArc = getUnsafe [ "isLargeArc" ]

_point1X :: PathSegment_ -> Number
_point1X = getUnsafe [ "point1X" ]

_point1Y :: PathSegment_ -> Number
_point1Y = getUnsafe [ "point1Y" ]

_point2X :: PathSegment_ -> Number
_point2X = getUnsafe [ "point2X" ]

_point2Y :: PathSegment_ -> Number
_point2Y = getUnsafe [ "point2Y" ]

_radiusX :: PathSegment_ -> Number
_radiusX = getUnsafe [ "radiusX" ]

_radiusY :: PathSegment_ -> Number
_radiusY = getUnsafe [ "radiusY" ]

_startAngle :: PathSegment_ -> Number
_startAngle = getUnsafe [ "startAngle" ]

_sweepAngle :: PathSegment_ -> Number
_sweepAngle = getUnsafe [ "sweepAngle" ]

_type :: PathSegment_ -> EnumValue_
_type = getUnsafe [ "type" ]

_xAxisRotation :: PathSegment_ -> Number
_xAxisRotation = getUnsafe [ "xAxisRotation" ]