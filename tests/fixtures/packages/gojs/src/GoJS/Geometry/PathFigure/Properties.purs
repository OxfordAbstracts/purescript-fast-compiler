module GoJS.Geometry.PathFigure.Properties where

import GoJS.Collection (List_)
import GoJS.Geometry.Types (PathFigure_, PathSegment_)
import GoJS.Unsafe (getUnsafe)

_isEvenOdd :: PathFigure_ -> Boolean
_isEvenOdd = getUnsafe ["isEvenOdd"]

_isFilled :: PathFigure_ -> Boolean
_isFilled = getUnsafe ["isFilled"]

_isShadowed :: PathFigure_ -> Boolean
_isShadowed = getUnsafe ["isShadowed"]

_segments :: PathFigure_ -> List_ PathSegment_
_segments = getUnsafe ["segments"]

_startX :: PathFigure_ -> Number
_startX = getUnsafe ["startX"]

_startY :: PathFigure_ -> Number
_startY = getUnsafe ["startY"]

