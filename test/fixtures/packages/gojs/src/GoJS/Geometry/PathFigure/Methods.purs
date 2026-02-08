module GoJS.Geometry.PathFigure.Methods where

import Effect (Effect)
import GoJS.Geometry.Types (PathFigure_, PathSegment_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)

add_ :: PathSegment_ -> PathFigure_ -> Effect PathFigure_
add_ = callUnsafe1 "add"

copy_ :: PathFigure_ -> Effect PathFigure_
copy_ = callUnsafe0 "copy"