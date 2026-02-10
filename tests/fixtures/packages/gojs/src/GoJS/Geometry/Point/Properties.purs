module GoJS.Geometry.Point.Properties where

import GoJS.Geometry.Types (Point_)
import GoJS.Unsafe (getUnsafe)

_x :: Point_ -> Number
_x = getUnsafe [ "x" ]

_y :: Point_ -> Number
_y = getUnsafe [ "y" ]