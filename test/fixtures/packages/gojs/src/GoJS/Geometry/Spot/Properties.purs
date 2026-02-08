module GoJS.Geometry.Spot.Properties where

import GoJS.Geometry.Types (Spot_)
import GoJS.Unsafe (getUnsafe)

_x :: Spot_ -> Number
_x = getUnsafe [ "x" ]

_y :: Spot_ -> Number
_y = getUnsafe [ "y" ]

_offsetX :: Spot_ -> Number
_offsetX = getUnsafe [ "offsetX" ]

_offsetY :: Spot_ -> Number
_offsetY = getUnsafe [ "offsetY" ]
