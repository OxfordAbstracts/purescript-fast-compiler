module GoJS.Geometry.Margin.Properties where

import GoJS.Geometry.Types (Margin_)
import GoJS.Unsafe (getUnsafe)

_bottom :: Margin_ -> Number
_bottom = getUnsafe [ "bottom" ]

_left :: Margin_ -> Number
_left = getUnsafe [ "left" ]

_right :: Margin_ -> Number
_right = getUnsafe [ "right" ]

_top :: Margin_ -> Number
_top = getUnsafe [ "top" ]
