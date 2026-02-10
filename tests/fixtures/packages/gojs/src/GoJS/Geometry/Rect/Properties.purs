module GoJS.Geometry.Rect.Properties where

import GoJS.Geometry.Types
import GoJS.Unsafe (getUnsafe)

_bottom :: Rect_ -> Number
_bottom = getUnsafe [ "bottom" ]

_center :: Rect_ -> Point_
_center = getUnsafe [ "center" ]

_centerX :: Rect_ -> Number
_centerX = getUnsafe [ "centerX" ]

_centerY :: Rect_ -> Number
_centerY = getUnsafe [ "centerY" ]

_height :: Rect_ -> Number
_height = getUnsafe [ "height" ]

_left :: Rect_ -> Number
_left = getUnsafe [ "left" ]

_position :: Rect_ -> Point_
_position = getUnsafe [ "position" ]

_right :: Rect_ -> Number
_right = getUnsafe [ "right" ]

_size :: Rect_ -> Size_
_size = getUnsafe [ "size" ]

_top :: Rect_ -> Number
_top = getUnsafe [ "top" ]

_width :: Rect_ -> Number
_width = getUnsafe [ "width" ]

_x :: Rect_ -> Number
_x = getUnsafe [ "x" ]

_y :: Rect_ -> Number
_y = getUnsafe [ "y" ]