module GoJS.Geometry.Size.Properties where

import GoJS.Geometry.Types (Size_)
import GoJS.Unsafe (getUnsafe)

_height :: Size_ -> Number
_height = getUnsafe [ "height" ]

_width :: Size_ -> Number
_width = getUnsafe [ "width" ]