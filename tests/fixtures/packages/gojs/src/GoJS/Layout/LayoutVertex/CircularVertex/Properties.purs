module GoJS.Layout.LayoutVertex.CircularVertex.Properties where

import GoJS.Layout.Types (CircularVertex_)
import GoJS.Unsafe (getUnsafe)

_actualAngle :: CircularVertex_ -> Number
_actualAngle = getUnsafe [ "actualAngle" ]

_diameter :: CircularVertex_ -> Number
_diameter = getUnsafe [ "diameter" ]
