module GoJS.Tool.MouseMoveTools.PanningTool.Properties where

import GoJS.Geometry.Types (Point_)
import GoJS.Tool.Types (PanningTool_)
import GoJS.Unsafe (getUnsafe)

_bubbles :: PanningTool_ -> Boolean
_bubbles = getUnsafe [ "bubbles" ]

-- Read-only
_originalPosition :: PanningTool_ -> Point_
_originalPosition = getUnsafe [ "originalPosition" ]