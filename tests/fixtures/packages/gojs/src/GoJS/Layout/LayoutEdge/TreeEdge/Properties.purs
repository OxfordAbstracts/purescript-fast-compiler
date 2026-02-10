module GoJS.Layout.LayoutEdge.TreeEdge.Properties where

import GoJS.Geometry.Types (Point_)
import GoJS.Layout.Types (TreeEdge_)
import GoJS.Unsafe (getUnsafe)

_relativePoint :: TreeEdge_ -> Point_
_relativePoint = getUnsafe ["relativePoint"]
