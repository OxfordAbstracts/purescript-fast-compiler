module GoJS.Diagram.DraggingInfo.Properties where

import GoJS.Diagram.Types (DraggingInfo_)
import GoJS.Geometry.Types (Point_)
import GoJS.Unsafe (getUnsafe)

_point :: DraggingInfo_ -> Point_
_point = getUnsafe [ "point" ]
