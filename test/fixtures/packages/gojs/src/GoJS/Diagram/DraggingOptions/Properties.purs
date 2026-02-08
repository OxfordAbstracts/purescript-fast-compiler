module GoJS.Diagram.DraggingOptions.Properties where

import GoJS.Diagram.Types (DraggingOptions_)
import GoJS.Geometry.Types (Point_, Size_, Spot_)
import GoJS.Unsafe (getUnsafe)

_dragsLink :: DraggingOptions_ -> Boolean
_dragsLink = getUnsafe [ "dragsLink" ]

_dragsMembers :: DraggingOptions_ -> Boolean
_dragsMembers = getUnsafe [ "dragsMembers" ]

_dragsTree :: DraggingOptions_ -> Boolean
_dragsTree = getUnsafe [ "dragsTree" ]

_gridSnapCellSize :: DraggingOptions_ -> Size_
_gridSnapCellSize = getUnsafe [ "gridSnapCellSize" ]

_gridSnapCellSpot :: DraggingOptions_ -> Spot_
_gridSnapCellSpot = getUnsafe [ "gridSnapCellSpot" ]

_gridSnapOrigin :: DraggingOptions_ -> Point_
_gridSnapOrigin = getUnsafe [ "gridSnapOrigin" ]

_groupsAlwaysMove :: DraggingOptions_ -> Boolean
_groupsAlwaysMove = getUnsafe [ "groupsAlwaysMove" ]

_groupsSnapMembers :: DraggingOptions_ -> Boolean
_groupsSnapMembers = getUnsafe [ "groupsSnapMembers" ]

_isGridSnapEnabled :: DraggingOptions_ -> Boolean
_isGridSnapEnabled = getUnsafe [ "isGridSnapEnabled" ]

_isGridSnapRealtime :: DraggingOptions_ -> Boolean
_isGridSnapRealtime = getUnsafe [ "isGridSnapRealtime" ]
