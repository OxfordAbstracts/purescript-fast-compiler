module GoJS.Tool.MouseDownTools.ResizingTool.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Geometry.Types (Point_, Size_)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Tool.Types (ResizingTool_)
import GoJS.Unsafe (getUnsafe)

_adornedObject :: forall g. IsGraphObject g => ResizingTool_ -> g
_adornedObject = getUnsafe ["adornedObject"]

_cellSize :: ResizingTool_ -> Size_
_cellSize = getUnsafe ["cellSize"]

_dragsMembers :: ResizingTool_ -> Boolean
_dragsMembers = getUnsafe ["dragsMembers"]

_handle :: forall g. IsGraphObject g => ResizingTool_ -> g
_handle = getUnsafe ["handle"]

_handleArchetype :: forall g. IsGraphObject g => ResizingTool_ -> Maybe g
_handleArchetype = toMaybe <<< getUnsafe ["handleArchetype"]

_isGridSnapEnabled :: ResizingTool_ -> Boolean
_isGridSnapEnabled = getUnsafe ["isGridSnapEnabled"]

_maxSize :: ResizingTool_ -> Size_
_maxSize = getUnsafe ["maxSize"]

_minSize :: ResizingTool_ -> Size_
_minSize = getUnsafe ["minSize"]

_oppositePoint :: ResizingTool_ -> Point_
_oppositePoint = getUnsafe ["oppositePoint"]

-- Read-only
_originalDesiredSize :: ResizingTool_ -> Size_
_originalDesiredSize = getUnsafe ["originalDesiredSize"]

-- Read-only
_originalLocation :: ResizingTool_ -> Point_
_originalLocation = getUnsafe ["originalLocation"]