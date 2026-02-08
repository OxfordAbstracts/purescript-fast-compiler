module GoJS.Tool.MouseUpTools.ContextMenuTool.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Geometry.Types (Point_)
import GoJS.GraphObject.Types (class IsGraphObject, ContextMenu_, toContextMenu)
import GoJS.Tool (ContextMenuTool_)
import GoJS.Unsafe (getUnsafe)

_currentContextMenu :: ContextMenuTool_ -> Maybe ContextMenu_
_currentContextMenu = toContextMenu <<< getUnsafe [ "currentContextMenu" ]

_currentObject :: forall @g. IsGraphObject g => ContextMenuTool_ -> Maybe g
_currentObject = toMaybe <<< getUnsafe [ "currentObject" ]

_defaultTouchContextMenu :: ContextMenuTool_ -> Maybe ContextMenu_
_defaultTouchContextMenu = toContextMenu <<< getUnsafe [ "defaultTouchContextMenu" ]

-- Read-only
_mouseDownPoint :: ContextMenuTool_ -> Point_
_mouseDownPoint = getUnsafe [ "mouseDownPoint" ]