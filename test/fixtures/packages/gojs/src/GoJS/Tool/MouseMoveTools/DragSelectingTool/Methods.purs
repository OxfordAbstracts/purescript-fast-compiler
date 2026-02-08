module GoJS.Tool.MouseMoveTools.DragSelectingTool.Methods where

import Prelude

import Effect (Effect)
import GoJS.Geometry.Types (Rect_)
import GoJS.Tool.Types (DragSelectingTool_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)

computeBoxBounds_ :: DragSelectingTool_ -> Effect Rect_
computeBoxBounds_ = callUnsafe0 "computeBoxBounds"

selectInRect_ :: Rect_ -> DragSelectingTool_ -> Effect Unit
selectInRect_ = callUnsafe1 "selectInRect"