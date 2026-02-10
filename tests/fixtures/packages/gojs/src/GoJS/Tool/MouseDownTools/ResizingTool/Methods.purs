module GoJS.Tool.MouseDownTools.ResizingTool.Methods where

import Prelude

import Effect (Effect)
import GoJS.Geometry.Types (Point_, Rect_, Size_, Spot_)
import GoJS.Tool.Types (ResizingTool_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe6)

computeCellSize_ :: ResizingTool_ -> Effect Size_
computeCellSize_ = callUnsafe0 "computeCellSize"

computeMaxSize_ :: ResizingTool_ -> Effect Size_
computeMaxSize_ = callUnsafe0 "computeMaxSize"

computeMinSize_ :: ResizingTool_ -> Effect Size_
computeMinSize_ = callUnsafe0 "computeMinSize"

computeReshape_ :: ResizingTool_ -> Effect Boolean
computeReshape_ = callUnsafe0 "computeReshape"

computeResize_ :: Point_ -> Spot_ -> Size_ -> Size_ -> Size_ -> Boolean -> ResizingTool_ -> Effect Size_
computeResize_ = callUnsafe6 "computeResize"

resize_ :: Rect_ -> ResizingTool_ -> Effect Unit
resize_ = callUnsafe1 "resize"
