module GoJS.Tool.MouseDownTools.RotatingTool.Methods where

import Prelude

import Effect (Effect)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Geometry.Types (Point_)
import GoJS.Tool.Types (RotatingTool_)
import GoJS.Unsafe (callUnsafe1)

rotate_ :: Number -> RotatingTool_ -> Effect Unit
rotate_ = callUnsafe1 "rotate"

computeRotate_ :: Point_ -> RotatingTool_ -> Effect Number
computeRotate_ = callUnsafe1 "computeRotate"

computeRotationPoint_ :: forall g. IsGraphObject g => g -> RotatingTool_ -> Effect Point_
computeRotationPoint_ = callUnsafe1 "computeRotationPoint"