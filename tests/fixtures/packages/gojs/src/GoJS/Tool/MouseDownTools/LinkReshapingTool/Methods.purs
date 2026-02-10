module GoJS.Tool.MouseDownTools.LinkReshapingTool.Methods where

import Prelude

import Effect (Effect)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Point_)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Tool.Types (LinkReshapingTool_)
import GoJS.Unsafe (callUnsafe1, callUnsafe2)

getReshapingBehavior_ :: forall g. IsGraphObject g => g -> LinkReshapingTool_ -> Effect EnumValue_
getReshapingBehavior_ = callUnsafe1 "getReshapingBehavior"

computeReshape_ :: Point_ -> LinkReshapingTool_ -> Effect Point_
computeReshape_ = callUnsafe1 "computeReshape"

reshape_ :: Point_ -> LinkReshapingTool_ -> Effect Unit
reshape_ = callUnsafe1 "reshape"

setReshapingBehavior_ :: forall g. IsGraphObject g => g -> EnumValue_ -> LinkReshapingTool_ -> Effect Unit
setReshapingBehavior_ = callUnsafe2 "setReshapingBehavior"