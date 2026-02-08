module GoJS.Tool.ToolManager.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import GoJS.GraphObject.Types (class IsGraphObject, Adornment_)
import GoJS.Tool.Types (class IsTool, ToolManager_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2)

doMouseHover_ :: forall g. IsGraphObject g => g -> ToolManager_ -> Effect Unit
doMouseHover_ = callUnsafe1 "doMouseHover"

doToolTip_ :: forall g. IsGraphObject g => g -> ToolManager_ -> Effect Unit
doToolTip_ = callUnsafe1 "doToolTip"

findTool_ :: forall @t. String -> ToolManager_ -> Effect (Maybe t)
findTool_ s m = toMaybe <$> callUnsafe1 "findTool" s m

hideToolTip_ :: ToolManager_ -> Effect Unit
hideToolTip_ = callUnsafe0 "hideToolTip"

initializeStandardTools_ :: ToolManager_ -> Effect Unit
initializeStandardTools_ = callUnsafe0 "initializeStandardTools"

positionToolTip_ :: forall g. IsGraphObject g => Adornment_ -> g -> ToolManager_ -> Effect Unit
positionToolTip_ = callUnsafe2 "positionToolTip"

replaceTool_ :: forall t. IsTool t => String -> Nullable t -> ToolManager_ -> Effect (Maybe t)
replaceTool_ s t m = toMaybe <$> callUnsafe2 "replaceTool" s t m

showToolTip_ :: forall g. IsGraphObject g => Adornment_ -> g -> ToolManager_ -> Effect Unit
showToolTip_ = callUnsafe2 "showToolTip"