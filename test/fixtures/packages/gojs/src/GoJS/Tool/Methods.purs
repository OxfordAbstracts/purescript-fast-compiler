module GoJS.Tool.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.Diagram (InputEvent_)
import GoJS.Geometry.Types (Point_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsPart)
import GoJS.Tool.Types (class IsTool)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2)

canStart_ :: forall t. IsTool t => t -> Effect Boolean
canStart_ = callUnsafe0 "canStart"

canStartMultiTouch_ :: forall t. IsTool t => t -> Effect Boolean
canStartMultiTouch_ = callUnsafe0 "canStartMultiTouch"

cancelWaitAfter_ :: forall t. IsTool t => t -> Effect Unit
cancelWaitAfter_ = callUnsafe0 "cancelWaitAfter"

doActivate_ :: forall t. IsTool t => t -> Effect Unit
doActivate_ = callUnsafe0 "doActivate"

doCancel_ :: forall t. IsTool t => t -> Effect Unit
doCancel_ = callUnsafe0 "doCancel"

doDeactivate_ :: forall t. IsTool t => t -> Effect Unit
doDeactivate_ = callUnsafe0 "doDeactivate"

doKeyDown_ :: forall t. IsTool t => t -> Effect Boolean
doKeyDown_ = callUnsafe0 "doKeyDown"

doKeyUp_ :: forall t. IsTool t => t -> Effect Boolean
doKeyUp_ = callUnsafe0 "doKeyUp"

doMouseDown_ :: forall t. IsTool t => t -> Effect Boolean
doMouseDown_ = callUnsafe0 "doMouseDown"

doMouseMove_ :: forall t. IsTool t => t -> Effect Boolean
doMouseMove_ = callUnsafe0 "doMouseMove"

doMouseUp_ :: forall t. IsTool t => t -> Effect Boolean
doMouseUp_ = callUnsafe0 "doMouseUp"

doMouseWheel_ :: forall t. IsTool t => t -> Effect Boolean
doMouseWheel_ = callUnsafe0 "doMouseWheel"

doStart_ :: forall t. IsTool t => t -> Effect Unit
doStart_ = callUnsafe0 "doStart"

doStop_ :: forall t. IsTool t => t -> Effect Unit
doStop_ = callUnsafe0 "doStop"

doWaitAfter_ :: forall t d. IsTool t => t -> InputEvent_ d ->  Effect Unit
doWaitAfter_ = callUnsafe1 "doWaitAfter"

findToolHandleAt_ :: forall t @g. IsTool t => IsGraphObject g => Point_ -> t -> Effect (Maybe g)
findToolHandleAt_ p t = toMaybe <$> callUnsafe1 "findToolHandleAt" p t

-- Optional parameters excluded: first: Point, last: Point
isBeyondDragSize_ :: forall t. IsTool t => t -> Effect Boolean
isBeyondDragSize_ = callUnsafe0 "isBeyondDragSize"

-- Optional parameters excluded: navig?: (a: GraphObject) => T, pred?: (a: T) => boolean
standardMouseClick_ :: forall t. IsTool t => t -> Effect Boolean
standardMouseClick_ = callUnsafe0 "standardMouseClick"

standardMouseOver_ :: forall t. IsTool t => t -> Effect Unit
standardMouseOver_ = callUnsafe0 "standardMouseOver"

standardMouseSelect_ :: forall t. IsTool t => t -> Effect Unit
standardMouseSelect_ = callUnsafe0 "standardMouseSelect"

standardMouseWheel_ :: forall t. IsTool t => t -> Effect Unit
standardMouseWheel_ = callUnsafe0 "standardMouseWheel"

standardPinchZoomMove_ :: forall t. IsTool t => t -> Effect Unit
standardPinchZoomMove_ = callUnsafe0 "standardPinchZoomMove"

standardPinchZoomStart_ :: forall t. IsTool t => t -> Effect Unit
standardPinchZoomStart_ = callUnsafe0 "standardPinchZoomStart"

-- Optional parameters: event: InputEvent
standardWaitAfter_ :: forall t d. IsTool t => Number -> InputEvent_ d -> t -> Effect Unit
standardWaitAfter_ = callUnsafe2 "standardWaitAfter"

-- Optional parameters: tname: string
startTransaction_ :: forall t. IsTool t => String -> t -> Effect Boolean
startTransaction_ = callUnsafe1 "startTransaction"

stopTool_ :: forall t. IsTool t => t -> Effect Unit
stopTool_ = callUnsafe0 "stopTool"

stopTransaction_ :: forall t. IsTool t => t -> Effect Boolean
stopTransaction_ = callUnsafe0 "stopTransaction"

updateAdornments_ :: forall t p. IsTool t => IsPart p => p -> t -> Effect Unit
updateAdornments_ = callUnsafe1 "updateAdornments"