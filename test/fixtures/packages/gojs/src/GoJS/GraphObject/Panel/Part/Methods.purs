module GoJS.GraphObject.Panel.Part.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.Geometry.Types (Point_, Rect_)
import GoJS.GraphObject.Types (class IsPart, Adornment_, Group_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2, callUnsafe3)

addAdornment_ :: forall p. IsPart p => String -> Adornment_ -> p -> Effect Unit
addAdornment_ = callUnsafe2 "addAdornment"

canCopy_ :: forall p. IsPart p => p -> Effect Boolean
canCopy_ = callUnsafe0 "canCopy"

canDelete_ :: forall p. IsPart p => p -> Effect Boolean
canDelete_ = callUnsafe0 "canDelete"

canEdit_ :: forall p. IsPart p => p -> Effect Boolean
canEdit_ = callUnsafe0 "canEdit"

canGroup_ :: forall p. IsPart p => p -> Effect Boolean
canGroup_ = callUnsafe0 "canGroup"

canLayout_ :: forall p. IsPart p => p -> Effect Boolean
canLayout_ = callUnsafe0 "canLayout"

canMove_ :: forall p. IsPart p => p -> Effect Boolean
canMove_ = callUnsafe0 "canMove"

canReshape_ :: forall p. IsPart p => p -> Effect Boolean
canReshape_ = callUnsafe0 "canReshape"

canResize_ :: forall p. IsPart p => p -> Effect Boolean
canResize_ = callUnsafe0 "canResize"

canRotate_ :: forall p. IsPart p => p -> Effect Boolean
canRotate_ = callUnsafe0 "canRotate"

canSelect_ :: forall p. IsPart p => p -> Effect Boolean
canSelect_ = callUnsafe0 "canSelect"

clearAdornments_ :: forall p. IsPart p => p -> Effect Unit
clearAdornments_ = callUnsafe0 "clearAdornments"

ensureBounds_ :: forall p. IsPart p => p -> Effect Unit
ensureBounds_ = callUnsafe0 "ensureBounds"

findAdornment_ :: forall p. IsPart p => String -> p -> Effect (Maybe Adornment_)
findAdornment_ s p = toMaybe <$> callUnsafe1 "findAdornment" s p

findCommonContainingGroup_ :: forall p1 p2. IsPart p1 => IsPart p2 => p1 -> p2 -> Effect (Maybe Group_)
findCommonContainingGroup_ p1 p2 = toMaybe <$> callUnsafe1 "findCommonContainingGroup" p1 p2

findSubGraphLevel_ :: forall p. IsPart p => p -> Effect Number
findSubGraphLevel_ = callUnsafe0 "findSubGraphLevel"

findTopLevelPart_ :: forall p1 @p2. IsPart p1 => IsPart p2 => p1 -> Effect (Maybe p2)
findTopLevelPart_ = callUnsafe0 "findTopLevelPart"

getDocumentBounds_ :: forall p. IsPart p => Rect_ -> p -> Effect Rect_
getDocumentBounds_ = callUnsafe1 "getDocumentBounds"

invalidateLayout_ :: forall p. IsPart p => Number -> p -> Effect Unit
invalidateLayout_ = callUnsafe1 "invalidateLayout"

isMemberOf_ :: forall p1 p2. IsPart p1 => IsPart p2 => p1 -> p2 -> Effect Boolean
isMemberOf_ = callUnsafe1 "isMemberOf"

isVisible_ :: forall p. IsPart p => p -> Effect Boolean
isVisible_ = callUnsafe0 "isVisible"

move_ :: forall p. IsPart p => Point_ -> Boolean -> p -> Effect Unit
move_ = callUnsafe2 "move"

moveTo_ :: forall p. IsPart p => Number -> Number -> Boolean -> p -> Effect Unit
moveTo_ = callUnsafe3 "moveTo"

removeAdornment_ :: forall p. IsPart p => String -> p -> Effect Unit
removeAdornment_ = callUnsafe1 "removeAdornment"

updateAdornments_ :: forall p. IsPart p => p -> Effect Unit
updateAdornments_ = callUnsafe0 "updateAdornments"

updateRelationshipsFromData_ :: forall p. IsPart p => p -> Effect Unit
updateRelationshipsFromData_ = callUnsafe0 "updateRelationshipsFromData"

updateTargetBindings_ :: forall p. IsPart p => String -> p -> Effect Unit
updateTargetBindings_ = callUnsafe1 "updateTargetBindings"
