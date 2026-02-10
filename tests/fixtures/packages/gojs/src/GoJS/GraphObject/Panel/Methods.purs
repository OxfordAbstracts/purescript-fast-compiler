module GoJS.GraphObject.Panel.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.GraphObject.Types (class IsGraphObject, class IsPanel)
import GoJS.Geometry.Types (Point_)
import GoJS.RowColumnDefinition.Types (RowColumnDefinition_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2)

add_ :: forall p g. IsPanel p => IsGraphObject g => g -> p -> Effect p
add_ = callUnsafe1 "add"

addColumnDefinition_ :: forall p. IsPanel p => Number -> RowColumnDefinition_ -> p -> Effect p
addColumnDefinition_ = callUnsafe2 "addColumnDefinition"

addRowColumnDefinition_ :: forall p. IsPanel p => RowColumnDefinition_ -> p -> Effect p
addRowColumnDefinition_ = callUnsafe1 "addRowColumnDefinition"

addRowDefinition_ :: forall p. IsPanel p => Number -> RowColumnDefinition_ -> p -> Effect p
addRowDefinition_ = callUnsafe2 "addRowDefinition"

copy_ :: forall p. IsPanel p => p -> Effect p
copy_ = callUnsafe0 "copy"

copyTemplate_ :: forall p. IsPanel p => Boolean -> p -> Effect p
copyTemplate_ = callUnsafe1 "copyTemplate"

elt_ :: forall p @g. IsPanel p => IsGraphObject g => Number -> p -> Effect g
elt_ = callUnsafe1 "elt"

findColumnForLocalX_ :: forall p. IsPanel p => Number -> p -> Effect Number
findColumnForLocalX_ = callUnsafe1 "findColumnForLocalX"

findItemPanelForData_ :: forall nodeData p. IsPanel p => Record nodeData -> p -> Effect (Maybe p)
findItemPanelForData_ d p = toMaybe <$> callUnsafe1 "findItemPanelForData" d p

findMainElement_ :: forall p @g. IsPanel p => IsGraphObject g => p -> Effect (Maybe g)
findMainElement_ p = toMaybe <$> callUnsafe0 "findMainElement" p

findObject_ :: forall p @g. IsPanel p => IsGraphObject g => String -> p -> Effect (Maybe g)
findObject_ s p = toMaybe <$> callUnsafe1 "findObject" s p

findRowForLocalY_ :: forall p. IsPanel p => Number -> p -> Effect Number
findRowForLocalY_ = callUnsafe1 "findRowForLocalY"

getColumnDefinition_ :: forall p. IsPanel p => Number -> p -> Effect (Maybe RowColumnDefinition_)
getColumnDefinition_ n p = toMaybe <$> callUnsafe1 "getColumnDefinition" n p

getRowDefinition_ :: forall p. IsPanel p => Number -> p -> Effect (Maybe RowColumnDefinition_)
getRowDefinition_ n p = toMaybe <$> callUnsafe1 "getRowDefinition" n p

graduatedPointForValue_ :: forall p. IsPanel p => Number -> Point_ -> p -> Effect Point_
graduatedPointForValue_ = callUnsafe2 "graduatedPointForValue"

graduatedValueForPoint_ :: forall p. IsPanel p => Point_ -> p -> Effect Number
graduatedValueForPoint_ = callUnsafe1 "graduatedValueForPoint"

insertAt_ :: forall p @g. IsPanel p => IsGraphObject g => Number -> g -> p -> Effect Unit
insertAt_ = callUnsafe2 "insertAt"

rebuildItemElements_ :: forall p. IsPanel p => p -> Effect Unit
rebuildItemElements_ = callUnsafe0 "rebuildItemElements"

remove_ :: forall p @g. IsPanel p => IsGraphObject g => g -> p -> Effect Unit
remove_ = callUnsafe1 "remove"

removeAt_ :: forall p. IsPanel p => Number -> p -> Effect Unit
removeAt_ = callUnsafe1 "removeAt"

removeColumnDefinition_ :: forall p. IsPanel p => Number -> p -> Effect Unit
removeColumnDefinition_ = callUnsafe1 "removeColumnDefinition"

removeRowDefinition_ :: forall p. IsPanel p => Number -> p -> Effect Unit
removeRowDefinition_ = callUnsafe1 "removeRowDefinition"

updateTargetBindings_ :: forall p. IsPanel p => String -> p -> Effect Unit
updateTargetBindings_ = callUnsafe1 "updateTargetBindings"

definePanelLayout_ :: forall p. IsPanel p => String -> String -> p -> Effect Unit
definePanelLayout_ = callUnsafe2 "definePanelLayout"
