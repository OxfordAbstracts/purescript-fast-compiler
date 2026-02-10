module GoJS.Diagram.CommandHandler.Methods where

import Prelude

import Data.Variant (Variant, case_, on)
import Effect (Effect)
import GoJS.Collection (Iterator_, Map_, Set_)
import GoJS.Diagram.CommandHandler.Types (CommandHandler_)
import GoJS.Diagram.Types (class IsDiagram, DraggingInfo_, DraggingOptions_)
import GoJS.Geometry.Types (Point_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, class IsPart, Group_, Part_, TextBlock_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2)
import Type.Prelude (Proxy(..))

-- Optional parameters: check: boolean
addTopLevelParts_ :: Iterator_ Part_ -> Boolean -> CommandHandler_ -> Effect Boolean
addTopLevelParts_ = callUnsafe2 "addTopLevelParts"

-- Optional parameters: group: Group
canCollapseSubGraph_ :: Group_ -> CommandHandler_ -> Effect Boolean
canCollapseSubGraph_ = callUnsafe1 "canCollapseSubGraph"

-- Optional parameters: node: Node
canCollapseTree_ :: forall n. IsNode n => n -> CommandHandler_ -> Effect Boolean
canCollapseTree_ = callUnsafe1 "canCollapseTree"

canCopySelection_ :: CommandHandler_ -> Effect Boolean
canCopySelection_ = callUnsafe0 "canCopySelection"

canCutSelection_ :: CommandHandler_ -> Effect Boolean
canCutSelection_ = callUnsafe0 "canCutSelection"

-- Optional parameters: factor: number
canDecreaseZoom_ :: Number -> CommandHandler_ -> Effect Boolean
canDecreaseZoom_ = callUnsafe1 "canDecreaseZoom"

canDeleteSelection_ :: CommandHandler_ -> Effect Boolean
canDeleteSelection_ = callUnsafe0 "canDeleteSelection"

-- Optional parameters: textblock: TextBlock
canEditTextBlock_ :: TextBlock_ -> CommandHandler_ -> Effect Boolean
canEditTextBlock_ = callUnsafe1 "canEditTextBlock"

-- Optional parameters: group: Group
canExpandSubGraph_ :: Group_ -> CommandHandler_ -> Effect Boolean
canExpandSubGraph_ = callUnsafe1 "canExpandSubGraph"

-- Optional parameters: node: Node
canExpandTree_ :: forall n. IsNode n => n -> CommandHandler_ -> Effect Boolean
canExpandTree_ = callUnsafe1 "canExpandTree"

canGroupSelection_ :: CommandHandler_ -> Effect Boolean
canGroupSelection_ = callUnsafe0 "canGroupSelection"

-- Optional parameters: factor: number
canIncreaseZoom_ :: Number -> CommandHandler_ -> Effect Boolean
canIncreaseZoom_ = callUnsafe1 "canIncreaseZoom"

-- Optional parameters: pos: Point
canPasteSelection_ :: Point_ -> CommandHandler_ -> Effect Boolean
canPasteSelection_ = callUnsafe1 "canPasteSelection"

canRedo_ :: CommandHandler_ -> Effect Boolean
canRedo_ = callUnsafe0 "canRedo"

-- Optional parameters: newscale: number
canResetZoom_ :: Number -> CommandHandler_ -> Effect Boolean
canResetZoom_ = callUnsafe1 "canResetZoom"

-- Optional parameters: part: Part
canScrollToPart_ :: forall p. IsPart p => p -> CommandHandler_ -> Effect Boolean
canScrollToPart_ = callUnsafe1 "canScrollToPart"

canSelectAll_ :: CommandHandler_ -> Effect Boolean
canSelectAll_ = callUnsafe0 "canSelectAll"

-- Optional parameters: obj: GraphObject | Diagram
canShowContextMenu_ :: forall graphObject diagram. IsGraphObject graphObject => IsDiagram diagram => Variant (graphObject :: graphObject, diagram :: diagram) -> CommandHandler_ -> Effect Boolean
canShowContextMenu_ obj commandHandler = obj #
  ( case_
      # on (Proxy @"graphObject") (\graphObject -> callUnsafe1 "canShowContextMenu" graphObject commandHandler)
      # on (Proxy @"diagram") (\diagram -> callUnsafe1 "canShowContextMenu" diagram commandHandler)
  )

canStopCommand_ :: CommandHandler_ -> Effect Boolean
canStopCommand_ = callUnsafe0 "canStopCommand"

canUndo_ :: CommandHandler_ -> Effect Boolean
canUndo_ = callUnsafe0 "canUndo"

-- Optional parameters: group: Group
canUngroupSelection_ :: Group_ -> CommandHandler_ -> Effect Boolean
canUngroupSelection_ = callUnsafe1 "canUngroupSelection"

canZoomToFit_ :: CommandHandler_ -> Effect Boolean
canZoomToFit_ = callUnsafe0 "canZoomToFit"

-- Optional parameters: group: Group
collapseSubGraph_ :: Group_ -> CommandHandler_ -> Effect Unit
collapseSubGraph_ = callUnsafe1 "collapseSubGraph"

-- Optional parameters: node: Node
collapseTree_ :: forall n. IsNode n => n -> CommandHandler_ -> Effect Unit
collapseTree_ = callUnsafe1 "collapseTree"

-- Optional parameters: options: DraggingOptions
computeEffectiveCollection_ :: Iterator_ Part_ -> DraggingOptions_ -> CommandHandler_ -> Effect (Map_ Part_ DraggingInfo_)
computeEffectiveCollection_ = callUnsafe2 "computeEffectiveCollection"

copySelection_ :: CommandHandler_ -> Effect Unit
copySelection_ = callUnsafe0 "copySelection"

copyToClipboard_ :: Iterator_ Part_ -> CommandHandler_ -> Effect Unit
copyToClipboard_ = callUnsafe1 "copyToClipboard"

cutSelection_ :: CommandHandler_ -> Effect Unit
cutSelection_ = callUnsafe0 "cutSelection"

-- Optional parameters: factor: number
decreaseZoom_ :: Number -> CommandHandler_ -> Effect Unit
decreaseZoom_ = callUnsafe1 "decreaseZoom"

deleteSelection_ :: CommandHandler_ -> Effect Unit
deleteSelection_ = callUnsafe0 "deleteSelection"

doKeyDown_ :: CommandHandler_ -> Effect Unit
doKeyDown_ = callUnsafe0 "doKeyDown"

doKeyUp_ :: CommandHandler_ -> Effect Unit
doKeyUp_ = callUnsafe0 "doKeyUp"

-- Optional parameters: textblock: TextBlock
editTextBlock_ :: TextBlock_ -> CommandHandler_ -> Effect Unit
editTextBlock_ = callUnsafe1 "editTextBlock"

-- Optional parameters: group: Group
expandSubGraph_ :: Group_ -> CommandHandler_ -> Effect Unit
expandSubGraph_ = callUnsafe1 "expandSubGraph"

-- Optional parameters: node: Node
expandTree_ :: forall n. IsNode n => n -> CommandHandler_ -> Effect Unit
expandTree_ = callUnsafe1 "expandTree"

groupSelection_ :: CommandHandler_ -> Effect Unit
groupSelection_ = callUnsafe0 "groupSelection"

-- Optional parameters: factor: number
increaseZoom_ :: Number -> CommandHandler_ -> Effect Unit
increaseZoom_ = callUnsafe1 "increaseZoom"

isValidMember_ :: forall p. IsPart p => Group_ -> p -> CommandHandler_ -> Effect Boolean
isValidMember_ = callUnsafe2 "isValidMember"

pasteFromClipboard_ :: forall @p. IsPart p => CommandHandler_ -> Effect (Set_ p)
pasteFromClipboard_ = callUnsafe0 "pasteFromClipboard"

-- Optional parameters: pos: Point
pasteSelection_ :: Point_ -> CommandHandler_ -> Effect Unit
pasteSelection_ = callUnsafe1 "pasteSelection"

redo_ :: CommandHandler_ -> Effect Unit
redo_ = callUnsafe0 "redo"

-- Optional parameters: newscale: number
resetZoom_ :: Number -> CommandHandler_ -> Effect Unit
resetZoom_ = callUnsafe1 "resetZoom"

-- Optional parameters: part: Part
scrollToPart_ :: forall p. IsPart p => p -> CommandHandler_ -> Effect Unit
scrollToPart_ = callUnsafe1 "scrollToPart"

selectAll_ :: CommandHandler_ -> Effect Unit
selectAll_ = callUnsafe0 "selectAll"

-- Optional parameters: obj: GraphObject | Diagram
showContextMenu_ :: forall graphObject diagram. IsGraphObject graphObject => IsDiagram diagram => Variant (graphObject :: graphObject, diagram :: diagram) -> CommandHandler_ -> Effect Unit
showContextMenu_ obj commandHandler = obj #
  ( case_
      # on (Proxy @"graphObject") (\graphObject -> callUnsafe1 "showContextMenu" graphObject commandHandler)
      # on (Proxy @"diagram") (\diagram -> callUnsafe1 "showContextMenu" diagram commandHandler)
  )

stopCommand_ :: CommandHandler_ -> Effect Unit
stopCommand_ = callUnsafe0 "stopCommand"

undo_ :: CommandHandler_ -> Effect Unit
undo_ = callUnsafe0 "undo"

-- Optional parameters: group: Group
ungroupSelection_ :: Group_ -> CommandHandler_ -> Effect Unit
ungroupSelection_ = callUnsafe1 "ungroupSelection"

zoomToFit_ :: CommandHandler_ -> Effect Unit
zoomToFit_ = callUnsafe0 "zoomToFit"
