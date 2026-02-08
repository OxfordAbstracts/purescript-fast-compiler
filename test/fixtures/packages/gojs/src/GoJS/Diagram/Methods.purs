module GoJS.Diagram.Methods where

import Prelude

import Data.Function.Uncurried (Fn1)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Data.Variant (Variant, case_, on)
import Effect (Effect)
import GoJS.Collection (Iterator_, List_, Map_)
import GoJS.Diagram.Types (class IsDiagram, DiagramEvent_, DraggingOptions_, Layer_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Point_, Rect_, Spot_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, class IsPart, Group_, Link_, GraphObject_, Node_, Part_)
import GoJS.Model (ChangedEvent_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2, callUnsafe3, callUnsafe4)
import Type.Prelude (Proxy(..))
import Web.HTML.HTMLImageElement (HTMLImageElement)

foreign import addNodeTemplate_ :: forall d n. String -> n -> d -> Effect Unit
foreign import addLinkTemplate_ :: forall d l. String -> l -> d -> Effect Unit
foreign import addGroupTemplate_ :: forall d g. String -> g -> d -> Effect Unit

add_ :: forall d p. IsDiagram d => IsPart p => p -> d -> Effect Unit
add_ = callUnsafe1 "add"

addDiagramListener_ :: forall d s. IsDiagram d => String -> (Fn1 (DiagramEvent_ s) Unit) -> d -> Effect d
addDiagramListener_ name listener d = callUnsafe2 "addDiagramListener" name listener d

addLayer_ :: forall d. IsDiagram d => Layer_ -> d -> Effect d
addLayer_ = callUnsafe1 "addLayer"

addLayerAfter_ :: forall d. IsDiagram d => Layer_ -> Layer_ -> d -> Effect d
addLayerAfter_ = callUnsafe2 "addLayerAfter"

addLayerBefore_ :: forall d. IsDiagram d => Layer_ -> Layer_ -> d -> Effect d
addLayerBefore_ = callUnsafe2 "addLayerBefore"

alignDocument_ :: forall d. IsDiagram d => Spot_ -> Spot_ -> d -> Effect Unit
alignDocument_ = callUnsafe2 "alignDocument"

attach_ :: forall r d. IsDiagram d => Record r -> d -> Effect d
attach_ = callUnsafe1 "attach"

centerRect_ :: forall d. IsDiagram d => Rect_ -> d -> Effect Unit
centerRect_ = callUnsafe1 "centerRect"

clear_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect Unit
clear_ = callUnsafe0 "clear"

clearHighlighteds_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect Unit
clearHighlighteds_ = callUnsafe0 "clearHighlighteds"

clearSelection_ :: forall d. IsDiagram d => Boolean -> d -> Effect Unit
clearSelection_ = callUnsafe1 "clearSelection"

commitTransaction_ :: forall d. IsDiagram d => String -> d -> Effect Boolean
commitTransaction_ = callUnsafe1 "commitTransaction"

computeBounds_ :: forall d. IsDiagram d => Rect_ -> d -> Effect Rect_
computeBounds_ = callUnsafe1 "computeBounds"

-- Optional parameters: includeLinks: boolean
computePartsBounds_ :: forall d. IsDiagram d => Variant (array :: Array Part_, iterator :: Iterator_ Part_) -> Boolean -> d -> Effect Rect_
computePartsBounds_ coll includeLinks diagram = coll #
  ( case_
      # on (Proxy @"array") (\array -> callUnsafe2 "computePartsBounds" array includeLinks diagram)
      # on (Proxy @"iterator") (\iterator -> callUnsafe2 "computePartsBounds" iterator includeLinks diagram)
  )

-- Optional parameters: check: boolean
copyParts_ :: forall d. IsDiagram d => Variant (array :: Array Part_, iterator :: Iterator_ Part_) -> Boolean -> d -> Effect (Map_ Part_ Part_)
copyParts_ coll check diagram = coll #
  ( case_
      # on (Proxy @"array") (\array -> callUnsafe2 "copyParts" array check diagram)
      # on (Proxy @"iterator") (\iterator -> callUnsafe2 "copyParts" iterator check diagram)
  )

ensureBounds_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect Unit
ensureBounds_ = callUnsafe0 "ensureBounds"

findLayer_ :: forall d. IsDiagram d => String -> d -> Effect (Maybe Layer_)
findLayer_ s d = toMaybe <$> callUnsafe1 "findLayer" s d

findLinkForData_ :: forall r d. IsDiagram d => Record r -> d -> Effect Link_
findLinkForData_ = callUnsafe1 "findLinkForData"

findLinkForKey_ :: forall d k. IsDiagram d => k -> d -> Effect Link_
findLinkForKey_ = callUnsafe1 "findLinkForKey"

findLinksByExample_ :: forall r d. IsDiagram d => Array (Record r) -> d -> Effect (Iterator_ Link_)
findLinksByExample_ = callUnsafe1 "findLinksByExample"

findNodeForData_ :: forall r d @n. IsDiagram d => IsNode n => Record r -> d -> Effect (Maybe n)
findNodeForData_ d di = toMaybe <$> callUnsafe1 "findNodeForData" d di

findNodeForKey_ :: forall d @n k. IsDiagram d => IsNode n => k -> d -> Effect (Maybe n)
findNodeForKey_ k d = toMaybe <$> callUnsafe1 "findNodeForKey" k d

findNodesByExample_ :: forall r d. IsDiagram d => Array (Record r) -> d -> Effect (Iterator_ Node_)
findNodesByExample_ = callUnsafe1 "findNodesByExample"

-- Optional parameters excluded: navig: a: GraphObject => T where T: GraphObject<T>
findObjectAt_ :: forall d @g. IsDiagram d => IsGraphObject g => Point_ -> Boolean -> d -> Effect (Maybe g)
findObjectAt_ p b d = toMaybe <$> callUnsafe2 "findObjectAt" p b d

-- Optional parameters excluded: navig: a: GraphObject => T where T: GraphObject<T>
-- TODO: Collection can be a Set or a List.
findObjectsAt_ :: forall d. IsDiagram d => Point_ -> Boolean -> d -> Effect (List_ GraphObject_)
findObjectsAt_ = callUnsafe2 "findObjectsAt"

-- Optional parameters excluded: navig: a: GraphObject => T, pred: a: T => boolean, partialInclusion: boolean, coll: S
-- where T: GraphObject<T>. S can be Set or List.
findObjectsIn_ :: forall d. IsDiagram d => Rect_ -> d -> Effect (List_ GraphObject_)
findObjectsIn_ = callUnsafe1 "findObjectsIn"

-- Optional parameters excluded: navig: a: GraphObject => T, pred: a: T => boolean, partialInclusion: boolean, coll: S
-- where T: GraphObject<T>. S can be Set or List.
findObjectsNear_ :: forall d. IsDiagram d => Point_ -> Number -> d -> Effect (List_ GraphObject_)
findObjectsNear_ = callUnsafe2 "findObjectsNear"

-- Optional parameters: selectable: boolean
findPartAt_ :: forall d @p. IsDiagram d => IsPart p => Point_ -> Boolean -> d -> Effect (Maybe p)
findPartAt_ p b d = toMaybe <$> callUnsafe2 "findPartAt" p b d

findPartForData_ :: forall r d @p. IsDiagram d => IsPart p => Record r -> d -> Effect (Maybe p)
findPartForData_ d di = toMaybe <$> callUnsafe1 "findPartForData" d di

findPartForKey_ :: forall d @p k. IsDiagram d => IsPart p => k -> d -> Effect (Maybe p)
findPartForKey_ k d = toMaybe <$> callUnsafe1 "findPartForKey" k d

-- Optional parameters: selectable: boolean
-- Optional parameters excluded: coll: S where S can be a Set or List of parts.
findPartsAt_ :: forall d. IsDiagram d => Point_ -> Boolean -> d -> Effect (List_ Part_)
findPartsAt_ = callUnsafe2 "findPartsAt"

-- Optional parameters: selectable: boolean, partialInclusion: boolean
-- Optional parameters excluded: coll: S where S can be a Set or List of parts.
findPartsIn_ :: forall d. IsDiagram d => Rect_ -> Boolean -> Boolean -> d -> Effect (List_ Part_)
findPartsIn_ = callUnsafe3 "findPartsIn"

-- Optional parameters: selectable: boolean, partialInclusion: boolean
-- Optional parameters excluded: coll: S where S can be a Set or List of parts.
findPartsNear_ :: forall d. IsDiagram d => Rect_ -> Boolean -> Boolean -> d -> Effect (List_ Part_)
findPartsNear_ = callUnsafe3 "findPartsNear"

findTopLevelGroups_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect (Iterator_ Group_)
findTopLevelGroups_ = callUnsafe0 "findTopLevelGroups"

findTreeRoots_ :: forall d. IsDiagram d => d -> Effect (Iterator_ Node_)
findTreeRoots_ = callUnsafe0 "findTreeRoots"

focus_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect Unit
focus_ = callUnsafe0 "focus"

highlight_ :: forall d p. IsDiagram d => IsPart p => p -> d -> Effect Unit
highlight_ = callUnsafe1 "highlight"

highlightCollection_ :: forall d p. IsDiagram d => IsPart p => Variant (array :: Array Part_, iterator :: Iterator_ Part_) -> d -> Effect Unit
highlightCollection_ coll diagram = coll #
  ( case_
      # on (Proxy @"array") (\array -> callUnsafe1 "highlightCollection" array diagram)
      # on (Proxy @"iterator") (\iterator -> callUnsafe1 "highlightCollection" iterator diagram)
  )

-- Optional parameters: invalidateAll: boolean
layoutDiagram_ :: forall d. IsDiagram d => Boolean -> d -> Effect Unit
layoutDiagram_ = callUnsafe1 "layoutDiagram"

-- Using purescript-web-html's binding to HTMLImageElement
-- Optional parameters excluded: options: ImageRendererOptions
makeImage_ :: forall d. IsDiagram d => d -> Effect HTMLImageElement
makeImage_ = callUnsafe0 "makeImage"

-- TODO: makeImageData is omitted because it returns a union type.

-- Optional parameters excluded: options: SvgRendererOptions
-- TODO: makeSvg is omitted because it returns an SVGElement - I couldn't find
-- an established library that handles the conversion of this type to PureScript.
-- makeSvg_ :: forall d. IsDiagram d => d -> Effect SVGElement
-- makeSvg_ = callUnsafe0 "makeSvg"

-- Optional parameters: check: boolean, dragOptions: DraggingOptions
moveParts_ :: forall d p. IsDiagram d => IsPart p => Variant (array :: Array Part_, iterator :: Iterator_ Part_) -> Point_ -> Boolean -> DraggingOptions_ -> d -> Effect Unit
moveParts_ coll offset check draggingOptions diagram = coll #
  ( case_
      # on (Proxy @"array") (\array -> callUnsafe4 "moveParts" array offset check draggingOptions diagram)
      # on (Proxy @"iterator") (\iterator -> callUnsafe4 "moveParts" iterator offset check draggingOptions diagram)
  )



-- Undocumented
raiseDiagramEvent_ :: forall d. String -> d -> Effect Unit
raiseDiagramEvent_ = callUnsafe1 "raiseDiagramEvent"

rebuildParts_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect Unit
rebuildParts_ = callUnsafe0 "rebuildParts"

remove_ :: forall d p. IsDiagram d => IsPart p => p -> d -> Effect Unit
remove_ = callUnsafe1 "remove"

removeChangedListener_ :: forall d. IsDiagram d => String -> (Fn1 ChangedEvent_ Unit) -> d -> Effect Unit
removeChangedListener_ name listener d = callUnsafe2 "removeChangedListener" name listener d

removeDiagramListener_ :: forall d s. IsDiagram d => String -> (Fn1 (DiagramEvent_ s) Unit) -> d -> Effect Unit
removeDiagramListener_ name listener d = callUnsafe2 "removeDiagramListener" name listener d

removeLayer_ :: forall d. IsDiagram d => Layer_ -> d -> Effect Unit
removeLayer_ = callUnsafe1 "removeLayer"

removeModelChangedListener_ :: forall d. IsDiagram d => String -> (Fn1 ChangedEvent_ Unit) -> d -> Effect Unit
removeModelChangedListener_ name listener d = callUnsafe2 "removeModelChangedListener" name listener d

-- Optional parameters: check: boolean
removeParts_ :: forall d. IsDiagram d => Variant (array :: Array Part_, iterator :: Iterator_ Part_) -> Boolean -> d -> Effect Unit
removeParts_ coll check diagram = coll #
  ( case_
      # on (Proxy @"array") (\array -> callUnsafe2 "removeParts" array check diagram)
      # on (Proxy @"iterator") (\iterator -> callUnsafe2 "removeParts" iterator check diagram)
  )

-- Optional parameters: alwaysQueueUpdate: boolean
requestUpdate_ :: forall d. IsDiagram d => Boolean -> d -> Effect Unit
requestUpdate_ = callUnsafe1 "requestUpdate"

rollbackTransaction_ :: forall d. IsDiagram d => d -> Effect Boolean
rollbackTransaction_ = callUnsafe0 "rollbackTransaction"

-- Optional parameters: dist: number
-- Params: unit: "pixel" | "line" | "page" | "document", dir: "up" | "down" | "left" | "right" 
scroll_ :: forall d. IsDiagram d => String -> String -> Number -> d -> Effect Unit
scroll_ = callUnsafe3 "scroll"

scrollToRect_ :: forall d. IsDiagram d => Rect_ -> d -> Effect Unit
scrollToRect_ = callUnsafe1 "scrollToRect"

select_ :: forall d p. IsDiagram d => IsPart p => p -> d -> Effect Unit
select_ = callUnsafe1 "select"

selectCollection_ :: forall d p. IsDiagram d => IsPart p => Variant (array :: Array Part_, iterator :: Iterator_ Part_) -> d -> Effect Unit
selectCollection_ coll diagram = coll #
  ( case_
      # on (Proxy @"array") (\array -> callUnsafe1 "selectCollection" array diagram)
      # on (Proxy @"iterator") (\iterator -> callUnsafe1 "selectCollection" iterator diagram)
  )

-- set, setProperties and attach are all handled via `setUnsafe`.

startTransaction_ :: forall d. IsDiagram d => String -> d -> Effect Boolean
startTransaction_ = callUnsafe1 "startTransaction"

transformDocToView_ :: forall d. IsDiagram d => Point_ -> d -> Effect Point_
transformDocToView_ = callUnsafe1 "transformDocToView"

transformViewToDoc_ :: forall d. IsDiagram d => Point_ -> d -> Effect Point_
transformViewToDoc_ = callUnsafe1 "transformViewToDoc"

updateAllRelationshipsFromData_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect Unit
updateAllRelationshipsFromData_ = callUnsafe0 "updateAllRelationshipsFromData"

-- Optional parameters: srcprop: string
updateAllTargetBindings_ :: forall d. IsDiagram d => String -> d -> Effect Unit
updateAllTargetBindings_ = callUnsafe1 "updateAllTargetBindings"

zoomToFit_ :: forall d. IsDiagram d => IsDiagram d => d -> Effect Unit
zoomToFit_ = callUnsafe0 "zoomToFit"

-- Optional parameters: scaling: EnumValue
zoomToRect_ :: forall d. IsDiagram d => Rect_ -> EnumValue_ -> d -> Effect Unit
zoomToRect_ = callUnsafe2 "zoomToRect"

-- TODO: Static methods: fromDiv, inherit, isUsingDOM, useDOM