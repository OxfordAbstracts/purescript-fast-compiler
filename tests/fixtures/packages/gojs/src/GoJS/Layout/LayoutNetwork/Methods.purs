module GoJS.Layout.LayoutNetwork.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.Collection (Iterator_, List_, Set_)
import GoJS.GraphObject.Types (class IsNode, Link_, Part_)
import GoJS.Layout.Types (class LayoutNetwork)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe3)

addEdge_ :: forall _l n e _v. LayoutNetwork _l n e _v => e -> n -> Effect Unit
addEdge_ = callUnsafe1 "addEdge"

-- Optional parameters excluded: toplevelonly: boolean, pred: (a: Part) => boolean
addParts_ :: forall _l n _e _v. LayoutNetwork _l n _e _v => Iterator_ Part_ -> n -> Effect Unit
addParts_ = callUnsafe1 "addParts"

addLink_ :: forall _l n e _v. LayoutNetwork _l n e _v => Link_ -> n -> Effect e
addLink_ = callUnsafe1 "addLink"

addNode_ :: forall _l n _e v node. LayoutNetwork _l n _e v => IsNode node => node -> n -> Effect v
addNode_ = callUnsafe1 "addNode"

addVertex_ :: forall _l n _e v. LayoutNetwork _l n _e v => v -> n -> Effect Unit
addVertex_ = callUnsafe1 "addVertex"

createEdge_ :: forall _l n e _v. LayoutNetwork _l n e _v => n -> Effect e
createEdge_ = callUnsafe0 "createEdge"

createVertex_ :: forall _l n _e v. LayoutNetwork _l n _e v => n -> Effect v
createVertex_ = callUnsafe0 "createVertex"

deleteArtificialVertexes_ :: forall _l n _e _v. LayoutNetwork _l n _e _v => n -> Effect Unit
deleteArtificialVertexes_ = callUnsafe0 "deleteArtificialVertexes"

deleteEdge_ :: forall _l n e _v. LayoutNetwork _l n e _v => e -> n -> Effect Unit
deleteEdge_ = callUnsafe1 "deleteEdge"

deleteLink_ :: forall _l n _e _v. LayoutNetwork _l n _e _v => Link_ -> n -> Effect Unit
deleteLink_ = callUnsafe1 "deleteLink"

deleteNode_ :: forall _l n _e _v node. LayoutNetwork _l n _e _v => IsNode node => node -> n -> Effect Unit
deleteNode_ = callUnsafe1 "deleteNode"

deleteSelfEdges_ :: forall _l n _e _v. LayoutNetwork _l n _e _v => n -> Effect Unit
deleteSelfEdges_ = callUnsafe0 "deleteSelfEdges"

deleteVertex_ :: forall _l n _e v. LayoutNetwork _l n _e v => v -> n -> Effect Unit
deleteVertex_ = callUnsafe1 "deleteVertex"

findAllParts_ :: forall _l n _e _v. LayoutNetwork _l n _e _v => n -> Effect (Set_ Part_)
findAllParts_ = callUnsafe0 "findAllParts"

findEdge_ :: forall _l n e _v. LayoutNetwork _l n e _v => Link_ -> n -> Effect (Maybe e)
findEdge_ l ln = toMaybe <$> callUnsafe1 "findEdge" l ln

findVertex_ :: forall _l n _e v node. LayoutNetwork _l n _e v => IsNode node => node -> n -> Effect (Maybe v)
findVertex_ n ln = toMaybe <$> callUnsafe1 "findVertex" n ln

linkVertexes_ :: forall _l n e v. LayoutNetwork _l n e v => v -> v -> Link_ -> n -> Effect e
linkVertexes_ = callUnsafe3 "linkVertexes"

reverseEdge_ :: forall _l n e _v. LayoutNetwork _l n e _v => e -> n -> Effect Unit
reverseEdge_ = callUnsafe1 "reverseEdge"

--- Optional parameters excluded: clean: boolean
splitIntoSubNetworks_ :: forall _l n _e _v. LayoutNetwork _l n _e _v => n -> Effect (List_ n)
splitIntoSubNetworks_ = callUnsafe0 "splitIntoSubNetworks"
