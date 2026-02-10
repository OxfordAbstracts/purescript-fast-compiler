module GoJS.Layout.LayoutVertex.Methods where

import Prelude

import Effect (Effect)
import GoJS.Layout.Types (class LayoutNetwork)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)

addDestinationEdge_ :: forall _l _n e v. LayoutNetwork _l _n e v => e -> v -> Effect Unit
addDestinationEdge_ = callUnsafe1 "addDestinationEdge"

addSourceEdge_ :: forall _l _n e v. LayoutNetwork _l _n e v => e -> v -> Effect Unit
addSourceEdge_ = callUnsafe1 "addSourceEdge"

commit_ :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Effect Unit
commit_ = callUnsafe0 "commit"

deleteDestinationEdge_ :: forall _l _n e v. LayoutNetwork _l _n e v => e -> v -> Effect Unit
deleteDestinationEdge_ = callUnsafe1 "deleteDestinationEdge"

deleteSourceEdge_ :: forall _l _n e v. LayoutNetwork _l _n e v => e -> v -> Effect Unit
deleteSourceEdge_ = callUnsafe1 "deleteSourceEdge"