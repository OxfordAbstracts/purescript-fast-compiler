module GoJS.Layout.LayoutEdge.Methods where

import Prelude

import Effect (Effect)
import GoJS.Layout.Types (class LayoutNetwork)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)

commit_ :: forall _l _n e _v. LayoutNetwork _l _n e _v => e -> Effect Unit
commit_ = callUnsafe0 "commit"

getOtherVertex_ :: forall _l _n e v. LayoutNetwork _l _n e v => v -> e -> Effect v
getOtherVertex_ = callUnsafe1 "getOtherVertex"