module GoJS.Layout.LayoutVertex.Static where

import GoJS.Layout.Types (class LayoutNetwork)
import GoJS.Unsafe (callStaticPure2)


smartComparer_ :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> v -> Number
smartComparer_ = callStaticPure2 "LayoutVertex" "smartComparer"

standardComparer_ :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> v -> Number
standardComparer_ = callStaticPure2 "LayoutVertex" "standardComparer"
