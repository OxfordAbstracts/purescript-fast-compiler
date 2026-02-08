module GoJS.Layout.LayoutVertex.TreeVertex.Methods where

import Prelude

import Effect (Effect)
import GoJS.Layout.Types (TreeVertex_)
import GoJS.Unsafe (callUnsafe1)

_copyInheritedPropertiesFrom :: TreeVertex_ -> TreeVertex_ -> Effect Unit
_copyInheritedPropertiesFrom = callUnsafe1 "copyInheritedPropertiesFrom"