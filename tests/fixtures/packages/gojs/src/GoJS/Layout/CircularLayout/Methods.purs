module GoJS.Layout.CircularLayout.Methods where

import Prelude

import Effect (Effect)
import GoJS.Layout.Types (CircularLayout_)
import GoJS.Unsafe (callUnsafe0)

commitLinks_ :: CircularLayout_ -> Effect Unit
commitLinks_ = callUnsafe0 "commitLinks"

commitNodes_ :: CircularLayout_ -> Effect Unit
commitNodes_ = callUnsafe0 "commitNodes"