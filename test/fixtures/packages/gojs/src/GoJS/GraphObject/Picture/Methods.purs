module GoJS.GraphObject.Picture.Methods where

import Prelude

import Effect (Effect)
import GoJS.GraphObject.Types (Picture_)
import GoJS.Unsafe (callUnsafe0)

redraw_ :: Picture_ -> Effect Unit
redraw_ = callUnsafe0 "redraw"

reloadSource_ :: Picture_ -> Effect Unit
reloadSource_ = callUnsafe0 "reloadSource"
