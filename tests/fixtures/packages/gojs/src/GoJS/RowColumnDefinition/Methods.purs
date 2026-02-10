module GoJS.RowColumnDefinition.Methods where

import Prelude

import Effect (Effect)
import GoJS.Model.Types (Binding_)
import GoJS.RowColumnDefinition.Types (RowColumnDefinition_)
import GoJS.Unsafe (callUnsafe1)

bind_ :: Binding_ -> RowColumnDefinition_ -> Effect Unit
bind_ = callUnsafe1 "bind"