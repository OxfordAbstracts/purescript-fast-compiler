module GoJS.Model.Transaction.Methods where

import Prelude

import Effect (Effect)
import GoJS.Model.Types (Transaction_)
import GoJS.Unsafe (callUnsafe0)

canRedo_ :: Transaction_ -> Effect Boolean
canRedo_ = callUnsafe0 "canRedo"

canUndo_ :: Transaction_ -> Effect Boolean
canUndo_ = callUnsafe0 "canUndo"

clear_ :: Transaction_ -> Effect Unit
clear_ = callUnsafe0 "clear"

optimize_ :: Transaction_ -> Effect Unit
optimize_ = callUnsafe0 "optimize"

redo_ :: Transaction_ -> Effect Unit
redo_ = callUnsafe0 "redo"

undo_ :: Transaction_ -> Effect Unit
undo_ = callUnsafe0 "undo"