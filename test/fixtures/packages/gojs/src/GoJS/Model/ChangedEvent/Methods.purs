module GoJS.Model.ChangedEvent.Methods where

import Prelude

import Effect (Effect)
import GoJS.Model.Types (ChangedEvent_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)

canRedo_ :: ChangedEvent_ -> Effect Boolean
canRedo_ = callUnsafe0 "canRedo"

canUndo_ :: ChangedEvent_ -> Effect Boolean
canUndo_ = callUnsafe0 "canUndo"

clear_ :: ChangedEvent_ -> Effect Unit
clear_ = callUnsafe0 "clear"

copy_ :: ChangedEvent_ -> Effect ChangedEvent_
copy_ = callUnsafe0 "copy"

getParam_ :: forall @param. Boolean -> ChangedEvent_ -> Effect param
getParam_ = callUnsafe1 "getParam"

getValue_ :: forall @value. Boolean -> ChangedEvent_ -> Effect value
getValue_ = callUnsafe1 "getValue"

redo_ :: ChangedEvent_ -> Effect Unit
redo_ = callUnsafe0 "redo"

undo_ :: ChangedEvent_ -> Effect Unit
undo_ = callUnsafe0 "undo"