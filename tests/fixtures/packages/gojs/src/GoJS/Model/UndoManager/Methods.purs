module GoJS.Model.UndoManager.Methods where

import Prelude

import Effect (Effect)
import GoJS.Model.Types (class IsModel, ChangedEvent_, UndoManager_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)

addModel_ :: forall m. IsModel m => m -> UndoManager_ -> Effect Unit
addModel_ = callUnsafe1 "addModel"

canRedo_ :: UndoManager_ -> Effect Boolean
canRedo_ = callUnsafe0 "canRedo"

canUndo_ :: UndoManager_ -> Effect Boolean
canUndo_ = callUnsafe0 "canUndo"

clear_ :: UndoManager_ -> Effect Unit
clear_ = callUnsafe0 "clear"

-- Optional parameters: tname: string
commitTransaction_ :: String -> UndoManager_ -> Effect Boolean
commitTransaction_ = callUnsafe1 "commitTransaction"

handleChanged_ :: ChangedEvent_ -> UndoManager_ -> Effect Unit
handleChanged_ = callUnsafe1 "handleChanged"

redo_ :: UndoManager_ -> Effect Unit
redo_ = callUnsafe0 "redo"

removeModel_ :: forall m. IsModel m => m -> UndoManager_ -> Effect Unit
removeModel_ = callUnsafe1 "removeModel"

rollbackTransaction_ :: UndoManager_ -> Effect Boolean
rollbackTransaction_ = callUnsafe0 "rollbackTransaction"

skipsEvent_ :: ChangedEvent_ -> UndoManager_ -> Effect Boolean
skipsEvent_ = callUnsafe1 "skipsEvent"

-- Optional parameters: tname: string
startTransaction_ :: String -> UndoManager_ -> Effect Boolean
startTransaction_ = callUnsafe1 "startTransaction"

undo_ :: UndoManager_ -> Effect Unit
undo_ = callUnsafe0 "undo"