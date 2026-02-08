module GoJS.Model.UndoManager.Constructors where

import Effect (Effect)
import GoJS.Model.Types (UndoManager_)
import GoJS.Unsafe (constructor0)

newUndoManager :: Effect UndoManager_
newUndoManager = constructor0 "UndoManager"