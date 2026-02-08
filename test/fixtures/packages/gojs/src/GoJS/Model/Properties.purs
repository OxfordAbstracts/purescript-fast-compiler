module GoJS.Model.Properties where

import Effect.Uncurried (EffectFn2)
import GoJS.Model.Types (class IsModel, UndoManager_)
import GoJS.Unsafe (getUnsafe)

_copiesArrayObjects :: forall m. IsModel m => m -> Boolean
_copiesArrayObjects = getUnsafe [ "copiesArrayObjects" ]

_copiesArrays :: forall m. IsModel m => m -> Boolean
_copiesArrays = getUnsafe [ "copiesArrays" ]

_copiesKey :: forall m. IsModel m => m -> Boolean
_copiesKey = getUnsafe [ "copiesKey" ]

_copyNodeDataFunction :: forall m nodeData. IsModel m => m -> EffectFn2 (Record nodeData) m (Record nodeData)
_copyNodeDataFunction = getUnsafe [ "copyNodeDataFunction" ]

_dataFormat :: forall m. IsModel m => m -> String
_dataFormat = getUnsafe [ "dataFormat" ]

_modelData :: forall m nodeData. IsModel m => m -> Record nodeData
_modelData = getUnsafe [ "modelData" ]

_name :: forall m. IsModel m => m -> String
_name = getUnsafe [ "name" ]

_nodeDataArray :: forall m nodeData. IsModel m => m -> Array (Record nodeData)
_nodeDataArray = getUnsafe [ "nodeDataArray" ]

_nodeKeyProperty :: forall m. IsModel m => m -> String
_nodeKeyProperty = getUnsafe [ "nodeKeyProperty" ]

_skipsUndoManager :: forall m. IsModel m => m -> Boolean
_skipsUndoManager = getUnsafe [ "skipsUndoManager" ]

_undoManager :: forall m. IsModel m => m -> UndoManager_
_undoManager = getUnsafe [ "undoManager" ]
