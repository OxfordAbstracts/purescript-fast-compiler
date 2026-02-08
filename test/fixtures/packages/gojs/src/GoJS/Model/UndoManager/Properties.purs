module GoJS.Model.UndoManager.Properties where

import GoJS.Collection (Iterator_, List_)
import GoJS.Model.Types (class IsModel, Transaction_, UndoManager_)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_currentTransaction :: UndoManager_ -> Transaction_
_currentTransaction = getUnsafe [ "currentTransaction" ]

-- Read-only
_history :: UndoManager_ -> List_ Transaction_
_history = getUnsafe [ "history" ]

-- Read-only
_historyIndex :: UndoManager_ -> Number
_historyIndex = getUnsafe [ "historyIndex" ]

_isEnabled :: UndoManager_ -> Boolean
_isEnabled = getUnsafe [ "isEnabled" ]

-- Read-only
_isInTransaction :: UndoManager_ -> Boolean
_isInTransaction = getUnsafe [ "isInTransaction" ]

-- Read-only
_isUndoingRedoing :: UndoManager_ -> Boolean
_isUndoingRedoing = getUnsafe [ "isUndoingRedoing" ]

_maxHistoryLength :: UndoManager_ -> Number
_maxHistoryLength = getUnsafe [ "maxHistoryLength" ]

-- Read-only
_models :: forall @m. IsModel m => UndoManager_ -> Iterator_ m
_models = getUnsafe [ "models" ]

-- Read-only
_nestedTransactionNames :: UndoManager_ -> List_ String
_nestedTransactionNames = getUnsafe [ "nestedTransactionNames" ]

-- Read-only
_transactionLevel :: UndoManager_ -> Number
_transactionLevel = getUnsafe [ "transactionLevel" ]

-- Read-only
_transactionToRedo :: UndoManager_ -> Transaction_
_transactionToRedo = getUnsafe [ "transactionToRedo" ]

-- Read-only
_transactionToUndo :: UndoManager_ -> Transaction_
_transactionToUndo = getUnsafe [ "transactionToUndo" ]
