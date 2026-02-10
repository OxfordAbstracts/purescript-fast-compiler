module GoJS.Model.Transaction.Properties where

import GoJS.Collection (List_)
import GoJS.Model.Types (ChangedEvent_, Transaction_)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_changes :: Transaction_ -> List_ ChangedEvent_
_changes = getUnsafe [ "changes" ]

_isComplete :: Transaction_ -> Boolean
_isComplete = getUnsafe [ "isComplete" ]

_name :: Transaction_ -> String
_name = getUnsafe [ "name" ]
