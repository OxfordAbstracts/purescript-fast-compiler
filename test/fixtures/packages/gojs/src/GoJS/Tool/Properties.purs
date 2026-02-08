module GoJS.Tool.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Diagram.Types (class IsDiagram)
import GoJS.Tool.Types (class IsTool)
import GoJS.Unsafe (getUnsafe)

_diagram :: forall t @d. IsTool t => IsDiagram d => t -> d
_diagram = getUnsafe [ "diagram" ]

_isActive :: forall t. IsTool t => t -> Boolean
_isActive = getUnsafe [ "isActive" ]

_isEnabled :: forall t. IsTool t => t -> Boolean
_isEnabled = getUnsafe [ "isEnabled" ]

_name :: forall t. IsTool t => t -> String
_name = getUnsafe [ "name" ]

_transactionResult :: forall t. IsTool t => t -> Maybe String
_transactionResult = toMaybe <<< getUnsafe [ "transactionResult" ]
