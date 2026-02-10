module GoJS.Model.ChangedEvent.Properties where

import Prelude

import GoJS.Diagram.Types (class IsDiagram)
import GoJS.EnumValue (EnumValue_)
import GoJS.Key (KeyProperty, toKeyProperty)
import GoJS.Model.Types (class IsModel, ChangedEvent_)
import GoJS.Unsafe (getUnsafe)

_change :: ChangedEvent_ -> EnumValue_
_change = getUnsafe [ "change" ]

_diagram :: forall d. IsDiagram d => ChangedEvent_ -> d
_diagram = getUnsafe [ "diagram" ]

-- Read-only
_isTransactionFinished :: ChangedEvent_ -> Boolean
_isTransactionFinished = getUnsafe [ "isTransactionFinished" ]

_model :: forall @m. IsModel m => ChangedEvent_ -> m
_model = getUnsafe [ "model" ]

_modelChange :: ChangedEvent_ -> String
_modelChange = getUnsafe [ "modelChange" ]

_newParam :: forall t. ChangedEvent_ -> t
_newParam = getUnsafe [ "newParam" ]

_newValue :: forall t. ChangedEvent_ -> t
_newValue = getUnsafe [ "newValue" ]

_object :: forall nodeData. ChangedEvent_ -> Record nodeData
_object = getUnsafe [ "object" ]

_oldParam :: forall t. ChangedEvent_ -> t
_oldParam = getUnsafe [ "oldParam" ]

_oldValue :: forall t. ChangedEvent_ -> t
_oldValue = getUnsafe [ "oldValue" ]

_propertyName :: forall nodeData @kt. ChangedEvent_ -> KeyProperty nodeData kt
_propertyName = toKeyProperty <<< getUnsafe [ "propertyName" ]
