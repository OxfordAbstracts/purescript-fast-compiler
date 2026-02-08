module GoJS.Diagram.DiagramEvent.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Diagram.Types (class IsDiagram, DiagramEvent_)
import GoJS.Unsafe (getUnsafe)

_diagram :: forall subjectType @diagramType. IsDiagram diagramType => DiagramEvent_ subjectType -> diagramType
_diagram = getUnsafe [ "diagram" ]

_name :: forall subjectType. DiagramEvent_ subjectType -> String
_name = getUnsafe [ "name" ]

_subject :: forall @subjectType. DiagramEvent_ subjectType -> Maybe subjectType
_subject = toMaybe <<< getUnsafe [ "subject" ]

_parameter :: forall subjectType @param. DiagramEvent_ subjectType -> Maybe param
_parameter = toMaybe <<< getUnsafe [ "parameter" ]
