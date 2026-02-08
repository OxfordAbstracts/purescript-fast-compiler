module GoJS.Diagram.InputEvent.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Diagram.Types (class IsDiagram, InputEvent_)
import GoJS.Geometry.Types (Point_)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Unsafe (getUnsafe)
import Web.Event.Event (Event)

_alt :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_alt = getUnsafe [ "alt" ]

_bubbles :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_bubbles = getUnsafe [ "bubbles" ]

_button :: forall d. IsDiagram d => InputEvent_ d -> Number
_button = getUnsafe [ "button" ]

_buttons :: forall d. IsDiagram d => InputEvent_ d -> Number
_buttons = getUnsafe [ "buttons" ]

_clickCount :: forall d. IsDiagram d => InputEvent_ d -> Number
_clickCount = getUnsafe [ "clickCount" ]

_control :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_control = getUnsafe [ "control" ]

_delta :: forall d. IsDiagram d => InputEvent_ d -> Number
_delta = getUnsafe [ "delta" ]

_diagram :: forall d. IsDiagram d => InputEvent_ d -> d
_diagram = getUnsafe [ "diagram" ]

_documentPoint :: forall d. IsDiagram d => InputEvent_ d -> Point_
_documentPoint = getUnsafe [ "documentPoint" ]

_down :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_down = getUnsafe [ "down" ]

_event :: forall d. IsDiagram d => InputEvent_ d -> Event
_event = getUnsafe ["event"]

_handled :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_handled = getUnsafe [ "handled" ]

_isMultiTouch :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_isMultiTouch = getUnsafe [ "isMultiTouch" ]

_isTouchEvent :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_isTouchEvent = getUnsafe [ "isTouchEvent" ]

_key :: forall d. IsDiagram d => InputEvent_ d -> String
_key = getUnsafe [ "key" ]

_left :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_left = getUnsafe [ "left" ]

_meta :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_meta = getUnsafe [ "meta" ]

_middle :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_middle = getUnsafe [ "middle" ]

_modifiers :: forall d. IsDiagram d => InputEvent_ d -> Number
_modifiers = getUnsafe [ "modifiers" ]

_right :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_right = getUnsafe [ "right" ]

_shift :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_shift = getUnsafe [ "shift" ]

_targetDiagram :: forall d. IsDiagram d => InputEvent_ d -> d
_targetDiagram = getUnsafe [ "targetDiagram" ]

_targetObject :: forall d @g. IsDiagram d => IsGraphObject g => InputEvent_ d -> Maybe g
_targetObject = toMaybe <<< getUnsafe [ "targetObject" ]

_timestamp :: forall d. IsDiagram d => InputEvent_ d -> Number
_timestamp = getUnsafe [ "timestamp" ]

_up :: forall d. IsDiagram d => InputEvent_ d -> Boolean
_up = getUnsafe [ "up" ]

_viewPoint :: forall d. IsDiagram d => InputEvent_ d -> Point_
_viewPoint = getUnsafe [ "viewPoint" ]