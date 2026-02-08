module GoJS.Diagram.Overview.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Diagram.Types (class IsDiagram, Overview_)
import GoJS.GraphObject.Types (class IsPart)
import GoJS.Unsafe (getUnsafe)

_box :: forall @p. IsPart p => Overview_-> p
_box = getUnsafe [ "box" ]

_drawsGrid :: Overview_-> Boolean
_drawsGrid = getUnsafe [ "drawsGrid" ]

_drawsTemporaryLayers :: Overview_-> Number
_drawsTemporaryLayers = getUnsafe [ "drawsTemporaryLayers" ]

_observed :: forall @d. IsDiagram d => Overview_-> Maybe d
_observed = toMaybe <<< getUnsafe [ "observed" ]

_updateDelay :: Overview_-> Number
_updateDelay = getUnsafe [ "updateDelay" ]
