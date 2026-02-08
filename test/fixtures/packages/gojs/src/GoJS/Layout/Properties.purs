module GoJS.Layout.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Diagram.Types (Diagram_)
import GoJS.GraphObject.Types (Group_)
import GoJS.Geometry.Types (Point_)
import GoJS.Layout.Types (class IsLayout, class LayoutNetwork)
import GoJS.Unsafe (getUnsafe)

_arrangementOrigin :: forall l. IsLayout l => l -> Point_
_arrangementOrigin = getUnsafe [ "arrangementOrigin" ]

_diagram :: forall l. IsLayout l => l -> Maybe Diagram_
_diagram = toMaybe <<< getUnsafe [ "diagram" ]

_group :: forall l. IsLayout l => l -> Maybe Group_
_group = toMaybe <<< getUnsafe [ "group" ]

_isInitial :: forall l. IsLayout l => l -> Boolean
_isInitial = getUnsafe [ "isInitial" ]

_isOngoing :: forall l. IsLayout l => l -> Boolean
_isOngoing = getUnsafe [ "isOngoing" ]

_isRealtime :: forall l. IsLayout l => l -> Boolean
_isRealtime = getUnsafe [ "isRealtime" ]

_isRouting :: forall l. IsLayout l => l -> Boolean
_isRouting = getUnsafe [ "isRouting" ]

_isValidLayout :: forall l. IsLayout l => l -> Boolean
_isValidLayout = getUnsafe [ "isValidLayout" ]

_isViewportSized :: forall l. IsLayout l => l -> Boolean
_isViewportSized = getUnsafe [ "isViewportSized" ]

_network :: forall l n _e _v. LayoutNetwork l n _e _v => l -> n
_network = getUnsafe [ "network" ]
