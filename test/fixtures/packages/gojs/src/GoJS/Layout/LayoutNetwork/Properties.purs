module GoJS.Layout.LayoutNetwork.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Collection (Set_)
import GoJS.Layout.Types (class LayoutNetwork)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_vertexes :: forall _l n _e v. LayoutNetwork _l n _e v => n -> Set_ v
_vertexes = getUnsafe [ "vertexes" ]

-- Read-only
_edges :: forall _l n e _v. LayoutNetwork _l n e _v => n -> Set_ e
_edges = getUnsafe [ "edges" ]

_layout :: forall l n _e _v. LayoutNetwork l n _e _v => n -> Maybe l
_layout = toMaybe <<< getUnsafe [ "layout" ]
