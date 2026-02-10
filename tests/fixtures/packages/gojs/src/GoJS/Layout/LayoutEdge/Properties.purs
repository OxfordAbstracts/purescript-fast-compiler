module GoJS.Layout.LayoutEdge.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.GraphObject.Types (Link_)
import GoJS.Layout.Types (class LayoutNetwork)
import GoJS.Unsafe (getUnsafe)

_data :: forall _l n _e _v nodeData. LayoutNetwork _l n _e _v => n -> Maybe (Record nodeData)
_data = toMaybe <<< getUnsafe [ "data" ]

_link :: forall _l _n e v. LayoutNetwork _l _n e v => e -> Maybe Link_
_link = toMaybe <<< getUnsafe [ "link" ]

_fromVertex :: forall _l _n e v. LayoutNetwork _l _n e v => e -> v
_fromVertex = getUnsafe [ "fromVertex" ]

_network :: forall _l n e _v. LayoutNetwork _l n e _v => e -> Maybe n
_network = toMaybe <<< getUnsafe [ "network" ]

_toVertex :: forall _l _n e v. LayoutNetwork _l _n e v => e -> v
_toVertex = getUnsafe [ "toVertex" ]
