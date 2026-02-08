module GoJS.Layout.LayoutVertex.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Collection (Iterator_)
import GoJS.Geometry.Types (Rect_)
import GoJS.GraphObject.Types (class IsNode)
import GoJS.Layout.Types (class LayoutNetwork)
import GoJS.Unsafe (getUnsafe)

_bounds :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Maybe Rect_
_bounds = toMaybe <<< getUnsafe [ "bounds" ]

_centerX :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_centerX = getUnsafe [ "centerX" ]

_centerY :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_centerY = getUnsafe [ "centerY" ]

_data :: forall _l _n _e v nodeData. LayoutNetwork _l _n _e v => v -> Maybe (Record nodeData)
_data = toMaybe <<< getUnsafe [ "data" ]

-- Read-only
_edges :: forall _l _n e v. LayoutNetwork _l _n e v => v -> Iterator_ e
_edges = getUnsafe [ "edges" ]

_level :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_level = getUnsafe [ "level" ]

-- Read-only
_destinationEdges :: forall _l _n e v. LayoutNetwork _l _n e v => v -> Iterator_ e
_destinationEdges = getUnsafe [ "destinationEdges" ]

-- Read-only
_destinationVertexes :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Iterator_ v
_destinationVertexes = getUnsafe [ "destinationVertexes" ]

-- Read-only
_edgesCount :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_edgesCount = getUnsafe [ "edgesCount" ]

_focusX :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_focusX = getUnsafe [ "focusX" ]

_focusY :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_focusY = getUnsafe [ "focusY" ]

_height :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_height = getUnsafe [ "height" ]

_network :: forall _l n _e v. LayoutNetwork _l n _e v => v -> Maybe n
_network = toMaybe <<< getUnsafe [ "network" ]

_node :: forall _l _n _e v @node. IsNode node => LayoutNetwork _l _n _e v => v -> Maybe node
_node = toMaybe <<< getUnsafe [ "node" ]

-- Read-only
_sourceEdges :: forall _l _n e v. LayoutNetwork _l _n e v => v -> Iterator_ e
_sourceEdges = getUnsafe [ "sourceEdges" ]

-- Read-only
_sourceVertexes :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Iterator_ v
_sourceVertexes = getUnsafe [ "sourceVertexes" ]

-- Read-only
_vertexes :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Iterator_ v
_vertexes = getUnsafe [ "vertexes" ]

_width :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_width = getUnsafe [ "width" ]

_x :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_x = getUnsafe [ "x" ]

_y :: forall _l _n _e v. LayoutNetwork _l _n _e v => v -> Number
_y = getUnsafe [ "y" ]