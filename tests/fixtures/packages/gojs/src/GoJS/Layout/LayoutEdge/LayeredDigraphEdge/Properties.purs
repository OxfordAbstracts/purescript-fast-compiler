module GoJS.Layout.LayoutEdge.LayeredDigraphEdge.Properties where

import GoJS.Layout.Types (LayeredDigraphEdge_)
import GoJS.Unsafe (getUnsafe)

_forest :: LayeredDigraphEdge_ -> Boolean
_forest = getUnsafe ["forest"]

_portFromColOffset :: LayeredDigraphEdge_ -> Number
_portFromColOffset = getUnsafe ["portFromColOffset"]

_portFromPos :: LayeredDigraphEdge_ -> Number
_portFromPos = getUnsafe ["portFromPos"]

_portToColOffset :: LayeredDigraphEdge_ -> Number
_portToColOffset = getUnsafe ["portToColOffset"]

_portToPos :: LayeredDigraphEdge_ -> Number
_portToPos = getUnsafe ["portToPos"]

_rev :: LayeredDigraphEdge_ -> Boolean
_rev = getUnsafe ["rev"]

_valid :: LayeredDigraphEdge_ -> Boolean
_valid = getUnsafe ["valid"]
