module GoJS.Layout.LayoutEdge.ForceDirectedEdge.Properties where

import GoJS.Layout.Types (ForceDirectedEdge_)
import GoJS.Unsafe (getUnsafe)

_length :: ForceDirectedEdge_ -> Number
_length = getUnsafe ["length"]

_stiffness :: ForceDirectedEdge_ -> Number
_stiffness = getUnsafe ["stiffness"]