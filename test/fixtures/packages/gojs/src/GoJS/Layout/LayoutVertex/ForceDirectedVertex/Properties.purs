module GoJS.Layout.LayoutVertex.ForceDirectedVertex.Properties where

import GoJS.Layout.Types (ForceDirectedVertex_)
import GoJS.Unsafe (getUnsafe)

_charge :: ForceDirectedVertex_ -> Number
_charge = getUnsafe [ "charge" ]

_forceX :: ForceDirectedVertex_ -> Number
_forceX = getUnsafe [ "forceX" ]

_forceY :: ForceDirectedVertex_ -> Number
_forceY = getUnsafe [ "forceY" ]

_isFixed :: ForceDirectedVertex_ -> Boolean
_isFixed = getUnsafe [ "isFixed" ]

_mass :: ForceDirectedVertex_ -> Number
_mass = getUnsafe [ "mass" ]