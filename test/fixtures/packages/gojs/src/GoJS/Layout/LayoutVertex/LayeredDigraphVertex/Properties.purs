module GoJS.Layout.LayoutVertex.LayeredDigraphVertex.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Layout.Types (LayeredDigraphVertex_)
import GoJS.Unsafe (getUnsafe)

_column :: LayeredDigraphVertex_ -> Number
_column = getUnsafe [ "column" ]

_component :: LayeredDigraphVertex_ -> Number
_component = getUnsafe [ "component" ]

_index :: LayeredDigraphVertex_ -> Number
_index = getUnsafe [ "index" ]

_layer :: LayeredDigraphVertex_ -> Number
_layer = getUnsafe [ "layer" ]

_near :: LayeredDigraphVertex_ -> Maybe LayeredDigraphVertex_
_near = toMaybe <<< getUnsafe [ "near" ]
