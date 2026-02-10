module GoJS.Model.Binding.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.EnumValue (EnumValue_)
import GoJS.Model (Binding_)
import GoJS.Unsafe (getUnsafe)

_backConverter :: forall from to. Binding_ -> Maybe (from -> to)
_backConverter = toMaybe <<< getUnsafe [ "backConverter" ]

_converter :: forall to from. Binding_ -> Maybe (to -> from)
_converter = toMaybe <<< getUnsafe [ "converter" ]

_isToModel :: Binding_ -> Boolean
_isToModel = getUnsafe [ "isToModel" ]

_mode :: Binding_ -> EnumValue_
_mode = getUnsafe [ "mode" ]

_sourceProperty :: Binding_ -> String
_sourceProperty = getUnsafe [ "sourceProperty" ]

_targetProperty :: Binding_ -> String
_targetProperty = getUnsafe [ "targetProperty" ]
