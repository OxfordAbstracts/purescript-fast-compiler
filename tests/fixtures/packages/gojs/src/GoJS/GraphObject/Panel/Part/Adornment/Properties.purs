module GoJS.GraphObject.Panel.Part.Adornment.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.GraphObject.Types (class IsGraphObject, class IsPart, Adornment_, Placeholder_)
import GoJS.Unsafe (getUnsafe)

_adornedObject :: forall @g. IsGraphObject g => Adornment_ -> Maybe g
_adornedObject = toMaybe <<< getUnsafe [ "adornedObject" ]

_adornedPart :: forall @p. IsPart p => Adornment_ -> Maybe p
_adornedPart = toMaybe <<< getUnsafe [ "adornedPart" ]

_placeholder :: Adornment_ -> Maybe Placeholder_
_placeholder = toMaybe <<< getUnsafe [ "placeholder" ]
