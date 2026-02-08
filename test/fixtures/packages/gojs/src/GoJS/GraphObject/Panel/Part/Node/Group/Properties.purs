module GoJS.GraphObject.Panel.Part.Node.Group.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.GraphObject.Types (Group_, Placeholder_, Part_)
import GoJS.Layout.Types (class IsLayout)
import GoJS.Unsafe (getUnsafe)

_computesBoundsAfterDrag :: Group_ -> Boolean
_computesBoundsAfterDrag = getUnsafe [ "computesBoundsAfterDrag" ]

_computesBoundsIncludingLinks :: Group_ -> Boolean
_computesBoundsIncludingLinks = getUnsafe [ "computesBoundsIncludingLinks" ]

_computesBoundsIncludingLocation :: Group_ -> Boolean
_computesBoundsIncludingLocation = getUnsafe [ "computesBoundsIncludingLocation" ]

_handlesDragDropForMembers :: Group_ -> Boolean
_handlesDragDropForMembers = getUnsafe [ "handlesDragDropForMembers" ]

_isSubGraphExpanded :: Group_ -> Boolean
_isSubGraphExpanded = getUnsafe [ "isSubGraphExpanded" ]

_layout :: forall @l. IsLayout l => Group_ -> l
_layout = getUnsafe [ "layout" ]

_memberAdded :: Group_ -> (Group_ -> Part_ -> Effect Unit)
_memberAdded = getUnsafe [ "memberAdded" ]

_memberRemoved :: Group_ -> (Group_ -> Part_ -> Effect Unit)
_memberRemoved = getUnsafe [ "memberRemoved" ]

_placeholder :: Group_ -> Maybe Placeholder_
_placeholder = toMaybe <<< getUnsafe [ "toMaybe" ]

_subGraphExpandedChanged :: Group_ -> (Group_ -> Effect Unit)
_subGraphExpandedChanged = getUnsafe [ "subGraphExpandedChanged" ]

_wasSubGraphExpanded :: Group_ -> Boolean
_wasSubGraphExpanded = getUnsafe [ "wasSubGraphExpanded" ]