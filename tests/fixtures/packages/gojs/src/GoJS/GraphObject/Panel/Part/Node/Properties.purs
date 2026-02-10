module GoJS.GraphObject.Panel.Part.Node.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn1, EffectFn3, EffectFn5)
import GoJS.Collection (Iterator_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Margin_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, GraphObject_, Link_)
import GoJS.Unsafe (getUnsafe)

_avoidable :: forall n. IsNode n => n -> Boolean
_avoidable = getUnsafe [ "avoidable" ]

_avoidableMargin :: forall n. IsNode n => n -> Margin_
_avoidableMargin = getUnsafe [ "avoidableMargin" ]

-- Read-only
_isLinkLabel :: forall n. IsNode n => n -> Boolean
_isLinkLabel = getUnsafe [ "isLinkLabel" ]

_isTreeExpanded :: forall n. IsNode n => n -> Boolean
_isTreeExpanded = getUnsafe [ "isTreeExpanded" ]

_isTreeLeaf :: forall n. IsNode n => n -> Boolean
_isTreeLeaf = getUnsafe [ "isTreeLeaf" ]

_labeledLink :: forall n. IsNode n => n -> Maybe Link_
_labeledLink = toMaybe <<< getUnsafe [ "labeledLink" ]

_linkConnected :: forall n g. IsNode n => IsGraphObject g => n -> Maybe (EffectFn3 n Link_ g Unit)
_linkConnected = toMaybe <<< getUnsafe [ "linkConnected" ]

_linkDisconnected :: forall n g. IsNode n => IsGraphObject g => n -> Maybe (EffectFn3 n Link_ g Unit)
_linkDisconnected = toMaybe <<< getUnsafe [ "linkDisconnected" ]

_linkValidation :: forall n fromPort toNode toPort. IsNode n => IsGraphObject fromPort => IsGraphObject toPort => IsNode toNode => n -> Maybe (EffectFn5 n fromPort toNode toPort Link_ Boolean)
_linkValidation = toMaybe <<< getUnsafe [ "linkValidation" ]

-- Read-only
_linksConnected :: forall n. IsNode n => n -> Iterator_ Link_
_linksConnected = getUnsafe [ "linksConnected" ]

-- Read-only
_port :: forall n @g. IsNode n => IsGraphObject g => n -> Maybe g
_port = toMaybe <<< getUnsafe [ "port" ]

_portSpreading :: forall n. IsNode n => n -> EnumValue_
_portSpreading = getUnsafe [ "portSpreading" ]

-- Read-only
_ports :: forall n. IsNode n => n -> Iterator_ GraphObject_
_ports = getUnsafe [ "ports" ]

_treeExpandedChanged :: forall n. IsNode n => n -> Maybe (EffectFn1 n Unit)
_treeExpandedChanged = toMaybe <<< getUnsafe [ "treeExpandedChanged" ]

_wasTreeExpanded :: forall n. IsNode n => n -> Boolean
_wasTreeExpanded = getUnsafe [ "wasTreeExpanded" ]
