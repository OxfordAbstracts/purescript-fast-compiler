module GoJS.Tool.MouseMoveTools.LinkingTool.Properties where

import GoJS.EnumValue (EnumValue_)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Tool.Types (LinkingTool_)
import GoJS.Unsafe (getUnsafe)

_archetypeLabelNodeData :: forall nodeData. LinkingTool_ -> Record nodeData
_archetypeLabelNodeData = getUnsafe ["archetypeLabelNodeData"]

_archetypeLinkData :: forall linkData. LinkingTool_ -> Record linkData
_archetypeLinkData = getUnsafe ["archetypeLinkData"]

_direction :: LinkingTool_ -> EnumValue_
_direction = getUnsafe ["direction"]

_startObject :: forall @g. IsGraphObject g => LinkingTool_ -> g
_startObject = getUnsafe ["startObject"]