module GoJS.Layout.LayoutVertex.TreeVertex.Properties where

import Prelude

import Data.Function.Uncurried (Fn2)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Point_, Size_, Spot_)
import GoJS.GraphObject.Types (Node_)
import GoJS.Layout.Types (TreeVertex_)
import GoJS.Unsafe (getUnsafe)

_alignment :: TreeVertex_ -> EnumValue_
_alignment = getUnsafe [ "alignment" ]

_angle :: TreeVertex_ -> Number
_angle = getUnsafe [ "angle" ]

_breadthLimit :: TreeVertex_ -> Number
_breadthLimit = getUnsafe [ "breadthLimit" ]

_childPortSpot :: TreeVertex_ -> Spot_
_childPortSpot = getUnsafe [ "childPortSpot" ]

_children :: TreeVertex_ -> Array TreeVertex_
_children = getUnsafe [ "children" ]

-- Read-only
_childrenCount :: TreeVertex_ -> Number
_childrenCount = getUnsafe [ "childrenCount" ]

_commentMargin :: TreeVertex_ -> Number
_commentMargin = getUnsafe [ "commentMargin" ]

_commentSpacing :: TreeVertex_ -> Number
_commentSpacing = getUnsafe [ "commentSpacing" ]

_comments :: TreeVertex_ -> Maybe (Array Node_)
_comments = toMaybe <<< getUnsafe [ "comments" ]

_compaction :: TreeVertex_ -> EnumValue_
_compaction = getUnsafe [ "compaction" ]

_comparer :: TreeVertex_ -> (Fn2 TreeVertex_ TreeVertex_ Number)
_comparer = getUnsafe [ "comparer" ]

_descendantCount :: TreeVertex_ -> Number
_descendantCount = getUnsafe [ "descendantCount" ]

_initialized :: TreeVertex_ -> Boolean
_initialized = getUnsafe [ "initialized" ]

_layerSpacing :: TreeVertex_ -> Number
_layerSpacing = getUnsafe [ "layerSpacing" ]

_layerSpacingParentOverlap :: TreeVertex_ -> Number
_layerSpacingParentOverlap = getUnsafe [ "layerSpacingParentOverlap" ]

_level :: TreeVertex_ -> Number
_level = getUnsafe [ "level" ]

_maxChildrenCount :: TreeVertex_ -> Number
_maxChildrenCount = getUnsafe [ "maxChildrenCount" ]

_maxGenerationCount :: TreeVertex_ -> Number
_maxGenerationCount = getUnsafe [ "maxGenerationCount" ]

_nodeIndent :: TreeVertex_ -> Number
_nodeIndent = getUnsafe [ "nodeIndent" ]

_nodeIndentPastParent :: TreeVertex_ -> Number
_nodeIndentPastParent = getUnsafe [ "nodeIndentPastParent" ]

_nodeSpacing :: TreeVertex_ -> Number
_nodeSpacing = getUnsafe [ "nodeSpacing" ]

_parent :: TreeVertex_ -> Maybe TreeVertex_
_parent = toMaybe <<< getUnsafe [ "parent" ]

_portSpot :: TreeVertex_ -> Spot_
_portSpot = getUnsafe [ "portSpot" ]

_relativePosition :: TreeVertex_ -> Point_
_relativePosition = getUnsafe [ "relativePosition" ]

_rowIndent :: TreeVertex_ -> Number
_rowIndent = getUnsafe [ "rowIndent" ]

_rowSpacing :: TreeVertex_ -> Number
_rowSpacing = getUnsafe [ "rowSpacing" ]

_setsChildPortSpot :: TreeVertex_ -> Boolean
_setsChildPortSpot = getUnsafe [ "setsChildPortSpot" ]

_setsPortSpot :: TreeVertex_ -> Boolean
_setsPortSpot = getUnsafe [ "setsPortSpot" ]

_sorting :: TreeVertex_ -> EnumValue_
_sorting = getUnsafe [ "sorting" ]

_subtreeOffset :: TreeVertex_ -> Point_
_subtreeOffset = getUnsafe [ "subtreeOffset" ]

_subtreeSize :: TreeVertex_ -> Size_
_subtreeSize = getUnsafe [ "subtreeSize" ]