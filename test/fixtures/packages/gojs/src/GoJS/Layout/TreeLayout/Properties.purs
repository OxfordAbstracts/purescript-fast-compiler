module GoJS.Layout.TreeLayout.Properties where

import Data.Function.Uncurried (Fn2)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Size_, Spot_)
import GoJS.Layout.Types (TreeLayout_, TreeVertex_)
import GoJS.Unsafe (getUnsafe)

_alignment :: TreeLayout_ -> EnumValue_
_alignment = getUnsafe [ "alignment" ]

_alternateAlignment :: TreeLayout_ -> EnumValue_
_alternateAlignment = getUnsafe [ "alternateAlignment" ]

_alternateAngle :: TreeLayout_ -> Number
_alternateAngle = getUnsafe [ "alternateAngle" ]

_alternateBreadthLimit :: TreeLayout_ -> Number
_alternateBreadthLimit = getUnsafe [ "alternateBreadthLimit" ]

_alternateChildPortSpot :: TreeLayout_ -> Spot_
_alternateChildPortSpot = getUnsafe [ "alternateChildPortSpot" ]

_alternateCommentMargin :: TreeLayout_ -> Number
_alternateCommentMargin = getUnsafe [ "alternateCommentMargin" ]

_alternateCommentSpacing :: TreeLayout_ -> Number
_alternateCommentSpacing = getUnsafe [ "alternateCommentSpacing" ]

_alternateCompaction :: TreeLayout_ -> EnumValue_
_alternateCompaction = getUnsafe [ "alternateCompaction" ]

_alternateComparer :: TreeLayout_ -> Fn2 TreeVertex_ TreeVertex_ Number
_alternateComparer = getUnsafe [ "alternateComparer" ]

_alternateDefaults :: TreeLayout_ -> TreeVertex_
_alternateDefaults = getUnsafe [ "alternateDefaults" ]

_alternateLayerSpacing :: TreeLayout_ -> Number
_alternateLayerSpacing = getUnsafe [ "alternateLayerSpacing" ]

_alternateLayerSpacingParentOverlap :: TreeLayout_ -> Number
_alternateLayerSpacingParentOverlap = getUnsafe [ "alternateLayerSpacingParentOverlap" ]

_alternateNodeIndent :: TreeLayout_ -> Number
_alternateNodeIndent = getUnsafe [ "alternateNodeIndent" ]

_alternateNodeIndentPastParent :: TreeLayout_ -> Number
_alternateNodeIndentPastParent = getUnsafe [ "alternateNodeIndentPastParent" ]

_alternateNodeSpacing :: TreeLayout_ -> Number
_alternateNodeSpacing = getUnsafe [ "alternateNodeSpacing" ]

_alternatePortSpot :: TreeLayout_ -> Spot_
_alternatePortSpot = getUnsafe [ "alternatePortSpot" ]

_alternateRowIndent :: TreeLayout_ -> Number
_alternateRowIndent = getUnsafe [ "alternateRowIndent" ]

_alternateRowSpacing :: TreeLayout_ -> Number
_alternateRowSpacing = getUnsafe [ "alternateRowSpacing" ]

_alternateSetsChildPortSpot :: TreeLayout_ -> Boolean
_alternateSetsChildPortSpot = getUnsafe [ "alternateSetsChildPortSpot" ]

_alternateSetsPortSpot :: TreeLayout_ -> Boolean
_alternateSetsPortSpot = getUnsafe [ "alternateSetsPortSpot" ]

_alternateSorting :: TreeLayout_ -> EnumValue_
_alternateSorting = getUnsafe [ "alternateSorting" ]

_angle :: TreeLayout_ -> Number
_angle = getUnsafe [ "angle" ]

_arrangement :: TreeLayout_ -> EnumValue_
_arrangement = getUnsafe [ "arrangement" ]

_arrangementSpacing :: TreeLayout_ -> Size_
_arrangementSpacing = getUnsafe [ "arrangementSpacing" ]

_breadthLimit :: TreeLayout_ -> Number
_breadthLimit = getUnsafe [ "breadthLimit" ]

_childPortSpot :: TreeLayout_ -> Spot_
_childPortSpot = getUnsafe [ "childPortSpot" ]

_commentMargin :: TreeLayout_ -> Number
_commentMargin = getUnsafe [ "commentMargin" ]

_commentSpacing :: TreeLayout_ -> Number
_commentSpacing = getUnsafe [ "commentSpacing" ]

_comments :: TreeLayout_ -> Boolean
_comments = getUnsafe [ "comments" ]

_compaction :: TreeLayout_ -> EnumValue_
_compaction = getUnsafe [ "compaction" ]

_comparer :: TreeLayout_ -> Fn2 TreeVertex_ TreeVertex_ Number
_comparer = getUnsafe [ "comparer" ]

_layerSpacing :: TreeLayout_ -> Number
_layerSpacing = getUnsafe [ "layerSpacing" ]

_layerSpacingParentOverlap :: TreeLayout_ -> Number
_layerSpacingParentOverlap = getUnsafe [ "layerSpacingParentOverlap" ]

_layerStyle :: TreeLayout_ -> EnumValue_
_layerStyle = getUnsafe [ "layerStyle" ]

_nodeIndent :: TreeLayout_ -> Number
_nodeIndent = getUnsafe [ "nodeIndent" ]

_nodeIndentPastParent :: TreeLayout_ -> Number
_nodeIndentPastParent = getUnsafe [ "nodeIndentPastParent" ]

_nodeSpacing :: TreeLayout_ -> Number
_nodeSpacing = getUnsafe [ "nodeSpacing" ]

_path :: TreeLayout_ -> EnumValue_
_path = getUnsafe [ "path" ]

_portSpot :: TreeLayout_ -> Spot_
_portSpot = getUnsafe [ "portSpot" ]

_rootDefaults :: TreeLayout_ -> TreeVertex_
_rootDefaults = getUnsafe [ "rootDefaults" ]

-- TODO: _roots should return a set of EITHER Node_ or TreeVertex_

_rowIndent :: TreeLayout_ -> Number
_rowIndent = getUnsafe [ "rowIndent" ]

_rowSpacing :: TreeLayout_ -> Number
_rowSpacing = getUnsafe [ "rowSpacing" ]

_setsChildPortSpot :: TreeLayout_ -> Boolean
_setsChildPortSpot = getUnsafe [ "setsChildPortSpot" ]

_setsPortSpot :: TreeLayout_ -> Boolean
_setsPortSpot = getUnsafe [ "setsPortSpot" ]

_sorting :: TreeLayout_ -> EnumValue_
_sorting = getUnsafe [ "sorting" ]

_treeStyle :: TreeLayout_ -> EnumValue_
_treeStyle = getUnsafe [ "treeStyle" ]