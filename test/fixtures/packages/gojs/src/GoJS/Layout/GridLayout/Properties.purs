module GoJS.Layout.GridLayout.Properties where


import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Size_)
import GoJS.Layout.Types (GridLayout_)
import GoJS.Unsafe (getUnsafe)

_alignment :: GridLayout_ -> EnumValue_
_alignment = getUnsafe [ "alignmentGrid" ]

_arrangement :: GridLayout_ -> EnumValue_
_arrangement = getUnsafe [ "arrangement" ]

_cellSize :: GridLayout_ -> Size_
_cellSize = getUnsafe [ "cellSize" ]

_sorting :: GridLayout_ -> EnumValue_
_sorting = getUnsafe [ "sorting" ]

_spacing :: GridLayout_ -> Size_
_spacing = getUnsafe [ "spacing" ]

_wrappingColumn :: GridLayout_ -> Number
_wrappingColumn = getUnsafe [ "wrappingColumn" ]

_wrappingWidth :: GridLayout_ -> Number
_wrappingWidth = getUnsafe [ "wrappingWidth" ]
