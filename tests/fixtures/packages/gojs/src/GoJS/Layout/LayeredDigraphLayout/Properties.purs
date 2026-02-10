module GoJS.Layout.LayeredDigraphLayout.Properties where

import GoJS.EnumValue (EnumValue_)
import GoJS.Layout.Types (LayeredDigraphLayout_)
import GoJS.Unsafe (getUnsafe)

_aggressiveOption :: LayeredDigraphLayout_ -> EnumValue_
_aggressiveOption = getUnsafe [ "aggressiveOption" ]

_alignOption :: LayeredDigraphLayout_ -> Number
_alignOption = getUnsafe [ "alignOption" ]

_columnSpacing :: LayeredDigraphLayout_ -> Number
_columnSpacing = getUnsafe [ "columnSpacing" ]

_cycleRemoveOption :: LayeredDigraphLayout_ -> EnumValue_
_cycleRemoveOption = getUnsafe [ "cycleRemoveOption" ]

_directionLayeredDigraph :: LayeredDigraphLayout_ -> Number
_directionLayeredDigraph = getUnsafe [ "directionLayeredDigraph" ]

_initializeOption :: LayeredDigraphLayout_ -> EnumValue_
_initializeOption = getUnsafe [ "initializeOption" ]

_iterations :: LayeredDigraphLayout_ -> Number
_iterations = getUnsafe [ "iterations" ]

_layerSpacing :: LayeredDigraphLayout_ -> Number
_layerSpacing = getUnsafe [ "layerSpacing" ]

_layeringOption :: LayeredDigraphLayout_ -> EnumValue_
_layeringOption = getUnsafe [ "layeringOption" ]

-- Read-only
_maxColumn :: LayeredDigraphLayout_ -> Number
_maxColumn = getUnsafe [ "maxColumn" ]

-- Read-only
_maxIndex :: LayeredDigraphLayout_ -> Number
_maxIndex = getUnsafe [ "maxIndex" ]

-- Read-only
_maxIndexLayer :: LayeredDigraphLayout_ -> Number
_maxIndexLayer = getUnsafe [ "maxIndexLayer" ]

-- Read-only
_maxLayer :: LayeredDigraphLayout_ -> Number
_maxLayer = getUnsafe [ "maxLayer" ]

-- Read-only
_minIndexLayer :: LayeredDigraphLayout_ -> Number
_minIndexLayer = getUnsafe [ "minIndexLayer" ]

_packOption :: LayeredDigraphLayout_ -> Number
_packOption = getUnsafe [ "packOption" ]

_setsPortSpots :: LayeredDigraphLayout_ -> Boolean
_setsPortSpots = getUnsafe [ "setsPortSpots" ]