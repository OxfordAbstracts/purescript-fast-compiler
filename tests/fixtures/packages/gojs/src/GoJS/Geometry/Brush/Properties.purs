module GoJS.Geometry.Brush.Properties where

import Prelude

import GoJS.Collection (Map_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Brush.BrushPattern (BrushPattern, whichBrushPattern)
import GoJS.Geometry.Types (Brush_, Spot_)
import GoJS.Unsafe (getUnsafe)

_color :: Brush_ -> String
_color = getUnsafe [ "color" ]

_colorStops :: Brush_ -> Map_ Number String
_colorStops = getUnsafe [ "colorStops" ]

_end :: Brush_ -> Spot_
_end = getUnsafe [ "end" ]

_endRadius :: Brush_ -> Number
_endRadius = getUnsafe [ "endRadius" ]

_pattern :: Brush_ -> BrushPattern
_pattern = whichBrushPattern <<< getUnsafe [ "pattern" ]

_start :: Brush_ -> Spot_
_start = getUnsafe [ "start" ]

_startRadius :: Brush_ -> Number
_startRadius = getUnsafe [ "startRadius" ]

_type :: Brush_ -> EnumValue_
_type = getUnsafe [ "type" ]