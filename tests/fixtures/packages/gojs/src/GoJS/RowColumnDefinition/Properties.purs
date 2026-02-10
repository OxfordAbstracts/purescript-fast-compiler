module GoJS.RowColumnDefinition.Properties where

import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Spot_)
import GoJS.GraphObject.Types (class IsPanel)
import GoJS.RowColumnDefinition.Types (RowColumnDefinition_)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_actual :: RowColumnDefinition_ -> Number
_actual = getUnsafe [ "actual" ]

_alignment :: RowColumnDefinition_ -> Spot_
_alignment = getUnsafe [ "alignment" ]

_background :: RowColumnDefinition_ -> String -- TODO: Could be Brush
_background = getUnsafe [ "background" ]

_coversSeparators :: RowColumnDefinition_ -> Boolean
_coversSeparators = getUnsafe [ "coversSeparators" ]

_height :: RowColumnDefinition_ -> Number
_height = getUnsafe [ "height" ]

-- Read-only
_index :: RowColumnDefinition_ -> Number
_index = getUnsafe [ "index" ]

-- Read-only
_isRow :: RowColumnDefinition_ -> Boolean
_isRow = getUnsafe [ "isRow" ]

_maximum :: RowColumnDefinition_ -> Number
_maximum = getUnsafe [ "maximum" ]

_minimum :: RowColumnDefinition_ -> Number
_minimum = getUnsafe [ "minimum" ]

-- Read-only
_panel :: forall @p. IsPanel p => RowColumnDefinition_ -> p
_panel = getUnsafe [ "panel" ]

-- Read-only
_position :: RowColumnDefinition_ -> Number
_position = getUnsafe [ "position" ]

_separatorDashArray :: RowColumnDefinition_ -> Array Number
_separatorDashArray = getUnsafe [ "separatorDashArray" ]

_separatorPadding :: RowColumnDefinition_ -> Number
_separatorPadding = getUnsafe [ "separatorPadding" ]

_separatorStroke :: RowColumnDefinition_ -> String -- TODO: Could be Brush
_separatorStroke = getUnsafe [ "separatorStroke" ]

_separatorStrokeWidth :: RowColumnDefinition_ -> Number
_separatorStrokeWidth = getUnsafe [ "separatorStrokeWidth" ]

_sizing :: RowColumnDefinition_ -> EnumValue_
_sizing = getUnsafe [ "sizing" ]

_stretch :: RowColumnDefinition_ -> EnumValue_
_stretch = getUnsafe [ "stretch" ]

-- Read-only
_total :: RowColumnDefinition_ -> Number
_total = getUnsafe [ "total" ]

_width :: RowColumnDefinition_ -> Number
_width = getUnsafe [ "width" ]