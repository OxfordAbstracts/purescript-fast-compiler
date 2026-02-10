module GoJS.GraphObject.Panel.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.Collection (Iterator_)
import GoJS.GraphObject.Types (class IsPanel, GraphObject_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Margin_, Point_, Size_, Spot_)
import GoJS.Unsafe (getUnsafe)

_alignmentFocusName :: forall p. IsPanel p => p -> String
_alignmentFocusName = getUnsafe [ "alignmentFocusName" ]

-- Read-only
_columnCount :: forall p. IsPanel p => p -> Number
_columnCount = getUnsafe [ "columnCount" ]

_columnSizing :: forall p. IsPanel p => p -> EnumValue_
_columnSizing = getUnsafe [ "columnSizing" ]

_data :: forall p @nodeData. IsPanel p => p -> Record nodeData
_data = getUnsafe [ "data" ]

_defaultAlignment :: forall p. IsPanel p => p -> Spot_
_defaultAlignment = getUnsafe [ "defaultAlignment" ]

_defaultRowSeparatorDashArray :: forall p. IsPanel p => p -> Array Number
_defaultRowSeparatorDashArray = getUnsafe [ "defaultRowSeparatorDashArray" ]

_defaultRowSeparatorStroke :: forall p. IsPanel p => p -> String -- TODO: Can be Brush
_defaultRowSeparatorStroke = getUnsafe [ "defaultRowSeparatorStroke" ]

_defaultRowSeparatorStrokeWidth :: forall p. IsPanel p => p -> Number
_defaultRowSeparatorStrokeWidth = getUnsafe [ "defaultRowSeparatorStrokeWidth" ]

_defaultSeparatorPadding :: forall p. IsPanel p => p -> Margin_
_defaultSeparatorPadding = getUnsafe [ "defaultSeparatorPadding" ]

_defaultStretch :: forall p. IsPanel p => p -> EnumValue_
_defaultStretch = getUnsafe [ "defaultStretch" ]

-- Read-only
_elements :: forall p. IsPanel p => p -> Iterator_ GraphObject_
_elements = getUnsafe [ "elements" ]

_graduatedMax :: forall p. IsPanel p => p -> Number
_graduatedMax = getUnsafe [ "graduatedMax" ]

_graduatedMin :: forall p. IsPanel p => p -> Number
_graduatedMin = getUnsafe [ "graduatedMin" ]

-- Read-only
_graduatedRange :: forall p. IsPanel p => p -> Number
_graduatedRange = getUnsafe [ "graduatedRange" ]

_graduatedTickUnit :: forall p. IsPanel p => p -> Number
_graduatedTickUnit = getUnsafe [ "graduatedTickUnit" ]

_gridCellSize :: forall p. IsPanel p => p -> Size_
_gridCellSize = getUnsafe [ "gridCellSize" ]

_gridOrigin :: forall p. IsPanel p => p -> Point_
_gridOrigin = getUnsafe [ "gridOrigin" ]

_isClipping :: forall p. IsPanel p => p -> Boolean
_isClipping = getUnsafe [ "isClipping" ]

_isEnabled :: forall p. IsPanel p => p -> Boolean
_isEnabled = getUnsafe [ "isEnabled" ]

_isOpposite :: forall p. IsPanel p => p -> Boolean
_isOpposite = getUnsafe [ "isOpposite" ]

_itemIndex :: forall p. IsPanel p => p -> Number
_itemIndex = getUnsafe [ "itemIndex" ]

_itemTemplate :: forall p @t. IsPanel p => IsPanel t => p -> Maybe t
_itemTemplate = toMaybe <<< getUnsafe [ "itemTemplate" ]

_leftIndex :: forall p. IsPanel p => p -> Number
_leftIndex = getUnsafe [ "leftIndex" ]

_padding :: forall p. IsPanel p => p -> Margin_
_padding = getUnsafe [ "padding" ]

-- Read-only
_rowCount :: forall p. IsPanel p => p -> Number
_rowCount = getUnsafe [ "rowCount" ]

_rowSizing :: forall p. IsPanel p => p -> EnumValue_
_rowSizing = getUnsafe [ "rowSizing" ]

_topIndex :: forall p. IsPanel p => p -> Number
_topIndex = getUnsafe [ "topIndex" ]

_viewboxStretch :: forall p. IsPanel p => p -> EnumValue_
_viewboxStretch = getUnsafe [ "viewboxStretch" ]

-- TODO: itemArray, itemCategoryProperty, itemTemplateMap
