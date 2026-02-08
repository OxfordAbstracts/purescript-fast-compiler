module GoJS.GraphObject.Panel.Part.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn1, EffectFn3)
import GoJS.Collection (Iterator_)
import GoJS.Diagram.Types (Layer_)
import GoJS.Geometry.Types (Point_, Size_, Spot_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsPart, Adornment_, Group_)
import GoJS.Key (Key, toKey)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_adornments :: forall p. IsPart p => p -> Iterator_ Adornment_
_adornments = getUnsafe [ "adornments" ]

_category :: forall p. IsPart p => p -> String
_category = getUnsafe [ "category" ]

_containingGroup :: forall p. IsPart p => p -> Maybe Group_
_containingGroup = toMaybe <<< getUnsafe [ "containingGroup" ]

_containingGroupChanged :: forall p. IsPart p => p -> Maybe (EffectFn3 p Group_ Group_ Unit)
_containingGroupChanged = toMaybe <<< getUnsafe [ "containingGroupChanged" ]

_copyable :: forall p. IsPart p => p -> Boolean
_copyable = getUnsafe [ "copyable" ]

_deletable :: forall p. IsPart p => p -> Boolean
_deletable = getUnsafe [ "deletable" ]

_dragComputation :: forall p. IsPart p => p -> Maybe (EffectFn3 p Point_ Point_ Point_)
_dragComputation = toMaybe <<< getUnsafe [ "dragComputation" ]

_groupable :: forall p. IsPart p => p -> Boolean
_groupable = getUnsafe [ "groupable" ]

_highlightedChanged :: forall p. IsPart p => p -> Maybe (EffectFn1 p Unit)
_highlightedChanged = toMaybe <<< getUnsafe [ "highlightedChanged" ]

_isAnimated :: forall p. IsPart p => p -> Boolean
_isAnimated = getUnsafe [ "isAnimated" ]

_isHighlighted :: forall p. IsPart p => p -> Boolean
_isHighlighted = getUnsafe [ "isHighlighted" ]

_isInDocumentBounds :: forall p. IsPart p => p -> Boolean
_isInDocumentBounds = getUnsafe [ "isInDocumentBounds" ]

_isLayoutPositioned :: forall p. IsPart p => p -> Boolean
_isLayoutPositioned = getUnsafe [ "isLayoutPositioned" ]

_isSelected :: forall p. IsPart p => p -> Boolean
_isSelected = getUnsafe [ "isSelected" ]

_isShadowed :: forall p. IsPart p => p -> Boolean
_isShadowed = getUnsafe [ "isShadowed" ]

-- Read-only
_isTopLevel :: forall p. IsPart p => p -> Boolean
_isTopLevel = getUnsafe [ "isTopLevel" ]

-- Read-only
_key :: forall p. IsPart p => p -> Key
_key = toKey <<< getUnsafe [ "key" ]

_layerChanged :: forall p. IsPart p => p -> Maybe (EffectFn3 p Layer_ Layer_ Unit)
_layerChanged = toMaybe <<< getUnsafe [ "layerChanged" ]

_layerName :: forall p. IsPart p => p -> String
_layerName = getUnsafe [ "layerName" ]

_layoutConditions :: forall p. IsPart p => p -> Number
_layoutConditions = getUnsafe [ "layoutConditions" ]

_location :: forall p. IsPart p => p -> Point_
_location = getUnsafe [ "location" ]

-- Read-only
_locationObject :: forall p @g. IsPart p => IsGraphObject g => p -> g
_locationObject = getUnsafe [ "locationObject" ]

_locationObjectName :: forall p. IsPart p => p -> String
_locationObjectName = getUnsafe [ "locationObjectName" ]

_locationSpot :: forall p. IsPart p => p -> Spot_
_locationSpot = getUnsafe [ "locationSpot" ]

_maxLocation :: forall p. IsPart p => p -> Spot_
_maxLocation = getUnsafe [ "maxLocation" ]

_minLocation :: forall p. IsPart p => p -> Spot_
_minLocation = getUnsafe [ "minLocation" ]

_movable :: forall p. IsPart p => p -> Boolean
_movable = getUnsafe [ "movable" ]

_reshapable :: forall p. IsPart p => p -> Boolean
_reshapable = getUnsafe [ "reshapable" ]

_resizable :: forall p. IsPart p => p -> Boolean
_resizable = getUnsafe [ "resizable" ]

_resizeAdornmentTemplate :: forall p. IsPart p => p -> Maybe Adornment_
_resizeAdornmentTemplate = toMaybe <<< getUnsafe [ "resizeAdornmentTemplate" ]

_resizeCellSize :: forall p. IsPart p => p -> Size_
_resizeCellSize = getUnsafe [ "resizeCellSize" ]

-- Read-only
_resizeObject :: forall p @g. IsPart p => IsGraphObject g => p -> g
_resizeObject = getUnsafe [ "resizeObject" ]

_resizeObjectName :: forall p. IsPart p => p -> String
_resizeObjectName = getUnsafe [ "resizeObjectName" ]

_rotatable :: forall p. IsPart p => p -> Boolean
_rotatable = getUnsafe [ "rotatable" ]

_rotateAdornmentTemplate :: forall p. IsPart p => p -> Adornment_
_rotateAdornmentTemplate = getUnsafe [ "rotateAdornmentTemplate" ]

-- Read-only
_rotateObject :: forall p @g. IsPart p => IsGraphObject g => p -> g
_rotateObject = getUnsafe [ "rotateObject" ]

_rotateObjectName :: forall p. IsPart p => p -> String
_rotateObjectName = getUnsafe [ "rotateObjectName" ]

_rotationSpot :: forall p. IsPart p => p -> Spot_
_rotationSpot = getUnsafe [ "rotationSpot" ]

_selectable :: forall p. IsPart p => p -> Boolean
_selectable = getUnsafe [ "selectable" ]

_selectionAdorned :: forall p. IsPart p => p -> Boolean
_selectionAdorned = getUnsafe [ "selectionAdorned" ]

_selectionAdornmentTemplate :: forall p. IsPart p => p -> Maybe Adornment_
_selectionAdornmentTemplate = toMaybe <<< getUnsafe [ "selectionAdornmentTemplate" ]

-- Read-only
_selectionObject :: forall p @g. IsPart p => IsGraphObject g => p -> g
_selectionObject = getUnsafe [ "selectionObject" ]

_selectionObjectName :: forall p. IsPart p => p -> String
_selectionObjectName = getUnsafe [ "selectionObjectName" ]

_shadowBlur :: forall p. IsPart p => p -> Number
_shadowBlur = getUnsafe [ "shadowBlur" ]

_shadowColor :: forall p. IsPart p => p -> String
_shadowColor = getUnsafe [ "shadowColor" ]

_shadowOffset :: forall p. IsPart p => p -> Point_
_shadowOffset = getUnsafe [ "shadowOffset" ]

_text :: forall p. IsPart p => p -> String
_text = getUnsafe [ "text" ]

_textEditable :: forall p. IsPart p => p -> Boolean
_textEditable = getUnsafe [ "textEditable" ]

_zOrder :: forall p. IsPart p => p -> Int
_zOrder = getUnsafe [ "zOrder" ]
