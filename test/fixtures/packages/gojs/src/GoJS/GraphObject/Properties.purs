module GoJS.GraphObject.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn2, EffectFn3)
import GoJS.Diagram.Types (class IsDiagram, Diagram_, InputEvent_, Layer_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Margin_, Point_, Rect_, Size_, Spot_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsPanel, class IsPart, ContextMenu_, toContextMenu)
import GoJS.Unsafe (getUnsafe)

_actionCancel :: forall g d. IsGraphObject g => IsDiagram d => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_actionCancel = toMaybe <<< getUnsafe [ "actionCancel" ]

_actionDown :: forall g d. IsGraphObject g => IsDiagram d => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_actionDown = toMaybe <<< getUnsafe [ "actionDown" ]

_actionMove :: forall g d. IsGraphObject g => IsDiagram d => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_actionMove = toMaybe <<< getUnsafe [ "actionMove" ]

_actionUp :: forall g d. IsGraphObject g => IsDiagram d => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_actionUp = toMaybe <<< getUnsafe [ "actionUp" ]

-- Read-only
_actualBounds :: forall g. IsGraphObject g => g -> Rect_
_actualBounds = getUnsafe [ "actualBounds" ]

_alignment :: forall g. IsGraphObject g => g -> Spot_
_alignment = getUnsafe [ "alignment" ]

_alignmentFocus :: forall g. IsGraphObject g => g -> Spot_
_alignmentFocus = getUnsafe [ "alignmentFocus" ]

_angle :: forall g. IsGraphObject g => g -> Number
_angle = getUnsafe [ "angle" ]

_background :: forall g. IsGraphObject g => g -> String -- TODO: Could be Brush
_background = getUnsafe [ "background" ]

_click :: forall g d. IsDiagram d => IsGraphObject g => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_click = toMaybe <<< getUnsafe [ "click" ]

_contextClick :: forall g d. IsDiagram d => IsGraphObject g => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_contextClick = toMaybe <<< getUnsafe [ "contextClick" ]

_column :: forall g. IsGraphObject g => g -> Number
_column = getUnsafe [ "column" ]

_columnSpan :: forall g. IsGraphObject g => g -> Number
_columnSpan = getUnsafe [ "columnSpan" ]

_contextMenu :: forall g. IsGraphObject g => g -> Maybe ContextMenu_
_contextMenu = toContextMenu <<< getUnsafe [ "contextMenu" ]

_cursor :: forall g. IsGraphObject g => g -> String
_cursor = getUnsafe [ "cursor" ]

_desiredSize :: forall g. IsGraphObject g => g -> Size_
_desiredSize = getUnsafe [ "desiredSize" ]

-- Read-only
-- TODO: Can be null, but in the vast majority of cases is not.
_diagram :: forall g. IsGraphObject g => g -> Diagram_
_diagram = getUnsafe [ "diagram" ]

_doubleClick :: forall g d. IsDiagram d => IsGraphObject g => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_doubleClick = toMaybe <<< getUnsafe [ "doubleClick" ]

_enabledChanged :: forall g. IsGraphObject g => g -> Maybe (EffectFn2 g Boolean Unit)
_enabledChanged = toMaybe <<< getUnsafe [ "enabledChanged" ]

_fromEndSegmentLength :: forall g. IsGraphObject g => g -> Number
_fromEndSegmentLength = getUnsafe [ "fromEndSegmentLength" ]

_fromLinkable :: forall g. IsGraphObject g => g -> Boolean
_fromLinkable = getUnsafe [ "fromLinkable" ]

_fromLinkableDuplicates :: forall g. IsGraphObject g => g -> Boolean
_fromLinkableDuplicates = getUnsafe [ "fromLinkableDuplicates" ]

_fromLinkableSelfNode :: forall g. IsGraphObject g => g -> Boolean
_fromLinkableSelfNode = getUnsafe [ "fromLinkableSelfNode" ]

_fromMaxLinks :: forall g. IsGraphObject g => g -> Number
_fromMaxLinks = getUnsafe [ "fromMaxLinks" ]

_fromShortLength :: forall g. IsGraphObject g => g -> Number
_fromShortLength = getUnsafe [ "fromShortLength" ]

_fromSpot :: forall g. IsGraphObject g => g -> Spot_
_fromSpot = getUnsafe [ "fromSpot" ]

_height :: forall g. IsGraphObject g => g -> Number
_height = getUnsafe [ "height" ]

_isActionable :: forall g. IsGraphObject g => g -> Boolean
_isActionable = getUnsafe [ "isActionable" ]

_isPanelMain :: forall g. IsGraphObject g => g -> Boolean
_isPanelMain = getUnsafe [ "isPanelMain" ]

-- Read-only
_layer :: forall g. IsGraphObject g => g -> Layer_
_layer = getUnsafe [ "layer" ]

_margin :: forall g. IsGraphObject g => g -> Margin_
_margin = getUnsafe [ "margin" ]

_maxSize :: forall g. IsGraphObject g => g -> Size_
_maxSize = getUnsafe [ "maxSize" ]

-- Read-only
_measuredBounds :: forall g. IsGraphObject g => g -> Rect_
_measuredBounds = getUnsafe [ "measuredBounds" ]

_minSize :: forall g. IsGraphObject g => g -> Size_
_minSize = getUnsafe [ "minSize" ]

_mouseDragEnter :: forall g1 g2 d. IsDiagram d => IsGraphObject g1 => IsGraphObject g2 => g1 -> Maybe (EffectFn3 (InputEvent_ d) g1 g2 Unit)
_mouseDragEnter = toMaybe <<< getUnsafe [ "mouseDragEnter" ]

_mouseDragLeave :: forall g1 g2 d. IsDiagram d => IsGraphObject g1 => IsGraphObject g2 => g1 -> Maybe (EffectFn3 (InputEvent_ d) g1 g2 Unit)
_mouseDragLeave = toMaybe <<< getUnsafe [ "mouseDragLeave" ]

_mouseDrop :: forall g d. IsDiagram d => IsGraphObject g => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_mouseDrop = toMaybe <<< getUnsafe [ "mouseDrop" ]

_mouseEnter :: forall g1 g2 d. IsDiagram d => IsGraphObject g1 => IsGraphObject g2 => g1 -> Maybe (EffectFn3 (InputEvent_ d) g1 g2 Unit)
_mouseEnter = toMaybe <<< getUnsafe [ "mouseEnter" ]

_mouseHold :: forall g d. IsDiagram d => IsGraphObject g => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_mouseHold = toMaybe <<< getUnsafe [ "mouseHold" ]

_mouseHover :: forall g d. IsDiagram d => IsGraphObject g => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_mouseHover = toMaybe <<< getUnsafe [ "mouseHover" ]

_mouseLeave :: forall g1 g2 d. IsDiagram d => IsGraphObject g1 => IsGraphObject g2 => g1 -> Maybe (EffectFn3 (InputEvent_ d) g1 g2 Unit)
_mouseLeave = toMaybe <<< getUnsafe [ "mouseLeave" ]

_mouseOver :: forall g d. IsDiagram d => IsGraphObject g => g -> Maybe (EffectFn2 (InputEvent_ d) g Unit)
_mouseOver = toMaybe <<< getUnsafe [ "mouseOver" ]

_name :: forall g. IsGraphObject g => g -> String
_name = getUnsafe [ "name" ]

-- Read-only
_naturalBounds :: forall g. IsGraphObject g => g -> Rect_
_naturalBounds = getUnsafe [ "naturalBounds" ]

_opacity :: forall g. IsGraphObject g => g -> Number
_opacity = getUnsafe [ "opacity" ]

-- Read-only
_panel :: forall g @p. IsGraphObject g => IsPanel p => g -> Maybe p
_panel = toMaybe <<< getUnsafe [ "panel" ]

-- Read-only
_part :: forall g @p. IsGraphObject g => IsPart p => g -> Maybe p
_part = toMaybe <<< getUnsafe [ "part" ]

_pickable :: forall g. IsGraphObject g => g -> Boolean
_pickable = getUnsafe [ "pickable" ]

_portId :: forall g. IsGraphObject g => g -> Maybe String
_portId = toMaybe <<< getUnsafe [ "portId" ]

_position :: forall g. IsGraphObject g => g -> Point_
_position = getUnsafe [ "position" ]

_row :: forall g. IsGraphObject g => g -> Number
_row = getUnsafe [ "row" ]

_rowSpan :: forall g. IsGraphObject g => g -> Number
_rowSpan = getUnsafe [ "rowSpan" ]

_scale :: forall g. IsGraphObject g => g -> Number
_scale = getUnsafe [ "scale" ]

_segmentFraction :: forall g. IsGraphObject g => g -> Number
_segmentFraction = getUnsafe [ "segmentFraction" ]

_segmentIndex :: forall g. IsGraphObject g => g -> Number
_segmentIndex = getUnsafe [ "segmentIndex" ]

_segmentOffset :: forall g. IsGraphObject g => g -> Point_
_segmentOffset = getUnsafe [ "segmentOffset" ]

_segmentOrientation :: forall g. IsGraphObject g => g -> EnumValue_
_segmentOrientation = getUnsafe [ "segmentOrientation" ]

_shadowVisible :: forall g. IsGraphObject g => g -> Boolean
_shadowVisible = getUnsafe [ "shadowVisible" ]

_stretch :: forall g. IsGraphObject g => g -> EnumValue_
_stretch = getUnsafe [ "stretch" ]

_toEndSegmentLength :: forall g. IsGraphObject g => g -> Number
_toEndSegmentLength = getUnsafe [ "toEndSegmentLength" ]

_toLinkable :: forall g. IsGraphObject g => g -> Boolean
_toLinkable = getUnsafe [ "toLinkable" ]

_toLinkableDuplicates :: forall g. IsGraphObject g => g -> Boolean
_toLinkableDuplicates = getUnsafe [ "toLinkableDuplicates" ]

_toLinkableSelfNode :: forall g. IsGraphObject g => g -> Boolean
_toLinkableSelfNode = getUnsafe [ "toLinkableSelfNode" ]

_toMaxLinks :: forall g. IsGraphObject g => g -> Number
_toMaxLinks = getUnsafe [ "toMaxLinks" ]

_toShortLengh :: forall g. IsGraphObject g => g -> Number
_toShortLengh = getUnsafe [ "toShortLengh" ]

_toSpot :: forall g. IsGraphObject g => g -> Spot_
_toSpot = getUnsafe [ "toSpot" ]

-- TODO: ToolTip has the same type as ContextMenu, perhaps change the type's name.
_toolTip :: forall g. IsGraphObject g => g -> Maybe ContextMenu_
_toolTip = toContextMenu <<< getUnsafe [ "toolTip" ]

_visible :: forall g. IsGraphObject g => g -> Boolean
_visible = getUnsafe [ "visible" ]

_width :: forall g. IsGraphObject g => g -> Number
_width = getUnsafe [ "width" ]
