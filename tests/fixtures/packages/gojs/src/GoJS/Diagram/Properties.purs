module GoJS.Diagram.Properties where

import Prelude

import Data.Function.Uncurried (Fn2)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn1)
import GoJS.Collection (Iterator_, Map_, Set_)
import GoJS.Diagram.CommandHandler.Types (CommandHandler_)
import GoJS.Diagram.Types (class IsDiagram, AnimationManager_, InputEvent_, Layer_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Margin_, Point_, Rect_, Size_, Spot_)
import GoJS.GraphObject.Types (class IsPanel, class IsPart, Adornment_, ContextMenu_, Group_, Link_, Node_, Part_, toContextMenu)
import GoJS.Layout.Types (class IsLayout)
import GoJS.Model.Types (class IsModel, UndoManager_)
import GoJS.Tool.Types (ToolManager_, Tool_)
import GoJS.Unsafe (getUnsafe)
import Web.HTML (HTMLDivElement)

_allowClipboard :: forall d. IsDiagram d => d -> Boolean
_allowClipboard = getUnsafe [ "allowClipboard" ]

_allowCopy :: forall d. IsDiagram d => d -> Boolean
_allowCopy = getUnsafe [ "allowCopy" ]

_allowDelete :: forall d. IsDiagram d => d -> Boolean
_allowDelete = getUnsafe [ "allowDelete" ]

_allowDragOut :: forall d. IsDiagram d => d -> Boolean
_allowDragOut = getUnsafe [ "allowDragOut" ]

_allowDrop :: forall d. IsDiagram d => d -> Boolean
_allowDrop = getUnsafe [ "allowDrop" ]

_allowGroup :: forall d. IsDiagram d => d -> Boolean
_allowGroup = getUnsafe [ "allowGroup" ]

_allowHorizontalScroll :: forall d. IsDiagram d => d -> Boolean
_allowHorizontalScroll = getUnsafe [ "allowHorizontalScroll" ]

_allowInsert :: forall d. IsDiagram d => d -> Boolean
_allowInsert = getUnsafe [ "allowInsert" ]

_allowLink :: forall d. IsDiagram d => d -> Boolean
_allowLink = getUnsafe [ "allowLink" ]

_allowMove :: forall d. IsDiagram d => d -> Boolean
_allowMove = getUnsafe [ "allowMove" ]

_allowRelink :: forall d. IsDiagram d => d -> Boolean
_allowRelink = getUnsafe [ "allowRelink" ]

_allowReshape :: forall d. IsDiagram d => d -> Boolean
_allowReshape = getUnsafe [ "allowReshape" ]

_allowResize :: forall d. IsDiagram d => d -> Boolean
_allowResize = getUnsafe [ "allowResize" ]

_allowRotate :: forall d. IsDiagram d => d -> Boolean
_allowRotate = getUnsafe [ "allowRotate" ]

_allowSelect :: forall d. IsDiagram d => d -> Boolean
_allowSelect = getUnsafe [ "allowSelect" ]

_allowTextEdit :: forall d. IsDiagram d => d -> Boolean
_allowTextEdit = getUnsafe [ "allowTextEdit" ]

_allowUndo :: forall d. IsDiagram d => d -> Boolean
_allowUndo = getUnsafe [ "allowUndo" ]

_allowUngroup :: forall d. IsDiagram d => d -> Boolean
_allowUngroup = getUnsafe [ "allowUngroup" ]

_allowVerticalScroll :: forall d. IsDiagram d => d -> Boolean
_allowVerticalScroll = getUnsafe [ "allowVerticalScroll" ]

_allowZoom :: forall d. IsDiagram d => d -> Boolean
_allowZoom = getUnsafe [ "allowZoom" ]

-- Read-only
_animationManager :: forall d. IsDiagram d => d -> AnimationManager_
_animationManager = getUnsafe [ "animationManager" ]

_autoScale :: forall d. IsDiagram d => d -> EnumValue_
_autoScale = getUnsafe [ "autoScale" ]

_autoScrollInterval :: forall d. IsDiagram d => d -> Number
_autoScrollInterval = getUnsafe [ "autoScrollInterval" ]

_autoScrollRegion :: forall d. IsDiagram d => d -> Margin_
_autoScrollRegion = getUnsafe [ "autoScrollRegion" ]

_click :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_click = toMaybe <<< getUnsafe [ "click" ]

_commandHandler :: forall d. IsDiagram d => d -> CommandHandler_
_commandHandler = getUnsafe [ "commandHandler" ]

_contentAlignment :: forall d. IsDiagram d => d -> Spot_
_contentAlignment = getUnsafe [ "contentAlignment" ]

_contextClick :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_contextClick = toMaybe <<< getUnsafe [ "contextClick" ]

_contextMenu :: forall d. IsDiagram d => d -> Maybe ContextMenu_
_contextMenu = toContextMenu <<< getUnsafe [ "contextMenu" ]

_currentCursor :: forall d. IsDiagram d => d -> String
_currentCursor = getUnsafe [ "currentCursor" ]

_currentTool :: forall d. IsDiagram d => d -> Tool_
_currentTool = getUnsafe [ "currentTool" ]

_defaultCursor :: forall d. IsDiagram d => d -> String
_defaultCursor = getUnsafe [ "defaultCursor" ]

_defaultScale :: forall d. IsDiagram d => d -> Number
_defaultScale = getUnsafe [ "defaultScale" ]

_defaultTool :: forall d. IsDiagram d => d -> Tool_
_defaultTool = getUnsafe [ "defaultTool" ]

_div :: forall d. IsDiagram d => d -> HTMLDivElement
_div = getUnsafe [ "div" ]

-- Read-only
_documentBounds :: forall d. IsDiagram d => d -> Rect_
_documentBounds = getUnsafe [ "documentBounds" ]

_doubleClick :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_doubleClick = toMaybe <<< getUnsafe [ "doubleClick" ]

_firstInput :: forall d. IsDiagram d => d -> InputEvent_ d
_firstInput = getUnsafe [ "firstInput" ]

_fixedBounds :: forall d. IsDiagram d => d -> Rect_
_fixedBounds = getUnsafe [ "fixedBounds" ]

_grid :: forall d p. IsPanel p => IsDiagram d => d -> Maybe p
_grid = toMaybe <<< getUnsafe [ "grid" ]

_groupSelectionAdornmentTemplate :: forall d. IsDiagram d => d -> Maybe Adornment_
_groupSelectionAdornmentTemplate = toMaybe <<< getUnsafe [ "groupSelectionAdornmentTemplate" ]

_groupTemplate :: forall d. IsDiagram d => d -> Maybe Group_
_groupTemplate = toMaybe <<< getUnsafe [ "groupTemplate" ]

_groupTemplateMap :: forall d. IsDiagram d => d -> Maybe (Map_ String Group_)
_groupTemplateMap = toMaybe <<< getUnsafe [ "groupTemplateMap" ]

_handlesDragDropForTopLevelParts :: forall d. IsDiagram d => d -> Boolean
_handlesDragDropForTopLevelParts = getUnsafe [ "handlesDragDropForTopLevelParts" ]

_hasHorizontalScrollbar :: forall d. IsDiagram d => d -> Boolean
_hasHorizontalScrollbar = getUnsafe [ "hasHorizontalScrollbar" ]

_hasVerticalScrollbar :: forall d. IsDiagram d => d -> Boolean
_hasVerticalScrollbar = getUnsafe [ "hasVerticalScrollbar" ]

-- Read-only
_highlighteds :: forall d. IsDiagram d => d -> Set_ Part_
_highlighteds = getUnsafe [ "highlighteds" ]

_initialAutoScale :: forall d. IsDiagram d => d -> EnumValue_
_initialAutoScale = getUnsafe [ "initialAutoScale" ]

_initialContentAlignment :: forall d. IsDiagram d => d -> Spot_
_initialContentAlignment = getUnsafe [ "initialContentAlignment" ]

_initialDocumentSpot :: forall d. IsDiagram d => d -> Spot_
_initialDocumentSpot = getUnsafe [ "initialDocumentSpot" ]

_initialPosition :: forall d. IsDiagram d => d -> Point_
_initialPosition = getUnsafe [ "initialPosition" ]

_initialScale :: forall d. IsDiagram d => d -> Number
_initialScale = getUnsafe [ "initialScale" ]

_initialViewportSpot :: forall d. IsDiagram d => d -> Spot_
_initialViewportSpot = getUnsafe [ "initialViewportSpot" ]

_isEnabled :: forall d. IsDiagram d => d -> Boolean
_isEnabled = getUnsafe [ "isEnabled" ]

_isModelReadOnly :: forall d. IsDiagram d => d -> Boolean
_isModelReadOnly = getUnsafe [ "isModelReadOnly" ]

_isModified :: forall d. IsDiagram d => d -> Boolean
_isModified = getUnsafe [ "isModified" ]

_isMouseCaptured :: forall d. IsDiagram d => d -> Boolean
_isMouseCaptured = getUnsafe [ "isMouseCaptured" ]

_isReadOnly :: forall d. IsDiagram d => d -> Boolean
_isReadOnly = getUnsafe [ "isReadOnly" ]

_isTreePathToChildren :: forall d. IsDiagram d => d -> Boolean
_isTreePathToChildren = getUnsafe [ "isTreePathToChildren" ]

_lastInput :: forall d. IsDiagram d => d -> InputEvent_ d
_lastInput = getUnsafe [ "lastInput" ]

-- Read-only
_layers :: forall d. IsDiagram d => d -> Iterator_ Layer_
_layers = getUnsafe [ "layers" ]

_layout :: forall d @l. IsDiagram d => IsLayout l => d -> l
_layout = getUnsafe [ "layout" ]

_linkSelectionAdornmentTemplate :: forall d. IsDiagram d => d -> Maybe Adornment_
_linkSelectionAdornmentTemplate = toMaybe <<< getUnsafe [ "linkSelectionAdornmentTemplate" ]

_linkTemplate :: forall d. IsDiagram d => d -> Link_
_linkTemplate = getUnsafe [ "linkTemplate" ]

_linkTemplateMap :: forall d. IsDiagram d => d -> Maybe (Map_ String Link_)
_linkTemplateMap = toMaybe <<< getUnsafe [ "linkTemplateMap" ]

-- Read-only
_links :: forall d. IsDiagram d => d -> Iterator_ Link_
_links = getUnsafe [ "links" ]

_maxScale :: forall d. IsDiagram d => d -> Number
_maxScale = getUnsafe [ "maxScale" ]

_maxSelectionCount :: forall d. IsDiagram d => d -> Number
_maxSelectionCount = getUnsafe [ "maxSelectionCount" ]

_minScale :: forall d. IsDiagram d => d -> Number
_minScale = getUnsafe [ "minScale" ]

_model :: forall d @m. IsDiagram d => IsModel m => d -> m
_model = getUnsafe [ "model" ]

_mouseDragOver :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_mouseDragOver = toMaybe <<< getUnsafe [ "mouseDragOver" ]

_mouseDrop :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_mouseDrop = toMaybe <<< getUnsafe [ "mouseDrop" ]

_mouseEnter :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_mouseEnter = toMaybe <<< getUnsafe [ "mouseEnter" ]

_mouseHold :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_mouseHold = toMaybe <<< getUnsafe [ "mouseHold" ]

_mouseHover :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_mouseHover = toMaybe <<< getUnsafe [ "mouseHover" ]

_mouseLeave :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_mouseLeave = toMaybe <<< getUnsafe [ "mouseLeave" ]

_mouseOver :: forall d. IsDiagram d => d -> Maybe (EffectFn1 (InputEvent_ d) Unit)
_mouseOver = toMaybe <<< getUnsafe [ "mouseOver" ]

_nodeSelectionAdornmentTemplate :: forall d. IsDiagram d => d -> Maybe Adornment_
_nodeSelectionAdornmentTemplate = toMaybe <<< getUnsafe [ "nodeSelectionAdornmentTemplate" ]

-- Read-only
_nodeTemplate :: forall d @p. IsDiagram d => IsPart p => d -> p
_nodeTemplate = getUnsafe [ "nodeTemplate" ]

_nodeTemplateMap :: forall d. IsDiagram d => d -> Maybe (Map_ String Part_)
_nodeTemplateMap = toMaybe <<< getUnsafe [ "nodeTemplateMap" ]

-- Read-only
_nodes :: forall d. IsDiagram d => d -> Iterator_ Node_
_nodes = getUnsafe [ "nodes" ]

_opacity :: forall d. IsDiagram d => d -> Number
_opacity = getUnsafe [ "opacity" ]

_padding :: forall d. IsDiagram d => d -> Margin_
_padding = getUnsafe [ "padding" ]

-- Read-only
_parts :: forall d. IsDiagram d => d -> Iterator_ Part_
_parts = getUnsafe [ "parts" ]

_position :: forall d. IsDiagram d => d -> Point_
_position = getUnsafe [ "position" ]

_positionComputation :: forall d. IsDiagram d => d -> Maybe (Fn2 d Point_ Point_)
_positionComputation = toMaybe <<< getUnsafe [ "positionComputation" ]

_renderer :: forall d. IsDiagram d => d -> String
_renderer = getUnsafe [ "renderer" ]

_scale :: forall d. IsDiagram d => d -> Number
_scale = getUnsafe [ "scale" ]

_scaleComputation :: forall d. IsDiagram d => d -> Maybe (Fn2 d Number Number)
_scaleComputation = toMaybe <<< getUnsafe [ "scaleComputation" ]

_scrollHorizontalLineChange :: forall d. IsDiagram d => d -> Number
_scrollHorizontalLineChange = getUnsafe [ "scrollHorizontalLineChange" ]

_scrollMargin :: forall d. IsDiagram d => d -> Margin_
_scrollMargin = getUnsafe [ "scrollMargin" ]

_scrollMode :: forall d. IsDiagram d => d -> EnumValue_
_scrollMode = getUnsafe [ "scrollMode" ]

_scrollVerticalLineChange :: forall d. IsDiagram d => d -> Number
_scrollVerticalLineChange = getUnsafe [ "scrollVerticalLineChange" ]

_scrollsPageOnFocus :: forall d. IsDiagram d => d -> Boolean
_scrollsPageOnFocus = getUnsafe [ "scrollsPageOnFocus" ]

-- Read-only
_selection :: forall d. IsDiagram d => d -> Set_ Part_
_selection = getUnsafe [ "selection" ]

_skipsUndoManager :: forall d. IsDiagram d => d -> Boolean
_skipsUndoManager = getUnsafe [ "skipsUndoManager" ]

_toolManager :: forall d. IsDiagram d => d -> ToolManager_
_toolManager = getUnsafe [ "toolManager" ]

-- Read-only
_undoManager :: forall d. IsDiagram d => d -> UndoManager_
_undoManager = getUnsafe [ "undoManager" ]

_validCycle :: forall d. IsDiagram d => d -> EnumValue_
_validCycle = getUnsafe [ "validCycle" ]

_viewSize :: forall d. IsDiagram d => d -> Size_
_viewSize = getUnsafe [ "viewSize" ]

-- Read-only
_viewportBounds :: forall d. IsDiagram d => d -> Rect_
_viewportBounds = getUnsafe [ "viewportBounds" ]

_zoomPoint :: forall d. IsDiagram d => d -> Point_
_zoomPoint = getUnsafe [ "zoomPoint" ]
