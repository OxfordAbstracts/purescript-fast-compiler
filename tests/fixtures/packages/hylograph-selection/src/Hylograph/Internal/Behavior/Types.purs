-- | Internal: Types for declarative behavior configuration.
-- |
-- | Provides ADTs for configuring user interactions:
-- | - `Behavior`: Sum type for all supported behaviors
-- | - `ZoomConfig` / `DragConfig`: Configuration records
-- | - `ScaleExtent`: Zoom level bounds
-- | - Mouse event handlers with info/datum access
-- | - Coordinated highlighting configuration
-- |
-- | **Internal module** - these types are re-exported by `Hylograph.Behavior`.
module Hylograph.Internal.Behavior.Types
  ( Behavior(..)
  , ZoomConfig(..)
  , DragConfig(..)
  , ScaleExtent(..)
  , simulationDragNested
  , defaultDrag
  , simulationDrag
  , defaultZoom
  , onClick
  , onClickWithDatum
  , onMouseEnter
  , onMouseLeave
  , HighlightStyle
  , onHover
  , MouseEventInfo
  , onMouseMoveWithInfo
  , onMouseEnterWithInfo
  , onMouseLeaveWithInfo
  , onMouseDown
  , onMouseDownWithInfo
  -- Tier 2: Coordinated highlighting
  , HighlightClass(..)
  , TooltipTrigger(..)
  , TooltipConfig
  , CoordinatedHighlightConfig
  , onCoordinatedHighlight
  ) where

import Prelude

import Data.Maybe (Maybe)
import Effect (Effect)

-- | Scale extent for zoom (min and max zoom levels)
-- |
-- | Example:
-- | - `ScaleExtent 0.5 4.0` allows zooming from 50% to 400%
-- | - `ScaleExtent 1.0 1.0` disables zoom (fixed at 100%)
data ScaleExtent = ScaleExtent Number Number

-- | Style changes for hover highlight effect
-- |
-- | Specifies attribute name-value pairs to apply on enter and leave.
-- | Uses String values for simplicity (works with any attribute type).
-- |
-- | Example:
-- | ```purescript
-- | highlightStyle = { enter: [Tuple "stroke" "#333", Tuple "stroke-width" "3"]
-- |                  , leave: [Tuple "stroke" "#ddd", Tuple "stroke-width" "1.5"]
-- |                  }
-- | ```
type HighlightStyle =
  { enter :: Array { attr :: String, value :: String }
  , leave :: Array { attr :: String, value :: String }
  }

-- | Mouse event information with position data
-- |
-- | Provides both page-relative and element-relative coordinates.
-- |
-- | - `clientX`/`clientY`: Position relative to viewport
-- | - `pageX`/`pageY`: Position relative to document (for tooltip positioning)
-- | - `offsetX`/`offsetY`: Position relative to target element
type MouseEventInfo datum =
  { datum :: datum
  , clientX :: Number
  , clientY :: Number
  , pageX :: Number
  , pageY :: Number
  , offsetX :: Number
  , offsetY :: Number
  }

-- =============================================================================
-- Tier 2: Coordinated Highlighting
-- =============================================================================

-- | Classification of an element's highlight state
-- |
-- | When an element is hovered, ALL elements with CoordinatedHighlight behavior
-- | are classified based on their relationship to the hovered element.
-- |
-- | - `Primary`: The hovered element itself
-- | - `Related`: Connected/related to the hovered element
-- | - `Upstream`: Dependencies (things this element depends on)
-- | - `Downstream`: Dependents (things that depend on this element)
-- | - `Dimmed`: Not related (de-emphasized)
-- | - `Neutral`: No highlight state change (default appearance)
data HighlightClass
  = Primary     -- The hovered element (receives .highlight-primary)
  | Related     -- Related elements (receives .highlight-related)
  | Upstream    -- Dependencies (receives .highlight-upstream)
  | Downstream  -- Dependents (receives .highlight-downstream)
  | Dimmed      -- Unrelated elements (receives .highlight-dimmed)
  | Neutral     -- No change (no class added)

derive instance Eq HighlightClass

instance Show HighlightClass where
  show Primary = "Primary"
  show Related = "Related"
  show Upstream = "Upstream"
  show Downstream = "Downstream"
  show Dimmed = "Dimmed"
  show Neutral = "Neutral"

-- | When to show a tooltip
-- |
-- | - `OnHover`: Traditional tooltip - only when mouse is directly over element
-- | - `WhenPrimary`: Show when this element becomes Primary (from any view's hover)
-- | - `WhenRelated`: Show when this element becomes Related (use judiciously!)
data TooltipTrigger
  = OnHover      -- Only when mouse is directly over this element
  | WhenPrimary  -- When this element becomes Primary (direct label)
  | WhenRelated  -- When this element becomes Related

derive instance Eq TooltipTrigger

instance Show TooltipTrigger where
  show OnHover = "OnHover"
  show WhenPrimary = "WhenPrimary"
  show WhenRelated = "WhenRelated"

-- | Tooltip configuration for coordinated highlighting
-- |
-- | - `content`: Function to generate tooltip text from datum
-- | - `showWhen`: Condition for showing the tooltip
type TooltipConfig datum =
  { content :: datum -> String
  , showWhen :: TooltipTrigger
  }

-- | Configuration for coordinated highlighting
-- |
-- | - `identify`: Extract a unique identity string from the datum
-- | - `classify`: Given the hovered id and this element's datum, return highlight class
-- | - `group`: Optional group name to scope highlighting (default: global)
-- | - `tooltip`: Optional tooltip configuration
-- |
-- | Example:
-- | ```purescript
-- | config :: CoordinatedHighlightConfig MyNode
-- | config =
-- |   { identify: _.name
-- |   , classify: \hoveredId datum ->
-- |       if datum.name == hoveredId then Primary
-- |       else if hoveredId `elem` datum.connections then Related
-- |       else Dimmed
-- |   , group: Nothing  -- global coordination
-- |   , tooltip: Just { content: _.name, showWhen: OnHover }
-- |   }
-- | ```
type CoordinatedHighlightConfig datum =
  { identify :: datum -> String
  , classify :: String -> datum -> HighlightClass
  , group :: Maybe String  -- Optional group name to scope coordination
  , tooltip :: Maybe (TooltipConfig datum)  -- Optional tooltip
  }

derive instance Eq ScaleExtent
derive instance Ord ScaleExtent

instance Show ScaleExtent where
  show (ScaleExtent min max) = "ScaleExtent " <> show min <> " " <> show max

-- | Zoom behavior configuration
-- |
-- | The `target` is the selection that will be transformed when zooming.
-- | Typically this is an inner <g> element, while the zoom behavior is
-- | attached to the outer <svg> element.
-- |
-- | Example:
-- | ```purescript
-- | zoomConfig = ZoomConfig
-- |   { scaleExtent: ScaleExtent 0.5 4.0  -- 50% to 400%
-- |   , targetSelector: ".zoom-group"      -- What to transform
-- |   }
-- | ```
newtype ZoomConfig = ZoomConfig
  { scaleExtent :: ScaleExtent
  , targetSelector :: String  -- CSS selector for the element to transform
  }

derive instance Eq ZoomConfig
derive instance Ord ZoomConfig

instance Show ZoomConfig where
  show (ZoomConfig cfg) =
    "ZoomConfig { scaleExtent: " <> show cfg.scaleExtent
    <> ", targetSelector: " <> show cfg.targetSelector <> " }"

-- | Drag behavior configuration
-- |
-- | - `SimpleDrag`: Basic dragging with transform
-- | - `SimulationDrag`: Drag with force simulation reheat (datum IS the simulation node)
-- | - `SimulationDragNested`: Drag where datum has a `.node` field containing the simulation node
data DragConfig
  = SimpleDrag
  | SimulationDrag String  -- Simulation ID, datum IS the node
  | SimulationDragNested String  -- Simulation ID, datum.node IS the node

derive instance Eq DragConfig
derive instance Ord DragConfig

instance Show DragConfig where
  show SimpleDrag = "SimpleDrag"
  show (SimulationDrag id) = "SimulationDrag " <> show id
  show (SimulationDragNested id) = "SimulationDragNested " <> show id

-- | Behaviors that can be attached to selections
-- |
-- | Parameterized by datum type to enable typed event handlers.
-- |
-- | **Tier 1 (element-local):**
-- | - `Zoom`: Pan and zoom with mouse/touch
-- | - `Drag`: Drag elements with mouse/touch (simple or simulation-aware)
-- | - `Click`: Click handler without datum access
-- | - `ClickWithDatum`: Click handler with typed datum access
-- | - `MouseEnter`/`MouseLeave`: Hover handlers with datum access
-- | - `Highlight`: Simple style changes on hover (Tier 1)
-- |
-- | **Tier 2 (coordinated across views):**
-- | - `CoordinatedHighlight`: Cross-view synchronized highlighting
data Behavior datum
  = Zoom ZoomConfig
  | Drag DragConfig
  | Click (Effect Unit)
  | ClickWithDatum (datum -> Effect Unit)
  | MouseEnter (datum -> Effect Unit)
  | MouseLeave (datum -> Effect Unit)
  | Highlight HighlightStyle  -- Tier 1: simple hover highlighting with style changes
  | CoordinatedHighlight (CoordinatedHighlightConfig datum)  -- Tier 2: cross-view coordination
  | MouseMoveWithInfo (MouseEventInfo datum -> Effect Unit)
  | MouseEnterWithInfo (MouseEventInfo datum -> Effect Unit)
  | MouseLeaveWithInfo (MouseEventInfo datum -> Effect Unit)
  | MouseDown (Effect Unit)  -- Mouse down without datum
  | MouseDownWithInfo (MouseEventInfo datum -> Effect Unit)  -- Mouse down with position info

-- Note: Can't derive Eq/Ord for function types
-- We only show structure, not function contents
instance Show (Behavior datum) where
  show (Zoom cfg) = "Zoom " <> show cfg
  show (Drag cfg) = "Drag " <> show cfg
  show (Click _) = "Click <handler>"
  show (ClickWithDatum _) = "ClickWithDatum <handler>"
  show (MouseEnter _) = "MouseEnter <handler>"
  show (MouseLeave _) = "MouseLeave <handler>"
  show (Highlight _) = "Highlight <styles>"
  show (CoordinatedHighlight _) = "CoordinatedHighlight <config>"
  show (MouseMoveWithInfo _) = "MouseMoveWithInfo <handler>"
  show (MouseEnterWithInfo _) = "MouseEnterWithInfo <handler>"
  show (MouseLeaveWithInfo _) = "MouseLeaveWithInfo <handler>"
  show (MouseDown _) = "MouseDown <handler>"
  show (MouseDownWithInfo _) = "MouseDownWithInfo <handler>"

-- | Default drag configuration
-- |
-- | Enables simple drag on the element with default D3 settings.
defaultDrag :: DragConfig
defaultDrag = SimpleDrag

-- | Simulation-aware drag configuration
-- |
-- | Enables drag with force simulation reheat.
-- | When dragging starts, simulation alpha is increased to reheat.
-- | When dragging ends, simulation cools back down.
-- |
-- | Example:
-- | ```purescript
-- | nodeCircles <- append Circle [...] nodeEnter
-- | _ <- on (Drag $ simulationDrag "lesmis") nodeCircles
-- | ```
simulationDrag :: String -> DragConfig
simulationDrag = SimulationDrag

-- | Simulation-aware drag for nested datum structures
-- |
-- | Like simulationDrag, but for when the bound datum has a `.node` field
-- | containing the actual simulation node. This is useful when you're binding
-- | a wrapper type (like RenderNode) that contains the simulation node.
-- |
-- | The drag behavior will set `datum.node.fx/fy` instead of `datum.fx/fy`.
-- |
-- | Example:
-- | ```purescript
-- | -- RenderNode has { node :: SimulationNode, ... }
-- | _ <- on (Drag $ simulationDragNested "lesmis-gup") nodeCircles
-- | ```
simulationDragNested :: String -> DragConfig
simulationDragNested = SimulationDragNested

-- | Default zoom configuration
-- |
-- | Requires you to specify:
-- | - Scale extent (min/max zoom)
-- | - Target selector (what element to transform)
-- |
-- | Example:
-- | ```purescript
-- | zoom <- on (Zoom $ defaultZoom (ScaleExtent 0.5 4.0) ".zoom-group") svg
-- | ```
defaultZoom :: ScaleExtent -> String -> ZoomConfig
defaultZoom scaleExtent targetSelector = ZoomConfig { scaleExtent, targetSelector }

-- | Click handler without datum access
-- |
-- | Use when you don't need the data bound to the clicked element.
-- |
-- | Example:
-- | ```purescript
-- | button <- append Circle [radius 20.0] container
-- | _ <- on (onClick (log "Button clicked!")) button
-- | ```
onClick :: forall datum. Effect Unit -> Behavior datum
onClick = Click

-- | Click handler with typed datum access
-- |
-- | The datum is recovered from the DOM element using D3's `__data__` property.
-- | Type safety is preserved through the Selection's phantom type parameter.
-- |
-- | Example:
-- | ```purescript
-- | type CircleData = { id :: Int, color :: String }
-- |
-- | circles <- append Circle [...] (joinData data)
-- | _ <- on (onClickWithDatum \d -> log ("Clicked circle: " <> show d.id)) circles
-- | ```
onClickWithDatum :: forall datum. (datum -> Effect Unit) -> Behavior datum
onClickWithDatum = ClickWithDatum

-- | Mouse enter handler with typed datum access
-- |
-- | Fires when mouse enters the element. Does not bubble.
-- | Useful for hover effects like highlighting.
-- |
-- | Example:
-- | ```purescript
-- | lines <- joinData "lines" "path" series (\s -> ...)
-- | _ <- on (onMouseEnter \s -> log ("Hovered: " <> s.division)) lines
-- | ```
onMouseEnter :: forall datum. (datum -> Effect Unit) -> Behavior datum
onMouseEnter = MouseEnter

-- | Mouse leave handler with typed datum access
-- |
-- | Fires when mouse leaves the element. Does not bubble.
-- | Pair with onMouseEnter for hover effects.
-- |
-- | Example:
-- | ```purescript
-- | _ <- on (onMouseLeave \_ -> resetHighlight) lines
-- | ```
onMouseLeave :: forall datum. (datum -> Effect Unit) -> Behavior datum
onMouseLeave = MouseLeave

-- | Hover highlight behavior
-- |
-- | Applies style changes on mouse enter and resets on mouse leave.
-- | Also raises the element to front on hover.
-- |
-- | Example:
-- | ```purescript
-- | _ <- on (onHover
-- |   { enter: [{ attr: "stroke", value: "#333" }, { attr: "stroke-width", value: "3" }]
-- |   , leave: [{ attr: "stroke", value: "#ddd" }, { attr: "stroke-width", value: "1.5" }]
-- |   }) lines
-- | ```
onHover :: forall datum. HighlightStyle -> Behavior datum
onHover = Highlight

-- | Mouse move handler with full event info
-- |
-- | Fires continuously as mouse moves over the element.
-- | Provides datum and mouse coordinates for tooltips, crosshairs, etc.
-- |
-- | Example:
-- | ```purescript
-- | _ <- on (onMouseMoveWithInfo \info -> do
-- |   -- info.datum is the bound data
-- |   -- info.pageX/pageY for tooltip positioning
-- |   -- info.offsetX/offsetY for data lookup
-- |   updateTooltip info.datum info.pageX info.pageY
-- | ) lines
-- | ```
onMouseMoveWithInfo :: forall datum. (MouseEventInfo datum -> Effect Unit) -> Behavior datum
onMouseMoveWithInfo = MouseMoveWithInfo

-- | Mouse enter handler with full event info
-- |
-- | Like onMouseEnter but also provides mouse coordinates.
onMouseEnterWithInfo :: forall datum. (MouseEventInfo datum -> Effect Unit) -> Behavior datum
onMouseEnterWithInfo = MouseEnterWithInfo

-- | Mouse leave handler with full event info
-- |
-- | Like onMouseLeave but also provides mouse coordinates.
onMouseLeaveWithInfo :: forall datum. (MouseEventInfo datum -> Effect Unit) -> Behavior datum
onMouseLeaveWithInfo = MouseLeaveWithInfo

-- | Mouse down handler without datum access
-- |
-- | Fires when mouse button is pressed on the element.
-- | Useful for starting drag operations.
onMouseDown :: forall datum. Effect Unit -> Behavior datum
onMouseDown = MouseDown

-- | Mouse down handler with full event info
-- |
-- | Fires when mouse button is pressed on the element.
-- | Provides datum and mouse coordinates for drag operations.
-- |
-- | Example:
-- | ```purescript
-- | _ <- on (onMouseDownWithInfo \info -> do
-- |   startDrag info.datum info.clientX
-- | ) element
-- | ```
onMouseDownWithInfo :: forall datum. (MouseEventInfo datum -> Effect Unit) -> Behavior datum
onMouseDownWithInfo = MouseDownWithInfo

-- =============================================================================
-- Tier 2: Coordinated Highlighting
-- =============================================================================

-- | Coordinated highlight behavior (Tier 2)
-- |
-- | Enables synchronized highlighting across multiple views. When any element
-- | with this behavior is hovered, ALL elements with CoordinatedHighlight
-- | receive CSS classes based on their relationship to the hovered element.
-- |
-- | CSS classes applied:
-- | - `.highlight-primary` - the hovered element
-- | - `.highlight-related` - elements related to hovered
-- | - `.highlight-dimmed` - unrelated elements
-- |
-- | Example:
-- | ```purescript
-- | -- Simple same-id highlighting across views
-- | _ <- on (onCoordinatedHighlight
-- |   { identify: _.moduleName
-- |   , classify: \hoveredId d ->
-- |       if d.moduleName == hoveredId then Primary
-- |       else Dimmed
-- |   , group: Nothing
-- |   }) bubblePackNodes
-- |
-- | -- Same config on chord arcs - they coordinate automatically
-- | _ <- on (onCoordinatedHighlight config) chordArcs
-- | ```
-- |
-- | For relationship-aware highlighting:
-- | ```purescript
-- | _ <- on (onCoordinatedHighlight
-- |   { identify: _.name
-- |   , classify: \hoveredId d ->
-- |       if d.name == hoveredId then Primary
-- |       else if hoveredId `elem` d.dependencies then Related
-- |       else Dimmed
-- |   , group: Nothing
-- |   }) nodes
-- | ```
onCoordinatedHighlight :: forall datum. CoordinatedHighlightConfig datum -> Behavior datum
onCoordinatedHighlight = CoordinatedHighlight
