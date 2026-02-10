-- | Unified Coordinated Interaction Framework
-- |
-- | This module provides a unified approach to coordinated interactions across
-- | multiple visualization components. It extends the existing CoordinatedHighlight
-- | pattern to support:
-- |
-- | - **Hover**: Highlight related elements across views (existing pattern)
-- | - **Brush**: Select elements within a region
-- | - **Selection**: Discrete set of selected items
-- | - **Focus**: Single focused item (e.g., clicked node)
-- |
-- | ## Design Principles
-- |
-- | 1. **Declarative**: Components declare how they respond to interactions
-- | 2. **Composable**: Multiple interaction types can coexist
-- | 3. **Framework-agnostic**: Works with Halogen, React, or vanilla JS
-- | 4. **Type-safe**: PureScript types ensure correct usage
-- |
-- | ## Example
-- |
-- | ```purescript
-- | -- Component A: Scatter plot
-- | registerCoordinated scatterElement
-- |   { identify: _.id
-- |   , respond: \trigger datum -> case trigger of
-- |       HoverTrigger id -> if datum.id == id then Primary else Dimmed
-- |       BrushTrigger box -> if inBox datum box then Selected else Neutral
-- |       _ -> Neutral
-- |   , group: Just "linked-views"
-- |   }
-- |
-- | -- Component B: Bar chart (same group, responds to same triggers)
-- | registerCoordinated barElement
-- |   { identify: _.category
-- |   , respond: \trigger datum -> ...
-- |   , group: Just "linked-views"
-- |   }
-- | ```
module Hylograph.Interaction.Coordinated
  ( -- * Interaction Triggers
    InteractionTrigger(..)
  , BoundingBox
  , emptyBox

    -- * Interaction State
  , InteractionState(..)
  , isHighlighted
  , isSelected

    -- * Configuration
  , CoordinatedConfig
  , simpleHover
  , withBrush
  , withSelection

    -- * Registration
  , CoordinatedHandle
  , registerCoordinated
  , emitTrigger
  , clearInteractions
  , mkHoverTrigger
  , mkBrushTrigger
  , mkClearTrigger
  , mkFocusTrigger

    -- * Utilities
  , pointInBox
  , boxesOverlap
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toNullable)
import Data.Set (Set)
import Data.Set as Set
import Effect (Effect)
import Web.DOM.Element (Element)

-- =============================================================================
-- Interaction Triggers
-- =============================================================================

-- | Bounding box for brush selections
-- |
-- | Coordinates are in the local coordinate system of the visualization.
type BoundingBox =
  { x0 :: Number  -- Left
  , y0 :: Number  -- Top
  , x1 :: Number  -- Right
  , y1 :: Number  -- Bottom
  }

-- | Empty bounding box (for clearing brush)
emptyBox :: BoundingBox
emptyBox = { x0: 0.0, y0: 0.0, x1: 0.0, y1: 0.0 }

-- | What triggered the interaction
-- |
-- | All components in a group receive the same trigger and respond based
-- | on their relationship to the triggering element/region.
data InteractionTrigger
  = HoverTrigger String
    -- ^ Element with given ID is being hovered
  | BrushTrigger BoundingBox
    -- ^ Region has been brush-selected
  | SelectionTrigger (Set String)
    -- ^ Discrete set of IDs are selected (e.g., from clicks)
  | FocusTrigger (Maybe String)
    -- ^ Single item is focused (clicked), Nothing to clear
  | ClearTrigger
    -- ^ Clear all interaction state

derive instance Eq InteractionTrigger

instance Show InteractionTrigger where
  show (HoverTrigger id) = "HoverTrigger " <> show id
  show (BrushTrigger box) = "BrushTrigger {" <> show box.x0 <> "," <> show box.y0 <> " → " <> show box.x1 <> "," <> show box.y1 <> "}"
  show (SelectionTrigger ids) = "SelectionTrigger " <> show (Set.size ids) <> " items"
  show (FocusTrigger mid) = "FocusTrigger " <> show mid
  show ClearTrigger = "ClearTrigger"

-- =============================================================================
-- Interaction State
-- =============================================================================

-- | How an element responds to the current interaction
-- |
-- | CSS classes are applied based on state:
-- | - Primary → `.coord-primary`
-- | - Related → `.coord-related`
-- | - Selected → `.coord-selected`
-- | - Dimmed → `.coord-dimmed`
-- | - Neutral → no class change
data InteractionState
  = Primary     -- Direct target of interaction (hovered element, focused item)
  | Related     -- Connected to primary (dependencies, same category)
  | Selected    -- Inside brush region or in selection set
  | Dimmed      -- Not related to current interaction
  | Neutral     -- Default state, no interaction active

derive instance Eq InteractionState
derive instance Ord InteractionState

instance Show InteractionState where
  show Primary = "Primary"
  show Related = "Related"
  show Selected = "Selected"
  show Dimmed = "Dimmed"
  show Neutral = "Neutral"

-- | Check if state represents any kind of highlighting
isHighlighted :: InteractionState -> Boolean
isHighlighted Primary = true
isHighlighted Related = true
isHighlighted _ = false

-- | Check if state represents selection
isSelected :: InteractionState -> Boolean
isSelected Selected = true
isSelected Primary = true  -- Primary is implicitly selected
isSelected _ = false

-- =============================================================================
-- Configuration
-- =============================================================================

-- | Configuration for coordinated interaction behavior
-- |
-- | The `respond` function is called for every element when any interaction
-- | occurs. It should be pure and fast since it runs on every hover/brush.
type CoordinatedConfig datum =
  { identify :: datum -> String
    -- ^ Extract unique ID from element's datum
  , respond :: InteractionTrigger -> datum -> InteractionState
    -- ^ Given current trigger, determine this element's state
  , group :: Maybe String
    -- ^ Group name for scoping (Nothing = global)
  , position :: Maybe (datum -> { x :: Number, y :: Number })
    -- ^ Optional: Extract position for brush hit-testing
  }

-- | Simple hover-only configuration
-- |
-- | Elements are Primary when hovered, Dimmed when something else is hovered,
-- | Neutral when nothing is hovered.
simpleHover :: forall datum. (datum -> String) -> CoordinatedConfig datum
simpleHover identify =
  { identify
  , respond: \trigger datum -> case trigger of
      HoverTrigger hoveredId ->
        if identify datum == hoveredId then Primary else Dimmed
      ClearTrigger -> Neutral
      _ -> Neutral
  , group: Nothing
  , position: Nothing
  }

-- | Add brush support to a configuration
-- |
-- | Elements inside the brush region become Selected.
withBrush
  :: forall datum
   . (datum -> { x :: Number, y :: Number })
  -> CoordinatedConfig datum
  -> CoordinatedConfig datum
withBrush getPos config = config
  { position = Just getPos
  , respond = \trigger datum -> case trigger of
      BrushTrigger box ->
        let pos = getPos datum
        in if pointInBox pos box then Selected else config.respond trigger datum
      _ -> config.respond trigger datum
  }

-- | Add discrete selection support to a configuration
-- |
-- | Elements whose ID is in the selection set become Selected.
withSelection :: forall datum. CoordinatedConfig datum -> CoordinatedConfig datum
withSelection config = config
  { respond = \trigger datum -> case trigger of
      SelectionTrigger ids ->
        if Set.member (config.identify datum) ids
          then Selected
          else config.respond trigger datum
      _ -> config.respond trigger datum
  }

-- =============================================================================
-- Handle (opaque type for cleanup)
-- =============================================================================

-- | Handle for managing coordinated interaction registration
-- |
-- | Use to unregister when component unmounts.
foreign import data CoordinatedHandle :: Type

-- =============================================================================
-- Utilities
-- =============================================================================

-- | Test if a point is inside a bounding box
pointInBox :: { x :: Number, y :: Number } -> BoundingBox -> Boolean
pointInBox { x, y } { x0, y0, x1, y1 } =
  x >= x0 && x <= x1 && y >= y0 && y <= y1

-- | Test if two bounding boxes overlap
boxesOverlap :: BoundingBox -> BoundingBox -> Boolean
boxesOverlap a b =
  a.x0 <= b.x1 && a.x1 >= b.x0 &&
  a.y0 <= b.y1 && a.y1 >= b.y0

-- =============================================================================
-- FFI
-- =============================================================================

-- | Convert InteractionState to Int for FFI
stateToInt :: InteractionState -> Int
stateToInt Primary = 0
stateToInt Related = 1
stateToInt Selected = 2
stateToInt Dimmed = 3
stateToInt Neutral = 4

-- | Register an element for coordinated interactions
-- |
-- | Returns an Effect that unregisters the element when called.
-- |
-- | ```purescript
-- | unregister <- registerCoordinated element config
-- | -- Later, on unmount:
-- | unregister
-- | ```
registerCoordinated
  :: forall datum
   . Element
  -> CoordinatedConfig datum
  -> Effect (Effect Unit)
registerCoordinated element config =
  registerCoordinated_
    element
    config.identify
    (\trigger datum -> stateToInt (config.respond trigger datum))
    (toNullable config.group)

-- | Emit a trigger to all elements in a group
-- |
-- | Used by brush handlers to dispatch brush regions.
emitTrigger :: Maybe String -> InteractionTrigger -> Effect Unit
emitTrigger group trigger = emitTrigger_ (toNullable group) trigger

-- | Clear all interaction state in a group
clearInteractions :: Maybe String -> Effect Unit
clearInteractions group = clearInteractions_ (toNullable group)

-- | Create a HoverTrigger
mkHoverTrigger :: String -> InteractionTrigger
mkHoverTrigger = mkHoverTrigger_

-- | Create a BrushTrigger
mkBrushTrigger :: BoundingBox -> InteractionTrigger
mkBrushTrigger = mkBrushTrigger_

-- | Create a ClearTrigger
mkClearTrigger :: InteractionTrigger
mkClearTrigger = mkClearTrigger_

-- | Create a FocusTrigger
mkFocusTrigger :: Maybe String -> InteractionTrigger
mkFocusTrigger = mkFocusTrigger_ <<< toNullable

-- FFI imports
foreign import registerCoordinated_
  :: forall datum
   . Element
  -> (datum -> String)
  -> (InteractionTrigger -> datum -> Int)
  -> Nullable String
  -> Effect (Effect Unit)

foreign import emitTrigger_
  :: Nullable String
  -> InteractionTrigger
  -> Effect Unit

foreign import clearInteractions_
  :: Nullable String
  -> Effect Unit

foreign import mkHoverTrigger_ :: String -> InteractionTrigger
foreign import mkBrushTrigger_ :: BoundingBox -> InteractionTrigger
foreign import mkClearTrigger_ :: InteractionTrigger
foreign import mkFocusTrigger_ :: Nullable String -> InteractionTrigger
