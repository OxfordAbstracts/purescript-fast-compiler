-- | Native Brush Implementation using Pointer Events
-- |
-- | This module provides brush selection behavior without D3 dependency.
-- | It integrates with `Hylograph.Interaction.Coordinated` for brush-and-link patterns.
-- |
-- | ## Basic Usage
-- |
-- | ```purescript
-- | import Hylograph.Interaction.Brush (attachNativeBrush, BrushHandle)
-- |
-- | -- Attach brush with callbacks
-- | handle <- attachNativeBrush svgElement extent
-- |   { onBrush: \box -> Console.log $ "Brushing: " <> show box
-- |   , onEnd: \maybeBox -> case maybeBox of
-- |       Just box -> Console.log "Selection complete"
-- |       Nothing -> Console.log "Cleared"
-- |   }
-- | ```
-- |
-- | ## Coordinated Usage
-- |
-- | For brush-and-link across multiple views:
-- |
-- | ```purescript
-- | import Hylograph.Interaction.Brush (attachCoordinatedBrush)
-- | import Hylograph.Interaction.Coordinated (registerCoordinated, withBrush)
-- |
-- | -- Register elements in both views
-- | for_ scatterPoints \el ->
-- |   registerCoordinated el (withBrush _.pos (simpleHover _.id))
-- |
-- | -- Attach brush to one view - it will emit BrushTrigger to all
-- | brushHandle <- attachCoordinatedBrush svgElement extent (Just "linked-views")
-- | ```
module Hylograph.Interaction.Brush
  ( -- * Types
    BrushHandle
  , BrushExtent
  , BrushSelection
  , BrushCallbacks

    -- * Basic Brush
  , attachNativeBrush

    -- * Coordinated Brush
  , attachCoordinatedBrush

    -- * Handle Operations
  , clearBrush
  , getBrushSelection
  , destroyBrush
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe, toNullable)
import Effect (Effect)
import Hylograph.Interaction.Coordinated (BoundingBox, InteractionTrigger, emitTrigger, mkBrushTrigger, mkClearTrigger)
import Web.DOM.Element (Element)

-- =============================================================================
-- Types
-- =============================================================================

-- | Opaque handle for controlling a brush
foreign import data BrushHandle :: Type

-- | Brush extent (the area where brushing is allowed)
type BrushExtent = BoundingBox

-- | Current brush selection (same as BoundingBox)
type BrushSelection = BoundingBox

-- | Callbacks for brush events
type BrushCallbacks =
  { onBrush :: BrushSelection -> Effect Unit
    -- ^ Called continuously during brushing
  , onEnd :: Maybe BrushSelection -> Effect Unit
    -- ^ Called when brush ends (Nothing if cleared/cancelled)
  }

-- =============================================================================
-- FFI
-- =============================================================================

foreign import attachNativeBrush_
  :: Element
  -> BrushExtent
  -> (BrushSelection -> Effect Unit)
  -> (Nullable BrushSelection -> Effect Unit)
  -> Effect BrushHandle

foreign import attachCoordinatedBrush_
  :: Element
  -> BrushExtent
  -> Nullable String
  -> (Nullable String -> InteractionTrigger -> Effect Unit)
  -> (BoundingBox -> InteractionTrigger)
  -> InteractionTrigger
  -> Effect BrushHandle

foreign import clearBrush_ :: BrushHandle -> Effect Unit
foreign import getBrushSelection_ :: BrushHandle -> Effect (Nullable BrushSelection)
foreign import destroyBrush_ :: BrushHandle -> Effect Unit

-- =============================================================================
-- Basic Brush
-- =============================================================================

-- | Attach a native brush to an SVG element
-- |
-- | The brush will:
-- | - Draw a selection rectangle when dragging on the SVG background
-- | - Call `onBrush` continuously with the current selection box
-- | - Call `onEnd` with the final selection (or Nothing if cancelled)
-- |
-- | The brush only activates when clicking on the SVG background or elements
-- | with class `brush-background`. This allows data elements to receive their
-- | own click/drag events.
attachNativeBrush :: Element -> BrushExtent -> BrushCallbacks -> Effect BrushHandle
attachNativeBrush element extent callbacks =
  attachNativeBrush_ element extent
    callbacks.onBrush
    (\nullable -> callbacks.onEnd (toMaybe nullable))

-- =============================================================================
-- Coordinated Brush
-- =============================================================================

-- | Attach a brush that integrates with the Coordinated framework
-- |
-- | This is the recommended way to use brush for linked views:
-- |
-- | 1. Register elements in all views with `registerCoordinated`
-- | 2. Use `withBrush` in the config to specify how elements get their position
-- | 3. Attach this brush to the view where brushing should occur
-- |
-- | The brush will automatically emit `BrushTrigger` to all elements in the
-- | specified group, causing them to update their `coord-selected` / `coord-dimmed`
-- | CSS classes.
attachCoordinatedBrush
  :: Element
  -> BrushExtent
  -> Maybe String  -- ^ Group name (Nothing for global)
  -> Effect BrushHandle
attachCoordinatedBrush element extent group =
  attachCoordinatedBrush_ element extent
    (toNullable group)
    (\g t -> emitTrigger (toMaybe g) t)
    mkBrushTrigger
    mkClearTrigger

-- =============================================================================
-- Handle Operations
-- =============================================================================

-- | Clear the brush selection programmatically
clearBrush :: BrushHandle -> Effect Unit
clearBrush = clearBrush_

-- | Get the current brush selection (if any)
getBrushSelection :: BrushHandle -> Effect (Maybe BrushSelection)
getBrushSelection handle = do
  nullable <- getBrushSelection_ handle
  pure (toMaybe nullable)

-- | Destroy the brush (remove event listeners and DOM elements)
-- |
-- | Call this when the component unmounts.
destroyBrush :: BrushHandle -> Effect Unit
destroyBrush = destroyBrush_
