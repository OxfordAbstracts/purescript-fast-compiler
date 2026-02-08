-- | Zoom and Pan support for Canvas
-- |
-- | Provides event subscriptions and transform helpers for implementing
-- | zoom/pan interactions on Canvas visualizations.
module Hylograph.Canvas.Zoom
  ( -- * Event Types
    ZoomEvent
  , DragState
  , DragEvent
    -- * Event Subscriptions
  , subscribeWheel
  , subscribeDrag
  , Unsubscribe
    -- * Transform Helpers
  , zoomAt
  , pan
  , screenToWorld
  , worldToScreen
  ) where

import Prelude

import Effect (Effect)
import Hylograph.Canvas (CanvasContext, CanvasElement, Transform, getCanvasElement)

-- =============================================================================
-- Types
-- =============================================================================

-- | Zoom event from mouse wheel
-- | delta: zoom factor (< 1 = zoom out, > 1 = zoom in)
-- | x, y: mouse position relative to canvas
type ZoomEvent =
  { delta :: Number
  , x :: Number
  , y :: Number
  }

-- | Drag event for panning
-- | dx, dy: movement delta since last event
type DragEvent =
  { dx :: Number
  , dy :: Number
  }

-- | Internal drag state (start position, button pressed)
type DragState =
  { startX :: Number
  , startY :: Number
  , lastX :: Number
  , lastY :: Number
  , active :: Boolean
  }

-- | Function to unsubscribe from events
type Unsubscribe = Effect Unit

-- =============================================================================
-- FFI Declarations
-- =============================================================================

-- | Subscribe to wheel events for zooming
foreign import subscribeWheel_ :: CanvasElement -> (ZoomEvent -> Effect Unit) -> Effect Unsubscribe

-- | Subscribe to drag events for panning
foreign import subscribeDrag_ :: CanvasElement -> (DragEvent -> Effect Unit) -> Effect Unsubscribe

-- =============================================================================
-- Public API
-- =============================================================================

-- | Subscribe to wheel events on a canvas context
subscribeWheel :: CanvasContext -> (ZoomEvent -> Effect Unit) -> Effect Unsubscribe
subscribeWheel ctx callback = do
  element <- getCanvasElement ctx
  subscribeWheel_ element callback

-- | Subscribe to drag events on a canvas context
subscribeDrag :: CanvasContext -> (DragEvent -> Effect Unit) -> Effect Unsubscribe
subscribeDrag ctx callback = do
  element <- getCanvasElement ctx
  subscribeDrag_ element callback

-- =============================================================================
-- Transform Helpers
-- =============================================================================

-- | Apply a zoom event to a transform, zooming toward the mouse position
-- | This keeps the point under the mouse stationary during zoom
zoomAt :: ZoomEvent -> Transform -> Transform
zoomAt event t =
  let
    -- New scale
    newScale = t.scale * event.delta

    -- Clamp scale to reasonable bounds
    clampedScale = max 0.1 (min 10.0 newScale)

    -- Calculate the world point under the mouse before zoom
    -- (mouse position in canvas coords, adjusted for current transform)
    worldX = (event.x - t.translateX) / t.scale
    worldY = (event.y - t.translateY) / t.scale

    -- Calculate new translation to keep world point under mouse
    newTranslateX = event.x - worldX * clampedScale
    newTranslateY = event.y - worldY * clampedScale
  in
    { scale: clampedScale
    , translateX: newTranslateX
    , translateY: newTranslateY
    }

-- | Apply a drag event to a transform (panning)
pan :: DragEvent -> Transform -> Transform
pan event t =
  { scale: t.scale
  , translateX: t.translateX + event.dx
  , translateY: t.translateY + event.dy
  }

-- | Convert screen coordinates to world coordinates
screenToWorld :: Transform -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
screenToWorld t point =
  { x: (point.x - t.translateX) / t.scale
  , y: (point.y - t.translateY) / t.scale
  }

-- | Convert world coordinates to screen coordinates
worldToScreen :: Transform -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
worldToScreen t point =
  { x: point.x * t.scale + t.translateX
  , y: point.y * t.scale + t.translateY
  }
