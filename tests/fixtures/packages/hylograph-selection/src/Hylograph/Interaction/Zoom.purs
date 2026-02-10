-- | Native Zoom using Pointer Events (no D3 dependency)
-- |
-- | This module provides zoom and pan behavior using native browser events:
-- | - Wheel events for zoom
-- | - Pointer events for pan/drag
-- | - Gesture events for trackpad pinch (Safari)
-- |
-- | The zoom transform math is adapted from d3-zoom (ISC licensed).
-- |
-- | ## Usage
-- |
-- | ### Simple API (drop-in replacement for existing zoom)
-- |
-- | ```purescript
-- | import Hylograph.Interaction.Zoom (attachZoomNative)
-- |
-- | svgElement <- select "#my-svg"
-- | handle <- attachZoomNative svgElement
-- |   { scaleMin: 0.5, scaleMax: 4.0, targetSelector: ".zoom-group" }
-- |
-- | -- Later:
-- | handle.destroy
-- | ```
-- |
-- | ### With Initial Transform
-- |
-- | ```purescript
-- | handle <- attachZoomWithTransform svgElement
-- |   0.5 4.0 ".zoom-group" savedTransform
-- | ```
-- |
-- | ### With Callback
-- |
-- | ```purescript
-- | handle <- attachZoomWithCallback svgElement
-- |   0.5 4.0 ".zoom-group" initialTransform \t -> do
-- |     log $ "Scale: " <> show t.k
-- | ```
-- |
-- | ### Full Control
-- |
-- | ```purescript
-- | handle <- attachNativeZoom svgElement
-- |   { scaleMin: 0.1
-- |   , scaleMax: 10.0
-- |   , targetSelector: ".zoom-group"
-- |   , initialTransform: Just { k: 1.0, x: 0.0, y: 0.0 }
-- |   , translateExtent: Nothing
-- |   , onZoom: Just \t -> log $ "Zoom: " <> show t.k
-- |   }
-- |
-- | -- Programmatic zoom
-- | handle.zoomTo 2.0 { x: 400.0, y: 300.0 }
-- | handle.zoomBy 1.5
-- | handle.resetZoom
-- |
-- | -- Get current state
-- | t <- handle.getTransform
-- |
-- | -- Cleanup
-- | handle.destroy
-- | ```
module Hylograph.Interaction.Zoom
  ( -- * Types
    ZoomTransform
  , ZoomConfig
  , ZoomHandle
  , BoundingBox
  , Point
    -- * Native Zoom API
  , attachNativeZoom
    -- * Simplified API (compatible with existing functions)
  , attachZoomNative
  , attachZoomWithTransform
  , attachZoomWithCallback
    -- * Identity transform
  , identity
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toNullable)
import Effect (Effect)
import Web.DOM.Element (Element)

-- | 2D point
type Point = { x :: Number, y :: Number }

-- | Bounding box for translate extent
type BoundingBox =
  { x0 :: Number
  , y0 :: Number
  , x1 :: Number
  , y1 :: Number
  }

-- | Zoom transform record {k, x, y}
-- | - k: scale factor (1.0 = 100%)
-- | - x: translate x
-- | - y: translate y
-- |
-- | The transform represents: translate(x, y) scale(k)
type ZoomTransform =
  { k :: Number
  , x :: Number
  , y :: Number
  }

-- | Identity transform (no zoom, no pan)
identity :: ZoomTransform
identity = { k: 1.0, x: 0.0, y: 0.0 }

-- | Configuration for native zoom behavior
type ZoomConfig =
  { scaleMin :: Number              -- ^ Minimum scale (default 0.1)
  , scaleMax :: Number              -- ^ Maximum scale (default 10.0)
  , targetSelector :: String        -- ^ CSS selector for element to transform
  , initialTransform :: Maybe ZoomTransform  -- ^ Optional starting transform
  , translateExtent :: Maybe BoundingBox     -- ^ Optional pan limits
  , onZoom :: Maybe (ZoomTransform -> Effect Unit)  -- ^ Optional callback
  }

-- | Handle returned by attachNativeZoom
-- |
-- | Provides methods for programmatic zoom control and cleanup.
type ZoomHandle =
  { getTransform :: Effect ZoomTransform  -- ^ Get current transform
  , setTransform :: ZoomTransform -> Effect Unit  -- ^ Set transform directly
  , resetZoom :: Effect Unit             -- ^ Reset to identity transform
  , zoomTo :: Number -> Point -> Effect Unit  -- ^ Zoom to scale at point
  , zoomBy :: Number -> Effect Unit      -- ^ Zoom by factor at center
  , destroy :: Effect Unit               -- ^ Remove all event listeners
  }

-- | Attach native zoom behavior with full configuration
-- |
-- | This is the main entry point for the zoom module.
attachNativeZoom
  :: Element
  -> ZoomConfig
  -> Effect ZoomHandle
attachNativeZoom element config = do
  let jsConfig =
        { scaleMin: config.scaleMin
        , scaleMax: config.scaleMax
        , targetSelector: config.targetSelector
        , initialTransform: toNullable config.initialTransform
        , translateExtent: toNullable (toJsExtent <$> config.translateExtent)
        , onZoom: toNullable config.onZoom
        }
  jsHandle <- attachNativeZoom_ element jsConfig
  pure
    { getTransform: pure (jsHandle.getTransform unit)
    , setTransform: \t -> jsHandle.setTransform t
    , resetZoom: jsHandle.resetZoom  -- Don't call immediately! It's already an Effect
    , zoomTo: \k p -> jsHandle.zoomTo k p
    , zoomBy: \f -> jsHandle.zoomBy f
    , destroy: jsHandle.destroy  -- Same fix - don't call immediately
    }
  where
  toJsExtent :: BoundingBox -> Array (Array Number)
  toJsExtent bb = [[bb.x0, bb.y0], [bb.x1, bb.y1]]

-- | Attach zoom behavior (simplified API)
-- |
-- | Drop-in replacement for the D3-based `attachZoom_`.
attachZoomNative
  :: Element
  -> Number      -- ^ Min scale
  -> Number      -- ^ Max scale
  -> String      -- ^ Target selector
  -> Effect ZoomHandle
attachZoomNative element scaleMin scaleMax targetSelector =
  attachNativeZoom element
    { scaleMin
    , scaleMax
    , targetSelector
    , initialTransform: Nothing
    , translateExtent: Nothing
    , onZoom: Nothing
    }

-- | Attach zoom with initial transform
-- |
-- | Drop-in replacement for `attachZoomWithTransform_`.
attachZoomWithTransform
  :: Element
  -> Number         -- ^ Min scale
  -> Number         -- ^ Max scale
  -> String         -- ^ Target selector
  -> ZoomTransform  -- ^ Initial transform
  -> Effect ZoomHandle
attachZoomWithTransform element scaleMin scaleMax targetSelector initialTransform =
  attachNativeZoom element
    { scaleMin
    , scaleMax
    , targetSelector
    , initialTransform: Just initialTransform
    , translateExtent: Nothing
    , onZoom: Nothing
    }

-- | Attach zoom with callback
-- |
-- | Drop-in replacement for `attachZoomWithCallback_`.
attachZoomWithCallback
  :: Element
  -> Number         -- ^ Min scale
  -> Number         -- ^ Max scale
  -> String         -- ^ Target selector
  -> ZoomTransform  -- ^ Initial transform
  -> (ZoomTransform -> Effect Unit)  -- ^ Callback
  -> Effect ZoomHandle
attachZoomWithCallback element scaleMin scaleMax targetSelector initialTransform onZoom =
  attachNativeZoom element
    { scaleMin
    , scaleMax
    , targetSelector
    , initialTransform: Just initialTransform
    , translateExtent: Nothing
    , onZoom: Just onZoom
    }

-- =============================================================================
-- FFI
-- =============================================================================

type JsZoomConfig =
  { scaleMin :: Number
  , scaleMax :: Number
  , targetSelector :: String
  , initialTransform :: Nullable ZoomTransform
  , translateExtent :: Nullable (Array (Array Number))
  , onZoom :: Nullable (ZoomTransform -> Effect Unit)
  }

type JsZoomHandle =
  { getTransform :: Unit -> ZoomTransform
  , setTransform :: ZoomTransform -> Effect Unit
  , resetZoom :: Effect Unit  -- Thunk, not a function taking Unit
  , zoomTo :: Number -> Point -> Effect Unit
  , zoomBy :: Number -> Effect Unit
  , destroy :: Effect Unit  -- Thunk, not a function taking Unit
  }

foreign import attachNativeZoom_
  :: Element
  -> JsZoomConfig
  -> Effect JsZoomHandle
