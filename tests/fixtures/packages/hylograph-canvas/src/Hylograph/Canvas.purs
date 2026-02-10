-- | Canvas Rendering Library for Hylograph
-- |
-- | High-performance Canvas-based rendering for visualizations.
-- | Designed for force simulations and other cases where DOM-per-element
-- | would be too slow.
-- |
-- | Key features:
-- | - Opaque CanvasContext handle for safe FFI
-- | - Transform support for zoom/pan
-- | - Batch drawing operations for performance
-- | - Simple primitives (circles, lines) with extensible specs
module Hylograph.Canvas
  ( -- * Context
    CanvasContext
  , CanvasElement
  , CanvasConfig
  , defaultConfig
  , createCanvas
  , clearCanvas
  , getCanvasElement
    -- * Transform (for zoom/pan)
  , Transform
  , defaultTransform
  , setTransform
  , resetTransform
  , applyTransform
    -- * Drawing Primitives
  , CircleSpec
  , LineSpec
  , drawCircle
  , drawLine
    -- * Batch Drawing (for performance)
  , drawCircles
  , drawLines
    -- * Scene Rendering
  , beginScene
  , endScene
  ) where

import Prelude

import Effect (Effect)

-- =============================================================================
-- Types
-- =============================================================================

-- | Opaque handle to a Canvas rendering context
foreign import data CanvasContext :: Type

-- | Configuration for creating a Canvas
type CanvasConfig =
  { width :: Int
  , height :: Int
  , background :: String
  , centerOrigin :: Boolean  -- If true, (0,0) is center instead of top-left
  }

-- | Default canvas configuration
defaultConfig :: CanvasConfig
defaultConfig =
  { width: 900
  , height: 600
  , background: "#f8f8f8"
  , centerOrigin: true
  }

-- | View transform for zoom/pan
type Transform =
  { scale :: Number      -- 1.0 = 100%, 2.0 = 200%
  , translateX :: Number -- Pan offset X
  , translateY :: Number -- Pan offset Y
  }

-- | Default transform (no zoom, no pan)
defaultTransform :: Transform
defaultTransform = { scale: 1.0, translateX: 0.0, translateY: 0.0 }

-- | Specification for drawing a circle
type CircleSpec =
  { x :: Number
  , y :: Number
  , radius :: Number
  , fill :: String
  , stroke :: String
  , strokeWidth :: Number
  , opacity :: Number
  }

-- | Specification for drawing a line
type LineSpec =
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  , stroke :: String
  , strokeWidth :: Number
  , opacity :: Number
  }

-- =============================================================================
-- FFI Declarations
-- =============================================================================

-- | Create a Canvas element in the given container
foreign import createCanvas_ :: String -> CanvasConfig -> Effect CanvasContext

-- | Clear the canvas
foreign import clearCanvas_ :: CanvasContext -> Effect Unit

-- | Get the underlying canvas DOM element (for event binding)
foreign import getCanvasElement_ :: CanvasContext -> Effect CanvasElement

-- | Set the current transform
foreign import setTransform_ :: CanvasContext -> Transform -> Effect Unit

-- | Reset transform to identity
foreign import resetTransform_ :: CanvasContext -> Effect Unit

-- | Draw a single circle
foreign import drawCircle_ :: CanvasContext -> CircleSpec -> Effect Unit

-- | Draw a single line
foreign import drawLine_ :: CanvasContext -> LineSpec -> Effect Unit

-- | Draw multiple circles (batched for performance)
foreign import drawCircles_ :: CanvasContext -> Array CircleSpec -> Effect Unit

-- | Draw multiple lines (batched for performance)
foreign import drawLines_ :: CanvasContext -> Array LineSpec -> Effect Unit

-- | Begin a scene (clear and prepare)
foreign import beginScene_ :: CanvasContext -> Effect Unit

-- | End a scene (flush any batched operations)
foreign import endScene_ :: CanvasContext -> Effect Unit

-- | Opaque canvas element type for event binding
foreign import data CanvasElement :: Type

-- =============================================================================
-- Public API
-- =============================================================================

-- | Create a Canvas in the specified container
createCanvas :: String -> CanvasConfig -> Effect CanvasContext
createCanvas = createCanvas_

-- | Clear the canvas
clearCanvas :: CanvasContext -> Effect Unit
clearCanvas = clearCanvas_

-- | Get the canvas DOM element (for attaching event listeners)
getCanvasElement :: CanvasContext -> Effect CanvasElement
getCanvasElement = getCanvasElement_

-- | Set the view transform (for zoom/pan)
setTransform :: CanvasContext -> Transform -> Effect Unit
setTransform = setTransform_

-- | Reset transform to default
resetTransform :: CanvasContext -> Effect Unit
resetTransform = resetTransform_

-- | Apply a transform to the current transform (multiply)
applyTransform :: Transform -> Transform -> Transform
applyTransform t1 t2 =
  { scale: t1.scale * t2.scale
  , translateX: t1.translateX + t2.translateX * t1.scale
  , translateY: t1.translateY + t2.translateY * t1.scale
  }

-- | Draw a single circle
drawCircle :: CanvasContext -> CircleSpec -> Effect Unit
drawCircle = drawCircle_

-- | Draw a single line
drawLine :: CanvasContext -> LineSpec -> Effect Unit
drawLine = drawLine_

-- | Draw multiple circles (more efficient than repeated drawCircle)
drawCircles :: CanvasContext -> Array CircleSpec -> Effect Unit
drawCircles = drawCircles_

-- | Draw multiple lines (more efficient than repeated drawLine)
drawLines :: CanvasContext -> Array LineSpec -> Effect Unit
drawLines = drawLines_

-- | Begin a new scene (clears canvas)
beginScene :: CanvasContext -> Effect Unit
beginScene = beginScene_

-- | End the current scene
endScene :: CanvasContext -> Effect Unit
endScene = endScene_
