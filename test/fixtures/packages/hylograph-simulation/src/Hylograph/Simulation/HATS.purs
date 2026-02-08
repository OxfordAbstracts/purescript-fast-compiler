-- | HATS Integration for Hylograph Simulation
-- |
-- | Provides efficient tick updates for force simulations using HATS templates.
-- |
-- | The key insight: simulation nodes change position every tick, but their
-- | structure (radius, color, children) is static. Instead of rebuilding the
-- | full HATS tree at 60fps, we:
-- |
-- | 1. Initial render: Use full HATS rerender for enter/exit/structural changes
-- | 2. Tick updates: Only update transform attribute via fast DOM mutation
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hylograph.HATS (forEach)
-- | import Hylograph.HATS.InterpreterTick (rerender)
-- | import Hylograph.Simulation.HATS (tickUpdate)
-- |
-- | -- Build your tree with forEach (keyed)
-- | nodesTree = forEach "nodes" Group nodes (\n -> show n.id) nodeTemplate
-- |
-- | -- Initial render creates elements with full HATS tree
-- | void $ rerender "#container" nodesTree
-- |
-- | -- On each tick, fast-path updates only transforms
-- | -- (nodes array has same elements, just different x/y values)
-- | tickUpdate "#container" currentNodes
-- | ```
-- |
-- | This gives HATS expressiveness for templates with D3-level performance
-- | for tick updates (~60fps with thousands of nodes).
-- |
-- | ## Element Requirements
-- |
-- | For tickUpdate to work, each node element MUST have:
-- | - `data-id` attribute containing the node's id (as string)
-- | - A `transform` attribute (will be set to `translate(x,y)`)
-- |
-- | Example HATS template:
-- | ```purescript
-- | nodeTemplate node =
-- |   elem Group
-- |     [ thunkedStr "data-id" (show node.id)  -- Required for tickUpdate
-- |     , thunkedStr "transform" ("translate(" <> show node.x <> "," <> show node.y <> ")")
-- |     ]
-- |     [ elem Circle [...] [] ]
-- | ```
module Hylograph.Simulation.HATS
  ( tickUpdate
  , tickUpdateWithRadius
  ) where

import Prelude

import Effect (Effect)

-- =============================================================================
-- Types (local, no export needed)
-- =============================================================================

-- | Minimal interface for positioned nodes
type PositionedNode r =
  { id :: Int
  , x :: Number
  , y :: Number
  | r
  }

-- | Node with radius (for collision updates)
type RadiusNode r =
  { id :: Int
  , x :: Number
  , y :: Number
  , r :: Number
  | r
  }

-- =============================================================================
-- Public API
-- =============================================================================

-- | Fast tick update - only updates transform attribute
-- |
-- | Uses direct DOM manipulation to set transform on each node element.
-- | Much faster than rebuilding the HATS tree at 60fps.
-- |
-- | Prerequisites:
-- | - Elements must have been created by initial rerender
-- | - Each element must have data-id attribute matching node.id
-- |
-- | Call this on simulation tick events when only positions change.
tickUpdate
  :: forall r
   . String                           -- Container selector
  -> Array (PositionedNode r)         -- Nodes with updated positions
  -> Effect Unit
tickUpdate = updateNodeTransformsFFI

-- | Fast tick update with radius changes
-- |
-- | Like tickUpdate but also updates the radius on child circles.
-- | Use when nodes can resize during simulation.
tickUpdateWithRadius
  :: forall r
   . String                           -- Container selector
  -> Array (RadiusNode r)             -- Nodes with updated positions and radii
  -> Effect Unit
tickUpdateWithRadius = updateNodeTransformsWithRadiusFFI

-- =============================================================================
-- FFI
-- =============================================================================

foreign import updateNodeTransformsFFI
  :: forall r
   . String
  -> Array (PositionedNode r)
  -> Effect Unit

foreign import updateNodeTransformsWithRadiusFFI
  :: forall r
   . String
  -> Array (RadiusNode r)
  -> Effect Unit
