-- | D3 Force Engine Core
-- |
-- | This module provides D3-based force simulation functions.
-- | We use D3's force calculation algorithms but manage the simulation ourselves.
-- |
-- | Key principle: Forces are just functions that mutate vx/vy on nodes.
-- | We control when they run and how alpha decays.
module Hylograph.Kernel.D3.Core
  ( -- * Force Handles (opaque)
    ForceHandle
    -- * Force Creation
  , createManyBody
  , createCollide
  , createLink
  , createCenter
  , createForceX
  , createForceY
  , createRadial
    -- * Filtered/Dynamic Forces
  , createManyBodyFiltered
  , createRadialFiltered
  , createCollideDynamic
  , createForceXDynamic
  , createForceYDynamic
  , createLinkDynamic
    -- * Optimized Grid Forces (no FFI callbacks)
  , createForceXGrid
  , createForceYGrid
  , createCollideGrid
    -- * Initialization
  , initializeNodes
  , initializeForce
  , initializeLinkForce
    -- * Simulation Step
  , applyForce
  , applyForces
  , integratePositions
  , decayAlpha
  , simulationTick
    -- * Animation
  , AnimationHandle
  , startAnimation
  , stopAnimation
    -- * Drag Behavior
  , attachDragWithReheat
  , attachGroupDragWithReheat
  , attachPinningDrag
    -- * DOM Utilities
  , querySelectorElements
    -- * Debug
  , logNodes
  ) where

import Prelude

import Data.Traversable (for_)
import Effect (Effect)
import Hylograph.Kernel.D3.Types (ManyBodyConfig, CollideConfig, LinkConfig, CenterConfig, ForceXConfig, ForceYConfig, RadialConfig, ManyBodyFilteredConfig, RadialFilteredConfig, CollideDynamicConfig, ForceXDynamicConfig, ForceYDynamicConfig, LinkDynamicConfig)
import Web.DOM.Element (Element)

-- =============================================================================
-- Foreign Imports
-- =============================================================================

-- Force handles are opaque JavaScript objects
foreign import data ForceHandle :: Type

-- Force creation
foreign import createManyBody_ :: ManyBodyConfig -> ForceHandle
foreign import createCollide_ :: CollideConfig -> ForceHandle
foreign import createLink_ :: LinkConfig -> ForceHandle
foreign import createCenter_ :: CenterConfig -> ForceHandle
foreign import createForceX_ :: ForceXConfig -> ForceHandle
foreign import createForceY_ :: ForceYConfig -> ForceHandle
foreign import createRadial_ :: RadialConfig -> ForceHandle

-- Filtered/Dynamic force creation
foreign import createManyBodyFiltered_ :: forall node. ManyBodyFilteredConfig node -> ForceHandle
foreign import createRadialFiltered_ :: forall node. RadialFilteredConfig node -> ForceHandle
foreign import createCollideDynamic_ :: forall node. CollideDynamicConfig node -> ForceHandle
foreign import createForceXDynamic_ :: forall node. ForceXDynamicConfig node -> ForceHandle
foreign import createForceYDynamic_ :: forall node. ForceYDynamicConfig node -> ForceHandle
foreign import createLinkDynamic_ :: forall link. LinkDynamicConfig link -> ForceHandle

-- Optimized Grid force creation (no PureScript callbacks - reads node properties directly)
foreign import createForceXGrid_ :: Number -> ForceHandle
foreign import createForceYGrid_ :: Number -> ForceHandle
foreign import createCollideGrid_ :: Number -> Number -> Int -> ForceHandle

-- Initialization
foreign import initializeNodes_ :: forall r. Array { | r } -> Effect Unit
foreign import initializeForce_ :: forall r. ForceHandle -> Array { | r } -> Effect ForceHandle
foreign import initializeLinkForce_ :: forall nodeRow linkRow. ForceHandle -> Array { | nodeRow } -> Array { | linkRow } -> Effect ForceHandle

-- Force application
foreign import applyForce_ :: ForceHandle -> Number -> Effect Unit

-- Position integration
foreign import integratePositions_ :: forall r. Array { | r } -> Number -> Effect Unit

-- Alpha decay (pure calculation)
foreign import decayAlpha_ :: Number -> Number -> Number -> Number -> Number

-- Animation
foreign import requestAnimationFrame_ :: (Number -> Effect Unit) -> Effect (Effect Unit)

-- Debug
foreign import logNodes_ :: forall r. String -> Array { | r } -> Effect Unit

-- =============================================================================
-- Force Creation (Pure)
-- =============================================================================

-- | Create a many-body (charge) force
createManyBody :: ManyBodyConfig -> ForceHandle
createManyBody = createManyBody_

-- | Create a collision force
createCollide :: CollideConfig -> ForceHandle
createCollide = createCollide_

-- | Create a link force
createLink :: LinkConfig -> ForceHandle
createLink = createLink_

-- | Create a centering force
createCenter :: CenterConfig -> ForceHandle
createCenter = createCenter_

-- | Create an X positioning force
createForceX :: ForceXConfig -> ForceHandle
createForceX = createForceX_

-- | Create a Y positioning force
createForceY :: ForceYConfig -> ForceHandle
createForceY = createForceY_

-- | Create a radial force
createRadial :: RadialConfig -> ForceHandle
createRadial = createRadial_

-- =============================================================================
-- Filtered/Dynamic Force Creation (Pure)
-- =============================================================================

-- | Create a many-body force that only applies to nodes matching a predicate
createManyBodyFiltered :: forall node. ManyBodyFilteredConfig node -> ForceHandle
createManyBodyFiltered = createManyBodyFiltered_

-- | Create a radial force that only applies to nodes matching a predicate
createRadialFiltered :: forall node. RadialFilteredConfig node -> ForceHandle
createRadialFiltered = createRadialFiltered_

-- | Create a collision force with dynamic radius per-node
createCollideDynamic :: forall node. CollideDynamicConfig node -> ForceHandle
createCollideDynamic = createCollideDynamic_

-- | Create an X positioning force with dynamic target per-node
createForceXDynamic :: forall node. ForceXDynamicConfig node -> ForceHandle
createForceXDynamic = createForceXDynamic_

-- | Create a Y positioning force with dynamic target per-node
createForceYDynamic :: forall node. ForceYDynamicConfig node -> ForceHandle
createForceYDynamic = createForceYDynamic_

-- | Create a link force with dynamic strength per-link
createLinkDynamic :: forall link. LinkDynamicConfig link -> ForceHandle
createLinkDynamic = createLinkDynamic_

-- =============================================================================
-- Optimized Grid Forces (no FFI callbacks)
-- =============================================================================

-- | Create an X positioning force that reads node.gridX directly
createForceXGrid :: Number -> ForceHandle
createForceXGrid = createForceXGrid_

-- | Create a Y positioning force that reads node.gridY directly
createForceYGrid :: Number -> ForceHandle
createForceYGrid = createForceYGrid_

-- | Create a collision force that reads node.r directly
createCollideGrid :: Number -> Number -> Int -> ForceHandle
createCollideGrid = createCollideGrid_

-- =============================================================================
-- Initialization (Effectful)
-- =============================================================================

-- | Initialize nodes with indices and default velocities
initializeNodes :: forall r. Array { | r } -> Effect Unit
initializeNodes = initializeNodes_

-- | Initialize a force with nodes
initializeForce :: forall r. ForceHandle -> Array { | r } -> Effect ForceHandle
initializeForce = initializeForce_

-- | Initialize a link force with nodes and links
initializeLinkForce :: forall nodeRow linkRow. ForceHandle -> Array { | nodeRow } -> Array { | linkRow } -> Effect ForceHandle
initializeLinkForce = initializeLinkForce_

-- =============================================================================
-- Simulation Step
-- =============================================================================

-- | Apply a single force
applyForce :: ForceHandle -> Number -> Effect Unit
applyForce = applyForce_

-- | Apply multiple forces in sequence
applyForces :: Array ForceHandle -> Number -> Effect Unit
applyForces forces alpha = for_ forces \f -> applyForce f alpha

-- | Integrate positions: apply velocity decay and update positions
integratePositions :: forall r. Array { | r } -> Number -> Effect Unit
integratePositions = integratePositions_

-- | Calculate new alpha value (the "cooling" step)
decayAlpha :: Number -> Number -> Number -> Number -> Number
decayAlpha = decayAlpha_

-- | Complete simulation tick
simulationTick :: forall r.
  { forces :: Array ForceHandle
  , nodes :: Array { | r }
  , alpha :: Number
  , alphaMin :: Number
  , alphaDecay :: Number
  , alphaTarget :: Number
  , velocityDecay :: Number
  }
  -> Effect Number
simulationTick params = do
  applyForces params.forces params.alpha
  integratePositions params.nodes params.velocityDecay
  pure $ decayAlpha params.alpha params.alphaMin params.alphaDecay params.alphaTarget

-- =============================================================================
-- Animation Loop
-- =============================================================================

type AnimationHandle = Effect Unit

-- | Start an animation loop
startAnimation :: (Number -> Effect Boolean) -> Effect AnimationHandle
startAnimation onFrame = do
  cancelRef <- newCancelRef
  let
    loop timestamp = do
      continue <- onFrame timestamp
      when continue do
        cancel <- requestAnimationFrame_ loop
        setCancelRef cancelRef cancel
  cancel <- requestAnimationFrame_ loop
  setCancelRef cancelRef cancel
  pure $ getCancelRef cancelRef >>= identity

foreign import newCancelRef :: Effect CancelRef
foreign import setCancelRef :: CancelRef -> Effect Unit -> Effect Unit
foreign import getCancelRef :: CancelRef -> Effect (Effect Unit)
foreign import data CancelRef :: Type

-- | Stop a running animation
stopAnimation :: AnimationHandle -> Effect Unit
stopAnimation cancel = cancel

-- =============================================================================
-- Drag Behavior
-- =============================================================================

foreign import attachDragWithReheat_ :: Array Element -> Effect Unit -> Effect Unit
foreign import attachGroupDragWithReheat_ :: Array Element -> String -> Effect Unit -> Effect Unit
foreign import attachPinningDrag_ :: Array Element -> Effect Unit -> Effect Unit

-- | Attach drag with reheat callback
attachDragWithReheat :: Array Element -> Effect Unit -> Effect Unit
attachDragWithReheat = attachDragWithReheat_

-- | Attach drag to transformed group elements
attachGroupDragWithReheat :: Array Element -> String -> Effect Unit -> Effect Unit
attachGroupDragWithReheat = attachGroupDragWithReheat_

-- | Attach drag with toggle-pinning behavior
attachPinningDrag :: Array Element -> Effect Unit -> Effect Unit
attachPinningDrag = attachPinningDrag_

-- =============================================================================
-- DOM Utilities
-- =============================================================================

foreign import querySelectorElements_ :: String -> Effect (Array Element)

-- | Query DOM elements by CSS selector
querySelectorElements :: String -> Effect (Array Element)
querySelectorElements = querySelectorElements_

-- =============================================================================
-- Debug
-- =============================================================================

-- | Log node positions for debugging
logNodes :: forall r. String -> Array { | r } -> Effect Unit
logNodes = logNodes_
