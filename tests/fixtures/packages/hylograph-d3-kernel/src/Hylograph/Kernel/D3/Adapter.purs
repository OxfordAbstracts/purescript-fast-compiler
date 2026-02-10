-- | D3 Kernel Adapter
-- |
-- | Creates an EngineAdapter from D3 kernel components.
-- | This is the integration point between the core orchestration and D3.
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Kernel.D3.Adapter as D3Adapter
-- | import Hylograph.Simulation.Core.Engine as Engine
-- |
-- | -- Create adapter from D3 simulation components
-- | adapter <- D3Adapter.mkAdapter { nodes: nodesRef, forces: forcesRef, ... }
-- |
-- | -- Use with core engine
-- | engine <- Engine.createEngine adapter
-- | Engine.transitionTo myScene engine
-- | ```
module Hylograph.Kernel.D3.Adapter
  ( -- * Adapter Creation
    mkAdapter
    -- * Re-exports
  , module Core
  ) where

import Prelude

import Data.Array (find)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object as Object
import Hylograph.Kernel.D3.Core (ForceHandle) as Core
import Hylograph.Simulation.Core.Engine (EngineAdapter)
import Hylograph.Simulation.Core.Types (PositionMap, NodeRule)

-- | Minimal node requirements for the D3 adapter
type MinimalNode r = { id :: Int, x :: Number, y :: Number | r }

-- | Create an EngineAdapter from D3 kernel components.
-- |
-- | This bridges the generic core engine with D3-specific functionality.
-- | The adapter provides position capture/update and rule application.
mkAdapter
  :: forall nodeRow
   . { nodesRef :: Ref (Array (MinimalNode nodeRow))
     , reheatFn :: Effect Unit
     , reinitForcesFn :: Effect Unit
     }
  -> EngineAdapter (MinimalNode nodeRow)
mkAdapter components =
  { getNodes: Ref.read components.nodesRef
  , capturePositions: capturePositions
  , interpolatePositions: interpolatePositions components.nodesRef
  , updatePositions: updatePositions components.nodesRef
  , applyRulesInPlace: applyRulesInPlace components.nodesRef
  , reinitializeForces: components.reinitForcesFn
  , reheat: components.reheatFn
  }

-- | Capture current positions from nodes as PositionMap
capturePositions :: forall r. Array (MinimalNode r) -> PositionMap
capturePositions nodes =
  Object.fromFoldable $ map (\n -> Tuple (show n.id) { x: n.x, y: n.y }) nodes

-- | Interpolate positions between start and target
interpolatePositions
  :: forall r
   . Ref (Array (MinimalNode r))
  -> PositionMap
  -> PositionMap
  -> Number
  -> Effect Unit
interpolatePositions nodesRef startPositions targetPositions progress = do
  nodes <- Ref.read nodesRef
  let updatedNodes = map (interpolateNode startPositions targetPositions progress) nodes
  Ref.write updatedNodes nodesRef

-- | Interpolate a single node's position
interpolateNode
  :: forall r
   . PositionMap
  -> PositionMap
  -> Number
  -> MinimalNode r
  -> MinimalNode r
interpolateNode startPositions targetPositions progress node =
  let key = show node.id
      newX = case Object.lookup key startPositions, Object.lookup key targetPositions of
        Just start, Just target -> start.x + (target.x - start.x) * progress
        _, Just target -> target.x
        Just start, _ -> start.x
        _, _ -> node.x
      newY = case Object.lookup key startPositions, Object.lookup key targetPositions of
        Just start, Just target -> start.y + (target.y - start.y) * progress
        _, Just target -> target.y
        Just start, _ -> start.y
        _, _ -> node.y
  in node { x = newX, y = newY }

-- | Update positions directly from a PositionMap
updatePositions
  :: forall r
   . Ref (Array (MinimalNode r))
  -> PositionMap
  -> Effect Unit
updatePositions nodesRef positions = do
  nodes <- Ref.read nodesRef
  let updatedNodes = map (updateNodePosition positions) nodes
  Ref.write updatedNodes nodesRef

-- | Update a single node's position from PositionMap
updateNodePosition :: forall r. PositionMap -> MinimalNode r -> MinimalNode r
updateNodePosition positions node =
  case Object.lookup (show node.id) positions of
    Just pos -> node { x = pos.x, y = pos.y }
    Nothing -> node

-- | Apply rules to nodes in place
applyRulesInPlace
  :: forall r
   . Ref (Array (MinimalNode r))
  -> Array (NodeRule (MinimalNode r))
  -> Effect Unit
applyRulesInPlace nodesRef rules = do
  nodes <- Ref.read nodesRef
  let updatedNodes = map (applyFirstMatchingRule rules) nodes
  Ref.write updatedNodes nodesRef

-- | Apply the first matching rule to a node
applyFirstMatchingRule
  :: forall r
   . Array (NodeRule (MinimalNode r))
  -> MinimalNode r
  -> MinimalNode r
applyFirstMatchingRule rules node =
  case find (\rule -> rule.select node) rules of
    Just rule -> rule.apply node
    Nothing -> node
