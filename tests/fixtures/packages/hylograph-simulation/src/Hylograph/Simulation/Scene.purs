-- | Scene Orchestration Module (Legacy)
-- |
-- | This module re-exports from the new Hylograph.Scene modules for backwards compatibility.
-- | It also provides the `applyRulesInPlace_` FFI which preserves object identity
-- | for D3 data binding.
-- |
-- | For new code, prefer importing from:
-- | - `Hylograph.Scene.Types` (types)
-- | - `Hylograph.Scene.Rules` (rule helpers)
-- | - `Hylograph.Scene.Engine` (orchestration)
module Hylograph.Simulation.Scene
  ( -- Re-exports from Types
    module ReExport
  -- Functions
  , applyRules
  -- FFI (unique to this module)
  , applyRulesInPlace_
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Ref (Ref)
import Hylograph.Scene.Types
  ( NodeRule
  , SceneConfig
  , TransitionState
  , EngineMode(..)
  , PositionMap
  ) as ReExport
import Hylograph.Scene.Types (NodeRule)

-- =============================================================================
-- Functions
-- =============================================================================

-- | Apply rules to nodes (first matching rule wins) - creates new array
applyRules :: forall node. Array (NodeRule node) -> Array node -> Array node
applyRules rules nodes = map (applyFirstMatch rules) nodes
  where
  applyFirstMatch :: Array (NodeRule node) -> node -> node
  applyFirstMatch rs node =
    case Array.find (\r -> r.select node) rs of
      Just r -> r.apply node
      Nothing -> node

-- =============================================================================
-- In-Place Mutation (FFI)
-- =============================================================================

-- | Apply rules in place with first-match-wins semantics (CSS-like cascade)
-- | For each node, find the first matching rule and apply it via Object.assign.
-- | Preserves object identity for D3 data binding.
foreign import applyRulesInPlace_
  :: forall node
   . Array (NodeRule node)
  -> Ref (Array node)
  -> Unit
