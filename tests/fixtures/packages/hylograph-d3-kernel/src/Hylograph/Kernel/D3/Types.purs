-- | D3 Force Engine Types
-- |
-- | Type definitions for D3 force configurations.
-- | These are D3-specific and not shared with other kernels.
module Hylograph.Kernel.D3.Types
  ( -- * Node Types
    SimNode
    -- * Link Types
  , SimLink
  , RawLink
    -- * Simulation State
  , SimulationState
  , defaultSimParams
    -- * Force Configurations
  , ManyBodyConfig
  , defaultManyBody
  , CollideConfig
  , defaultCollide
  , LinkConfig
  , defaultLink
  , CenterConfig
  , defaultCenter
  , ForceXConfig
  , ForceYConfig
  , RadialConfig
    -- * Filtered/Dynamic Configurations
  , ManyBodyFilteredConfig
  , RadialFilteredConfig
  , CollideDynamicConfig
  , ForceXDynamicConfig
  , ForceYDynamicConfig
  , LinkDynamicConfig
    -- * Force Specification
  , ForceSpec(..)
  , forceName
  ) where

import Prelude


-- =============================================================================
-- Core Node Type
-- =============================================================================

-- | A simulation node with position and velocity.
type SimNode extra =
  { x :: Number
  , y :: Number
  , vx :: Number
  , vy :: Number
  , index :: Int
  | extra
  }

-- =============================================================================
-- Link Type
-- =============================================================================

-- | A link between nodes (post-swizzle)
type SimLink nodeRow linkData =
  { source :: { x :: Number, y :: Number | nodeRow }
  , target :: { x :: Number, y :: Number | nodeRow }
  , index :: Int
  | linkData
  }

-- | Raw link with source/target as indices (pre-swizzle)
type RawLink linkData =
  { source :: Int
  , target :: Int
  | linkData
  }

-- =============================================================================
-- Simulation State
-- =============================================================================

type SimulationState nodeRow linkData =
  { nodes :: Array (SimNode nodeRow)
  , links :: Array (RawLink linkData)
  , alpha :: Number
  , alphaMin :: Number
  , alphaDecay :: Number
  , alphaTarget :: Number
  , velocityDecay :: Number
  , running :: Boolean
  }

defaultSimParams ::
  { alpha :: Number
  , alphaMin :: Number
  , alphaDecay :: Number
  , alphaTarget :: Number
  , velocityDecay :: Number
  }
defaultSimParams =
  { alpha: 1.0
  , alphaMin: 0.001
  , alphaDecay: 0.01
  , alphaTarget: 0.0
  , velocityDecay: 0.4
  }

-- =============================================================================
-- Force Configuration
-- =============================================================================

type ManyBodyConfig =
  { strength :: Number
  , theta :: Number
  , distanceMin :: Number
  , distanceMax :: Number
  }

defaultManyBody :: ManyBodyConfig
defaultManyBody =
  { strength: -30.0
  , theta: 0.9
  , distanceMin: 1.0
  , distanceMax: infinity
  }
  where
  infinity = 1.0e10

type CollideConfig =
  { radius :: Number
  , strength :: Number
  , iterations :: Int
  }

defaultCollide :: CollideConfig
defaultCollide =
  { radius: 1.0
  , strength: 1.0
  , iterations: 1
  }

type LinkConfig =
  { distance :: Number
  , strength :: Number
  , iterations :: Int
  }

defaultLink :: LinkConfig
defaultLink =
  { distance: 30.0
  , strength: 1.0
  , iterations: 1
  }

type CenterConfig =
  { x :: Number
  , y :: Number
  , strength :: Number
  }

defaultCenter :: CenterConfig
defaultCenter =
  { x: 0.0
  , y: 0.0
  , strength: 1.0
  }

type ForceXConfig =
  { x :: Number
  , strength :: Number
  }

type ForceYConfig =
  { y :: Number
  , strength :: Number
  }

type RadialConfig =
  { radius :: Number
  , x :: Number
  , y :: Number
  , strength :: Number
  }

-- =============================================================================
-- Filtered/Dynamic Force Configurations
-- =============================================================================

type ManyBodyFilteredConfig node =
  { strength :: Number
  , theta :: Number
  , distanceMin :: Number
  , distanceMax :: Number
  , filter :: node -> Boolean
  }

type RadialFilteredConfig node =
  { radius :: Number
  , x :: Number
  , y :: Number
  , strength :: Number
  , filter :: node -> Boolean
  }

type CollideDynamicConfig node =
  { radiusAccessor :: node -> Number
  , strength :: Number
  , iterations :: Int
  }

type ForceXDynamicConfig node =
  { xAccessor :: node -> Number
  , strength :: Number
  }

type ForceYDynamicConfig node =
  { yAccessor :: node -> Number
  , strength :: Number
  }

type LinkDynamicConfig link =
  { distance :: Number
  , strengthAccessor :: link -> Number
  , iterations :: Int
  }

-- =============================================================================
-- Force Sum Type
-- =============================================================================

data ForceSpec
  = ManyBody String ManyBodyConfig
  | Collide String CollideConfig
  | Link String LinkConfig
  | Center String CenterConfig
  | PositionX String ForceXConfig
  | PositionY String ForceYConfig
  | Radial String RadialConfig

forceName :: ForceSpec -> String
forceName = case _ of
  ManyBody name _ -> name
  Collide name _ -> name
  Link name _ -> name
  Center name _ -> name
  PositionX name _ -> name
  PositionY name _ -> name
  Radial name _ -> name
