-- | WASM Force Simulation FFI
-- |
-- | PureScript bindings to the Rust WASM force kernel.
-- | The WASM module must be initialized via `initWasm` before creating simulations.
module Test.WASMSimulation
  ( WASMSimulation
  , initWasm
  , isWasmReady
  , createSimulation
  , setPositions
  , configureManyBody
  , configureCenter
  , enableForces
  , tick
  , getAlpha
  , isRunning
  , reheat
  , getPositions
  , getNodePosition
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Opaque type for WASM simulation instance
foreign import data WASMSimulation :: Type

-- | Initialize the WASM module. Must be called before creating simulations.
-- | Takes the path to the WASM JS wrapper module.
foreign import initWasm_ :: String -> EffectFnAff Unit

initWasm :: String -> Aff Unit
initWasm path = fromEffectFnAff (initWasm_ path)

-- | Check if WASM module is initialized
foreign import isWasmReady :: Effect Boolean

-- | Create a new simulation with the given number of nodes
foreign import createSimulation :: Int -> Effect WASMSimulation

-- | Set initial positions for all nodes (flat array: [x0, y0, x1, y1, ...])
foreign import setPositions :: WASMSimulation -> Array Number -> Effect Unit

-- | Configure many-body (charge) force
foreign import configureManyBody
  :: WASMSimulation
  -> Number  -- ^ strength (negative = repel)
  -> Number  -- ^ theta (Barnes-Hut approximation, default 0.9)
  -> Number  -- ^ distanceMin
  -> Number  -- ^ distanceMax
  -> Effect Unit

-- | Configure center force
foreign import configureCenter
  :: WASMSimulation
  -> Number  -- ^ x
  -> Number  -- ^ y
  -> Number  -- ^ strength
  -> Effect Unit

-- | Enable/disable forces
foreign import enableForces
  :: WASMSimulation
  -> Boolean  -- ^ many-body
  -> Boolean  -- ^ links
  -> Boolean  -- ^ center
  -> Effect Unit

-- | Run one tick of the simulation, returns current alpha
foreign import tick :: WASMSimulation -> Effect Number

-- | Get current alpha value
foreign import getAlpha :: WASMSimulation -> Effect Number

-- | Check if simulation is still running (alpha >= alphaMin)
foreign import isRunning :: WASMSimulation -> Effect Boolean

-- | Reheat simulation (set alpha back to 1.0)
foreign import reheat :: WASMSimulation -> Effect Unit

-- | Get all positions as flat array [x0, y0, x1, y1, ...]
foreign import getPositions :: WASMSimulation -> Effect (Array Number)

-- | Get position of a specific node
foreign import getNodePosition :: WASMSimulation -> Int -> Effect { x :: Number, y :: Number }
