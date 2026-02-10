-- | Framework-Agnostic Event Emitter
-- |
-- | Provides a universal subscription mechanism that any UI framework can consume.
-- | The core simulation library emits events through this interface, and thin
-- | framework adapters convert it to Halogen subscriptions, React hooks, etc.
-- |
-- | ## Design
-- |
-- | The emitter is based on a simple callback pattern:
-- | - `subscribe` takes a callback and returns an unsubscribe function
-- | - This is the minimal interface that all frameworks can work with
-- |
-- | ## Framework Integration
-- |
-- | **Halogen**: Convert to `HS.Emitter` using `toHalogenEmitter` from
-- | `Hylograph.ForceEngine.Halogen`:
-- |
-- | ```purescript
-- | import Hylograph.ForceEngine.Halogen (toHalogenEmitter)
-- |
-- | handleAction Initialize = do
-- |   { handle, events } <- liftEffect $ runSimulation config
-- |   halogenEmitter <- liftEffect $ toHalogenEmitter events
-- |   void $ H.subscribe $ halogenEmitter <#> SimEvent
-- | ```
-- |
-- | **React**: Use in `useEffect` with cleanup. The unsubscribe function
-- | returned by `subscribe` works perfectly as a React cleanup function:
-- |
-- | ```javascript
-- | // In a React component:
-- | useEffect(() => {
-- |   const { handle, events } = runSimulation(config)();
-- |
-- |   // Subscribe returns an unsubscribe function
-- |   const unsubscribe = subscribe(events)(event => {
-- |     if (event.tag === 'Tick') {
-- |       setAlpha(event.alpha);
-- |     } else if (event.tag === 'Completed') {
-- |       console.log('Simulation converged!');
-- |     }
-- |   })();
-- |
-- |   // Cleanup: unsubscribe when component unmounts
-- |   return () => unsubscribe();
-- | }, []);
-- | ```
-- |
-- | **Vanilla JS**: Just call subscribe directly:
-- |
-- | ```javascript
-- | const { handle, events } = runSimulation(config)();
-- | const unsubscribe = subscribe(events)(event => {
-- |   console.log('Event:', event);
-- | })();
-- | ```
module Hylograph.Simulation.Emitter
  ( -- * Types
    SimulationEmitter
  , SimulationEvent(..)
  , Unsubscribe

    -- * Creating Emitters
  , create
  , EmitterHandle

    -- * Subscribing
  , subscribe

    -- * Emitting (internal use)
  , emit
  ) where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Ref as Ref

-- | Event types emitted by simulations
-- |
-- | These are the same regardless of whether D3 or WASM is running the physics.
data SimulationEvent
  = Tick
      { alpha :: Number      -- Current alpha (convergence measure)
      , nodeCount :: Int     -- Number of nodes in simulation
      }
  | Started                  -- Simulation started or restarted
  | Stopped                  -- Simulation stopped (converged or manually)
  | Completed                -- Simulation fully converged (alpha below threshold)

derive instance eqSimulationEvent :: Eq SimulationEvent

instance showSimulationEvent :: Show SimulationEvent where
  show (Tick r) = "Tick { alpha: " <> show r.alpha <> ", nodeCount: " <> show r.nodeCount <> " }"
  show Started = "Started"
  show Stopped = "Stopped"
  show Completed = "Completed"

-- | Unsubscribe function returned by subscribe
type Unsubscribe = Effect Unit

-- | Listener with unique ID for unsubscription
type Listener =
  { id :: Int
  , callback :: SimulationEvent -> Effect Unit
  }

-- | Framework-agnostic event emitter
-- |
-- | This is intentionally opaque - use `subscribe` to listen for events.
-- | The internal representation is a list of listeners with unique IDs.
newtype SimulationEmitter = SimulationEmitter
  { listeners :: Ref.Ref (Array Listener)
  , nextId :: Ref.Ref Int
  }

-- | Handle for emitting events (kept by the simulation, not exposed to users)
newtype EmitterHandle = EmitterHandle
  { emitter :: SimulationEmitter
  }

-- | Create a new emitter
-- |
-- | Returns both the emitter (for subscribers) and a handle (for the simulation
-- | to emit events). This separation ensures only the simulation can emit.
create :: Effect { emitter :: SimulationEmitter, handle :: EmitterHandle }
create = do
  listeners <- Ref.new []
  nextId <- Ref.new 0
  let emitter = SimulationEmitter { listeners, nextId }
  pure { emitter, handle: EmitterHandle { emitter } }

-- | Subscribe to events
-- |
-- | Returns an unsubscribe function that removes the listener.
-- |
-- | ```purescript
-- | unsubscribe <- subscribe emitter \event -> case event of
-- |   Tick { alpha } -> log $ "Alpha: " <> show alpha
-- |   Completed -> log "Simulation converged!"
-- |   _ -> pure unit
-- |
-- | -- Later, to stop listening:
-- | unsubscribe
-- | ```
subscribe :: SimulationEmitter -> (SimulationEvent -> Effect Unit) -> Effect Unsubscribe
subscribe (SimulationEmitter { listeners, nextId }) callback = do
  -- Get unique ID for this listener
  listenerId <- Ref.read nextId
  Ref.modify_ (_ + 1) nextId

  -- Add listener with ID
  Ref.modify_ (\ls -> Array.snoc ls { id: listenerId, callback }) listeners

  -- Return unsubscribe function that removes by ID
  pure do
    Ref.modify_ (Array.filter (\l -> l.id /= listenerId)) listeners

-- | Emit an event to all subscribers (internal use only)
-- |
-- | This is called by the simulation implementation, not by users.
emit :: EmitterHandle -> SimulationEvent -> Effect Unit
emit (EmitterHandle { emitter: SimulationEmitter { listeners } }) event = do
  ls <- Ref.read listeners
  -- Notify all listeners
  Array.foldM (\_ listener -> listener.callback event) unit ls
