-- | Coordinator Example
-- |
-- | A simple example showing how to use the TickCoordinator
-- | with multiple transitions running simultaneously.
-- |
-- | This module is for demonstration and testing purposes.
module Hylograph.Transition.Example
  ( runExample
  , exampleWithCallback
  ) where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Hylograph.Transition.Coordinator as C
import Hylograph.Transition.Consumers (transitionConsumer, transitionGroupConsumer)
import Hylograph.Transition.Engine as E
import Hylograph.Transition.Easing (EasingType(..))

-- =============================================================================
-- Example: Two Independent Transitions
-- =============================================================================

-- | Run a simple example with two transitions:
-- | - Opacity: 0 → 1 over 500ms
-- | - Radius: 5 → 20 over 1000ms
-- |
-- | The opacity transition will complete first, then radius.
runExample :: Effect Unit
runExample = do
  log "Starting coordinator example..."

  -- Create coordinator
  coord <- C.create

  -- Create opacity transition: 0 → 1 over 500ms
  let opacitySpec = E.transition { from: 0.0, to: 1.0 } { duration: 500.0, easing: QuadOut }
  opacityRef <- Ref.new (E.start opacitySpec)

  -- Create radius transition: 5 → 20 over 1000ms
  let radiusSpec = E.transition { from: 5.0, to: 20.0 } { duration: 1000.0, easing: CubicInOut }
  radiusRef <- Ref.new (E.start radiusSpec)

  -- Register opacity consumer
  _ <- C.register coord
    { tick: transitionConsumer opacityRef \value ->
        log $ "Opacity: " <> show value
    , onComplete: log "Opacity transition complete!"
    }

  -- Register radius consumer
  _ <- C.register coord
    { tick: transitionConsumer radiusRef \value ->
        log $ "Radius: " <> show value
    , onComplete: log "Radius transition complete!"
    }

  -- Start the loop
  C.start coord

  log "Coordinator started. Transitions running..."

-- =============================================================================
-- Example: Grouped Transitions (Multiple Values)
-- =============================================================================

-- | Run an example with a transition group (x, y, opacity together).
-- | Calls the provided callback with current values each frame.
exampleWithCallback
  :: ({ x :: Number, y :: Number, opacity :: Number } -> Effect Unit)
  -> Effect { coordinator :: C.Coordinator, stop :: Effect Unit }
exampleWithCallback onUpdate = do
  log "Starting grouped transition example..."

  coord <- C.create

  -- Create specs for x, y, and opacity
  let
    specs =
      [ E.transition { from: 0.0, to: 100.0 } { duration: 800.0, easing: QuadOut }      -- x
      , E.transition { from: 0.0, to: 50.0 } { duration: 800.0, easing: QuadOut }       -- y
      , E.transition { from: 0.0, to: 1.0 } { duration: 400.0, easing: Linear }          -- opacity (faster)
      ]

  -- Create the group
  groupRef <- Ref.new (E.group specs)

  -- Register group consumer
  _ <- C.register coord
    { tick: transitionGroupConsumer groupRef \values -> do
        case values of
          [x, y, opacity] -> onUpdate { x, y, opacity }
          _ -> pure unit
    , onComplete: log "All transitions complete!"
    }

  -- Start
  C.start coord

  pure
    { coordinator: coord
    , stop: C.stop coord
    }

-- =============================================================================
-- Example: Staggered Entry (Multiple Elements)
-- =============================================================================

-- | This would demonstrate staggered transitions where each element
-- | starts its animation after a delay.
-- |
-- | TODO: Implement when we add delay support to TransitionSpec
-- staggeredExample :: Int -> Effect Unit
