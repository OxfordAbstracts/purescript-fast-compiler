-- | Transition Engine
-- |
-- | A tick-driven transition engine for managing animated state changes.
-- | This provides a framework-agnostic way to animate values over time,
-- | suitable for both Halogen and React integrations.
-- |
-- | Key concepts:
-- | - **TransitionSpec**: Defines what to animate (from/to values, duration, easing)
-- | - **TransitionState**: Current state of an in-flight transition
-- | - **TransitionGroup**: Manages multiple coordinated transitions
-- |
-- | Design goals:
-- | - Pure, deterministic state updates (no side effects)
-- | - Works with any tick source (simulation tick, RAF, manual)
-- | - Composable with existing Hylograph infrastructure
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Transition.Engine as E
-- | import Hylograph.Transition.Easing (EasingType(..))
-- |
-- | -- Create a transition spec
-- | let spec = E.transition
-- |       { from: 0.0, to: 100.0 }
-- |       { duration: 500.0, easing: QuadOut }
-- |
-- | -- Start the transition
-- | let state = E.start spec
-- |
-- | -- In tick handler: advance by delta (milliseconds)
-- | let state' = E.tick 16.67 state
-- |
-- | -- Get current value
-- | let current = E.currentValue state'
-- | ```
module Hylograph.Transition.Engine
  ( -- * Transition specification
    TransitionSpec
  , TransitionConfig
  , transition
  , transitionWith
  , withDelay
    -- * Transition state
  , TransitionState
  , start
  , tick
  , tickBy
  , currentValue
  , currentProgress
  , isComplete
  , remaining
    -- * Transition groups (multiple coordinated transitions)
  , TransitionGroup
  , group
  , groupTick
  , groupValues
  , groupComplete
  , groupRemaining
    -- * Staggered transitions
  , staggeredGroup
  , staggeredSpecs
  , IndexedTransition
  , IndexedTransitionGroup
  , staggeredGroupIndexed
  , indexedGroupTick
  , indexedValues
  , indexedGroupComplete
  , indexedGroupRemaining
    -- * Utilities
  , defaultConfig
  , Milliseconds
  ) where

import Prelude

import Data.Array (mapWithIndex, (..))
import Data.Foldable (all, maximum)
import Data.Int (toNumber)
import Data.Maybe (fromMaybe)
import Hylograph.Transition.Tick (Progress, lerp)
import Hylograph.Transition.Easing (EasingType(..), toFunction)

-- =============================================================================
-- Types
-- =============================================================================

-- | Duration in milliseconds
type Milliseconds = Number

-- | Configuration for a transition
type TransitionConfig =
  { duration :: Milliseconds  -- ^ How long the transition takes
  , easing :: EasingType      -- ^ Easing function to apply
  , delay :: Milliseconds     -- ^ Optional delay before starting
  }

-- | Default configuration: 300ms, QuadOut, no delay
defaultConfig :: TransitionConfig
defaultConfig =
  { duration: 300.0
  , easing: QuadOut
  , delay: 0.0
  }

-- | Specification for a transition
-- | Defines the start/end values and how to get there
type TransitionSpec a =
  { from :: a
  , to :: a
  , interpolate :: a -> a -> Progress -> a
  , config :: TransitionConfig
  }

-- | Create a transition spec for Numbers
-- | Uses linear interpolation by default
transition
  :: { from :: Number, to :: Number }
  -> { duration :: Milliseconds, easing :: EasingType }
  -> TransitionSpec Number
transition values opts =
  { from: values.from
  , to: values.to
  , interpolate: lerp
  , config:
      { duration: opts.duration
      , easing: opts.easing
      , delay: 0.0
      }
  }

-- | Create a transition spec with custom interpolation
transitionWith
  :: forall a
   . (a -> a -> Progress -> a)  -- ^ Interpolation function
  -> { from :: a, to :: a }
  -> TransitionConfig
  -> TransitionSpec a
transitionWith interpolate values config =
  { from: values.from
  , to: values.to
  , interpolate
  , config
  }

-- =============================================================================
-- Transition State
-- =============================================================================

-- | State of an active transition
type TransitionState a =
  { spec :: TransitionSpec a
  , elapsed :: Milliseconds   -- ^ Time elapsed since start
  , current :: a              -- ^ Current interpolated value
  }

-- | Start a transition from the beginning
start :: forall a. TransitionSpec a -> TransitionState a
start spec =
  { spec
  , elapsed: 0.0
  , current: spec.from
  }

-- | Advance a transition by a time delta (in milliseconds)
tick :: forall a. Milliseconds -> TransitionState a -> TransitionState a
tick delta state = tickBy delta state

-- | Advance a transition by a time delta (in milliseconds)
-- | Alias for tick with clearer name
tickBy :: forall a. Milliseconds -> TransitionState a -> TransitionState a
tickBy delta state =
  let
    newElapsed = state.elapsed + delta
    effectiveElapsed = max 0.0 (newElapsed - state.spec.config.delay)
    rawProgress = effectiveElapsed / state.spec.config.duration
    clampedProgress = min 1.0 (max 0.0 rawProgress)
    easingFn = toFunction state.spec.config.easing
    easedProgress = easingFn clampedProgress
    newValue = state.spec.interpolate state.spec.from state.spec.to easedProgress
  in
    state
      { elapsed = newElapsed
      , current = newValue
      }

-- | Get the current interpolated value
currentValue :: forall a. TransitionState a -> a
currentValue = _.current

-- | Get the current progress (0.0 to 1.0)
currentProgress :: forall a. TransitionState a -> Progress
currentProgress state =
  let
    effectiveElapsed = max 0.0 (state.elapsed - state.spec.config.delay)
    raw = effectiveElapsed / state.spec.config.duration
  in
    min 1.0 (max 0.0 raw)

-- | Check if the transition is complete
isComplete :: forall a. TransitionState a -> Boolean
isComplete state =
  state.elapsed >= (state.spec.config.duration + state.spec.config.delay)

-- | Get remaining time in milliseconds
remaining :: forall a. TransitionState a -> Milliseconds
remaining state =
  max 0.0 (state.spec.config.duration + state.spec.config.delay - state.elapsed)

-- =============================================================================
-- Transition Groups
-- =============================================================================

-- | A group of coordinated transitions that tick together
-- | Useful for animating multiple properties in sync
newtype TransitionGroup = TransitionGroup
  { transitions :: Array (TransitionState Number)
  }

-- | Create a group from multiple transition specs
group :: Array (TransitionSpec Number) -> TransitionGroup
group specs = TransitionGroup
  { transitions: map start specs
  }

-- | Tick all transitions in a group
groupTick :: Milliseconds -> TransitionGroup -> TransitionGroup
groupTick delta (TransitionGroup g) = TransitionGroup
  { transitions: map (tick delta) g.transitions
  }

-- | Get current values from all transitions in group
groupValues :: TransitionGroup -> Array Number
groupValues (TransitionGroup g) = map currentValue g.transitions

-- | Check if all transitions in group are complete
groupComplete :: TransitionGroup -> Boolean
groupComplete (TransitionGroup g) = all isComplete g.transitions

-- | Get maximum remaining time in group
groupRemaining :: TransitionGroup -> Milliseconds
groupRemaining (TransitionGroup g) =
  fromMaybe 0.0 $ maximum $ map remaining g.transitions

-- =============================================================================
-- Staggered Transitions
-- =============================================================================

-- | Add a delay to a transition spec
withDelay :: forall a. Milliseconds -> TransitionSpec a -> TransitionSpec a
withDelay delay spec =
  spec { config = spec.config { delay = delay } }

-- | Create staggered specs from a base spec and count
-- | Each transition gets an additional delay based on its index
-- |
-- | Example: staggeredSpecs 5 50.0 baseSpec
-- |   -> 5 specs with delays 0ms, 50ms, 100ms, 150ms, 200ms
staggeredSpecs
  :: Int                   -- ^ Number of transitions
  -> Milliseconds          -- ^ Delay between each transition
  -> TransitionSpec Number -- ^ Base spec (from/to will be the same for all)
  -> Array (TransitionSpec Number)
staggeredSpecs count staggerDelay baseSpec =
  map mkSpec (0 .. (count - 1))
  where
    mkSpec :: Int -> TransitionSpec Number
    mkSpec i =
      let indexDelay = toNumber i * staggerDelay
      in withDelay (baseSpec.config.delay + indexDelay) baseSpec

-- | Create a staggered group from multiple value pairs
-- | Each transition animates between its own from/to values with staggered timing
-- |
-- | Example:
-- | ```purescript
-- | let specs = staggeredGroup
-- |       [{ from: 0.0, to: 100.0 }, { from: 50.0, to: 150.0 }]
-- |       50.0
-- |       { duration: 300.0, easing: QuadOut }
-- | ```
staggeredGroup
  :: Array { from :: Number, to :: Number }  -- ^ Value pairs for each element
  -> Milliseconds                            -- ^ Delay between each transition
  -> { duration :: Milliseconds, easing :: EasingType }
  -> TransitionGroup
staggeredGroup valuePairs staggerDelay opts =
  TransitionGroup { transitions: mapWithIndex mkTransition valuePairs }
  where
    mkTransition :: Int -> { from :: Number, to :: Number } -> TransitionState Number
    mkTransition i values =
      let
        indexDelay = toNumber i * staggerDelay
        spec = transition values opts
        delayedSpec = withDelay indexDelay spec
      in start delayedSpec

-- | A transition with its associated index (for tracking which element it belongs to)
type IndexedTransition =
  { index :: Int
  , state :: TransitionState Number
  }

-- | Newtype for indexed transition groups
newtype IndexedTransitionGroup = IndexedTransitionGroup
  { transitions :: Array IndexedTransition
  }

-- | Create a staggered group that tracks element indices
-- | Useful when you need to know which value corresponds to which data element
staggeredGroupIndexed
  :: Array { from :: Number, to :: Number }  -- ^ Value pairs for each element
  -> Milliseconds                            -- ^ Delay between each transition
  -> { duration :: Milliseconds, easing :: EasingType }
  -> IndexedTransitionGroup
staggeredGroupIndexed valuePairs staggerDelay opts =
  IndexedTransitionGroup { transitions: mapWithIndex mkTransition valuePairs }
  where
    mkTransition :: Int -> { from :: Number, to :: Number } -> IndexedTransition
    mkTransition i values =
      let
        indexDelay = toNumber i * staggerDelay
        spec = transition values opts
        delayedSpec = withDelay indexDelay spec
      in { index: i, state: start delayedSpec }

-- | Tick all transitions in an indexed group
indexedGroupTick :: Milliseconds -> IndexedTransitionGroup -> IndexedTransitionGroup
indexedGroupTick delta (IndexedTransitionGroup g) = IndexedTransitionGroup
  { transitions: map tickIndexed g.transitions
  }
  where
    tickIndexed :: IndexedTransition -> IndexedTransition
    tickIndexed t = t { state = tick delta t.state }

-- | Get current values with their indices
indexedValues :: IndexedTransitionGroup -> Array { index :: Int, value :: Number }
indexedValues (IndexedTransitionGroup g) =
  map (\t -> { index: t.index, value: currentValue t.state }) g.transitions

-- | Check if all transitions in indexed group are complete
indexedGroupComplete :: IndexedTransitionGroup -> Boolean
indexedGroupComplete (IndexedTransitionGroup g) =
  all (\t -> isComplete t.state) g.transitions

-- | Get maximum remaining time in indexed group
indexedGroupRemaining :: IndexedTransitionGroup -> Milliseconds
indexedGroupRemaining (IndexedTransitionGroup g) =
  fromMaybe 0.0 $ maximum $ map (\t -> remaining t.state) g.transitions
