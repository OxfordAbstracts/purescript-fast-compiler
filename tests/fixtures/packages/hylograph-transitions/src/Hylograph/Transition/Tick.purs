-- | Tick-Driven Transitions
-- |
-- | Primitives for animating transitions using simulation ticks rather than CSS.
-- | This is the simulation-aware analog to d3-transition.
-- |
-- | Key insight: Force simulations already have a tick loop. We can use that
-- | same loop to drive enter/exit/update animations, giving us:
-- | - Predictable, debuggable behavior
-- | - No CSS timing coordination
-- | - Pure PureScript interpolation
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Transition.Tick as T
-- |
-- | -- In your state
-- | type State = { entering :: Map String Progress, exiting :: Array (Transitioning Node) }
-- |
-- | -- In tick handler
-- | onTick state = do
-- |   let { active: stillEntering } = T.tickProgressMap 0.025 state.entering
-- |   let { active: stillExiting } = T.tickTransitions 0.025 state.exiting
-- |   -- render with interpolated values
-- |
-- | -- In render
-- | radius = case enterProgress of
-- |   Just p -> T.lerp 20.0 5.0 (T.easeOut p)
-- |   Nothing -> 5.0
-- | ```
module Hylograph.Transition.Tick
  ( -- * Types
    Progress
  , TickDelta
  , Transitioning
  , Easing
    -- * Progress Map operations (for key-based tracking)
  , tickProgressMap
  , startProgress
  , startProgressFrom
    -- * Transitioning Array operations (for item-based tracking)
  , tickTransitions
  , startTransitions
  , startTransitionsFrom
    -- * Interpolation
  , lerp
  , lerpClamped
  , lerpInt
    -- * Easing functions (Quad/Cubic)
  , linear
  , easeIn
  , easeOut
  , easeInOut
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
    -- * Easing functions (Sinusoidal)
  , easeInSin
  , easeOutSin
  , easeInOutSin
    -- * Easing functions (Exponential)
  , easeInExp
  , easeOutExp
  , easeInOutExp
    -- * Easing functions (Circular)
  , easeInCircle
  , easeOutCircle
  , easeInOutCircle
    -- * Easing functions (Back - overshoot)
  , easeInBack
  , easeOutBack
  , easeInOutBack
    -- * Easing functions (Elastic - spring)
  , easeInElastic
  , easeOutElastic
  , easeInOutElastic
    -- * Easing functions (Bounce)
  , easeInBounce
  , easeOutBounce
  , easeInOutBounce
    -- * Combinators
  , withEasing
  , ticksForDuration
  ) where

import Prelude

import Data.Array as Array
import Data.Int (round, toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Number (cos, pi, pow, sin, sqrt)
import Data.Set as Set

-- =============================================================================
-- Types
-- =============================================================================

-- | Progress from 0.0 (start) to 1.0 (complete)
type Progress = Number

-- | Amount to advance progress each tick
-- | At 60fps: 0.025 ≈ 40 ticks ≈ 0.67 seconds
-- | At 60fps: 0.020 ≈ 50 ticks ≈ 0.83 seconds
-- | At 60fps: 0.015 ≈ 67 ticks ≈ 1.1 seconds
type TickDelta = Number

-- | An item in transition, carrying its state and progress
type Transitioning a = { item :: a, progress :: Progress }

-- | Easing function: maps linear progress to eased progress
type Easing = Progress -> Progress

-- =============================================================================
-- Progress Map Operations
-- =============================================================================

-- | Advance all progress values in a Map, partitioning into active and completed
-- |
-- | ```purescript
-- | let { active, completed } = tickProgressMap 0.025 enteringNodes
-- | -- active: nodes still animating
-- | -- completed: keys that just finished (for cleanup, callbacks, etc.)
-- | ```
tickProgressMap
  :: forall k
   . Ord k
  => TickDelta
  -> Map k Progress
  -> { active :: Map k Progress, completed :: Array k }
tickProgressMap delta progressMap =
  let
    advanced = map (\p -> min 1.0 (p + delta)) progressMap
    active = Map.filter (\p -> p < 1.0) advanced
    completed = Set.toUnfoldable $ Map.keys $ Map.filter (\p -> p >= 1.0) advanced
  in
    { active, completed }

-- | Start tracking progress for new keys (from 0.0)
startProgress :: forall k. Ord k => Array k -> Map k Progress -> Map k Progress
startProgress keys existing =
  Array.foldl (\m k -> Map.insert k 0.0 m) existing keys

-- | Start tracking progress for new keys from a specific value
startProgressFrom :: forall k. Ord k => Progress -> Array k -> Map k Progress -> Map k Progress
startProgressFrom initial keys existing =
  Array.foldl (\m k -> Map.insert k initial m) existing keys

-- =============================================================================
-- Transitioning Array Operations
-- =============================================================================

-- | Advance all transitions, partitioning into active and completed
-- |
-- | ```purescript
-- | let { active, completed } = tickTransitions 0.025 exitingNodes
-- | -- active: items still animating out
-- | -- completed: items that finished (now safe to remove from DOM)
-- | ```
tickTransitions
  :: forall a
   . TickDelta
  -> Array (Transitioning a)
  -> { active :: Array (Transitioning a), completed :: Array a }
tickTransitions delta transitions =
  let
    advanced = map (\t -> t { progress = min 1.0 (t.progress + delta) }) transitions
    active = Array.filter (\t -> t.progress < 1.0) advanced
    completed = map _.item $ Array.filter (\t -> t.progress >= 1.0) advanced
  in
    { active, completed }

-- | Wrap items as transitions starting at progress 0.0
startTransitions :: forall a. Array a -> Array (Transitioning a)
startTransitions = map (\item -> { item, progress: 0.0 })

-- | Wrap items as transitions starting at a specific progress
startTransitionsFrom :: forall a. Progress -> Array a -> Array (Transitioning a)
startTransitionsFrom initial = map (\item -> { item, progress: initial })

-- =============================================================================
-- Interpolation
-- =============================================================================

-- | Linear interpolation between two numbers
-- |
-- | ```purescript
-- | lerp 0.0 100.0 0.5  -- 50.0
-- | lerp 20.0 5.0 1.0   -- 5.0 (shrink from 20 to 5)
-- | ```
lerp :: Number -> Number -> Progress -> Number
lerp start end t = start + (end - start) * t

-- | Linear interpolation with progress clamped to [0, 1]
lerpClamped :: Number -> Number -> Progress -> Number
lerpClamped start end t = lerp start end (clamp 0.0 1.0 t)

-- | Linear interpolation for integers
lerpInt :: Int -> Int -> Progress -> Int
lerpInt start end t = round $ lerp (toNumber start) (toNumber end) t

-- =============================================================================
-- Easing Functions
-- =============================================================================

-- | No easing (linear)
linear :: Easing
linear t = t

-- | Ease in (slow start, fast end) - alias for easeInQuad
easeIn :: Easing
easeIn = easeInQuad

-- | Ease out (fast start, slow end) - alias for easeOutQuad
easeOut :: Easing
easeOut = easeOutQuad

-- | Ease in-out (slow start and end) - alias for easeInOutQuad
easeInOut :: Easing
easeInOut = easeInOutQuad

-- | Quadratic ease in: t²
easeInQuad :: Easing
easeInQuad t = t * t

-- | Quadratic ease out: 1 - (1-t)²
easeOutQuad :: Easing
easeOutQuad t = 1.0 - (1.0 - t) * (1.0 - t)

-- | Quadratic ease in-out
easeInOutQuad :: Easing
easeInOutQuad t =
  if t < 0.5
    then 2.0 * t * t
    else 1.0 - ((-2.0 * t + 2.0) * (-2.0 * t + 2.0)) / 2.0

-- | Cubic ease in: t³
easeInCubic :: Easing
easeInCubic t = t * t * t

-- | Cubic ease out: 1 - (1-t)³
easeOutCubic :: Easing
easeOutCubic t = 1.0 - (1.0 - t) * (1.0 - t) * (1.0 - t)

-- | Cubic ease in-out
easeInOutCubic :: Easing
easeInOutCubic t =
  if t < 0.5
    then 4.0 * t * t * t
    else 1.0 - ((-2.0 * t + 2.0) * (-2.0 * t + 2.0) * (-2.0 * t + 2.0)) / 2.0

-- =============================================================================
-- Sinusoidal Easing
-- =============================================================================

-- | Sinusoidal ease in: 1 - cos(t * π/2)
easeInSin :: Easing
easeInSin t = 1.0 - cos(t * pi / 2.0)

-- | Sinusoidal ease out: sin(t * π/2)
easeOutSin :: Easing
easeOutSin t = sin(t * pi / 2.0)

-- | Sinusoidal ease in-out: -(cos(π * t) - 1) / 2
easeInOutSin :: Easing
easeInOutSin t = -(cos(pi * t) - 1.0) / 2.0

-- =============================================================================
-- Exponential Easing
-- =============================================================================

-- | Exponential ease in: 2^(10 * (t - 1))
easeInExp :: Easing
easeInExp t =
  if t == 0.0 then 0.0
  else pow 2.0 (10.0 * (t - 1.0))

-- | Exponential ease out: 1 - 2^(-10 * t)
easeOutExp :: Easing
easeOutExp t =
  if t == 1.0 then 1.0
  else 1.0 - pow 2.0 (-10.0 * t)

-- | Exponential ease in-out
easeInOutExp :: Easing
easeInOutExp t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else if t < 0.5 then pow 2.0 (20.0 * t - 10.0) / 2.0
  else (2.0 - pow 2.0 (-20.0 * t + 10.0)) / 2.0

-- =============================================================================
-- Circular Easing
-- =============================================================================

-- | Circular ease in: 1 - sqrt(1 - t²)
easeInCircle :: Easing
easeInCircle t = 1.0 - sqrt(1.0 - t * t)

-- | Circular ease out: sqrt(1 - (t - 1)²)
easeOutCircle :: Easing
easeOutCircle t = sqrt(1.0 - (t - 1.0) * (t - 1.0))

-- | Circular ease in-out
easeInOutCircle :: Easing
easeInOutCircle t =
  if t < 0.5
    then (1.0 - sqrt(1.0 - (2.0 * t) * (2.0 * t))) / 2.0
    else (sqrt(1.0 - (-2.0 * t + 2.0) * (-2.0 * t + 2.0)) + 1.0) / 2.0

-- =============================================================================
-- Back Easing (Overshoot)
-- =============================================================================

-- Overshoot constant (standard value from Robert Penner's easing)
backC1 :: Number
backC1 = 1.70158

backC2 :: Number
backC2 = backC1 * 1.525

backC3 :: Number
backC3 = backC1 + 1.0

-- | Back ease in: overshoots then returns
easeInBack :: Easing
easeInBack t = backC3 * t * t * t - backC1 * t * t

-- | Back ease out: overshoots past target then settles
easeOutBack :: Easing
easeOutBack t =
  let t' = t - 1.0
  in 1.0 + backC3 * t' * t' * t' + backC1 * t' * t'

-- | Back ease in-out: overshoots on both ends
easeInOutBack :: Easing
easeInOutBack t =
  if t < 0.5
    then ((2.0 * t) * (2.0 * t) * ((backC2 + 1.0) * 2.0 * t - backC2)) / 2.0
    else ((2.0 * t - 2.0) * (2.0 * t - 2.0) * ((backC2 + 1.0) * (t * 2.0 - 2.0) + backC2) + 2.0) / 2.0

-- =============================================================================
-- Elastic Easing (Spring)
-- =============================================================================

-- Elastic constants
elasticC4 :: Number
elasticC4 = (2.0 * pi) / 3.0

elasticC5 :: Number
elasticC5 = (2.0 * pi) / 4.5

-- | Elastic ease in: spring-like start
easeInElastic :: Easing
easeInElastic t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else -pow 2.0 (10.0 * t - 10.0) * sin((t * 10.0 - 10.75) * elasticC4)

-- | Elastic ease out: spring-like end (most common)
easeOutElastic :: Easing
easeOutElastic t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else pow 2.0 (-10.0 * t) * sin((t * 10.0 - 0.75) * elasticC4) + 1.0

-- | Elastic ease in-out: spring on both ends
easeInOutElastic :: Easing
easeInOutElastic t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else if t < 0.5
    then -(pow 2.0 (20.0 * t - 10.0) * sin((20.0 * t - 11.125) * elasticC5)) / 2.0
    else (pow 2.0 (-20.0 * t + 10.0) * sin((20.0 * t - 11.125) * elasticC5)) / 2.0 + 1.0

-- =============================================================================
-- Bounce Easing
-- =============================================================================

-- Bounce constants
bounceN1 :: Number
bounceN1 = 7.5625

bounceD1 :: Number
bounceD1 = 2.75

-- | Bounce ease out: ball bouncing to rest
easeOutBounce :: Easing
easeOutBounce t =
  if t < 1.0 / bounceD1 then
    bounceN1 * t * t
  else if t < 2.0 / bounceD1 then
    let t' = t - 1.5 / bounceD1
    in bounceN1 * t' * t' + 0.75
  else if t < 2.5 / bounceD1 then
    let t' = t - 2.25 / bounceD1
    in bounceN1 * t' * t' + 0.9375
  else
    let t' = t - 2.625 / bounceD1
    in bounceN1 * t' * t' + 0.984375

-- | Bounce ease in: reverse of bounce out
easeInBounce :: Easing
easeInBounce t = 1.0 - easeOutBounce (1.0 - t)

-- | Bounce ease in-out: bounce on both ends
easeInOutBounce :: Easing
easeInOutBounce t =
  if t < 0.5
    then (1.0 - easeOutBounce (1.0 - 2.0 * t)) / 2.0
    else (1.0 + easeOutBounce (2.0 * t - 1.0)) / 2.0

-- =============================================================================
-- Combinators
-- =============================================================================

-- | Apply easing to an interpolation function
-- |
-- | ```purescript
-- | -- Ease-out shrink from 20 to 5
-- | radius = withEasing easeOut (lerp 20.0 5.0) progress
-- | ```
withEasing :: forall a. Easing -> (Progress -> a) -> Progress -> a
withEasing ease f t = f (ease t)

-- | Calculate tick delta for a desired duration at assumed 60fps
-- |
-- | ```purescript
-- | ticksForDuration 1000  -- 0.0167 (1 second at 60fps)
-- | ticksForDuration 500   -- 0.0333 (0.5 seconds)
-- | ```
ticksForDuration :: Int -> TickDelta
ticksForDuration milliseconds =
  let ticks = toNumber milliseconds / 16.67  -- ~60fps
  in 1.0 / ticks

-- Note: Uses Prelude's clamp function
