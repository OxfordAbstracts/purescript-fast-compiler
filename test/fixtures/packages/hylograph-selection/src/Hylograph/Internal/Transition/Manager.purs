-- | Element Transition Manager
-- |
-- | Manages per-element attribute animations using the pure transition engine.
-- | This module bridges the `AnimatedAttr` type from the DSL to the actual
-- | animation execution via the Coordinator.
-- |
-- | Key responsibilities:
-- | - Track active transitions per element/attribute pair
-- | - Handle interruption (new transition cancels existing one for same target)
-- | - Provide tick function for Coordinator integration
-- | - Clean up completed transitions
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Internal.Transition.Manager as Manager
-- |
-- | -- Create a manager
-- | manager <- Manager.create
-- |
-- | -- Register a transition
-- | Manager.registerTransition manager element "opacity"
-- |   { from: 0.0, to: 1.0, duration: 500.0, easing: QuadOut, delay: 0.0 }
-- |
-- | -- Convert to Coordinator consumer
-- | let consumer = Manager.toCoordinatorConsumer manager
-- | Coordinator.register coordinator { tick: consumer, onComplete: pure unit }
-- | ```
module Hylograph.Internal.Transition.Manager
  ( -- * Manager type
    ElementTransitionManager
  , TransitionId
  , TransitionSpec
  , CompoundTransitionSpec
  , Milliseconds
    -- * Creation and registration
  , create
  , registerTransition
  , registerAnimatedAttr
  , registerAnimatedCompound
    -- * Coordinator integration
  , toCoordinatorConsumer
  , tick
    -- * Utilities
  , activeCount
  , clear
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Int (toNumber)
import Hylograph.Transition.Coordinator (TickResult(..)) as Coordinator
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Web.DOM.Element (Element)
import Web.DOM.Element as Element

import Hylograph.Internal.Attribute (AnimatedValue(..), AnimationConfig, EasingType(..))

-- =============================================================================
-- Types
-- =============================================================================

-- | Milliseconds type alias
type Milliseconds = Number

-- | Unique identifier for a transition
newtype TransitionId = TransitionId Int

derive instance Eq TransitionId
derive instance Ord TransitionId

instance Show TransitionId where
  show (TransitionId n) = "TransitionId(" <> show n <> ")"

-- | Key for tracking transitions: element identity + attribute name
type TransitionKey =
  { elementId :: String  -- Element identifier (we'll use a generated ID)
  , attrName :: String
  }

-- | Specification for a single-value transition
type TransitionSpec =
  { from :: Number
  , to :: Number
  , duration :: Milliseconds
  , easing :: EasingType
  , delay :: Milliseconds
  }

-- | Specification for a compound transition (multiple values → generated string)
-- | Used for paths where we animate sourceX, sourceY, targetX, targetY
-- | and regenerate the path string on each frame
type CompoundTransitionSpec =
  { fromValues :: Array Number   -- From values for each component
  , toValues :: Array Number     -- To values for each component
  , generator :: Array Number -> String  -- Combines interpolated values into final string
  , duration :: Milliseconds
  , easing :: EasingType
  , delay :: Milliseconds
  }

-- | Transition type (single value or compound)
data TransitionType
  = SingleTransition TransitionSpec
  | CompoundTransition CompoundTransitionSpec

-- | State of an active transition
type ActiveTransition =
  { id :: TransitionId
  , element :: Element
  , attrName :: String
  , transitionType :: TransitionType
  , elapsed :: Milliseconds
  , onComplete :: Effect Unit
  }

-- | Manager state
type ManagerState =
  { transitions :: Map TransitionKey ActiveTransition
  , nextId :: Int
  , elementIds :: Map String String  -- Maps element reference to generated ID
  , nextElementId :: Int
  }

-- | The Element Transition Manager
newtype ElementTransitionManager = ElementTransitionManager (Ref ManagerState)

-- =============================================================================
-- Creation
-- =============================================================================

-- | Create a new transition manager
create :: Effect ElementTransitionManager
create = do
  ref <- Ref.new
    { transitions: Map.empty
    , nextId: 0
    , elementIds: Map.empty
    , nextElementId: 0
    }
  pure $ ElementTransitionManager ref

-- =============================================================================
-- Registration
-- =============================================================================

-- | Register a transition for an element attribute
-- |
-- | If a transition already exists for the same element/attribute pair,
-- | it will be interrupted (replaced) by this new transition.
-- |
-- | Returns the transition ID.
registerTransition
  :: ElementTransitionManager
  -> Element
  -> String  -- Attribute name
  -> TransitionSpec
  -> Effect TransitionId
registerTransition manager element attrName spec = do
  registerTransitionWithCallback manager element attrName spec (pure unit)

-- | Register a transition with a completion callback
registerTransitionWithCallback
  :: ElementTransitionManager
  -> Element
  -> String
  -> TransitionSpec
  -> Effect Unit  -- Completion callback
  -> Effect TransitionId
registerTransitionWithCallback manager element attrName spec onComplete =
  registerTransitionInternal manager element attrName (SingleTransition spec) onComplete

-- | Internal registration for any transition type
registerTransitionInternal
  :: ElementTransitionManager
  -> Element
  -> String
  -> TransitionType
  -> Effect Unit  -- Completion callback
  -> Effect TransitionId
registerTransitionInternal (ElementTransitionManager ref) element attrName transitionType onComplete = do
  state <- Ref.read ref

  -- Get or create element ID for this element
  let elemRef = unsafeElementRef element
  Tuple elementId newState <- case Map.lookup elemRef state.elementIds of
    Just eid -> pure $ Tuple eid state
    Nothing -> do
      let eid = "elem-" <> show state.nextElementId
      let newIds = Map.insert elemRef eid state.elementIds
      pure $ Tuple eid (state { elementIds = newIds, nextElementId = state.nextElementId + 1 })

  -- Create transition key
  let key = { elementId, attrName }

  -- Create new transition
  let transitionId = TransitionId newState.nextId
  let transition =
        { id: transitionId
        , element
        , attrName
        , transitionType
        , elapsed: 0.0
        , onComplete
        }

  -- Insert (replacing any existing transition for this key)
  let newTransitions = Map.insert key transition newState.transitions

  Ref.write
    (newState { transitions = newTransitions, nextId = newState.nextId + 1 })
    ref

  pure transitionId

-- | Register an animated attribute for an element
-- |
-- | Evaluates the AnimatedValue specifications with the datum and index,
-- | creates a TransitionSpec, and registers the transition.
registerAnimatedAttr
  :: forall datum
   . ElementTransitionManager
  -> Element
  -> datum
  -> Int  -- Element index
  -> String  -- Attribute name
  -> Maybe (AnimatedValue datum)  -- From value (Nothing = read from DOM)
  -> AnimatedValue datum  -- To value
  -> AnimationConfig
  -> Effect Unit  -- Completion callback
  -> Effect TransitionId
registerAnimatedAttr manager element datum index attrName maybeFrom toValue config onComplete = do
  -- Evaluate the to value
  let to = evalAnimatedValue toValue datum index

  -- Evaluate the from value (or read from DOM if Nothing)
  from <- case maybeFrom of
    Just fromVal -> pure $ evalAnimatedValue fromVal datum index
    Nothing -> readAttributeNumber element attrName

  -- Create spec
  let spec =
        { from
        , to
        , duration: config.duration
        , easing: config.easing
        , delay: config.delay
        }

  registerTransitionWithCallback manager element attrName spec onComplete

-- | Register a compound animated attribute (for paths and other generated values)
-- |
-- | Evaluates the AnimatedValue arrays for from/to values, and registers
-- | a compound transition that interpolates all values and calls the generator
-- | to produce the final string value on each frame.
registerAnimatedCompound
  :: forall datum
   . ElementTransitionManager
  -> Element
  -> datum
  -> Int  -- Element index
  -> String  -- Attribute name (e.g., "d" for paths)
  -> Array (AnimatedValue datum)  -- From values
  -> Array (AnimatedValue datum)  -- To values
  -> (Array Number -> String)     -- Generator function
  -> AnimationConfig
  -> Effect Unit  -- Completion callback
  -> Effect TransitionId
registerAnimatedCompound manager element datum index attrName fromValues toValues generator config onComplete = do
  -- Evaluate all from/to values
  let evaluatedFroms = map (\av -> evalAnimatedValue av datum index) fromValues
  let evaluatedTos = map (\av -> evalAnimatedValue av datum index) toValues

  -- Create compound spec
  let compoundSpec =
        { fromValues: evaluatedFroms
        , toValues: evaluatedTos
        , generator
        , duration: config.duration
        , easing: config.easing
        , delay: config.delay
        }

  registerTransitionInternal manager element attrName (CompoundTransition compoundSpec) onComplete

-- | Evaluate an AnimatedValue with datum and index
evalAnimatedValue :: forall datum. AnimatedValue datum -> datum -> Int -> Number
evalAnimatedValue (StaticAnimValue n) _ _ = n
evalAnimatedValue (DataAnimValue f) d _ = f d
evalAnimatedValue (IndexedAnimValue f) d i = f d i

-- =============================================================================
-- Tick Processing
-- =============================================================================

-- | Process a single tick, advancing all transitions
-- |
-- | Returns array of completed transition IDs
tick :: ElementTransitionManager -> Milliseconds -> Effect (Array TransitionId)
tick (ElementTransitionManager ref) deltaMs = do
  state <- Ref.read ref

  -- Process each transition
  let transitions = Map.toUnfoldable state.transitions :: Array (Tuple TransitionKey ActiveTransition)

  completedIds <- Ref.new []

  for_ transitions \(Tuple key trans) -> do
    -- Advance elapsed time
    let newElapsed = trans.elapsed + deltaMs

    -- Get timing info based on transition type
    let { duration, delay, easing } = case trans.transitionType of
          SingleTransition spec -> { duration: spec.duration, delay: spec.delay, easing: spec.easing }
          CompoundTransition spec -> { duration: spec.duration, delay: spec.delay, easing: spec.easing }

    -- Calculate effective elapsed (accounting for delay)
    let effectiveElapsed = max 0.0 (newElapsed - delay)

    -- Calculate progress
    let rawProgress = effectiveElapsed / duration
    let clampedProgress = min 1.0 (max 0.0 rawProgress)

    -- Apply easing
    let easedProgress = applyEasing easing clampedProgress

    -- Apply value based on transition type
    case trans.transitionType of
      SingleTransition spec -> do
        -- Interpolate single value
        let currentValue = lerp spec.from spec.to easedProgress
        setAttribute trans.element trans.attrName (show currentValue)

      CompoundTransition spec -> do
        -- Interpolate all values and generate string
        let interpolatedValues = Array.zipWith
              (\from to -> lerp from to easedProgress)
              spec.fromValues
              spec.toValues
        let generatedValue = spec.generator interpolatedValues
        setAttribute trans.element trans.attrName generatedValue

    -- Check completion
    let isComplete = newElapsed >= (duration + delay)

    if isComplete then do
      -- Call completion callback
      trans.onComplete
      -- Mark for removal
      Ref.modify_ (\ids -> ids <> [trans.id]) completedIds
      -- Remove from map
      Ref.modify_ (\s -> s { transitions = Map.delete key s.transitions }) ref
    else do
      -- Update elapsed time
      Ref.modify_ (\s -> s { transitions = Map.update (\t -> Just (t { elapsed = newElapsed })) key s.transitions }) ref

  Ref.read completedIds

-- | Convert to a Coordinator-compatible consumer tick function
toCoordinatorConsumer :: ElementTransitionManager -> Milliseconds -> Effect Coordinator.TickResult
toCoordinatorConsumer manager deltaMs = do
  _ <- tick manager deltaMs
  count <- activeCount manager
  pure $ if count == 0 then Coordinator.Completed else Coordinator.StillRunning

-- =============================================================================
-- Utilities
-- =============================================================================

-- | Get the number of active transitions
activeCount :: ElementTransitionManager -> Effect Int
activeCount (ElementTransitionManager ref) = do
  state <- Ref.read ref
  pure $ Map.size state.transitions

-- | Clear all transitions (without calling completion callbacks)
clear :: ElementTransitionManager -> Effect Unit
clear (ElementTransitionManager ref) = do
  Ref.modify_ (_ { transitions = Map.empty }) ref

-- =============================================================================
-- Easing Functions
-- =============================================================================

-- | Apply an easing function to a progress value (0 to 1)
applyEasing :: EasingType -> Number -> Number
applyEasing Linear t = t
applyEasing QuadIn t = t * t
applyEasing QuadOut t = t * (2.0 - t)
applyEasing QuadInOut t =
  if t < 0.5
    then 2.0 * t * t
    else -1.0 + (4.0 - 2.0 * t) * t
applyEasing CubicIn t = t * t * t
applyEasing CubicOut t =
  let t' = t - 1.0
  in t' * t' * t' + 1.0
applyEasing CubicInOut t =
  if t < 0.5
    then 4.0 * t * t * t
    else (t - 1.0) * (2.0 * t - 2.0) * (2.0 * t - 2.0) + 1.0
applyEasing SinIn t = 1.0 - cos (t * pi / 2.0)
applyEasing SinOut t = sin (t * pi / 2.0)
applyEasing SinInOut t = -(cos (pi * t) - 1.0) / 2.0
applyEasing ExpIn t = if t == 0.0 then 0.0 else pow 2.0 (10.0 * (t - 1.0))
applyEasing ExpOut t = if t == 1.0 then 1.0 else 1.0 - pow 2.0 (-10.0 * t)
applyEasing ExpInOut t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else if t < 0.5 then pow 2.0 (20.0 * t - 10.0) / 2.0
  else (2.0 - pow 2.0 (-20.0 * t + 10.0)) / 2.0
applyEasing CircleIn t = 1.0 - sqrt (1.0 - t * t)
applyEasing CircleOut t = sqrt (1.0 - pow (t - 1.0) 2.0)
applyEasing CircleInOut t =
  if t < 0.5
    then (1.0 - sqrt (1.0 - pow (2.0 * t) 2.0)) / 2.0
    else (sqrt (1.0 - pow (-2.0 * t + 2.0) 2.0) + 1.0) / 2.0
applyEasing BackIn t =
  let c1 = 1.70158
      c3 = c1 + 1.0
  in c3 * t * t * t - c1 * t * t
applyEasing BackOut t =
  let c1 = 1.70158
      c3 = c1 + 1.0
      t' = t - 1.0
  in 1.0 + c3 * t' * t' * t' + c1 * t' * t'
applyEasing BackInOut t =
  let c1 = 1.70158
      c2 = c1 * 1.525
  in if t < 0.5
       then (pow (2.0 * t) 2.0 * ((c2 + 1.0) * 2.0 * t - c2)) / 2.0
       else (pow (2.0 * t - 2.0) 2.0 * ((c2 + 1.0) * (t * 2.0 - 2.0) + c2) + 2.0) / 2.0
applyEasing ElasticIn t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else
    let c4 = (2.0 * pi) / 3.0
    in -pow 2.0 (10.0 * t - 10.0) * sin ((t * 10.0 - 10.75) * c4)
applyEasing ElasticOut t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else
    let c4 = (2.0 * pi) / 3.0
    in pow 2.0 (-10.0 * t) * sin ((t * 10.0 - 0.75) * c4) + 1.0
applyEasing ElasticInOut t =
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else
    let c5 = (2.0 * pi) / 4.5
    in if t < 0.5
         then -(pow 2.0 (20.0 * t - 10.0) * sin ((20.0 * t - 11.125) * c5)) / 2.0
         else (pow 2.0 (-20.0 * t + 10.0) * sin ((20.0 * t - 11.125) * c5)) / 2.0 + 1.0
applyEasing BounceIn t = 1.0 - bounceOut (1.0 - t)
applyEasing BounceOut t = bounceOut t
applyEasing BounceInOut t =
  if t < 0.5
    then (1.0 - bounceOut (1.0 - 2.0 * t)) / 2.0
    else (1.0 + bounceOut (2.0 * t - 1.0)) / 2.0

-- | Bounce out helper
bounceOut :: Number -> Number
bounceOut t =
  let n1 = 7.5625
      d1 = 2.75
  in if t < 1.0 / d1 then
       n1 * t * t
     else if t < 2.0 / d1 then
       let t' = t - 1.5 / d1
       in n1 * t' * t' + 0.75
     else if t < 2.5 / d1 then
       let t' = t - 2.25 / d1
       in n1 * t' * t' + 0.9375
     else
       let t' = t - 2.625 / d1
       in n1 * t' * t' + 0.984375

-- =============================================================================
-- Math Helpers
-- =============================================================================

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp from to t = from + (to - from) * t

-- | Power function
foreign import pow :: Number -> Number -> Number

-- | Pi constant
pi :: Number
pi = 3.141592653589793

-- | Sine function
foreign import sin :: Number -> Number

-- | Cosine function
foreign import cos :: Number -> Number

-- | Square root
foreign import sqrt :: Number -> Number

-- =============================================================================
-- DOM Helpers
-- =============================================================================

-- | Set an attribute on an element
foreign import setAttribute :: Element -> String -> String -> Effect Unit

-- | Read a numeric attribute from an element (returns 0.0 if not parseable)
foreign import readAttributeNumber :: Element -> String -> Effect Number

-- | Get a unique reference string for an element (for comparison)
foreign import unsafeElementRef :: Element -> String
