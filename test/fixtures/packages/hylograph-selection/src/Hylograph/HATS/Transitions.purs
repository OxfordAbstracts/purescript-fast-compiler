-- | HATS Tick-Driven Transitions
-- |
-- | Provides tick-driven transition state management for HATS GUP animations.
-- | Instead of using Web Animations API, transitions are driven by explicit
-- | tick calls, allowing integration with force simulations and other tick sources.
-- |
-- | Architecture note: The transition primitives (Tick, Easing, Interpolate, Engine)
-- | live in Hylograph.Transition.*. These are general-purpose and could potentially be
-- | extracted to a separate hylograph-transitions library in the future, mirroring
-- | D3's d3-ease/d3-interpolate/d3-transition structure.
-- |
-- | Usage:
-- | ```purescript
-- | -- In your component, after rerender:
-- | result <- HATS.rerenderWithTransitions selector tree
-- | case result.transitions of
-- |   Nothing -> pure unit
-- |   Just ts -> startTickLoop ts
-- |
-- | -- In your tick handler:
-- | case tickTransitions deltaMs transitions of
-- |   Complete -> stopTickLoop
-- |   Running newTs -> continue with newTs
-- | ```
module Hylograph.HATS.Transitions
  ( -- * Transition state types
    HATSTransitions(..)
  , ElementTransitions
  , AttrTransition
  , TransitionResult(..)
    -- * Tick function
  , tickTransitions
  , isComplete
    -- * Easing conversion
  , toTickEasing
  ) where

import Prelude

import Data.Array (filter, null)
import Data.Foldable (all)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Hylograph.Internal.Transition.Types (Easing(..)) as HATS
import Hylograph.Transition.Tick (Progress, lerp)
import Hylograph.Transition.Tick as Tick
import Web.DOM.Element (Element)

-- Foreign imports for DOM operations
foreign import setAttribute :: Element -> String -> String -> Effect Unit
foreign import removeElement :: Element -> Effect Unit

-- =============================================================================
-- Types
-- =============================================================================

-- | State for a single attribute transition
type AttrTransition =
  { attrName :: String
  , from :: Number
  , to :: Number
  , elapsed :: Number      -- Milliseconds elapsed
  , duration :: Number     -- Total duration in ms
  , delay :: Number        -- Delay before starting in ms
  , easing :: Tick.Easing  -- Easing function
  }

-- | All transitions for one element
type ElementTransitions =
  { element :: Element
  , attrs :: Array AttrTransition
  }

-- | All active HATS transitions
-- | Entering/updating elements just need attr updates
-- | Exiting elements need to be removed when complete
newtype HATSTransitions = HATSTransitions
  { entering :: Array ElementTransitions
  , updating :: Array ElementTransitions
  , exiting :: Array ElementTransitions
  }

-- | Result of ticking transitions
data TransitionResult
  = Running HATSTransitions  -- Still animating
  | Complete                 -- All done

-- =============================================================================
-- Tick Function
-- =============================================================================

-- | Advance all transitions by deltaMs and apply current values to DOM
-- |
-- | Returns Running with updated state, or Complete when all finished.
tickTransitions :: Number -> HATSTransitions -> Effect TransitionResult
tickTransitions deltaMs (HATSTransitions ts) = do
  -- Tick and apply entering transitions
  entering' <- traverse (tickElement deltaMs) ts.entering
  let activeEntering = filter (not <<< elementComplete) entering'

  -- Tick and apply updating transitions
  updating' <- traverse (tickElement deltaMs) ts.updating
  let activeUpdating = filter (not <<< elementComplete) updating'

  -- Tick exiting transitions and remove completed ones
  exiting' <- traverse (tickElement deltaMs) ts.exiting
  let completedExits = filter elementComplete exiting'
  let activeExiting = filter (not <<< elementComplete) exiting'

  -- Remove completed exit elements from DOM
  _ <- traverse (\et -> removeElement et.element) completedExits

  -- Check if all done
  if null activeEntering && null activeUpdating && null activeExiting
    then pure Complete
    else pure $ Running $ HATSTransitions
      { entering: activeEntering
      , updating: activeUpdating
      , exiting: activeExiting
      }

-- | Check if all transitions are complete (without ticking)
isComplete :: HATSTransitions -> Boolean
isComplete (HATSTransitions ts) =
  all elementComplete ts.entering &&
  all elementComplete ts.updating &&
  all elementComplete ts.exiting

-- =============================================================================
-- Internal: Element and Attribute Ticking
-- =============================================================================

-- | Tick all attributes on an element and apply current values
tickElement :: Number -> ElementTransitions -> Effect ElementTransitions
tickElement deltaMs et = do
  -- Tick each attribute
  let attrs' = map (tickAttr deltaMs) et.attrs
  -- Apply current values to DOM
  _ <- traverse (applyAttr et.element) attrs'
  pure { element: et.element, attrs: attrs' }

-- | Tick a single attribute transition
tickAttr :: Number -> AttrTransition -> AttrTransition
tickAttr deltaMs attr =
  attr { elapsed = attr.elapsed + deltaMs }

-- | Apply current interpolated value to DOM
applyAttr :: Element -> AttrTransition -> Effect Unit
applyAttr el attr = do
  let value = currentAttrValue attr
  setAttribute el attr.attrName (show value)

-- | Get the current interpolated value for an attribute
currentAttrValue :: AttrTransition -> Number
currentAttrValue attr =
  let
    -- Account for delay
    effectiveElapsed = max 0.0 (attr.elapsed - attr.delay)
    -- Calculate raw progress (0 to 1)
    rawProgress = if attr.duration <= 0.0
      then 1.0
      else min 1.0 (effectiveElapsed / attr.duration)
    -- Apply easing
    easedProgress = attr.easing rawProgress
  in
    lerp attr.from attr.to easedProgress

-- | Check if an element's transitions are all complete
elementComplete :: ElementTransitions -> Boolean
elementComplete et = all attrComplete et.attrs

-- | Check if a single attribute transition is complete
attrComplete :: AttrTransition -> Boolean
attrComplete attr = attr.elapsed >= (attr.duration + attr.delay)

-- =============================================================================
-- Easing Conversion
-- =============================================================================

-- | Convert HATS Easing to Tick Easing function
toTickEasing :: Maybe HATS.Easing -> Tick.Easing
toTickEasing = case _ of
  Nothing -> Tick.easeOutCubic  -- Default
  Just e -> case e of
    HATS.Linear -> Tick.linear
    HATS.Cubic -> Tick.easeOutCubic
    HATS.CubicIn -> Tick.easeInCubic
    HATS.CubicOut -> Tick.easeOutCubic
    HATS.CubicInOut -> Tick.easeInOutCubic
    HATS.Quad -> Tick.easeOutQuad
    HATS.QuadIn -> Tick.easeInQuad
    HATS.QuadOut -> Tick.easeOutQuad
    HATS.QuadInOut -> Tick.easeInOutQuad
    HATS.Sin -> Tick.easeOutSin
    HATS.SinIn -> Tick.easeInSin
    HATS.SinOut -> Tick.easeOutSin
    HATS.SinInOut -> Tick.easeInOutSin
    HATS.Exp -> Tick.easeOutExp
    HATS.ExpIn -> Tick.easeInExp
    HATS.ExpOut -> Tick.easeOutExp
    HATS.ExpInOut -> Tick.easeInOutExp
    HATS.Circle -> Tick.easeOutCircle
    HATS.CircleIn -> Tick.easeInCircle
    HATS.CircleOut -> Tick.easeOutCircle
    HATS.CircleInOut -> Tick.easeInOutCircle
    HATS.Elastic -> Tick.easeOutElastic
    HATS.ElasticIn -> Tick.easeInElastic
    HATS.ElasticOut -> Tick.easeOutElastic
    HATS.ElasticInOut -> Tick.easeInOutElastic
    HATS.Back -> Tick.easeOutBack
    HATS.BackIn -> Tick.easeInBack
    HATS.BackOut -> Tick.easeOutBack
    HATS.BackInOut -> Tick.easeInOutBack
    HATS.Bounce -> Tick.easeOutBounce
    HATS.BounceIn -> Tick.easeInBounce
    HATS.BounceOut -> Tick.easeOutBounce
    HATS.BounceInOut -> Tick.easeInOutBounce
