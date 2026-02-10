-- | Easing Types
-- |
-- | An enumeration of all supported easing functions with runtime selection.
-- | This module complements Hylograph.Transition.Tick by providing a data type
-- | that can be stored, serialized, and used for UI selection.
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Transition.Easing (EasingType(..), toFunction)
-- | import Hylograph.Transition.Tick (lerp, withEasing)
-- |
-- | -- Store easing preference
-- | type Config = { easing :: EasingType, duration :: Int }
-- |
-- | -- Apply at runtime
-- | animate config progress =
-- |   withEasing (toFunction config.easing) (lerp 0.0 100.0) progress
-- | ```
module Hylograph.Transition.Easing
  ( EasingType(..)
  , toFunction
  , allEasingTypes
  , easingLabel
  , easingCategory
  ) where

import Prelude

import Hylograph.Transition.Tick as T

-- | Enumeration of all easing types
-- | Organized by category for UI presentation
data EasingType
  -- Standard
  = Linear
  -- Quadratic
  | QuadIn
  | QuadOut
  | QuadInOut
  -- Cubic
  | CubicIn
  | CubicOut
  | CubicInOut
  -- Sinusoidal
  | SinIn
  | SinOut
  | SinInOut
  -- Exponential
  | ExpIn
  | ExpOut
  | ExpInOut
  -- Circular
  | CircleIn
  | CircleOut
  | CircleInOut
  -- Back (overshoot)
  | BackIn
  | BackOut
  | BackInOut
  -- Elastic (spring)
  | ElasticIn
  | ElasticOut
  | ElasticInOut
  -- Bounce
  | BounceIn
  | BounceOut
  | BounceInOut

derive instance Eq EasingType
derive instance Ord EasingType

instance Show EasingType where
  show = easingLabel

-- | Convert EasingType to the actual easing function
toFunction :: EasingType -> T.Easing
toFunction = case _ of
  Linear -> T.linear
  QuadIn -> T.easeInQuad
  QuadOut -> T.easeOutQuad
  QuadInOut -> T.easeInOutQuad
  CubicIn -> T.easeInCubic
  CubicOut -> T.easeOutCubic
  CubicInOut -> T.easeInOutCubic
  SinIn -> T.easeInSin
  SinOut -> T.easeOutSin
  SinInOut -> T.easeInOutSin
  ExpIn -> T.easeInExp
  ExpOut -> T.easeOutExp
  ExpInOut -> T.easeInOutExp
  CircleIn -> T.easeInCircle
  CircleOut -> T.easeOutCircle
  CircleInOut -> T.easeInOutCircle
  BackIn -> T.easeInBack
  BackOut -> T.easeOutBack
  BackInOut -> T.easeInOutBack
  ElasticIn -> T.easeInElastic
  ElasticOut -> T.easeOutElastic
  ElasticInOut -> T.easeInOutElastic
  BounceIn -> T.easeInBounce
  BounceOut -> T.easeOutBounce
  BounceInOut -> T.easeInOutBounce

-- | Human-readable label for each easing type
easingLabel :: EasingType -> String
easingLabel = case _ of
  Linear -> "Linear"
  QuadIn -> "Quad In"
  QuadOut -> "Quad Out"
  QuadInOut -> "Quad In-Out"
  CubicIn -> "Cubic In"
  CubicOut -> "Cubic Out"
  CubicInOut -> "Cubic In-Out"
  SinIn -> "Sine In"
  SinOut -> "Sine Out"
  SinInOut -> "Sine In-Out"
  ExpIn -> "Expo In"
  ExpOut -> "Expo Out"
  ExpInOut -> "Expo In-Out"
  CircleIn -> "Circ In"
  CircleOut -> "Circ Out"
  CircleInOut -> "Circ In-Out"
  BackIn -> "Back In"
  BackOut -> "Back Out"
  BackInOut -> "Back In-Out"
  ElasticIn -> "Elastic In"
  ElasticOut -> "Elastic Out"
  ElasticInOut -> "Elastic In-Out"
  BounceIn -> "Bounce In"
  BounceOut -> "Bounce Out"
  BounceInOut -> "Bounce In-Out"

-- | Category for grouping in UI
easingCategory :: EasingType -> String
easingCategory = case _ of
  Linear -> "Standard"
  QuadIn -> "Quadratic"
  QuadOut -> "Quadratic"
  QuadInOut -> "Quadratic"
  CubicIn -> "Cubic"
  CubicOut -> "Cubic"
  CubicInOut -> "Cubic"
  SinIn -> "Sinusoidal"
  SinOut -> "Sinusoidal"
  SinInOut -> "Sinusoidal"
  ExpIn -> "Exponential"
  ExpOut -> "Exponential"
  ExpInOut -> "Exponential"
  CircleIn -> "Circular"
  CircleOut -> "Circular"
  CircleInOut -> "Circular"
  BackIn -> "Back"
  BackOut -> "Back"
  BackInOut -> "Back"
  ElasticIn -> "Elastic"
  ElasticOut -> "Elastic"
  ElasticInOut -> "Elastic"
  BounceIn -> "Bounce"
  BounceOut -> "Bounce"
  BounceInOut -> "Bounce"

-- | All easing types in order (for populating dropdowns, etc.)
allEasingTypes :: Array EasingType
allEasingTypes =
  [ Linear
  , QuadIn, QuadOut, QuadInOut
  , CubicIn, CubicOut, CubicInOut
  , SinIn, SinOut, SinInOut
  , ExpIn, ExpOut, ExpInOut
  , CircleIn, CircleOut, CircleInOut
  , BackIn, BackOut, BackInOut
  , ElasticIn, ElasticOut, ElasticInOut
  , BounceIn, BounceOut, BounceInOut
  ]
