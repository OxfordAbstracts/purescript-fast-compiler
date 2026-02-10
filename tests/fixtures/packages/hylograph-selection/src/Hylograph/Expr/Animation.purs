-- | Animation DSL
-- |
-- | A fluent API for creating animated attributes that compose with the
-- | existing Hylograph expression system. Animated attributes define start and
-- | end values with timing configuration, and are rendered using pure
-- | PureScript transitions (no D3 dependency).
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hylograph.Expr.Animation
-- |
-- | -- Animate from 0 to the datum's x value over 500ms
-- | cx $ animated $ animatedFrom (num 0.0) $ animatedTo (field @"x")
-- |   # withDuration 500.0
-- |   # withEasing QuadOut
-- |
-- | -- Shorthand for common patterns
-- | [ fadeIn
-- | , animated $ animatedTo (field @"radius") # withDuration 300.0
-- | ]
-- | ```
-- |
-- | ## Design
-- |
-- | The animation DSL uses a builder pattern:
-- | 1. `animatedTo` creates a builder targeting an attribute value
-- | 2. `animatedFrom` optionally sets the starting value
-- | 3. Config modifiers (`withDuration`, `withEasing`, `withDelay`) adjust timing
-- | 4. `animated` converts the builder to an `Attribute`
-- |
-- | The DSL integrates with the expression system (EvalD), so you can use
-- | `field @"x"`, `num 5.0`, arithmetic expressions, etc.
module Hylograph.Expr.Animation
  ( -- * Builder type
    AnimatedBuilder
  , AnimatedPathBuilder
    -- * Core operators
  , animatedTo
  , animatedToIndexed
  , animatedFrom
  , animatedFromStatic
  , animatedFromIndexed
    -- * Path animation operators
  , animatedLinkVertical
  , animatedLinkHorizontal
  , pathWithDuration
  , pathWithEasing
  , pathWithDelay
  , animatedPathAttr
    -- * Config modifiers
  , withDuration
  , withEasing
  , withDelay
  , withStagger
    -- * Builder to Attribute conversion
  , animated
  , animatedAttr
    -- * Convenience constructors
  , fadeIn
  , fadeOut
  , growFrom
  , shrinkTo
    -- * Re-exports for convenience
  , module AttrTypes
  ) where

import Prelude

import Data.Array (index)
import Data.Maybe (Maybe(..), fromMaybe)
import Hylograph.Internal.Attribute (AnimatedValue(..), AnimationConfig, AttributeName(..), Attribute(..), EasingType(..), defaultAnimationConfig)
import Hylograph.Internal.Attribute (EasingType(..)) as AttrTypes
import Hylograph.Expr.Interpreter.Eval (EvalD, runEvalD)

-- =============================================================================
-- Builder Type
-- =============================================================================

-- | Builder for animated attributes
-- |
-- | Accumulates the animation specification before converting to Attribute.
-- | Use `animatedTo` to create, config modifiers to adjust, and `animated` to finalize.
type AnimatedBuilder datum =
  { name :: String
  , fromValue :: Maybe (AnimatedValue datum)
  , toValue :: AnimatedValue datum
  , config :: AnimationConfig
  }

-- =============================================================================
-- Core Operators
-- =============================================================================

-- | Create an animated attribute builder targeting a value
-- |
-- | The attribute name is required. The target value can be:
-- | - A constant: `animatedTo "opacity" (num 1.0)`
-- | - A field: `animatedTo "cx" (field @"x")`
-- | - An expression: `animatedTo "cx" (field @"x" `timesN` 20.0)`
-- |
-- | ```purescript
-- | opacity $ animated $ animatedTo (num 1.0)
-- |   # withDuration 500.0
-- | ```
animatedTo :: forall datum. String -> EvalD datum Number -> AnimatedBuilder datum
animatedTo name toExpr =
  { name
  , fromValue: Nothing  -- Will read from DOM or default to target
  , toValue: DataAnimValue (\d -> runEvalD toExpr d 0)
  , config: defaultAnimationConfig
  }

-- | Set the starting value for an animation
-- |
-- | Without `animatedFrom`, the animation reads the current DOM value as start.
-- | With `animatedFrom`, the animation uses the specified value.
-- |
-- | ```purescript
-- | -- Animate from 0 to 1
-- | opacity $ animated $ animatedFrom (num 0.0) $ animatedTo (num 1.0)
-- |
-- | -- Animate from current DOM value to target (no animatedFrom)
-- | opacity $ animated $ animatedTo (field @"targetOpacity")
-- | ```
animatedFrom :: forall datum. EvalD datum Number -> AnimatedBuilder datum -> AnimatedBuilder datum
animatedFrom fromExpr builder =
  builder { fromValue = Just (DataAnimValue (\d -> runEvalD fromExpr d 0)) }

-- | Set a static starting value for an animation
-- |
-- | ```purescript
-- | animated $ animatedFromStatic 0.0 $ animatedTo "opacity" (num 1.0)
-- | ```
animatedFromStatic :: forall datum. Number -> AnimatedBuilder datum -> AnimatedBuilder datum
animatedFromStatic n builder =
  builder { fromValue = Just (StaticAnimValue n) }

-- | Set an indexed starting value for an animation (uses datum and element index)
-- |
-- | ```purescript
-- | animated $ animatedFromIndexed (\d i -> d.baseX + toNumber i * 10.0) $ animatedTo "cx" (field @"x")
-- | ```
animatedFromIndexed :: forall datum. (datum -> Int -> Number) -> AnimatedBuilder datum -> AnimatedBuilder datum
animatedFromIndexed f builder =
  builder { fromValue = Just (IndexedAnimValue f) }

-- | Create an indexed animated attribute builder (uses datum and element index for target)
-- |
-- | ```purescript
-- | animated $ animatedToIndexed "cx" (\d i -> d.x + toNumber i * spacing)
-- | ```
animatedToIndexed :: forall datum. String -> (datum -> Int -> Number) -> AnimatedBuilder datum
animatedToIndexed name toFn =
  { name
  , fromValue: Nothing
  , toValue: IndexedAnimValue toFn
  , config: defaultAnimationConfig
  }

-- =============================================================================
-- Config Modifiers
-- =============================================================================

-- | Set the animation duration in milliseconds
-- |
-- | ```purescript
-- | animated $ animatedTo (num 1.0) # withDuration 500.0
-- | ```
withDuration :: forall datum. Number -> AnimatedBuilder datum -> AnimatedBuilder datum
withDuration ms builder =
  builder { config = builder.config { duration = ms } }

-- | Set the easing function
-- |
-- | ```purescript
-- | animated $ animatedTo (num 1.0)
-- |   # withEasing ElasticOut
-- | ```
withEasing :: forall datum. EasingType -> AnimatedBuilder datum -> AnimatedBuilder datum
withEasing easing builder =
  builder { config = builder.config { easing = easing } }

-- | Set the delay before animation starts (in milliseconds)
-- |
-- | ```purescript
-- | animated $ animatedTo (num 1.0)
-- |   # withDelay 200.0  -- Wait 200ms before starting
-- | ```
withDelay :: forall datum. Number -> AnimatedBuilder datum -> AnimatedBuilder datum
withDelay ms builder =
  builder { config = builder.config { delay = ms } }

-- | Set staggered delay based on element index
-- |
-- | Creates an indexed animation where each element's delay is:
-- | baseDelay + (index * staggerDelay)
-- |
-- | ```purescript
-- | animated $ animatedTo (num 1.0)
-- |   # withStagger 50.0  -- Each element starts 50ms after the previous
-- | ```
withStagger :: forall datum. Number -> AnimatedBuilder datum -> AnimatedBuilder datum
withStagger staggerMs builder =
  builder
    { toValue = toIndexed builder.toValue staggerMs
    , fromValue = toIndexed <$> builder.fromValue <*> pure staggerMs
    }
  where
    -- Convert to indexed value that adds stagger delay
    toIndexed :: AnimatedValue datum -> Number -> AnimatedValue datum
    toIndexed (StaticAnimValue n) _ = StaticAnimValue n
    toIndexed (DataAnimValue f) _ = DataAnimValue f
    toIndexed (IndexedAnimValue f) _ = IndexedAnimValue f

-- =============================================================================
-- Builder to Attribute Conversion
-- =============================================================================

-- | Convert an AnimatedBuilder to an Attribute
-- |
-- | This is the final step after building the animation specification.
-- |
-- | ```purescript
-- | myAttr = animated $ animatedFrom (num 0.0) $ animatedTo (num 1.0)
-- |   # withDuration 500.0
-- |   # withEasing QuadOut
-- | ```
animated :: forall datum. AnimatedBuilder datum -> Attribute datum
animated builder = AnimatedAttr
  { name: AttributeName builder.name
  , fromValue: builder.fromValue
  , toValue: builder.toValue
  , config: builder.config
  }

-- | Create an animated attribute with explicit name (alternative syntax)
-- |
-- | ```purescript
-- | animatedAttr "opacity" $ animatedFrom (num 0.0) $ animatedTo (num 1.0)
-- | ```
animatedAttr :: forall datum. String -> AnimatedBuilder datum -> Attribute datum
animatedAttr name builder = animated (builder { name = name })

-- =============================================================================
-- Convenience Constructors
-- =============================================================================

-- | Fade in from 0 to 1 opacity
-- |
-- | ```purescript
-- | enterAttrs = [ fadeIn # withDuration 300.0 ]
-- | ```
fadeIn :: forall datum. Attribute datum
fadeIn = AnimatedAttr
  { name: AttributeName "opacity"
  , fromValue: Just (StaticAnimValue 0.0)
  , toValue: StaticAnimValue 1.0
  , config: defaultAnimationConfig
  }

-- | Fade out from current opacity to 0
-- |
-- | ```purescript
-- | exitAttrs = [ fadeOut # withDuration 300.0 ]
-- | ```
fadeOut :: forall datum. Attribute datum
fadeOut = AnimatedAttr
  { name: AttributeName "opacity"
  , fromValue: Nothing  -- Read current from DOM
  , toValue: StaticAnimValue 0.0
  , config: defaultAnimationConfig
  }

-- | Grow from a starting radius to the datum's radius
-- |
-- | ```purescript
-- | enterAttrs = [ growFrom 0.0 # withDuration 300.0 ]
-- | ```
growFrom :: forall datum. Number -> Attribute datum
growFrom startRadius = AnimatedAttr
  { name: AttributeName "r"
  , fromValue: Just (StaticAnimValue startRadius)
  , toValue: StaticAnimValue 0.0  -- Placeholder - needs to be set externally
  , config: defaultAnimationConfig
  }

-- | Shrink to a target radius (for exit animations)
-- |
-- | ```purescript
-- | exitAttrs = [ shrinkTo 0.0 # withDuration 300.0 ]
-- | ```
shrinkTo :: forall datum. Number -> Attribute datum
shrinkTo endRadius = AnimatedAttr
  { name: AttributeName "r"
  , fromValue: Nothing  -- Read current from DOM
  , toValue: StaticAnimValue endRadius
  , config: defaultAnimationConfig
  }

-- =============================================================================
-- Path Animation
-- =============================================================================

-- | Builder for animated path attributes
-- |
-- | Tracks the from/to values for path components and the generator function.
-- | Used for animating paths like linkVertical where we interpolate coordinates
-- | and regenerate the path string on each frame.
type AnimatedPathBuilder datum =
  { fromValues :: Array (AnimatedValue datum)  -- From values for each component
  , toValues :: Array (AnimatedValue datum)    -- To values for each component
  , generator :: Array Number -> String        -- Combines interpolated values into final string
  , config :: AnimationConfig
  }

-- | Create an animated vertical link path
-- |
-- | Animates from current positions to new positions, regenerating the cubic
-- | bezier path on each frame. Used for tree visualizations.
-- |
-- | ```purescript
-- | animatedLinkVertical
-- |   { fromSourceX: field @"sourceX", fromSourceY: field @"sourceY"
-- |   , fromTargetX: field @"targetX", fromTargetY: field @"targetY" }
-- |   { toSourceX: field @"newSourceX", toSourceY: field @"newSourceY"
-- |   , toTargetX: field @"newTargetX", toTargetY: field @"newTargetY" }
-- |   # pathWithDuration 500.0
-- | ```
animatedLinkVertical
  :: forall datum
   . { fromSourceX :: EvalD datum Number
     , fromSourceY :: EvalD datum Number
     , fromTargetX :: EvalD datum Number
     , fromTargetY :: EvalD datum Number
     }
  -> { toSourceX :: EvalD datum Number
     , toSourceY :: EvalD datum Number
     , toTargetX :: EvalD datum Number
     , toTargetY :: EvalD datum Number
     }
  -> AnimatedPathBuilder datum
animatedLinkVertical from to =
  { fromValues:
      [ DataAnimValue (\d -> runEvalD from.fromSourceX d 0)
      , DataAnimValue (\d -> runEvalD from.fromSourceY d 0)
      , DataAnimValue (\d -> runEvalD from.fromTargetX d 0)
      , DataAnimValue (\d -> runEvalD from.fromTargetY d 0)
      ]
  , toValues:
      [ DataAnimValue (\d -> runEvalD to.toSourceX d 0)
      , DataAnimValue (\d -> runEvalD to.toSourceY d 0)
      , DataAnimValue (\d -> runEvalD to.toTargetX d 0)
      , DataAnimValue (\d -> runEvalD to.toTargetY d 0)
      ]
  , generator: linkVerticalGenerator
  , config: defaultAnimationConfig
  }

-- | Create an animated horizontal link path
-- |
-- | Same as animatedLinkVertical but for horizontal (left-to-right) trees.
animatedLinkHorizontal
  :: forall datum
   . { fromSourceX :: EvalD datum Number
     , fromSourceY :: EvalD datum Number
     , fromTargetX :: EvalD datum Number
     , fromTargetY :: EvalD datum Number
     }
  -> { toSourceX :: EvalD datum Number
     , toSourceY :: EvalD datum Number
     , toTargetX :: EvalD datum Number
     , toTargetY :: EvalD datum Number
     }
  -> AnimatedPathBuilder datum
animatedLinkHorizontal from to =
  { fromValues:
      [ DataAnimValue (\d -> runEvalD from.fromSourceX d 0)
      , DataAnimValue (\d -> runEvalD from.fromSourceY d 0)
      , DataAnimValue (\d -> runEvalD from.fromTargetX d 0)
      , DataAnimValue (\d -> runEvalD from.fromTargetY d 0)
      ]
  , toValues:
      [ DataAnimValue (\d -> runEvalD to.toSourceX d 0)
      , DataAnimValue (\d -> runEvalD to.toSourceY d 0)
      , DataAnimValue (\d -> runEvalD to.toTargetX d 0)
      , DataAnimValue (\d -> runEvalD to.toTargetY d 0)
      ]
  , generator: linkHorizontalGenerator
  , config: defaultAnimationConfig
  }

-- | Set the animation duration for a path animation
pathWithDuration :: forall datum. Number -> AnimatedPathBuilder datum -> AnimatedPathBuilder datum
pathWithDuration ms builder =
  builder { config = builder.config { duration = ms } }

-- | Set the easing function for a path animation
pathWithEasing :: forall datum. EasingType -> AnimatedPathBuilder datum -> AnimatedPathBuilder datum
pathWithEasing easing builder =
  builder { config = builder.config { easing = easing } }

-- | Set the delay for a path animation
pathWithDelay :: forall datum. Number -> AnimatedPathBuilder datum -> AnimatedPathBuilder datum
pathWithDelay ms builder =
  builder { config = builder.config { delay = ms } }

-- | Convert an AnimatedPathBuilder to an Attribute
-- |
-- | This creates an AnimatedCompound attribute that will interpolate all
-- | path coordinates and regenerate the path string on each animation frame.
animatedPathAttr :: forall datum. AnimatedPathBuilder datum -> Attribute datum
animatedPathAttr builder = AnimatedCompound
  { name: AttributeName "d"
  , fromValues: builder.fromValues
  , toValues: builder.toValues
  , generator: builder.generator
  , config: builder.config
  }

-- =============================================================================
-- Path Generators
-- =============================================================================

-- | Generate a vertical link path (for top-down trees)
-- | Takes [sourceX, sourceY, targetX, targetY]
-- | Generates: "M sourceX,sourceY C sourceX,midY targetX,midY targetX,targetY"
linkVerticalGenerator :: Array Number -> String
linkVerticalGenerator vals =
  let sourceX = fromMaybe 0.0 (index vals 0)
      sourceY = fromMaybe 0.0 (index vals 1)
      targetX = fromMaybe 0.0 (index vals 2)
      targetY = fromMaybe 0.0 (index vals 3)
      midY = (sourceY + targetY) / 2.0
  in "M" <> show sourceX <> "," <> show sourceY
     <> " C" <> show sourceX <> "," <> show midY
     <> " " <> show targetX <> "," <> show midY
     <> " " <> show targetX <> "," <> show targetY

-- | Generate a horizontal link path (for left-to-right trees)
-- | Takes [sourceX, sourceY, targetX, targetY]
-- | Generates: "M sourceX,sourceY C midX,sourceY midX,targetY targetX,targetY"
linkHorizontalGenerator :: Array Number -> String
linkHorizontalGenerator vals =
  let sourceX = fromMaybe 0.0 (index vals 0)
      sourceY = fromMaybe 0.0 (index vals 1)
      targetX = fromMaybe 0.0 (index vals 2)
      targetY = fromMaybe 0.0 (index vals 3)
      midX = (sourceX + targetX) / 2.0
  in "M" <> show sourceX <> "," <> show sourceY
     <> " C" <> show midX <> "," <> show sourceY
     <> " " <> show midX <> "," <> show targetY
     <> " " <> show targetX <> "," <> show targetY

-- =============================================================================
-- Internal Helpers
-- =============================================================================

-- Note: The convenience constructors (fadeIn, fadeOut, etc.) use static values
-- because they're meant for common enter/exit patterns where the values are
-- known at compile time. For data-driven animations, use the builder pattern.
