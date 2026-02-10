-- | Type Conversions for Selection Operations
-- |
-- | Pure functions for converting between types used in selection operations.
-- | No Effect, no cross-dependencies with other Operations modules.
module Hylograph.Internal.Selection.Operations.Conversions
  ( -- * Easing conversions
    transitionEasingToAnimEasing
    -- * Attribute value conversions
  , attributeValueToNumber
  , attributeValueToString
  , isNumericAttributeValue
    -- * Element type conversions
  , elementTypeToString
  , stringToElementType
    -- * Behavior type conversions
  , highlightClassToInt
  , tooltipTriggerToInt
    -- * FFI helpers
  , parseNumberOrZero
  , isNumericString
  ) where

import Prelude

import Hylograph.Internal.Attribute (AttributeValue(..), EasingType(..))
import Hylograph.Internal.Behavior.Types (HighlightClass(..), TooltipTrigger(..))
import Hylograph.Internal.Selection.Types (ElementType(..))
import Hylograph.Internal.Transition.Types (Easing(..)) as TransitionTypes

-- =============================================================================
-- Easing Conversions
-- =============================================================================

-- | Convert TransitionTypes.Easing to Attribute.EasingType
-- |
-- | These are parallel type hierarchies to avoid circular dependencies.
transitionEasingToAnimEasing :: TransitionTypes.Easing -> EasingType
transitionEasingToAnimEasing TransitionTypes.Linear = Linear
transitionEasingToAnimEasing TransitionTypes.QuadIn = QuadIn
transitionEasingToAnimEasing TransitionTypes.QuadOut = QuadOut
transitionEasingToAnimEasing TransitionTypes.QuadInOut = QuadInOut
transitionEasingToAnimEasing TransitionTypes.CubicIn = CubicIn
transitionEasingToAnimEasing TransitionTypes.CubicOut = CubicOut
transitionEasingToAnimEasing TransitionTypes.CubicInOut = CubicInOut
transitionEasingToAnimEasing TransitionTypes.SinIn = SinIn
transitionEasingToAnimEasing TransitionTypes.SinOut = SinOut
transitionEasingToAnimEasing TransitionTypes.SinInOut = SinInOut
transitionEasingToAnimEasing TransitionTypes.ExpIn = ExpIn
transitionEasingToAnimEasing TransitionTypes.ExpOut = ExpOut
transitionEasingToAnimEasing TransitionTypes.ExpInOut = ExpInOut
transitionEasingToAnimEasing TransitionTypes.ElasticIn = ElasticIn
transitionEasingToAnimEasing TransitionTypes.ElasticOut = ElasticOut
transitionEasingToAnimEasing TransitionTypes.ElasticInOut = ElasticInOut
transitionEasingToAnimEasing TransitionTypes.BounceIn = BounceIn
transitionEasingToAnimEasing TransitionTypes.BounceOut = BounceOut
transitionEasingToAnimEasing TransitionTypes.BounceInOut = BounceInOut
transitionEasingToAnimEasing TransitionTypes.BackIn = BackIn
transitionEasingToAnimEasing TransitionTypes.BackOut = BackOut
transitionEasingToAnimEasing TransitionTypes.BackInOut = BackInOut
transitionEasingToAnimEasing TransitionTypes.CircleIn = CircleIn
transitionEasingToAnimEasing TransitionTypes.CircleOut = CircleOut
transitionEasingToAnimEasing TransitionTypes.CircleInOut = CircleInOut
-- Fallback for any unmatched variants
transitionEasingToAnimEasing _ = Linear

-- =============================================================================
-- Attribute Value Conversions
-- =============================================================================

-- | Convert AttributeValue to Number for animation
-- |
-- | For string values, attempts to parse as number. Returns 0.0 on failure.
attributeValueToNumber :: AttributeValue -> Number
attributeValueToNumber (NumberValue n) = n
attributeValueToNumber (StringValue s) = parseNumberOrZero s
attributeValueToNumber (BooleanValue true) = 1.0
attributeValueToNumber (BooleanValue false) = 0.0

-- | Convert AttributeValue to String for DOM attributes
attributeValueToString :: AttributeValue -> String
attributeValueToString (StringValue s) = s
attributeValueToString (NumberValue n) = show n
attributeValueToString (BooleanValue b) = show b

-- | Check if an AttributeValue is numeric (can be animated)
-- |
-- | NumberValue is always numeric.
-- | StringValue is numeric only if it parses as a valid number.
-- | BooleanValue could be animated as 0/1 but for simplicity we treat as non-numeric.
isNumericAttributeValue :: AttributeValue -> Boolean
isNumericAttributeValue (NumberValue _) = true
isNumericAttributeValue (StringValue s) = isNumericString s
isNumericAttributeValue (BooleanValue _) = false

-- =============================================================================
-- Element Type Conversions
-- =============================================================================

-- | Convert ElementType to its string representation for DOM creation
elementTypeToString :: ElementType -> String
elementTypeToString Circle = "circle"
elementTypeToString Rect = "rect"
elementTypeToString Path = "path"
elementTypeToString Line = "line"
elementTypeToString Polygon = "polygon"
elementTypeToString Text = "text"
elementTypeToString Group = "g"
elementTypeToString SVG = "svg"
elementTypeToString Defs = "defs"
elementTypeToString LinearGradient = "linearGradient"
elementTypeToString Stop = "stop"
elementTypeToString PatternFill = "pattern"
elementTypeToString Div = "div"
elementTypeToString Span = "span"
elementTypeToString Table = "table"
elementTypeToString Tr = "tr"
elementTypeToString Td = "td"
elementTypeToString Th = "th"
elementTypeToString Tbody = "tbody"
elementTypeToString Thead = "thead"

-- | Convert string to ElementType (inverse of elementTypeToString)
stringToElementType :: String -> ElementType
stringToElementType "circle" = Circle
stringToElementType "rect" = Rect
stringToElementType "path" = Path
stringToElementType "line" = Line
stringToElementType "polygon" = Polygon
stringToElementType "text" = Text
stringToElementType "g" = Group
stringToElementType "svg" = SVG
stringToElementType "defs" = Defs
stringToElementType "linearGradient" = LinearGradient
stringToElementType "stop" = Stop
stringToElementType "pattern" = PatternFill
stringToElementType "div" = Div
stringToElementType "span" = Span
stringToElementType "table" = Table
stringToElementType "tr" = Tr
stringToElementType "td" = Td
stringToElementType "th" = Th
stringToElementType "tbody" = Tbody
stringToElementType "thead" = Thead
stringToElementType _ = Group -- Default to Group for unknown types

-- =============================================================================
-- Behavior Type Conversions
-- =============================================================================

-- | Convert HighlightClass to Int for FFI
-- | Must match the constants in FFI.js: HC_PRIMARY=0, HC_RELATED=1, HC_DIMMED=2, HC_NEUTRAL=3, HC_UPSTREAM=4, HC_DOWNSTREAM=5
highlightClassToInt :: HighlightClass -> Int
highlightClassToInt Primary = 0
highlightClassToInt Related = 1
highlightClassToInt Dimmed = 2
highlightClassToInt Neutral = 3
highlightClassToInt Upstream = 4
highlightClassToInt Downstream = 5

-- | Convert TooltipTrigger to Int for FFI
-- | Must match the constants in FFI.js: TT_ON_HOVER=0, TT_WHEN_PRIMARY=1, TT_WHEN_RELATED=2
tooltipTriggerToInt :: TooltipTrigger -> Int
tooltipTriggerToInt OnHover = 0
tooltipTriggerToInt WhenPrimary = 1
tooltipTriggerToInt WhenRelated = 2

-- =============================================================================
-- FFI Helpers
-- =============================================================================

-- | Parse a string as a number, returning 0.0 if parsing fails
foreign import parseNumberOrZero :: String -> Number

-- | Check if a string can be parsed as a number
foreign import isNumericString :: String -> Boolean
