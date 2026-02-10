-- | Core Attribute Types
-- |
-- | Defines the fundamental types for SVG/HTML attributes in Hylograph.
-- | These types are the target of the finally-tagless expression system.
-- |
-- | The `Attribute` ADT supports three patterns:
-- | - Static: Same value for all elements
-- | - Data-driven: Value computed from datum
-- | - Indexed: Value computed from datum and index
-- |
-- | ## Historical Note
-- |
-- | This module previously contained a `ToAttr` typeclass with polymorphic
-- | smart constructors (fill, cx, radius, etc.). That pattern was superseded
-- | by the finally-tagless expression system which provides multi-interpretation
-- | capabilities. See `kept-for-historical-context/ToAttr-Pattern-Documentation.md`.
module Hylograph.Internal.Attribute
  ( Attribute(..)
  , AttributeName(..)
  , AttributeValue(..)
  , AttrSource(..)
    -- * Animated attribute support
  , AnimatedValue(..)
  , AnimationConfig
  , EasingType(..)
  , Milliseconds
  , defaultAnimationConfig
  ) where

import Prelude
import Data.Array (length)
import Data.Functor.Contravariant (class Contravariant)
import Data.Maybe (Maybe(..))

-- =============================================================================
-- Animation Types
-- =============================================================================

-- | Time in milliseconds for animation configuration
type Milliseconds = Number

-- | Enumeration of easing types for animations
-- |
-- | Note: This mirrors Hylograph.Transition.Easing.EasingType but is defined here
-- | to avoid circular dependencies. The Manager module will convert between them.
data EasingType
  = Linear
  | QuadIn | QuadOut | QuadInOut
  | CubicIn | CubicOut | CubicInOut
  | SinIn | SinOut | SinInOut
  | ExpIn | ExpOut | ExpInOut
  | CircleIn | CircleOut | CircleInOut
  | BackIn | BackOut | BackInOut
  | ElasticIn | ElasticOut | ElasticInOut
  | BounceIn | BounceOut | BounceInOut

derive instance Eq EasingType
derive instance Ord EasingType

instance Show EasingType where
  show Linear = "Linear"
  show QuadIn = "QuadIn"
  show QuadOut = "QuadOut"
  show QuadInOut = "QuadInOut"
  show CubicIn = "CubicIn"
  show CubicOut = "CubicOut"
  show CubicInOut = "CubicInOut"
  show SinIn = "SinIn"
  show SinOut = "SinOut"
  show SinInOut = "SinInOut"
  show ExpIn = "ExpIn"
  show ExpOut = "ExpOut"
  show ExpInOut = "ExpInOut"
  show CircleIn = "CircleIn"
  show CircleOut = "CircleOut"
  show CircleInOut = "CircleInOut"
  show BackIn = "BackIn"
  show BackOut = "BackOut"
  show BackInOut = "BackInOut"
  show ElasticIn = "ElasticIn"
  show ElasticOut = "ElasticOut"
  show ElasticInOut = "ElasticInOut"
  show BounceIn = "BounceIn"
  show BounceOut = "BounceOut"
  show BounceInOut = "BounceInOut"

-- | Animated value specification
-- |
-- | Describes where the animation value comes from:
-- | - StaticAnimValue: Constant number
-- | - DataAnimValue: Computed from datum
-- | - IndexedAnimValue: Computed from datum and element index
data AnimatedValue datum
  = StaticAnimValue Number
  | DataAnimValue (datum -> Number)
  | IndexedAnimValue (datum -> Int -> Number)

instance Show (AnimatedValue datum) where
  show (StaticAnimValue n) = "(StaticAnimValue " <> show n <> ")"
  show (DataAnimValue _) = "(DataAnimValue <fn>)"
  show (IndexedAnimValue _) = "(IndexedAnimValue <fn>)"

-- | Configuration for a single animated attribute
-- |
-- | Specifies timing, easing, and delay for the animation.
type AnimationConfig =
  { duration :: Milliseconds
  , easing :: EasingType
  , delay :: Milliseconds
  }

-- | Default animation configuration: 300ms, QuadOut, no delay
defaultAnimationConfig :: AnimationConfig
defaultAnimationConfig =
  { duration: 300.0
  , easing: QuadOut
  , delay: 0.0
  }

-- | Source metadata for attributes
-- |
-- | Describes where the attribute value comes from, enabling interpreters
-- | like MetaAST to show meaningful information about attribute bindings.
-- |
-- | This is automatically captured when using the DSL (field, num, etc.)
-- | but is `UnknownSource` for raw PureScript functions (escape hatches).
data AttrSource
  = UnknownSource           -- ^ Raw function, can't introspect
  | StaticSource String     -- ^ Constant value with its string representation
  | FieldSource String      -- ^ Single field access: d.fieldName
  | ExprSource String       -- ^ Computed expression: "d.x * 20 + 50"
  | IndexSource             -- ^ Uses element index
  | OpaqueSource            -- ^ Placeholder requiring metadata substitution (Emmet round-trip)

derive instance Eq AttrSource
derive instance Ord AttrSource

instance Show AttrSource where
  show UnknownSource = "UnknownSource"
  show (StaticSource s) = "(StaticSource " <> show s <> ")"
  show (FieldSource f) = "(FieldSource " <> show f <> ")"
  show (ExprSource e) = "(ExprSource " <> show e <> ")"
  show IndexSource = "IndexSource"
  show OpaqueSource = "OpaqueSource"

-- | Type-safe attribute with datum phantom type
-- |
-- | Attributes can be:
-- | - Static: Same value for all elements
-- | - Data-driven: Value computed from datum (with source metadata)
-- | - Indexed: Value computed from datum and index (with source metadata)
-- |
-- | The phantom type `datum` ensures attributes are only applied
-- | to selections with matching data types.
-- |
-- | The `AttrSource` field enables interpreters to inspect attribute origins
-- | without evaluating the functions.
data Attribute datum
  = StaticAttr AttributeName AttributeValue
  | DataAttr AttributeName AttrSource (datum -> AttributeValue)
  | IndexedAttr AttributeName AttrSource (datum -> Int -> AttributeValue)
  | AnimatedAttr
      { name :: AttributeName
      , fromValue :: Maybe (AnimatedValue datum)  -- Nothing = read from DOM
      , toValue :: AnimatedValue datum
      , config :: AnimationConfig
      }
  -- | Animated compound attribute for paths and other generated strings
  -- |
  -- | Animates multiple numeric values and calls a generator function to produce
  -- | the final string value. Used for:
  -- | - linkVertical (4 numbers → path string)
  -- | - sankeyLink (6 numbers → path string)
  -- | - arc (4 numbers → arc path)
  -- |
  -- | The generator receives interpolated values in the same order as fromValues/toValues.
  | AnimatedCompound
      { name :: AttributeName               -- Output attribute (e.g., "d" for paths)
      , fromValues :: Array (AnimatedValue datum)  -- From values for each component
      , toValues :: Array (AnimatedValue datum)    -- To values for each component
      , generator :: Array Number -> String        -- Combines interpolated values into final string
      , config :: AnimationConfig
      }

-- We can't derive Show for function types, but we can show the structure
instance Show (Attribute datum) where
  show (StaticAttr name val) = "(StaticAttr " <> show name <> " " <> show val <> ")"
  show (DataAttr name src _) = "(DataAttr " <> show name <> " " <> show src <> " <fn>)"
  show (IndexedAttr name src _) = "(IndexedAttr " <> show name <> " " <> show src <> " <fn>)"
  show (AnimatedAttr rec) = "(AnimatedAttr " <> show rec.name <> " from=" <> show rec.fromValue <> " to=" <> show rec.toValue <> ")"
  show (AnimatedCompound rec) = "(AnimatedCompound " <> show rec.name <> " components=" <> show (length rec.toValues) <> ")"

-- | Contravariant instance for Attribute
-- |
-- | Attributes *consume* data (they're data sinks), making them naturally contravariant.
-- | This enables attribute reuse via `cmap`:
-- |
-- | ```purescript
-- | -- Define attribute for specific type
-- | radiusAttr :: Attribute Number
-- | radiusAttr = DataAttr (AttributeName "r") NumberValue
-- |
-- | -- Adapt to work with richer type
-- | type Circle = { radius :: Number, x :: Number, y :: Number }
-- | circleRadiusAttr :: Attribute Circle
-- | circleRadiusAttr = cmap _.radius radiusAttr
-- | ```
-- |
-- | The key insight: `cmap` composes the projection function with the attribute's
-- | data accessor, allowing attributes written for simple types to work with
-- | complex types via field selection.
instance Contravariant Attribute where
  cmap _ (StaticAttr name val) = StaticAttr name val -- Static doesn't depend on datum
  cmap f (DataAttr name src g) = DataAttr name src (g <<< f) -- Compose: first project, then extract value
  cmap f (IndexedAttr name src g) = IndexedAttr name src (\b i -> g (f b) i) -- Project datum before indexing
  cmap f (AnimatedAttr rec) = AnimatedAttr
    { name: rec.name
    , fromValue: cmapAnimatedValue f <$> rec.fromValue
    , toValue: cmapAnimatedValue f rec.toValue
    , config: rec.config
    }
  cmap f (AnimatedCompound rec) = AnimatedCompound
    { name: rec.name
    , fromValues: map (cmapAnimatedValue f) rec.fromValues
    , toValues: map (cmapAnimatedValue f) rec.toValues
    , generator: rec.generator  -- Generator doesn't depend on datum type
    , config: rec.config
    }

-- | Helper for contravariant mapping of AnimatedValue
cmapAnimatedValue :: forall a b. (b -> a) -> AnimatedValue a -> AnimatedValue b
cmapAnimatedValue _ (StaticAnimValue n) = StaticAnimValue n
cmapAnimatedValue f (DataAnimValue g) = DataAnimValue (g <<< f)
cmapAnimatedValue f (IndexedAnimValue g) = IndexedAnimValue (\b i -> g (f b) i)

-- | Attribute names (SVG/HTML properties)
-- |
-- | We use a newtype to prevent typos and enable IDE autocomplete.
-- | The String inside is the actual DOM attribute name.
newtype AttributeName = AttributeName String

derive instance Eq AttributeName
derive instance Ord AttributeName
derive newtype instance Show AttributeName

-- | Attribute values
-- |
-- | We support the most common value types.
-- | The ADT ensures type safety when setting attributes.
data AttributeValue
  = StringValue String
  | NumberValue Number
  | BooleanValue Boolean

derive instance Eq AttributeValue
derive instance Ord AttributeValue

instance Show AttributeValue where
  show (StringValue s) = "StringValue " <> show s
  show (NumberValue n) = "NumberValue " <> show n
  show (BooleanValue b) = "BooleanValue " <> show b
