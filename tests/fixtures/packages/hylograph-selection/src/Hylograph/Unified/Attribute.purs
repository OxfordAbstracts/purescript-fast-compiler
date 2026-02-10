-- | Hylograph.Unified.Attribute - Bridge between Display and Attributes
-- |
-- | This module bridges the Display profunctor system with Hylograph's existing
-- | Attribute type, enabling gradual migration to the new display system.
-- |
-- | ## Two Styles, One System
-- |
-- | **Old style** (still works):
-- | ```purescript
-- | elem Circle
-- |   [ cx (num d.x)
-- |   , cy (num d.y)
-- |   , r (num d.radius)
-- |   ]
-- | ```
-- |
-- | **New style** (using Display):
-- | ```purescript
-- | elem Circle
-- |   [ attr "cx" _.x showNumD
-- |   , attr "cy" _.y showNumD
-- |   , attr "r" _.radius (roundD 1 >>> showNumD)
-- |   ]
-- | ```
-- |
-- | Both can be used together in the same visualization!
-- |
-- | ## Benefits of New Style
-- |
-- | 1. **Composable formatting**: Chain displays with `>>>`
-- | 2. **Reusable displays**: Define once, use everywhere
-- | 3. **Type-safe adaptation**: `lmapD` adapts to different data types
-- | 4. **Same display in sheet and viz**: Unified formatting
module Hylograph.Unified.Attribute
  ( -- * Smart Constructors
    attr
  , attrStatic
  , attrIndexed
    -- * Common Attributes with Display
  , cxD
  , cyD
  , xD
  , yD
  , rD
  , widthD
  , heightD
  , fillD
  , strokeD
  , opacityD
  , textContentD
  , transformD
    -- * Adapters
  , toAttribute
  , fromDisplay
    -- * Re-exports
  , module Exports
  ) where

import Prelude hiding ((>>>))

import Hylograph.Internal.Attribute (Attribute(..), AttributeName(..), AttributeValue(..), AttrSource(..))
import Hylograph.Internal.Attribute (Attribute, AttributeName, AttributeValue, AttrSource) as Exports
import Hylograph.Unified.Display (Display, runDisplay, showNumD, idD, (>>>))
import Hylograph.Unified.Display as D

-- =============================================================================
-- Smart Constructors
-- =============================================================================

-- | Create an attribute from extraction function and display
-- |
-- | This is the primary way to create attributes in the new style.
-- |
-- | Example:
-- | ```purescript
-- | attr "cx" _.x (scaleD 10.0 >>> showNumD)
-- | attr "fill" _.category idD
-- | attr "opacity" _.importance (clampD 0.0 1.0 >>> showNumD)
-- | ```
attr :: forall datum a.
  String ->              -- Attribute name (e.g., "cx", "fill")
  (datum -> a) ->        -- Extract value from datum
  Display a String ->    -- Format for display
  Attribute datum
attr name extract display =
  DataAttr
    (AttributeName name)
    (ExprSource $ "display:" <> name)  -- Source metadata
    (\d -> StringValue (runDisplay display (extract d)))

-- | Create a static attribute (same for all data)
-- |
-- | Example:
-- | ```purescript
-- | attrStatic "fill" "steelblue"
-- | attrStatic "stroke-width" "2"
-- | ```
attrStatic :: forall datum.
  String ->    -- Attribute name
  String ->    -- Static value
  Attribute datum
attrStatic name value =
  StaticAttr (AttributeName name) (StringValue value)

-- | Create an indexed attribute (uses datum and index)
-- |
-- | Example:
-- | ```purescript
-- | attrIndexed "fill" (\d i -> if i `mod` 2 == 0 then "red" else "blue") idD
-- | ```
attrIndexed :: forall datum a.
  String ->
  (datum -> Int -> a) ->
  Display a String ->
  Attribute datum
attrIndexed name extract display =
  IndexedAttr
    (AttributeName name)
    IndexSource
    (\d i -> StringValue (runDisplay display (extract d i)))

-- =============================================================================
-- Common Attributes (convenience constructors with Display)
-- =============================================================================

-- | cx attribute with display formatting
cxD :: forall datum. (datum -> Number) -> Display Number String -> Attribute datum
cxD = attr "cx"

-- | cy attribute with display formatting
cyD :: forall datum. (datum -> Number) -> Display Number String -> Attribute datum
cyD = attr "cy"

-- | x attribute with display formatting
xD :: forall datum. (datum -> Number) -> Display Number String -> Attribute datum
xD = attr "x"

-- | y attribute with display formatting
yD :: forall datum. (datum -> Number) -> Display Number String -> Attribute datum
yD = attr "y"

-- | r (radius) attribute with display formatting
rD :: forall datum. (datum -> Number) -> Display Number String -> Attribute datum
rD = attr "r"

-- | width attribute with display formatting
widthD :: forall datum. (datum -> Number) -> Display Number String -> Attribute datum
widthD = attr "width"

-- | height attribute with display formatting
heightD :: forall datum. (datum -> Number) -> Display Number String -> Attribute datum
heightD = attr "height"

-- | fill attribute with display formatting
fillD :: forall datum. (datum -> String) -> Attribute datum
fillD extract = attr "fill" extract idD

-- | stroke attribute with display formatting
strokeD :: forall datum. (datum -> String) -> Attribute datum
strokeD extract = attr "stroke" extract idD

-- | opacity attribute with display formatting
opacityD :: forall datum. (datum -> Number) -> Attribute datum
opacityD extract = attr "opacity" extract showNumD

-- | text content with display formatting
textContentD :: forall datum a. (datum -> a) -> Display a String -> Attribute datum
textContentD = attr "textContent"

-- | transform attribute with display formatting
transformD :: forall datum. (datum -> String) -> Attribute datum
transformD extract = attr "transform" extract idD

-- =============================================================================
-- Adapters (for working with existing code)
-- =============================================================================

-- | Convert a Display-based spec to an Attribute
-- |
-- | This is useful when you have a Display and want to use it with
-- | existing attribute-based code.
toAttribute :: forall datum a.
  AttributeName ->
  (datum -> a) ->
  Display a String ->
  Attribute datum
toAttribute name extract display =
  DataAttr name (ExprSource "display") (\d -> StringValue (runDisplay display (extract d)))

-- | Create an attribute that just uses a Display for formatting
-- |
-- | The extraction is identity - useful when datum is already the right type.
fromDisplay :: forall a.
  AttributeName ->
  Display a String ->
  Attribute a
fromDisplay name display =
  DataAttr name (ExprSource "display") (\d -> StringValue (runDisplay display d))

-- =============================================================================
-- Utilities for common patterns
-- =============================================================================

-- | Create a position attribute (x or y) with scaling
-- |
-- | Example:
-- | ```purescript
-- | posAttr "cx" _.x 0.0 100.0 0.0 800.0  -- Map [0,100] to [0,800]
-- | ```
posAttr :: forall datum.
  String ->
  (datum -> Number) ->
  Number -> Number ->  -- Domain (data range)
  Number -> Number ->  -- Range (pixel range)
  Attribute datum
posAttr name extract domainMin domainMax rangeMin rangeMax =
  attr name extract (D.scaleD scale >>> D.showNumD)
  where
  scale = (rangeMax - rangeMin) / (domainMax - domainMin)
