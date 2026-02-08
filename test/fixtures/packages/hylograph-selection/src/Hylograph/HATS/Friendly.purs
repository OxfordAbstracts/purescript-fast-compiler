-- | HATS Friendly API
-- |
-- | Convenience helpers for building HATS attributes.
-- | These produce the new thunked `Attr` type for use in HATS trees.
module Hylograph.HATS.Friendly
  ( -- Attribute constructors
    attr
  , attrNum
  , viewBox
  , transform
  , class_
  , style
  -- SVG attributes
  , cx, cy, r
  , x, y, x1, y1, x2, y2
  , width, height
  , d
  , fill, stroke, strokeWidth
  , opacity, fillOpacity, strokeOpacity
  , textAnchor, fontSize, fontFamily, fontWeight
  , preserveAspectRatio
  , points
  ) where

import Prelude

import Hylograph.HATS (Attr, staticStr, staticNum)

-- =============================================================================
-- Generic Attribute Constructors
-- =============================================================================

-- | Create a string attribute
attr :: String -> String -> Attr
attr = staticStr

-- | Create a numeric attribute
attrNum :: String -> Number -> Attr
attrNum = staticNum

-- =============================================================================
-- Layout Attributes
-- =============================================================================

-- | SVG viewBox attribute
viewBox :: Number -> Number -> Number -> Number -> Attr
viewBox minX minY w h = staticStr "viewBox" $
  show minX <> " " <> show minY <> " " <> show w <> " " <> show h

-- | Transform attribute
transform :: String -> Attr
transform = staticStr "transform"

-- | Class attribute
class_ :: String -> Attr
class_ = staticStr "class"

-- | Style attribute
style :: String -> Attr
style = staticStr "style"

-- =============================================================================
-- Position Attributes
-- =============================================================================

-- | cx attribute (circle center x)
cx :: Number -> Attr
cx = staticNum "cx"

-- | cy attribute (circle center y)
cy :: Number -> Attr
cy = staticNum "cy"

-- | r attribute (radius)
r :: Number -> Attr
r = staticNum "r"

-- | x attribute
x :: Number -> Attr
x = staticNum "x"

-- | y attribute
y :: Number -> Attr
y = staticNum "y"

-- | x1 attribute (line start x)
x1 :: Number -> Attr
x1 = staticNum "x1"

-- | y1 attribute (line start y)
y1 :: Number -> Attr
y1 = staticNum "y1"

-- | x2 attribute (line end x)
x2 :: Number -> Attr
x2 = staticNum "x2"

-- | y2 attribute (line end y)
y2 :: Number -> Attr
y2 = staticNum "y2"

-- | width attribute
width :: Number -> Attr
width = staticNum "width"

-- | height attribute
height :: Number -> Attr
height = staticNum "height"

-- =============================================================================
-- Path Attributes
-- =============================================================================

-- | d attribute (path data)
d :: String -> Attr
d = staticStr "d"

-- | points attribute (polygon/polyline)
points :: String -> Attr
points = staticStr "points"

-- =============================================================================
-- Styling Attributes
-- =============================================================================

-- | fill attribute
fill :: String -> Attr
fill = staticStr "fill"

-- | stroke attribute
stroke :: String -> Attr
stroke = staticStr "stroke"

-- | stroke-width attribute
strokeWidth :: Number -> Attr
strokeWidth = staticNum "stroke-width"

-- | opacity attribute
opacity :: String -> Attr
opacity = staticStr "opacity"

-- | fill-opacity attribute
fillOpacity :: String -> Attr
fillOpacity = staticStr "fill-opacity"

-- | stroke-opacity attribute
strokeOpacity :: String -> Attr
strokeOpacity = staticStr "stroke-opacity"

-- =============================================================================
-- Text Attributes
-- =============================================================================

-- | text-anchor attribute
textAnchor :: String -> Attr
textAnchor = staticStr "text-anchor"

-- | font-size attribute
fontSize :: String -> Attr
fontSize = staticStr "font-size"

-- | font-family attribute
fontFamily :: String -> Attr
fontFamily = staticStr "font-family"

-- | font-weight attribute
fontWeight :: String -> Attr
fontWeight = staticStr "font-weight"

-- =============================================================================
-- Other Attributes
-- =============================================================================

-- | preserveAspectRatio attribute
preserveAspectRatio :: String -> Attr
preserveAspectRatio = staticStr "preserveAspectRatio"
