-- | Value Interpolation
-- |
-- | Type-safe interpolation functions for various value types.
-- | Used with easing functions from Hylograph.Transition.Tick to create
-- | smooth transitions.
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Transition.Interpolate as I
-- | import Hylograph.Transition.Tick (easeOutQuad, withEasing)
-- |
-- | -- Interpolate a color with easing
-- | let color = withEasing easeOutQuad (I.lerpRGB red blue) progress
-- |
-- | -- Interpolate a point
-- | let pos = I.lerpPoint origin target progress
-- | ```
module Hylograph.Transition.Interpolate
  ( -- * Point interpolation
    Point
  , lerpPoint
  , lerpPointXY
    -- * Color interpolation (RGB)
  , RGB(..)
  , lerpRGB
  , rgbToCSS
  , cssToRGB
    -- * Color interpolation (HSL)
  , HSL(..)
  , lerpHSL
  , hslToCSS
  , hslToRGB
  , rgbToHSL
    -- * Generic interpolation
  , class Interpolatable
  , interpolate
    -- * Interpolator type
  , Interpolator
  , makeInterpolator
  ) where

import Prelude

import Control.Alt ((<|>))
import Data.Int (round, toNumber)
import Data.Int as Int
import Data.Maybe (Maybe)
import Data.Number (abs)
import Data.String.Regex (regex, match)
import Data.String.Regex.Flags (noFlags)
import Data.Array.NonEmpty as NEA
import Data.Either (hush)
import Data.Number as Number
import Hylograph.Transition.Tick (Progress, lerp, lerpInt)

-- =============================================================================
-- Point Interpolation
-- =============================================================================

-- | 2D point
type Point = { x :: Number, y :: Number }

-- | Linear interpolation between two points
lerpPoint :: Point -> Point -> Progress -> Point
lerpPoint p1 p2 t =
  { x: lerp p1.x p2.x t
  , y: lerp p1.y p2.y t
  }

-- | Interpolate x and y separately (for asymmetric easing)
lerpPointXY
  :: { fromX :: Number, fromY :: Number }
  -> { toX :: Number, toY :: Number }
  -> { progressX :: Progress, progressY :: Progress }
  -> Point
lerpPointXY from to progress =
  { x: lerp from.fromX to.toX progress.progressX
  , y: lerp from.fromY to.toY progress.progressY
  }

-- =============================================================================
-- RGB Color Interpolation
-- =============================================================================

-- | RGB color with components in 0-255 range
newtype RGB = RGB { r :: Int, g :: Int, b :: Int }

derive instance Eq RGB

instance Show RGB where
  show (RGB c) = "RGB(" <> show c.r <> "," <> show c.g <> "," <> show c.b <> ")"

-- | Linear interpolation in RGB space
-- | Note: For perceptually uniform transitions, consider lerpHSL
lerpRGB :: RGB -> RGB -> Progress -> RGB
lerpRGB (RGB c1) (RGB c2) t = RGB
  { r: lerpInt c1.r c2.r t
  , g: lerpInt c1.g c2.g t
  , b: lerpInt c1.b c2.b t
  }

-- | Convert RGB to CSS color string
rgbToCSS :: RGB -> String
rgbToCSS (RGB c) = "rgb(" <> show c.r <> "," <> show c.g <> "," <> show c.b <> ")"

-- | Parse CSS rgb() or hex color to RGB
-- | Supports: rgb(r,g,b), #RRGGBB, #RGB
cssToRGB :: String -> Maybe RGB
cssToRGB s = parseRGB s <|> parseHex s
  where
    parseRGB str = do
      re <- hush $ regex "rgb\\s*\\(\\s*(\\d+)\\s*,\\s*(\\d+)\\s*,\\s*(\\d+)\\s*\\)" noFlags
      matches <- match re str
      rStr <- join $ NEA.index matches 1
      gStr <- join $ NEA.index matches 2
      bStr <- join $ NEA.index matches 3
      r <- Number.fromString rStr
      g <- Number.fromString gStr
      b <- Number.fromString bStr
      pure $ RGB { r: round r, g: round g, b: round b }

    parseHex str = do
      re <- hush $ regex "^#([0-9a-fA-F]{2})([0-9a-fA-F]{2})([0-9a-fA-F]{2})$" noFlags
      matches <- match re str
      rStr <- join $ NEA.index matches 1
      gStr <- join $ NEA.index matches 2
      bStr <- join $ NEA.index matches 3
      r <- Int.fromStringAs Int.hexadecimal rStr
      g <- Int.fromStringAs Int.hexadecimal gStr
      b <- Int.fromStringAs Int.hexadecimal bStr
      pure $ RGB { r, g, b }

-- =============================================================================
-- HSL Color Interpolation
-- =============================================================================

-- | HSL color
-- | h: hue in degrees (0-360)
-- | s: saturation (0-1)
-- | l: lightness (0-1)
newtype HSL = HSL { h :: Number, s :: Number, l :: Number }

derive instance Eq HSL

instance Show HSL where
  show (HSL c) = "HSL(" <> show c.h <> "," <> show c.s <> "," <> show c.l <> ")"

-- | Linear interpolation in HSL space
-- | Takes the shortest path around the hue circle
lerpHSL :: HSL -> HSL -> Progress -> HSL
lerpHSL (HSL c1) (HSL c2) t = HSL
  { h: lerpHue c1.h c2.h t
  , s: lerp c1.s c2.s t
  , l: lerp c1.l c2.l t
  }
  where
    -- Take shortest path around hue circle
    lerpHue h1 h2 progress =
      let
        diff = h2 - h1
        shortDiff =
          if abs diff > 180.0 then
            if diff > 0.0 then diff - 360.0 else diff + 360.0
          else diff
        result = h1 + shortDiff * progress
      in
        if result < 0.0 then result + 360.0
        else if result >= 360.0 then result - 360.0
        else result

-- | Convert HSL to CSS color string
hslToCSS :: HSL -> String
hslToCSS (HSL c) =
  "hsl(" <> show (round c.h) <> "," <> show (round (c.s * 100.0)) <> "%," <> show (round (c.l * 100.0)) <> "%)"

-- | Convert HSL to RGB
hslToRGB :: HSL -> RGB
hslToRGB (HSL { h, s, l }) =
  let
    c = (1.0 - abs (2.0 * l - 1.0)) * s
    x = c * (1.0 - abs (mod' (h / 60.0) 2.0 - 1.0))
    m = l - c / 2.0

    { r', g', b' } =
      if h < 60.0 then { r': c, g': x, b': 0.0 }
      else if h < 120.0 then { r': x, g': c, b': 0.0 }
      else if h < 180.0 then { r': 0.0, g': c, b': x }
      else if h < 240.0 then { r': 0.0, g': x, b': c }
      else if h < 300.0 then { r': x, g': 0.0, b': c }
      else { r': c, g': 0.0, b': x }
  in
    RGB
      { r: round ((r' + m) * 255.0)
      , g: round ((g' + m) * 255.0)
      , b: round ((b' + m) * 255.0)
      }
  where
    -- Floating point modulo
    mod' :: Number -> Number -> Number
    mod' a b = a - b * Number.floor (a / b)

-- | Convert RGB to HSL
rgbToHSL :: RGB -> HSL
rgbToHSL (RGB { r, g, b }) =
  let
    r' = toNumber r / 255.0
    g' = toNumber g / 255.0
    b' = toNumber b / 255.0

    cmax = max r' (max g' b')
    cmin = min r' (min g' b')
    delta = cmax - cmin

    l = (cmax + cmin) / 2.0

    s = if delta == 0.0 then 0.0
        else delta / (1.0 - abs (2.0 * l - 1.0))

    h = if delta == 0.0 then 0.0
        else if cmax == r' then 60.0 * mod' ((g' - b') / delta) 6.0
        else if cmax == g' then 60.0 * ((b' - r') / delta + 2.0)
        else 60.0 * ((r' - g') / delta + 4.0)

    h' = if h < 0.0 then h + 360.0 else h
  in
    HSL { h: h', s, l }
  where
    mod' :: Number -> Number -> Number
    mod' x y = x - y * Number.floor (x / y)

-- =============================================================================
-- Generic Interpolation
-- =============================================================================

-- | Typeclass for types that can be interpolated
class Interpolatable a where
  interpolate :: a -> a -> Progress -> a

instance Interpolatable Number where
  interpolate = lerp

instance Interpolatable Int where
  interpolate = lerpInt

instance Interpolatable RGB where
  interpolate = lerpRGB

instance Interpolatable HSL where
  interpolate = lerpHSL

-- | An interpolation function between two values
type Interpolator a = a -> a -> Progress -> a

-- | Create an interpolator that captures the start and end values
makeInterpolator :: forall a. Interpolatable a => a -> a -> (Progress -> a)
makeInterpolator from to = interpolate from to
