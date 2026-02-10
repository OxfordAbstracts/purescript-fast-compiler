-- | Hylograph.Unified.Display - Profunctor-based Display Transformations
-- |
-- | Non-destructive display formatting as composable typed pipelines.
-- |
-- | ## Core Insight
-- |
-- | Display transformations are typed morphisms that compose:
-- | ```
-- | f :: a -> b
-- | g :: b -> c
-- | f >>> g :: a -> c
-- | ```
-- |
-- | The key property is **non-destructiveness**: the underlying value
-- | is preserved; only the presentation changes.
-- |
-- | ## Profunctor Structure
-- |
-- | `Display a b` is a profunctor:
-- | - Contravariant in `a` (input type)
-- | - Covariant in `b` (output type)
-- |
-- | This enables:
-- | - `lmapD f`: Change input type (e.g., extract field from record)
-- | - `rmapD g`: Change output type (e.g., further transform result)
-- | - Composition via `>>>`
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Define reusable displays
-- | percentageD :: Display Number String
-- | percentageD = scaleD 100.0 >>> roundD 1 >>> showNumD >>> suffixD "%"
-- |
-- | -- Adapt to different sources
-- | rateDisplay :: Display { rate :: Number } String
-- | rateDisplay = lmapD _.rate percentageD
-- |
-- | -- Use in spreadsheet
-- | cellValue = format percentageD computedValue
-- |
-- | -- Use in visualization label
-- | labelText = runDisplay percentageD dataPoint.value
-- | ```
module Hylograph.Unified.Display
  ( -- * Core Type
    Display(..)
  , runDisplay
    -- * Composition
  , idD
  , composeD
  , (>>>)
    -- * Profunctor Operations
  , lmapD
  , rmapD
  , dimapD
    -- * Numeric -> Numeric (chainable)
  , roundD
  , scaleD
  , clampD
  , absD
  , negateD
  , floorD
  , ceilD
    -- * Numeric -> String (terminal)
  , showNumD
  , fixedD
  , sciD
  , intD
    -- * String -> String (chainable)
  , prefixD
  , suffixD
  , padLeftD
  , padRightD
  , upperD
  , lowerD
  , trimD
    -- * Composite Displays
  , percentageD
  , currencyD
  , currencyWithSymbol
  , thousandsD
  , signedD
  , compactD
    -- * Boolean -> String
  , boolD
  , yesNoD
  ) where

import Prelude hiding (compose)

import Data.Array as Array
import Data.Foldable (foldr)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Number as Number
import Data.String as String
import Data.String.CodeUnits as SCU

-- =============================================================================
-- Core Display Type
-- =============================================================================

-- | Display transformation from type `a` to type `b`
-- |
-- | This is essentially a newtype around `a -> b`, but with a semantic
-- | meaning: it's a non-destructive presentation transformation.
-- |
-- | The profunctor structure (contravariant in a, covariant in b) enables
-- | flexible composition and adaptation.
newtype Display a b = Display (a -> b)

-- | Run a display transformation
runDisplay :: forall a b. Display a b -> a -> b
runDisplay (Display f) = f

-- =============================================================================
-- Composition
-- =============================================================================

-- | Identity display (does nothing)
idD :: forall a. Display a a
idD = Display identity

-- | Compose two displays (left to right)
-- |
-- | `f >>> g` means: first apply f, then apply g
composeD :: forall a b c. Display a b -> Display b c -> Display a c
composeD (Display f) (Display g) = Display (g <<< f)

infixl 9 composeD as >>>

-- =============================================================================
-- Profunctor Operations
-- =============================================================================

-- | Contravariant map: change input type
-- |
-- | Given a way to get `a` from `a'`, adapt a `Display a b` to `Display a' b`
-- |
-- | Example:
-- | ```purescript
-- | percentageD :: Display Number String
-- | lmapD _.rate percentageD :: Display { rate :: Number } String
-- | ```
lmapD :: forall a a' b. (a' -> a) -> Display a b -> Display a' b
lmapD f (Display g) = Display (g <<< f)

-- | Covariant map: change output type
-- |
-- | Given a way to transform `b` to `b'`, adapt a `Display a b` to `Display a b'`
rmapD :: forall a b b'. (b -> b') -> Display a b -> Display a b'
rmapD f (Display g) = Display (f <<< g)

-- | Profunctor dimap: change both types
dimapD :: forall a a' b b'. (a' -> a) -> (b -> b') -> Display a b -> Display a' b'
dimapD f g (Display h) = Display (g <<< h <<< f)

-- =============================================================================
-- Numeric -> Numeric (chainable, preserve numeric type)
-- =============================================================================

-- | Round to N decimal places
-- |
-- | Example: `roundD 2` makes `3.14159` display as `3.14`
roundD :: Int -> Display Number Number
roundD decimals = Display \n ->
  let factor = Number.pow 10.0 (Int.toNumber decimals)
  in Number.round (n * factor) / factor

-- | Scale by a factor
-- |
-- | Example: `scaleD 100.0` for percentages (0.5 -> 50.0)
scaleD :: Number -> Display Number Number
scaleD factor = Display (_ * factor)

-- | Clamp to range [lo, hi]
clampD :: Number -> Number -> Display Number Number
clampD lo hi = Display \n -> max lo (min hi n)

-- | Absolute value
absD :: Display Number Number
absD = Display \n -> if n < 0.0 then negate n else n

-- | Negate
negateD :: Display Number Number
negateD = Display negate

-- | Floor (round down)
floorD :: Display Number Number
floorD = Display Number.floor

-- | Ceiling (round up)
ceilD :: Display Number Number
ceilD = Display Number.ceil

-- =============================================================================
-- Numeric -> String (terminal displays)
-- =============================================================================

-- | Default numeric display (smart formatting)
-- |
-- | - Integers display without decimal point
-- | - Floats display with minimal precision (trimmed trailing zeros)
showNumD :: Display Number String
showNumD = Display formatNumber

-- | Fixed decimal places
-- |
-- | Example: `fixedD 2` makes `3.1` display as `3.10`
fixedD :: Int -> Display Number String
fixedD decimals = Display (formatFixed decimals)

-- | Scientific notation
-- |
-- | Example: `sciD 2` makes `1234.5` display as `1.23e3`
sciD :: Int -> Display Number String
sciD precision = Display (formatScientific precision)

-- | Integer display (truncates decimal part)
intD :: Display Number String
intD = Display (show <<< Int.round)

-- =============================================================================
-- String -> String (chainable)
-- =============================================================================

-- | Add prefix
-- |
-- | Example: `prefixD "$"` makes `100` display as `$100`
prefixD :: String -> Display String String
prefixD p = Display (p <> _)

-- | Add suffix
-- |
-- | Example: `suffixD "%"` makes `50` display as `50%`
suffixD :: String -> Display String String
suffixD s = Display (_ <> s)

-- | Pad left to width with character
padLeftD :: Int -> Char -> Display String String
padLeftD width c = Display \s ->
  let padding = String.fromCodePointArray (replicate (width - String.length s) (String.codePointFromChar c))
  in padding <> s

-- | Pad right to width with character
padRightD :: Int -> Char -> Display String String
padRightD width c = Display \s ->
  let padding = String.fromCodePointArray (replicate (width - String.length s) (String.codePointFromChar c))
  in s <> padding

-- | Convert to uppercase
upperD :: Display String String
upperD = Display String.toUpper

-- | Convert to lowercase
lowerD :: Display String String
lowerD = Display String.toLower

-- | Trim whitespace
trimD :: Display String String
trimD = Display String.trim

-- =============================================================================
-- Composite Displays (common patterns)
-- =============================================================================

-- | Percentage display: 0.156 -> "15.6%"
percentageD :: Display Number String
percentageD = scaleD 100.0 >>> roundD 1 >>> showNumD >>> suffixD "%"

-- | Currency display (USD): 1234.56 -> "$1,234.56"
currencyD :: Display Number String
currencyD = currencyWithSymbol "$"

-- | Currency with custom symbol
currencyWithSymbol :: String -> Display Number String
currencyWithSymbol symbol =
  roundD 2 >>> showNumD >>> thousandsD >>> prefixD symbol

-- | Add thousands separators: 1234567 -> "1,234,567"
thousandsD :: Display String String
thousandsD = Display insertThousandsSeparators

-- | Signed display: negative in parentheses (accounting style)
-- |
-- | Example: -100 -> "(100)", 100 -> "100"
signedD :: Display Number String
signedD = Display \n ->
  if n < 0.0
    then "(" <> formatNumber (negate n) <> ")"
    else formatNumber n

-- | Compact display for large numbers
-- |
-- | Example: 1500000 -> "1.5M", 1500 -> "1.5K"
compactD :: Display Number String
compactD = Display \n ->
  if n >= 1000000.0
    then formatNumber (n / 1000000.0) <> "M"
  else if n >= 1000.0
    then formatNumber (n / 1000.0) <> "K"
  else formatNumber n

-- =============================================================================
-- Boolean -> String
-- =============================================================================

-- | Boolean display: true -> "true", false -> "false"
boolD :: Display Boolean String
boolD = Display show

-- | Boolean display: true -> "Yes", false -> "No"
yesNoD :: Display Boolean String
yesNoD = Display \b -> if b then "Yes" else "No"

-- =============================================================================
-- Formatting Helpers
-- =============================================================================

-- | Format number intelligently
formatNumber :: Number -> String
formatNumber n =
  let rounded = Number.round n
  in if n == rounded
    then show (Int.round n)
    else trimTrailingZeros (show n)

-- | Format with fixed decimals
formatFixed :: Int -> Number -> String
formatFixed decimals n =
  let factor = Number.pow 10.0 (Int.toNumber decimals)
      rounded = Number.round (n * factor) / factor
      str = show rounded
  in ensureDecimals decimals str

-- | Format in scientific notation
formatScientific :: Int -> Number -> String
formatScientific precision n =
  -- Simple implementation - could use proper scientific formatting
  let exponent = Number.floor (Number.log n / Number.ln10)
      mantissa = n / Number.pow 10.0 exponent
  in formatFixed precision mantissa <> "e" <> show (Int.round exponent)

-- | Ensure string has exactly N decimal places
ensureDecimals :: Int -> String -> String
ensureDecimals n str =
  case String.indexOf (String.Pattern ".") str of
    Nothing -> str <> "." <> repeatChar n '0'
    Just idx ->
      let decimals = String.length str - idx - 1
      in if decimals < n
           then str <> repeatChar (n - decimals) '0'
           else str

-- | Trim trailing zeros after decimal point
trimTrailingZeros :: String -> String
trimTrailingZeros s =
  if String.contains (String.Pattern ".") s
    then dropRightWhile (\c -> c == '0') (dropRightWhile (\c -> c == '.') s)
    else s

-- | Insert thousands separators
insertThousandsSeparators :: String -> String
insertThousandsSeparators s =
  case String.indexOf (String.Pattern ".") s of
    Nothing -> insertSeps s
    Just idx ->
      let intPart = String.take idx s
          decPart = String.drop idx s
      in insertSeps intPart <> decPart
  where
  insertSeps str =
    let chars = SCU.toCharArray str
        reversed = reverse chars
        grouped = groupsOf 3 reversed
        withCommas = intercalate [','] grouped
    in SCU.fromCharArray (reverse withCommas)

-- Helper functions
repeatChar :: Int -> Char -> String
repeatChar n c = SCU.fromCharArray (replicate n c)

replicate :: forall a. Int -> a -> Array a
replicate n x = if n <= 0 then [] else [x] <> replicate (n - 1) x

reverse :: forall a. Array a -> Array a
reverse = foldr (\x acc -> acc <> [x]) []

intercalate :: forall a. Array a -> Array (Array a) -> Array a
intercalate _ arr | Array.null arr = []
intercalate _ arr | Array.length arr == 1 = case Array.head arr of
  Just x -> x
  Nothing -> []
intercalate sep arr = case Array.uncons arr of
  Just { head: x, tail: xs } -> x <> sep <> intercalate sep xs
  Nothing -> []

groupsOf :: forall a. Int -> Array a -> Array (Array a)
groupsOf _ arr | Array.null arr = []
groupsOf n arr =
  let { before, after } = splitAt n arr
  in [before] <> groupsOf n after

splitAt :: forall a. Int -> Array a -> { before :: Array a, after :: Array a }
splitAt n arr = { before: Array.take n arr, after: Array.drop n arr }

-- Use Array.uncons directly instead of our own uncons
-- These helpers are no longer needed since we use Data.Array functions

dropRightWhile :: (Char -> Boolean) -> String -> String
dropRightWhile pred s =
  let chars = SCU.toCharArray s
      trimmed = dropWhileEnd pred chars
  in SCU.fromCharArray trimmed

dropWhileEnd :: forall a. (a -> Boolean) -> Array a -> Array a
dropWhileEnd pred arr = reverse (dropWhileArray pred (reverse arr))

dropWhileArray :: forall a. (a -> Boolean) -> Array a -> Array a
dropWhileArray pred arr = case Array.uncons arr of
  Nothing -> []
  Just { head, tail } ->
    if pred head
      then dropWhileArray pred tail
      else arr
