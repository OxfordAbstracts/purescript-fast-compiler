module Web.Punycode
  ( decode
  , encode
  , toAscii
  , toUnicode
  , Error(..)
  ) where

import Prelude

import Data.Array (filter, findLastIndex, foldl, take)
import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Enum (fromEnum, toEnum)
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.String (CodePoint, Pattern(..), codePointFromChar, toCodePointArray)
import Data.String as String
import Data.String.Regex (Regex, test)
import Data.String.Regex as Regex
import Data.String.Regex.Flags (global)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)

maxInt :: Int
maxInt = 0x7FFFFFFF

-- Bootstring parameters
base :: Int
base = 36

tMin :: Int
tMin = 1

tMax :: Int
tMax = 26

skew :: Int
skew = 38

damp :: Int
damp = 700

delim :: CodePoint
delim = codePointFromChar '-'

basicLimit :: CodePoint
basicLimit = unsafePartial $ fromJust $ toEnum 0x80

baseMinusTMin :: Int
baseMinusTMin = base - tMin

nonAsciiRegex :: Regex
nonAsciiRegex = unsafeRegex "[^\x00-\x7F]" global

separatorRegex :: Regex
separatorRegex = unsafeRegex "[\x2E\x3002\xFF0E\xFF61]" global

data Error = NotBasic CodePoint | InvalidInput | Overflow

instance showError :: Show Error where
  show (NotBasic c) = "NotBasic" <> " " <> show c
  show InvalidInput = "InvalidInput"
  show Overflow = "Overflow"

derive instance eqError :: Eq Error

type DecodeState =
  { output :: Array CodePoint
  , input :: Array CodePoint
  , bias :: Int
  , n :: Int
  , i :: Int
  , index :: Int
  }

initDecodeState :: String -> DecodeState
initDecodeState input =
  { output: []
  , input: toCodePointArray input
  , bias: 72
  , n: 128
  , i: 0
  , index: 0
  }

type EncodeState =
  { output :: Array CodePoint
  , input :: Array CodePoint
  , basicLen :: Int
  , n :: Int
  , delta :: Int
  , bias :: Int
  , handled :: Int
  }

initEncodeState :: String -> EncodeState
initEncodeState input =
  { output: []
  , input: toCodePointArray input
  , basicLen: 0
  , n: 128
  , delta: 0
  , bias: 72
  , handled: 0
  }

-- The basic code points are
-- the ASCII [ASCII] code points (0..7F), of which U+002D (-) is the
-- delimiter, and some of the others have digit-values as follows:

--    code points    digit-values
--    ------------   ----------------------
--    41..5A (A-Z) =  0 to 25, respectively
--    61..7A (a-z) =  0 to 25, respectively
--    30..39 (0-9) = 26 to 35, respectively
basicToDigit :: CodePoint -> Either Error Int
basicToDigit c | Just c >= toEnum 0x30 && Just c < toEnum 0x3A = Right $ 26 + (fromEnum c) - 0x30
basicToDigit c | Just c >= toEnum 0x41 && Just c < toEnum 0x5B = Right $ fromEnum c - 0x41
basicToDigit c | Just c >= toEnum 0x61 && Just c < toEnum 0x7B = Right $ fromEnum c - 0x61
basicToDigit c = Left $ NotBasic c

digitToBasic :: Int -> Either Error CodePoint
digitToBasic digit | digit < 26 = note InvalidInput $ toEnum $ digit + 22 + 75
digitToBasic digit = note InvalidInput $ toEnum $ digit + 22

guardOverflow :: Int -> Either Error Int
guardOverflow n | n < 0 = Left Overflow
guardOverflow n = Right n

adapt :: Int -> Int -> Boolean -> Int
adapt delta numPoints firstTime =
  k' + (baseMinusTMin + 1) * delta' / (delta' + skew)
  where
  innerAdapt :: Int -> Int -> (Tuple Int Int)
  innerAdapt k d | d <= baseMinusTMin * tMax / 2 = Tuple k d
  innerAdapt k d = innerAdapt (k + base) (d / baseMinusTMin)
  initialDelta
    | firstTime = delta / damp
    | otherwise = delta / 2
  initialDelta' = initialDelta + (initialDelta / numPoints)
  (Tuple k' delta') = innerAdapt 0 initialDelta'

basicDecode :: DecodeState -> Either Error DecodeState
basicDecode state =
  wrap <$> (traverse mapBasic $ before)
  where
  { input } = state
  lastDelim = fromMaybe 0 $ findLastIndex (eq delim) input
  before = take lastDelim input
  index
    | lastDelim > 0 = lastDelim + 1
    | otherwise = 0

  mapBasic :: CodePoint -> Either Error CodePoint
  mapBasic c | c < basicLimit = Right c
  mapBasic c = Left $ NotBasic c

  wrap :: Array CodePoint -> DecodeState
  wrap s = state { output = s, index = index, i = 0 }

stepInnerDecode :: Int -> Int -> DecodeState -> Either Error DecodeState
stepInnerDecode w k state =
  do
    digit <- note InvalidInput $ Array.index input index
    digit' <- basicToDigit digit
    i' <- guardOverflow $ i + (digit' * w)
    w' <- guardOverflow $ w * (base - t)
    step w' digit' (state { i = i', index = index + 1 })
  where
  { input, index, bias, i } = state
  t
    | k <= bias + tMin = tMin
    | k >= bias + tMax = tMax
    | otherwise = k - bias

  step :: Int -> Int -> DecodeState -> Either Error DecodeState
  step _ digit state' | digit < t = Right state'
  step w' _ state' = stepInnerDecode w' (k + base) state'

stepOuterDecode :: DecodeState -> Either Error DecodeState
stepOuterDecode state =
  if (state.index >= Array.length state.input) then Right state
  else do
    { i, index } <- stepInnerDecode 1 base state
    let out = (Array.length state.output) + 1
    let bias = adapt (i - state.i) out (state.i == 0)
    let i' = i `mod` out
    n <- guardOverflow $ state.n + i / out
    codepointN <- note InvalidInput $ toEnum n
    output <- note InvalidInput $ Array.insertAt i' codepointN state.output
    stepOuterDecode (state { output = output, bias = bias, n = n, i = i' + 1, index = index })

basicEncode :: EncodeState -> EncodeState
basicEncode { input, bias, delta, n } =
  wrap $ filter filterBasic input
  where
  filterBasic :: CodePoint -> Boolean
  filterBasic c = c < basicLimit

  delimit :: Array CodePoint -> Array CodePoint
  delimit s
    | Array.length s > 0 = Array.snoc s delim
    | otherwise = s

  wrap :: Array CodePoint -> EncodeState
  wrap s =
    { output: delimit s
    , handled: Array.length s
    , basicLen: Array.length s
    , input
    , bias
    , delta
    , n
    }

stepFinalEncodeHelper :: Int -> Int -> Int -> EncodeState -> Either Error EncodeState
stepFinalEncodeHelper _ q t state | q < t = do
  c <- digitToBasic q
  let output' = Array.snoc state.output c
  let { delta, handled } = state
  let bias = adapt delta (handled + 1) (handled == state.basicLen)
  pure $ state { output = output', bias = bias, delta = 0, handled = handled + 1 }
stepFinalEncodeHelper k q t state = do
  c <- digitToBasic $ t + (q - t) `mod` (base - t)
  let state' = state { output = Array.snoc state.output c }
  let q' = (q - t) / (base - t)
  stepFinalEncode (Right state') (k + base) q'

stepFinalEncode :: Either Error EncodeState -> Int -> Int -> Either Error EncodeState
stepFinalEncode (Left e) _ _ = Left e
stepFinalEncode (Right state) k q = stepFinalEncodeHelper k q t state
  where
  { bias } = state
  t
    | k <= bias + tMin = tMin
    | k >= bias + tMax = tMax
    | otherwise = k - bias

stepInnerEncode :: Either Error EncodeState -> Int -> Either Error EncodeState
stepInnerEncode (Left e) _ = Left e
stepInnerEncode (Right { delta, n }) c | c < n && delta + 1 < 0 = Left Overflow
stepInnerEncode (Right state) c | c /= state.n = Right state { delta = delta' }
  where
  delta'
    | c < state.n = state.delta + 1
    | otherwise = state.delta
stepInnerEncode (Right state) c = stepFinalEncode (Right state { delta = delta' }) base delta'
  where
  delta'
    | c < state.n = state.delta + 1
    | otherwise = state.delta

stepOuterEncode :: EncodeState -> Either Error EncodeState
stepOuterEncode state | state.handled >= Array.length state.input = Right state
stepOuterEncode state = do
  delta <- guardOverflow $ state.delta + (m' - state.n) * (state.handled + 1)
  state' <- foldl stepInnerEncode (Right $ state { delta = delta, n = m' }) inputInts
  stepOuterEncode (state' { delta = state'.delta + 1, n = state'.n + 1 })
  where
  inputInts = fromEnum <$> state.input

  findM :: Int -> Int -> Int
  findM m v
    | m > v && v >= state.n = v
    | otherwise = m
  m' = foldl findM maxInt inputInts

-- Convert a Punycode string of ASCII-only code points to a string of Unicode
-- code points.
decode :: String -> Either Error String
decode encoded = do
  state <- basicDecode $ initDecodeState encoded
  { output } <- stepOuterDecode state
  pure $ String.fromCodePointArray $ output

-- Convert a string of Unicode code points to a Punycode string of ASCII-only
-- code points.
encode :: String -> Either Error String
encode decoded = do
  let state = basicEncode $ initEncodeState decoded
  { output } <- stepOuterEncode state
  pure $ String.fromCodePointArray $ output

labelToUnicode :: String -> Either Error String
labelToUnicode input = fromMaybe (Right input) $ decode <$> String.stripPrefix (Pattern "xn--") input

labelToAscii :: String -> Either Error String
labelToAscii input | test nonAsciiRegex input = (<>) "xn--" <$> encode input
labelToAscii input = Right input

mapLabels :: (String -> Either Error String) -> String -> Either Error String
mapLabels f input = do
  let i = fromMaybe 0 $ (add 1) <$> String.indexOf (Pattern "@") input
  let { before, after } = String.splitAt i input
  let labels = Regex.split separatorRegex after
  labels' <- traverse f labels
  pure $ before <> (String.joinWith "." labels')

toUnicode :: String -> Either Error String
toUnicode input = mapLabels labelToUnicode input

toAscii :: String -> Either Error String
toAscii input = mapLabels labelToAscii input