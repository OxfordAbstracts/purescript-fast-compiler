module Webb.Random 
( random
, maybe
, alpha, alpha', ascii, ascii'
, numeric, numeric', alphaNumeric, alphaNumeric'
, bool, int, int', id, className, word, words, name
, randomId
)
where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Gen (chooseInt)
import Data.Char.Gen (genAlpha, genAsciiChar, genDigitChar)
import Data.Maybe (Maybe(..))
import Data.String (codePointFromChar, fromCodePointArray, joinWith)
import Data.Tuple (Tuple(..))
import Effect.Class (class MonadEffect)
import Effect.Ref (Ref)
import Effect.Unsafe (unsafePerformEffect)
import Random.LCG (Seed, randomSeed)
import Webb.State.Prelude (aread, awrite, newRef)
import Webb.Monad.Prelude (timesRepeat)
import Test.QuickCheck.Gen (Gen, runGen)

{- Random generators that are commonly useful, and a way to run them. -}

single :: Ref Seed
single = unsafePerformEffect do
  s <- randomSeed
  ref <- newRef s
  pure ref

random :: forall m a. MonadEffect m => Gen a -> m a
random gen = do
  seed <- aread single
  let 
    state = { newSeed: seed, size: 1 }
    (Tuple a { newSeed }) = runGen gen state
  awrite newSeed single
  pure a

randomId :: forall m. MonadEffect m => m String
randomId = random id
  
maybe :: forall a. Gen a -> Gen (Maybe a)
maybe gen = do
  just <- bool
  if just then do
    a <- gen
    pure $ Just a
  else do
    pure $ Nothing
  
alpha :: Int -> Int -> Gen String
alpha min max = do
  i <- int min max
  chars <- timesRepeat i genAlpha
  pure $ asString chars
  
alpha' :: Int -> Gen String
alpha' len = alpha len len
  
ascii :: Int -> Int -> Gen String
ascii min max = do 
  i <- int min max
  chars <- timesRepeat i genAsciiChar
  pure $ asString chars
  
ascii' :: Int -> Gen String
ascii' len = ascii len len
  
numeric :: Int -> Int -> Gen String
numeric min max = do
  i <- int min max
  chars <- timesRepeat i genDigitChar
  pure $ asString chars

numeric' :: Int -> Gen String
numeric' len = numeric len len

alphaNumeric :: Int -> Int -> Gen String
alphaNumeric min max = do
  i <- int min max
  chars <- timesRepeat i (genAlpha <|> genDigitChar)
  pure $ asString chars

alphaNumeric' :: Int -> Gen String
alphaNumeric' len = alphaNumeric len len
  
int :: Int -> Int -> Gen Int
int low high = chooseInt (min low high) (max low high)

int' :: Int -> Gen Int
int' high = int 0 high

bool :: Gen Boolean
bool = do 
  i <- int 0 1
  if i > 0 then do
    pure true 
  else do
    pure false

asString :: Array Char -> String
asString chars = chars # (_ <#> codePointFromChar) >>> fromCodePointArray

id :: Gen String
id = alphaNumeric' 32

className :: String -> Gen String
className prefix = do
  start <- alpha' 1
  end <- alphaNumeric' 11
  let suffix = start <> end
  pure $ prefix <> "-" <> suffix
  
word :: Gen String
word = alphaNumeric 4 9

words :: Int -> Int -> Gen String
words min max = do
  i <- int min max
  arr <- timesRepeat i word
  pure $ joinWith " " arr
  
name :: Gen String
name = words 2 4
