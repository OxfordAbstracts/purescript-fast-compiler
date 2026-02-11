module Example where

import Prelude

import Control.Monad.Reader (ReaderT(..))
import Data.ArgsRotater (rotate, (<<^), (<^))
import Data.EtaConversionTransformer ((:>>), (<<:), (<<|), (|>>))
import Data.ReaderTEtaConversionTransformer (readerT)
import Type.Equality (class TypeEquals, to)

newtype Result a = Result a

fun :: String -> Int -> Boolean -> String
fun _ _ _ = ""

exampleA1 :: String -> Int -> Boolean -> Result String
exampleA1 s i b = Result $ fun s i b

exampleA2 :: String -> Int -> Boolean -> Result String
exampleA2 = Result <<| fun

exampleA3 :: String -> Int -> Boolean -> Result String
exampleA3 = fun |>> Result

newtype Functions = Functions {
  fun :: String -> Int -> Boolean -> String
}
runFunctions :: Functions -> { fun :: String -> Int -> Boolean -> String }
runFunctions (Functions r) = r

exampleB1 :: String -> Int -> Boolean -> Result (Functions -> String)
exampleB1 s i b = Result $ (\f -> f.fun s i b) <<< runFunctions

exampleB2 :: String -> Int -> Boolean -> Result (Functions -> String)
exampleB2 = Result <<: _.fun <<< runFunctions

exampleB3 :: String -> Int -> Boolean -> Result (Functions -> String)
exampleB3 = runFunctions >>> _.fun :>> Result

exampleC1 :: forall r m. TypeEquals r { fun :: String -> m Unit } => String -> ReaderT r m Unit
exampleC1 s = ReaderT $ \r -> (to r).fun s

exampleC2 :: forall r m. TypeEquals r { fun :: String -> m Unit } => String -> ReaderT r m Unit
exampleC2 = readerT _.fun

rotate1 :: Boolean -> String -> Int -> String
rotate1 = rotate fun

rotate2 :: Int -> Boolean -> String -> String
rotate2 = rotate $ rotate fun

rotate3 :: String -> Int -> Boolean -> String
rotate3 = rotate $ rotate $ rotate fun

appliedLast :: String -> Int -> String
appliedLast = fun <^ true

reverseExample :: String -> String
reverseExample = fun <<^ true <<^ 10