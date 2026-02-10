module Test.Main where

import Prelude

import Control.Monad.Gen.Class (chooseInt)
import Control.Monad.Gen.Class as MGen
import Control.Monad.Gen.Trans (Gen, evalGen, randomSampleN, resizeGen, sized, vectorOf)
import Data.Array (all)
import Data.Array.Partial (head)
import Data.Foldable (sum)
import Data.Number (isFinite)
import Effect (Effect)
import Effect.Console (log, logShow)
import Partial.Unsafe (unsafePartial)
import Random.LCG (mkSeed)
import Test.Assert (assert)

testResize :: (forall a. Int -> Gen a -> Gen a) -> Boolean
testResize resize' =
  let
    initialSize = 2
    gen = do
      s1 <- sized pure
      s2 <- resize' 1 (sized pure)
      s3 <- sized pure
      pure $ [ s1, s2, s3 ] == [ initialSize, 1, initialSize ]
  in
    evalGen gen { newSeed: mkSeed 0, size: initialSize }

main :: Effect Unit
main = do
  log "MonadGen.resize"
  assert (testResize (MGen.resize <<< const))
  log "Gen.resize"
  assert (testResize (resizeGen))

  log "Try with some little Gens first"
  logShow =<< go 10
  logShow =<< go 100
  logShow =<< go 1000
  logShow =<< go 10000

  log "Testing stack safety of Gen"
  logShow =<< go 20000
  logShow =<< go 100000

  log "Checking that chooseFloat over the whole Number range always yields a finite value"
  randomSampleN 10 (MGen.chooseFloat ((-1.7976931348623157e+308)) (1.7976931348623157e+308)) >>= assert <<< all isFinite

  where
  go n = map (sum <<< unsafeHead) $ randomSampleN 1 (vectorOf n (chooseInt bottom top))

  unsafeHead :: forall x. Array x -> x
  unsafeHead xs = unsafePartial (head xs)
