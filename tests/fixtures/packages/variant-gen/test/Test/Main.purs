module Test.Main where

import Prelude hiding ((/))

import Data.String.Gen (genAlphaString)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as V
import Effect (Effect)
import Test.QuickCheck ((===))
import Test.QuickCheck.Gen (Gen, vectorOf)
import Test.Spec (it)
import Test.Spec.QuickCheck (quickCheck)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Data.Variant.Gen (genVariantFrequency, genVariantUniform)
import Data.Set as Set

genUniform :: Gen (Variant (id :: String, unit :: Unit))
genUniform =
  genVariantUniform
    { id: genAlphaString
    , unit: pure unit
    }

genFrequency :: Gen (Variant (id :: String, unit :: Unit))
genFrequency =
  genVariantFrequency
    { id: Tuple 0.0 genAlphaString
    , unit: Tuple 1.0 (pure unit)
    }

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  it "generates all tags from genUniform" do
    quickCheck do
      (samples :: Array (Variant _)) <- vectorOf 100 genUniform
      let getTag = V.match { id: const "id", unit: const "unit" }
      let tags = Set.fromFoldable $ map getTag samples
      let allTags = Set.fromFoldable $ [ "id", "unit" ]
      pure $ tags === allTags

  it "generates only one tag from genFrequency" do
    quickCheck do
      (samples :: Array (Variant _)) <- vectorOf 100 genFrequency
      let getTag = V.match { id: const "id", unit: const "unit" }
      let tags = Set.fromFoldable $ map getTag samples
      let allTags = Set.fromFoldable $ [ "unit" ]
      pure $ tags === allTags
