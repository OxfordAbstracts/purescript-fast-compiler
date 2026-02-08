module Test.DataMVC.Variant.ExtractSpec
  ( spec
  ) where

import Prelude

import Data.Variant (Variant)
import DataMVC.Types (DataResult)
import DataMVC.Variant.Extract as ME
import MVC.Variant (VariantState)
import Test.DataMVC.TestTypes (S1, T1)
import Test.Spec (Spec, describe, it)

testExtractVariant
  :: Record
       ( field1 :: S1 -> DataResult T1
       , field2 :: S1 -> DataResult T1
       , field3 :: S1 -> DataResult T1
       )
  -> VariantState
       ( field1 :: S1
       , field2 :: S1
       , field3 :: S1
       )
  -> DataResult
       ( Variant
           ( field1 :: T1
           , field2 :: T1
           , field3 :: T1
           )
       )
testExtractVariant = ME.extractVariant

spec :: Spec Unit
spec = do
  describe "DataMVC.Variant.Extract" do
    it "should compile" do
      void $ pure testExtractVariant
