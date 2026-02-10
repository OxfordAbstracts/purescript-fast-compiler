module Test.DataMVC.Variant.DataUISpec
  ( spec
  ) where

import Prelude

import Data.Identity (Identity)
import Data.Variant (Variant)
import DataMVC.Types (DataUI, DataUiInterface)
import DataMVC.Variant.DataUI as ME
import MVC.Variant (CaseKey, VariantMsg, VariantState)
import Test.DataMVC.TestTypes (HTML, M1, M2, M3, S1, S2, S3, T1, T2, T3)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

testDataUiVariant
  :: Record
       ( case1 :: DataUI HTML Identity Identity M1 S1 T1
       , case2 :: DataUI HTML Identity Identity M1 S1 T1
       , case3 :: DataUI HTML Identity Identity M1 S1 T1
       )
  -> Proxy "case1"
  -> { view ::
         forall msg
          . { caseKey :: CaseKey
            , caseKeys :: Array CaseKey
            , mkMsg :: CaseKey -> msg
            , viewCase :: HTML msg
            }
         -> HTML msg
     }
  -> DataUI HTML Identity Identity
       ( VariantMsg
           ( case1 :: Unit
           , case2 :: Unit
           , case3 :: Unit
           )
           ( case1 :: Identity M1
           , case2 :: Identity M1
           , case3 :: Identity M1
           )
       )
       ( VariantState
           ( case1 :: Identity S1
           , case2 :: Identity S1
           , case3 :: Identity S1
           )
       )
       ( Variant
           ( case1 :: T1
           , case2 :: T1
           , case3 :: T1
           )
       )
testDataUiVariant = ME.dataUiVariant

spec :: Spec Unit
spec = do
  describe "DataMVC.Variant.DataUI" do
    it "should compile" do
      void $ pure testDataUiVariant
