module Test.DataMVC.Variant.DataUiInterfaceSpec
  ( spec
  ) where

import Prelude

import Data.Variant (Variant)
import DataMVC.Types (DataUiInterface)
import DataMVC.Variant.DataUiInterface as ME
import Test.DataMVC.TestTypes (HTML)
import MVC.Variant (CaseKey, VariantMsg, VariantState)
import Test.DataMVC.TestTypes (M1, M2, M3, S1, S2, S3, T1, T2, T3)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

testDataUiInterfaceVariant
  :: Record
       ( case1 :: DataUiInterface HTML M1 S1 T1
       , case2 :: DataUiInterface HTML M2 S2 T2
       , case3 :: DataUiInterface HTML M3 S3 T3
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
  -> DataUiInterface HTML
       ( VariantMsg
           ( case1 :: Unit
           , case2 :: Unit
           , case3 :: Unit
           )
           ( case1 :: M1
           , case2 :: M2
           , case3 :: M3
           )
       )
       ( VariantState
           ( case1 :: S1
           , case2 :: S2
           , case3 :: S3
           )
       )
       ( Variant
           ( case1 :: T1
           , case2 :: T2
           , case3 :: T3
           )
       )
testDataUiInterfaceVariant = ME.dataUiInterfaceVariant

spec :: Spec Unit
spec = do
  describe "DataMVC.Variant.DataUiInterface" do
    it "should compile" do
      void $ pure testDataUiInterfaceVariant
