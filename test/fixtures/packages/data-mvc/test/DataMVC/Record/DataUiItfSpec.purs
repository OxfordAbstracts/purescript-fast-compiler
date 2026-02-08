module Test.DataMVC.Record.DataUiInterfaceSpec
  ( spec
  ) where

import Prelude

import DataMVC.Record.DataUiInterface as ME
import DataMVC.Types (DataUiInterface)
import MVC.Record (RecordMsg, RecordState)
import Test.DataMVC.TestTypes (HTML, M1, M2, M3, S1, S2, S3, T1, T2, T3)
import Test.Spec (Spec, describe, it)

testDataUiInterfaceRecord
  :: { viewEntries ::
         Array
           { key :: String
           , viewValue ::
               HTML
                 ( RecordMsg
                     ( field1 :: M1
                     , field2 :: M2
                     , field3 :: M3
                     )
                 )
           }
         -> HTML
              ( RecordMsg
                  ( field1 :: M1
                  , field2 :: M2
                  , field3 :: M3
                  )
              )
     }
  -> Record
       ( field1 :: DataUiInterface HTML M1 S1 T1
       , field2 :: DataUiInterface HTML M2 S2 T2
       , field3 :: DataUiInterface HTML M3 S3 T3
       )
  -> DataUiInterface HTML
       ( RecordMsg
           ( field1 :: M1
           , field2 :: M2
           , field3 :: M3
           )
       )
       ( RecordState
           ( field1 :: S1
           , field2 :: S2
           , field3 :: S3
           )
       )
       ( Record
           ( field1 :: T1
           , field2 :: T2
           , field3 :: T3
           )
       )
testDataUiInterfaceRecord = ME.dataUiInterfaceRecord

spec :: Spec Unit
spec = do
  describe "DataMVC.Record.DataUiInterface" do
    it "should compile" do
      void $ pure testDataUiInterfaceRecord
