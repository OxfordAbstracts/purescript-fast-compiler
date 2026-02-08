module Test.DataMVC.Record.DataUISpec
  ( spec
  ) where

import Prelude

import Data.Identity (Identity)
import DataMVC.Types (DataUI)
import DataMVC.Record.DataUI as ME
import MVC.Record (RecordMsg, RecordState)
import Test.DataMVC.TestTypes (HTML, M1, M2, M3, S1, S2, S3, T1, T2, T3)
import Test.Spec (Spec, describe, it)

testDataUiRecord
  :: { viewEntries ::
         Array
           { key :: String
           , viewValue ::
               HTML
                 ( RecordMsg
                     ( field1 :: Identity M1
                     , field2 :: Identity M2
                     , field3 :: Identity M3
                     )
                 )
           }
         -> HTML
              ( RecordMsg
                  ( field1 :: Identity M1
                  , field2 :: Identity M2
                  , field3 :: Identity M3
                  )
              )
     }
  -> Record
       ( field1 :: DataUI HTML Identity Identity M1 S1 T1
       , field2 :: DataUI HTML Identity Identity M2 S2 T2
       , field3 :: DataUI HTML Identity Identity M3 S3 T3
       )
  -> DataUI HTML Identity Identity
       ( RecordMsg
           ( field1 :: Identity M1
           , field2 :: Identity M2
           , field3 :: Identity M3
           )
       )
       ( RecordState
           ( field1 :: Identity S1
           , field2 :: Identity S2
           , field3 :: Identity S3
           )
       )
       ( Record
           ( field1 :: T1
           , field2 :: T2
           , field3 :: T3
           )
       )
testDataUiRecord = ME.dataUiRecord

testDataUiRecord2
  :: { viewEntries ::
         Array
           { key :: String
           , viewValue ::
               HTML
                 ( RecordMsg
                     ( field1 :: Identity M1
                     )
                 )
           }
         -> HTML
              ( RecordMsg
                  ( field1 :: Identity M1
                  )
              )
     }
  -> Record
       ( field1 :: DataUI HTML Identity Identity M1 S1 T1
       )
  -> DataUI HTML Identity Identity
       ( RecordMsg
           ( field1 :: Identity M1
           )
       )
       ( RecordState
           ( field1 :: Identity S1
           )
       )
       { field1 :: T1
       }

testDataUiRecord2 = ME.dataUiRecord

spec :: Spec Unit
spec = do
  describe "DataMVC.Record.DataUI" do
    it "should compile" do
      void $ pure testDataUiRecord
    it "should compile" do
      void $ pure testDataUiRecord2

