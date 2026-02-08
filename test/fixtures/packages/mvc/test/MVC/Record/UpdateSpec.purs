module Test.MVC.Record.UpdateSpec where

import Prelude

import Data.Variant as V
import MVC.Record (RecordMsg(..), RecordState(..), updateRecord, updateRecordRL)
import Prim.RowList as RL
import Test.MVC.TestTypes (M1(..), M2(..), M3(..), S1(..), S2(..), S3(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Function (type (#), type ($))
import Type.Proxy (Proxy(..))

testUpdate :: RecordState (field1 :: S1, field2 :: S2, field3 :: S3)
testUpdate = updateRecord
  { field1: \(_ :: M1) (_ :: S1) -> S1
  , field2: \(_ :: M2) (_ :: S2) -> S2
  , field3: \(_ :: M3) (_ :: S3) -> S3
  }
  (SetField (V.inj (Proxy :: _ "field2") M2))
  ( RecordState
      { field1: S1
      , field2: S2
      , field3: S3
      }
  )

type State = RecordState (field1 :: S1, field2 :: S2, field3 :: S3)

testUpdateRL
  :: RecordState
       ( field1 :: S1
       , field2 :: S2
       , field3 :: S3
       )
testUpdateRL = updateRecordRL
  ( Proxy
      :: _ $ RL.Nil
           # RL.Cons "field3" Unit
           # RL.Cons "field2" Unit
           # RL.Cons "field1" Unit
  )
  { field1: \(_ :: M1) (_ :: S1) -> S1
  , field2: \(_ :: M2) (_ :: S2) -> S2
  , field3: \(_ :: M3) (_ :: S3) -> S3
  }
  ( RecordState
      { field1: S1
      , field2: S2
      , field3: S3
      }
  )
  (V.inj (Proxy :: _ "field2") M2)

spec :: Spec Unit
spec =
  describe "MVC.Record.Update" do
    describe "updateRecord" do
      it "should update fields correctly" do
        let
          actual :: State
          actual = updateRecord
            { field1: \msg _ -> case msg of
                M1 -> S1
                M1' -> S1'
                M1'' -> S1''
            , field2: \msg _ -> case msg of
                M2 -> S2
                M2' -> S2'
                M2'' -> S2''
            , field3: \msg _ -> case msg of
                M3 -> S3
                M3' -> S3'
                M3'' -> S3''
            }
            (SetField (V.inj (Proxy :: _ "field2") M2'))
            ( RecordState
                { field1: S1
                , field2: S2
                , field3: S3
                }
            )

          expected :: State
          expected = RecordState
            { field1: S1
            , field2: S2'
            , field3: S3
            }

        actual `shouldEqual` expected
