module Test.MVC.Record.UISpec where

import Prelude

import MVC.Record (RecordMsg, RecordState)
import MVC.Record.UI (uiRecord)
import MVC.Types (UI)
import Test.MVC.TestTypes (HTML(..), M1, M2, M3, S1(..), S2(..), S3(..))
import Test.Spec (Spec, describe, it)

type Msg = RecordMsg
  ( field1 :: M1
  , field2 :: M2
  , field3 :: M3
  )

type State = RecordState
  ( field1 :: S1
  , field2 :: S2
  , field3 :: S3
  )

ui1 :: UI HTML M1 S1
ui1 =
  { init: S1
  , update: \(_ :: M1) (_ :: S1) -> S1
  , view: \(_ :: S1) -> HTML
  }

ui2 :: UI HTML M2 S2
ui2 =
  { init: S2
  , update: \(_ :: M2) (_ :: S2) -> S2
  , view: \(_ :: S2) -> HTML
  }

ui3 :: UI HTML M3 S3
ui3 =
  { init: S3
  , update: \(_ :: M3) (_ :: S3) -> S3
  , view: \(_ :: S3) -> HTML
  }

testUi :: UI HTML Msg State
testUi = uiRecord
  { field1: ui1
  , field2: ui2
  , field3: ui3
  }
  { viewEntries: \_ -> HTML }

spec :: Spec Unit
spec =
  describe "MVC.Record.UI" do
    it "should compile" do
      void $ pure testUi
