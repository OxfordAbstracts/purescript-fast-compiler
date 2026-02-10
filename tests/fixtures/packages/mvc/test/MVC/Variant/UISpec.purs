module Test.MVC.Variant.UISpec where

import Prelude

import MVC.Types (UI)
import MVC.Variant.Types (VariantMsg, VariantState)
import MVC.Variant.UI (uiVariant)
import Test.MVC.TestTypes (HTML(..), M1, M2, M3, S1(..), S2(..), S3(..))
import Type.Proxy (Proxy(..))
import Test.Spec (Spec, describe, it)

type Msg = VariantMsg
  ( case1 :: Unit
  , case2 :: Unit
  , case3 :: Unit
  )
  ( case1 :: M1
  , case2 :: M2
  , case3 :: M3
  )

type State = VariantState
  ( case1 :: S1
  , case2 :: S2
  , case3 :: S3
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
testUi = uiVariant
  { case1: ui1
  , case2: ui2
  , case3: ui3
  }
  { view: \_ -> HTML
  , initCase: Proxy :: _ "case1"
  }

spec :: Spec Unit
spec =
  describe "MVC.Variant.UI" do
    it "should compile" do
      void $ pure testUi
