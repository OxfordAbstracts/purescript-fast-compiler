module Test.MVC.Variant.InitSpec where

import Prelude

import MVC.Variant.Init (initVariant)
import MVC.Variant.Types (VariantState)
import Test.MVC.TestTypes (S1(..), S2(..), S3(..))
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

testInitStateVariant :: VariantState (case1 :: S1, case2 :: S2, case3 :: S3)
testInitStateVariant = initVariant
  (Proxy :: _ "case1")
  { case1: S1
  , case2: S2
  , case3: S3
  }

spec :: Spec Unit
spec =
  describe "MVC.Variant.Init" do
    it "should compile" do
      void $ pure testInitStateVariant
