module Test.MVC.UtilSpec where

import Prelude

import Type.Proxy (Proxy(..))
import MVC.Util (mapProp) as ME
import Test.Spec (Spec, describe, it)

testMapProp :: { field1 :: Int, field2 :: Int, field3 :: Int }
testMapProp = ME.mapProp (Proxy :: _ "a")
  { field1: { a: 1 }
  , field2: { a: 2 }
  , field3: { a: 3 }
  }

spec :: Spec Unit
spec =
  describe "MVC.Util"
    do
      describe "mapProp" do
        it "should compile" do
          void $ pure testMapProp

