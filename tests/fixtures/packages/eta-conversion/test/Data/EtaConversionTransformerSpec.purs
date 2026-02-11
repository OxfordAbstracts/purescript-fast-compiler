module Test.Data.EtaConversionTransformerSpec where

import Prelude

import Data.Eq.Generic (genericEq)
import Data.EtaConversionTransformer ((<<:), (<<|))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: Spec Unit
spec = do
  describe "transform to eta conversion" do
    it "args 1" do
      let
        f = Data <<| f1
        g = \a -> Data $ f1 a
      f "a" `shouldEqual` g "a"
    
    it "args 2" do
      let
        f = Data <<| f2
        g = \a1 a2 -> Data $ f2 a1 a2
      f "a" 1 `shouldEqual` g "a" 1

    it "args 3" do
      let 
        f = Data <<| f3
        g = \a1 a2 a3 -> Data $ f3 a1 a2 a3
      f "a" 1 true `shouldEqual` g "a" 1 true

    it "args 4" do
      let 
        f = Data <<| f4
        g = \a1 a2 a3 a4 -> Data $ f4 a1 a2 a3 a4
      f "a" 1 true "b" `shouldEqual` g "a" 1 true "b"

    it "args 5" do
      let 
        f = Data <<| f5
        g = \a1 a2 a3 a4 a5 -> Data $ f5 a1 a2 a3 a4 a5
      f "a" 1 true "b" 2 `shouldEqual` g "a" 1 true "b" 2

    it "args 6" do
      let 
        f = Data <<| f6
        g = \a1 a2 a3 a4 a5 a6 -> Data $ f6 a1 a2 a3 a4 a5 a6
      f "a" 1 true "b" 2 false `shouldEqual` g "a" 1 true "b" 2 false

    it "args 7" do
      let 
        f = Data <<| f7
        g = \a1 a2 a3 a4 a5 a6 a7 -> Data $ f7 a1 a2 a3 a4 a5 a6 a7
      f "a" 1 true "b" 2 false "c" `shouldEqual` g "a" 1 true "b" 2 false "c"

    it "args 8" do
      let 
        f = Data <<| f8
        g = \a1 a2 a3 a4 a5 a6 a7 a8 -> Data $ f8 a1 a2 a3 a4 a5 a6 a7 a8
      f "a" 1 true "b" 2 false "c" 3 `shouldEqual` g "a" 1 true "b" 2 false "c" 3

    it "args 9" do
      let 
        f = Data <<| f9
        g = \a1 a2 a3 a4 a5 a6 a7 a8 a9 -> Data $ f9 a1 a2 a3 a4 a5 a6 a7 a8 a9
      f "a" 1 true "b" 2 false "c" 3 true `shouldEqual` g "a" 1 true "b" 2 false "c" 3 true

  describe "transform to eta conversion (with input)" do
    it "args 1" do
      let
        f = Data <<: \(Functions r) -> r.f1
        g = \a1 -> Data $ \(Functions r) -> r.f1 a1
        v = runData (f "a") functions
        w = runData (g "a") functions
      v `shouldEqual` w

    it "args 2" do
      let
        f = Data <<: \(Functions r) -> r.f2
        g = \a1 a2 -> Data $ \(Functions r) -> r.f2 a1 a2
        v = runData (f "a" 1) functions
        w = runData (g "a" 1) functions
      v `shouldEqual` w

    it "args 3" do
      let
        f = Data <<: \(Functions r) -> r.f3
        g = \a1 a2 a3 -> Data $ \(Functions r) -> r.f3 a1 a2 a3
        v = runData (f "a" 1 true) functions
        w = runData (g "a" 1 true) functions
      v `shouldEqual` w

    it "args 4" do
      let 
        f = Data <<: \(Functions r) -> r.f4
        g = \a1 a2 a3 a4 -> Data $ \(Functions r) -> r.f4 a1 a2 a3 a4
        v = runData (f "a" 1 true "b") functions
        w = runData (g "a" 1 true "b") functions
      v `shouldEqual` w

    it "args 5" do
      let 
        f = Data <<: \(Functions r) -> r.f5
        g = \a1 a2 a3 a4 a5 -> Data $ \(Functions r) -> r.f5 a1 a2 a3 a4 a5
        v = runData (f "a" 1 true "b" 2) functions
        w = runData (g "a" 1 true "b" 2) functions
      v `shouldEqual` w

    it "args 6" do
      let 
        f = Data <<: \(Functions r) -> r.f6
        g = \a1 a2 a3 a4 a5 a6 -> Data $ \(Functions r) -> r.f6 a1 a2 a3 a4 a5 a6
        v = runData (f "a" 1 true "b" 2 false) functions
        w = runData (g "a" 1 true "b" 2 false) functions
      v `shouldEqual` w

    it "args 7" do
      let 
        f = Data <<: \(Functions r) -> r.f7
        g = \a1 a2 a3 a4 a5 a6 a7 -> Data $ \(Functions r) -> r.f7 a1 a2 a3 a4 a5 a6 a7
        v = runData (f "a" 1 true "b" 2 false "c") functions
        w = runData (g "a" 1 true "b" 2 false "c") functions
      v `shouldEqual` w

    it "args 8" do
      let 
        f = Data <<: \(Functions r) -> r.f8
        g = \a1 a2 a3 a4 a5 a6 a7 a8 -> Data $ \(Functions r) -> r.f8 a1 a2 a3 a4 a5 a6 a7 a8
        v = runData (f "a" 1 true "b" 2 false "c" 3) functions
        w = runData (g "a" 1 true "b" 2 false "c" 3) functions
      v `shouldEqual` w

    it "args 9" do
      let 
        f = Data <<: \(Functions r) -> r.f9
        g = \a1 a2 a3 a4 a5 a6 a7 a8 a9 -> Data $ \(Functions r) -> r.f9 a1 a2 a3 a4 a5 a6 a7 a8 a9
        v = runData (f "a" 1 true "b" 2 false "c" 3 true) functions
        w = runData (g "a" 1 true "b" 2 false "c" 3 true) functions
      v `shouldEqual` w

data Data a = Data a
derive instance genericData :: Generic (Data a) _
instance showData :: Show a => Show (Data a) where
  show = genericShow
instance eqData :: Eq a => Eq (Data a) where
  eq = genericEq

runData :: forall a. Data a -> a
runData (Data a) = a

f1 :: String -> String
f1 a = "[" <> a <> "]"
f2 :: String -> Int -> String
f2 a b = "[" <> a <> show b <> "]"
f3 :: String -> Int -> Boolean -> String
f3 a b c = "[" <> a <> show b <> show c <> "]"
f4 :: String -> Int -> Boolean -> String -> String
f4 a b c d = "[" <> a <> show b <> show c <> d <> "]"
f5 :: String -> Int -> Boolean -> String -> Int -> String
f5 a b c d e = "[" <> a <> show b <> show c <> d <> show e <> "]"
f6 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String
f6 a b c d e f = "[" <> a <> show b <> show c <> d <> show e <> show f <> "]"
f7 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String -> String
f7 a b c d e f g = "[" <> a <> show b <> show c <> d <> show e <> show f <> g <> "]"
f8 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String -> Int -> String
f8 a b c d e f g h = "[" <> a <> show b <> show c <> d <> show e <> show f <> g <> show h <> "]"
f9 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String -> Int -> Boolean -> String
f9 a b c d e f g h i = "[" <> a <> show b <> show c <> d <> show e <> show f <> g <> show h <> show i <> "]"

newtype Functions = Functions {
  f1 :: String -> String,
  f2 :: String -> Int -> String,
  f3 :: String -> Int -> Boolean -> String,
  f4 :: String -> Int -> Boolean -> String -> String,
  f5 :: String -> Int -> Boolean -> String -> Int -> String,
  f6 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String,
  f7 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String -> String,
  f8 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String -> Int -> String,
  f9 :: String -> Int -> Boolean -> String -> Int -> Boolean -> String -> Int -> Boolean -> String
}

functions :: Functions
functions = Functions {
  f1,
  f2,
  f3,
  f4,
  f5,
  f6,
  f7,
  f8,
  f9
}
