module Test.Data.ArgsRotaterSpec where

import Prelude

import Data.ArgsRotater (rotate, (<<^), (<^))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: Spec Unit
spec = do
  describe "rotate args" do
    it "args 2" do
      rotate f2 "2" 1 `shouldEqual` "12"
    it "args 3" do
      rotate f3 "3" 1 2 `shouldEqual` "123"
    it "args 4" do
      rotate f4 "4" 1 2 3 `shouldEqual` "1234"
    it "args 5" do
      rotate f5 "5" 1 2 3 4 `shouldEqual` "12345"
    it "args 6" do
      rotate f6 "6" 1 2 3 4 5 `shouldEqual` "123456"
    it "args 7" do
      rotate f7 "7" 1 2 3 4 5 6 `shouldEqual` "1234567"
    it "args 8" do
      rotate f8 "8" 1 2 3 4 5 6 7 `shouldEqual` "12345678"
    it "args 9" do
      rotate f9 "9" 1 2 3 4 5 6 7 8 `shouldEqual` "123456789"

  describe "<^" do
    it "args 2" do
      let f = f2 <^ "2"
      f 1 `shouldEqual` "12"
    it "args 3" do
      let f = f3 <^ "3"
      f 1 2 `shouldEqual` "123"
    it "args 4" do
      let f = f4 <^ "4"
      f 1 2 3 `shouldEqual` "1234"
    it "args 5" do
      let f = f5 <^ "5"
      f 1 2 3 4 `shouldEqual` "12345"
    it "args 6" do
      let f = f6 <^ "6"
      f 1 2 3 4 5 `shouldEqual` "123456"
    it "args 7" do
      let f = f7 <^ "7"
      f 1 2 3 4 5 6 `shouldEqual` "1234567"
    it "args 8" do
      let f = f8 <^ "8"
      f 1 2 3 4 5 6 7 `shouldEqual` "12345678"
    it "args 9" do
      let f = f9 <^ "9"
      f 1 2 3 4 5 6 7 8 `shouldEqual` "123456789"
    it "args 9 (repeat)" do
      let f = f9 <<^ "9" <<^ 8 <<^ 7 <<^ 6 <<^ 5 <<^ 4 <<^ 3 <<^ 2
      f 1 `shouldEqual` "123456789"

f2 :: Int -> String -> String
f2 a b = show a <> b
f3 :: Int -> Int -> String -> String
f3 a b c = show a <> show b <> c
f4 :: Int -> Int -> Int -> String -> String
f4 a b c d = show a <> show b <> show c <> d
f5 :: Int -> Int -> Int -> Int -> String -> String
f5 a b c d e = show a <> show b <> show c <> show d <> e
f6 :: Int -> Int -> Int -> Int -> Int -> String -> String
f6 a b c d e f = show a <> show b <> show c <> show d <> show e <> f
f7 :: Int -> Int -> Int -> Int -> Int -> Int -> String -> String
f7 a b c d e f g = show a <> show b <> show c <> show d <> show e <> show f <> g
f8 :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> String -> String
f8 a b c d e f g h = show a <> show b <> show c <> show d <> show e <> show f <> show g <> h
f9 :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> String -> String
f9 a b c d e f g h i = show a <> show b <> show c <> show d <> show e <> show f <> show g <> show h <> i