module Test.Record.Optional.Fields where

import Prelude

import Data.Maybe (Maybe(..))
import Record.Optional.Fields (optional)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

type T =
  { foo :: Int
  , bar :: String
  , baz ::
      { quz :: Number
      , qux :: Array Boolean
      }
  }

type S = { foo :: Int, bar :: Maybe String }

spec :: Spec Unit
spec = describe "Optional.Fields" do
  describe "optional" do
    it "should map `a` to `Maybe a`" do
      optional @Int
        42 `shouldEqual` (Just 42)

    it "should map `Maybe a` to `Maybe a`." do
      optional @Boolean (Just true) `shouldEqual` Just true
      optional @String (Nothing :: _ String) `shouldEqual` Nothing

    it "should map overly `Just`ed value with flattening" do
      optional @Int (Just (Just (Just 1))) `shouldEqual` Just 1
      optional @Int (Just (Just (Nothing @Int))) `shouldEqual` Nothing

    it "should map an empty record" do
      optional @T {} `shouldEqual` Just
        { foo: Nothing
        , bar: Nothing
        , baz: Nothing
        }

    it "should map records with some of the fields absent" do
      optional @T { foo: 42 } `shouldEqual` Just
        { foo: Just 42
        , bar: Nothing
        , baz: Nothing
        }

    it "should map records with some of the fields wrapped in Just" do
      optional @T { foo: 42, bar: Just "abc" } `shouldEqual` Just
        { foo: Just 42
        , bar: Just "abc"
        , baz: Nothing
        }

    it "should map records with some of the fields marked as Nothing explicitly" do
      optional @T { foo: 42, bar: Nothing @String } `shouldEqual` Just
        { foo: Just 42
        , bar: Nothing
        , baz: Nothing
        }

    it "should map records with nested record fields (empty)" do
      optional @T { foo: 42, baz: {} } `shouldEqual` Just
        { foo: Just 42
        , bar: Nothing
        , baz: Just
            { quz: Nothing
            , qux: Nothing
            }
        }

    it "should map records with nested record fields (with absent fields)" do
      optional @T { foo: 42, baz: { quz: 2.718 } } `shouldEqual` Just
        { foo: Just 42
        , bar: Nothing
        , baz: Just
            { quz: Just 2.718
            , qux: Nothing
            }
        }

    it "should map records with fields mixture of above cases" do
      optional @T { foo: 42, baz: Just { quz: 2.718, qux: Just [ true, false, false ] } } `shouldEqual` Just
        { foo: Just 42
        , bar: Nothing
        , baz: Just
            { quz: Just 2.718
            , qux: Just [ true, false, false ]
            }
        }

    it "should map records with originally Maybe field" do
      optional @S { bar: Nothing @String } `shouldEqual` Just
        { foo: Nothing
        , bar: Nothing
        }

    it "should map records with originally Maybe field (no duplicated Maybe wrapping)" do
      optional @S { bar: Just "abc" } `shouldEqual` Just
        { foo: Nothing
        , bar: Just "abc"
        }