module Test.CssClassNameExtractor.Data.OutputSpec where

import Prelude

import CssClassNameExtractor.CssParser (SelectorF(..))
import CssClassNameExtractor.Data.Output (FileBody(..), Namespace(..), Output(..), getDistPath, makeCssFile, makeJsFile, makePursFile, renderOutput)
import Data.List as L
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: Spec Unit
spec = do
  describe "renderOutput" do
    describe "when css file" do
      it "should be body" do
        let body = FileBody ".foo { display: flex; }"
        renderOutput (CssFile { body, namespace: Namespace "Unused", name: "unused" }) `shouldEqual` body

    describe "when js file" do
      it "should be ffi implementation" do
        let
          body = FileBody
            """
import s from "./styles.module.css"
export const _styles = (name) => s[name]
"""
        renderOutput (makeJsFile "./styles.module.css") `shouldEqual` body

      describe "when nested directory" do
        it "should be ffi implementation" do
          let
            body = FileBody
              """
import s from "./styles.module.css"
export const _styles = (name) => s[name]
"""
          renderOutput (makeJsFile "./foo/styles.module.css") `shouldEqual` body

    describe "when PursFile" do
      describe "single class" do
        it "should be include helper functions" do
          let
            body = FileBody
              """module Foo (foo) where
foreign import _styles :: String -> String
foo :: String
foo = _styles "foo""""
          renderOutput (makePursFile (Namespace "Foo") "./src/components/styles.module.css" (L.fromFoldable [ Class "foo" ])) `shouldEqual` body
      describe "multi class" do
        it "should be include helper functions" do
          let
            body = FileBody
              """module Foo (foo,bar) where
foreign import _styles :: String -> String
foo :: String
foo = _styles "foo"
bar :: String
bar = _styles "bar""""
          renderOutput (makePursFile (Namespace "Foo") "./src/components/styles.module.css" (L.fromFoldable [ Class "foo", Class "bar" ])) `shouldEqual` body

  describe "getDistPath" do
    describe "when css files" do
      it "should be output/Components.Foo/styles.module.css" do
        let result = getDistPath (makeCssFile (Namespace "Components.Foo") (FileBody ".foo { display: flex; }") "styles.module.css")
        result `shouldEqual` "output/Components.Foo/styles.module.css"
