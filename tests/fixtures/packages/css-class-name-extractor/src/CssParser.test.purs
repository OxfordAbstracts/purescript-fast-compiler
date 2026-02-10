module Test.CssClassNameExtractor.CssParserSpec where

import Prelude

import CssClassNameExtractor.CssParser (AttributeSelector(..), CombinatorType(..), SelectorF(..), attributeOperator, attributeSelector, classSelector, combinatorType, erasureDeclarationBlocks, extractClassNames, firstChar, idSelector, identifier, makeAttributeSelector, quotedString, restChar, selectors, typeSelector, universalSelector)
import Data.Either (Either(..), isLeft)
import Data.Enum (enumFromTo)
import Data.Foldable (traverse_)
import Data.Identity (Identity)
import Data.List (List)
import Data.List as L
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (singleton, charAt)
import Effect.Aff (Aff)
import Parsing (ParseError(..), initialPos, runParser)
import Test.Spec (SpecT, Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

alphabets :: List String
alphabets = map (\c -> singleton c) (enumFromTo 'a' 'z' <> enumFromTo 'A' 'Z')

getFirstChar :: String -> Either ParseError Char
getFirstChar str = case charAt 0 str of
  Just c -> Right c
  Nothing -> Left $ ParseError "Empty string" initialPos

spec :: Spec Unit
spec = do
  describe "firstChar" do
    describe "when [a-zA-Z]" do
      it "should be parsed" do
        traverse_
          ( \c -> do
              runParser c firstChar `shouldEqual` getFirstChar c
          )
          alphabets

    describe "when -" do
      it "should be parsed" do
        runParser "-" firstChar `shouldEqual` Right '-'

    describe "when _" do
      it "should be parsed" do
        runParser "_" firstChar `shouldEqual` Right '_'

    describe "when 1" do
      it "should be errror" do
        isLeft (runParser "1" firstChar) `shouldEqual` true

    describe "when empty string" do
      it "should be errror" do
        isLeft (runParser "" firstChar) `shouldEqual` true

  describe "restChar" do
    describe "when [a-zA-Z]" do
      it "should be parsed" do
        traverse_
          ( \c -> do
              runParser c restChar `shouldEqual` getFirstChar c
          )
          alphabets

    describe "when -" do
      it "should be parsed" do
        runParser "-" restChar `shouldEqual` Right '-'

    describe "when _" do
      it "should be parsed" do
        runParser "_" restChar `shouldEqual` Right '_'

    describe "when 1" do
      it "should be passed" do
        runParser "1" restChar `shouldEqual` Right '1'

  describe "identifier" do
    describe "when \"foooooF-_1\"" do
      it "should be parsed" do
        let input = "foooooF-_1"
        runParser input identifier `shouldEqual` Right input

    describe "1aaaaa" do
      it "should be error" do
        let input = "1aaaaa"
        isLeft (runParser input identifier) `shouldEqual` true

  describe "quotedString" do
    describe "when quoted string" do
      it "should be parsed" do
        runParser "\"fooo\"" quotedString `shouldEqual` Right "fooo"
    describe "when not quoted string" do
      it "should be error" do
        isLeft (runParser "\"fooo" quotedString) `shouldEqual` true

  describe "attributeOperator" do
    traverse_ attributeOperatorPassTest [ "=", "~=", "|=", "^=", "$=", "*=" ]
    describe "when !!" do
      it "should be error" do
        isLeft (runParser "!!" quotedString) `shouldEqual` true
    describe "when sss" do
      it "should be error" do
        isLeft (runParser "sss" quotedString) `shouldEqual` true

  describe "makeAttributeSelector" do
    describe "when op is =" do
      it "should be return AttributeEquals" do
        makeAttributeSelector "=" "foo" "bar" `shouldEqual` AttributeEquals "foo" "bar"
    describe "when op is ~=" do
      it "should be return AttributeContains" do
        makeAttributeSelector "~=" "foo" "bar" `shouldEqual` AttributeContains "foo" "bar"
    describe "when op is ^=" do
      it "should be return AttributeStartWith" do
        makeAttributeSelector "^=" "foo" "bar" `shouldEqual` AttributeStartWith "foo" "bar"
    describe "when op is $=" do
      it "should be return AttributeEndWith" do
        makeAttributeSelector "$=" "foo" "bar" `shouldEqual` AttributeEndWith "foo" "bar"
    describe "other" do
      it "should be fallbacked AttributeEquals" do
        makeAttributeSelector "aa=" "foo" "bar" `shouldEqual` AttributeEquals "foo" "bar"

  describe "combinatorType" do
    describe "when >" do
      it "should be return Child" do
        runParser ">" combinatorType `shouldEqual` Right Child

    describe "when +" do
      it "should be return Adjacent" do
        runParser "+" combinatorType `shouldEqual` Right Adjacent

    describe "when ~" do
      it "should be return Sibling" do
        runParser "~" combinatorType `shouldEqual` Right Sibling

    describe "when x" do
      it "should be return Sibling" do
        runParser "x" combinatorType `shouldEqual` Right Descendant

  describe "classSelector" do
    describe "when .foobar" do
      it "should be parsed" do
        runParser ".foo" classSelector `shouldEqual` Right (Class "foo")

    describe "when #foobar" do
      it "should be error" do
        isLeft (runParser "#foo" classSelector) `shouldEqual` true

    describe "" do
      it "should be error" do
        isLeft (runParser "#foo" classSelector) `shouldEqual` true

  describe "idSelector" do
    describe "when #foobar" do
      it "should be parsed" do
        runParser "#foo" idSelector `shouldEqual` Right (Id "foo")

    describe "when .foobar" do
      it "should be error" do
        isLeft (runParser ".foo" idSelector) `shouldEqual` true

  describe "universalSelector" do
    describe "when *" do
      it "should be parsed" do
        runParser "*" universalSelector `shouldEqual` Right (Universal)

    describe "when .foobar" do
      it "should be error" do
        isLeft (runParser ".foo" universalSelector) `shouldEqual` true

    describe "when empty" do
      it "should be error" do
        isLeft (runParser "" universalSelector) `shouldEqual` true

  describe "typeSelector" do
    describe "when foobar" do
      it "should be parsed" do
        runParser "foobar" typeSelector `shouldEqual` Right (Type "foobar")

    describe "when .foobar" do
      it "should be error" do
        isLeft (runParser ".foo" typeSelector) `shouldEqual` true

    describe "when empty" do
      it "should be error" do
        isLeft (runParser "" typeSelector) `shouldEqual` true

  describe "attributeSelector" do
    describe "when [foo=\"bar\"]" do
      it "should be parsed" do
        runParser "[foo=\"bar\"]" attributeSelector `shouldEqual` Right (Attribute $ makeAttributeSelector "=" "foo" "bar")

    describe "when [foo]" do
      it "should be parsed" do
        runParser "[foo]" attributeSelector `shouldEqual` Right (Attribute $ AttributeExists "foo")

    describe "when .foobar" do
      it "should be error" do
        isLeft (runParser ".foo" attributeSelector) `shouldEqual` true

  describe "selectors" do
    describe "when .foo .bar" do
      it "should be parsed" do
        runParser ".foo .bar" selectors `shouldEqual` Right (L.fromFoldable [ Class "foo", Class "bar" ])

    describe "when .foo .bar { display: flex; }" do
      it "should be parsed" do
        runParser ".foo .bar" selectors `shouldEqual` Right (L.fromFoldable [ Class "foo", Class "bar" ])

  describe "erasureDeclarationBlocks" do
    it "should return to .foo" do
      erasureDeclarationBlocks ".foo { display: flex; }" `shouldEqual` Right (L.singleton ".foo ")

    it "should return to .foo > #bar" do
      erasureDeclarationBlocks ".foo > #bar { display: flex; }" `shouldEqual` Right (L.singleton ".foo > #bar ")

    describe "include newline" do
      it "should return to .foo > #bar and .foo h1" do
        erasureDeclarationBlocks ".foo > #bar { display: flex }\n.foo h1 { display: flex; }" `shouldEqual` Right (L.fromFoldable [ ".foo > #bar ", ".foo h1 " ])

  describe "extractClassNames" do
    it "should return to .foo" do
      extractClassNames ".foo { display: flex; }" `shouldEqual` Right (L.singleton $ Class "foo")
    it "should return to .foo .bar" do
      extractClassNames ".foo .bar { display: flex; }" `shouldEqual` Right (L.fromFoldable [ Class "foo", Class "bar" ])

    it "should return to .foo > .bar" do
      extractClassNames ".foo > .bar { display: flex; }" `shouldEqual` Right (L.fromFoldable [ Class "foo", Class "bar" ])

    it "should return to .foo + .bar" do
      extractClassNames ".foo + .bar { display: flex; }" `shouldEqual` Right (L.fromFoldable [ Class "foo", Class "bar" ])

    it "should return to .foo ~ .bar" do
      extractClassNames ".foo ~ .bar { display: flex; }" `shouldEqual` Right (L.fromFoldable [ Class "foo", Class "bar" ])

    describe "when include pseudo" do
      it "should return to className" do
        extractClassNames ".foo:hover { display: flex; } .bar {}" `shouldEqual` Right (L.fromFoldable [Class "foo", Class "bar" ])

    describe "when include keyframe" do
      it "should return to className" do
        extractClassNames ".foo:hover { display: flex; } .bar {} @keyframes foo {}" `shouldEqual` Right (L.fromFoldable [Class "foo", Class "bar" ])

    it "should return to .foo ~ .bar { display: flex; } .hoge #id {}" do
      extractClassNames ".foo ~ .bar { display: flex; } .hoge #id {}" `shouldEqual` Right (L.fromFoldable [ Class "foo", Class "bar", Class "hoge", Id "id" ])
  where
  attributeOperatorPassTest :: String -> SpecT Aff Unit Identity Unit
  attributeOperatorPassTest pattern = do
    describe ("when" <> pattern) do
      it "should be parsed" do
        runParser pattern attributeOperator `shouldEqual` Right pattern
