module Test.Formatting.Dodo where

import Prelude

import Color (Color)
import Color (rgb) as Color

import Effect (Effect)
import Effect.Class.Console as Console

import Data.Text.Format.Dodo.Format as F
import Data.Text.Format.Dodo.Printer as FDodo
import Data.Text.Output.Markdown (markdown)

import Dodo (Doc, PrintOptions, print, twoSpaces, plainText) as Dodo
import Dodo (text, indent, lines, words) as D
import Dodo.Ansi as Ansi

import Test.Spec (Spec, describe, it, it)
import Test.Spec.Assertions (shouldEqual)


testA :: Dodo.Doc F.Directive
testA =
  D.words
    [ D.text "pre"
    , F.bold $ D.words
      [ D.text "bold"
      , F.underline $ D.text "bold&under"
      , D.text "bold2"
      ]
    , D.text "post"
    ]


testB :: Dodo.Doc F.Directive
testB =
  F.fgc red $ F.thru $ D.words
    [ D.text "This is"
    , F.fgc blue $ F.bold $ D.text "blue and bold"
    , F._null $ F.underline $ D.text "underlined text."
    , D.text "The end."
    ]


yellow = Color.rgb 0 255 255 :: Color
red = Color.rgb 255 0 0 :: Color
blue = Color.rgb 0 0 255 :: Color


testC :: Dodo.Doc F.Directive
testC =
  D.lines
    [ D.text "Line with no style"
    , F.bgc yellow $ F.bold $ D.lines
            [ F.thru $ D.text "strikethrough"
            , D.indent $ F.fgc red
              $ D.lines
                [ D.text "Red"
                , F._null $ D.text "Lines"
                , D.text "And bold"
                ]
            ]
    ]


ghostOptions :: Dodo.PrintOptions
ghostOptions = { indentUnit : "", indentWidth : 0, pageWidth : 120, ribbonRatio : 1.0 }



qTest :: Dodo.Doc F.Directive -> String
-- qTest = Dodo.print Dodo.plainText ghostOptions
qTest = Dodo.print Dodo.plainText ghostOptions <<< Dodo.print (FDodo.printer markdown) Dodo.twoSpaces


spec :: Spec Unit
spec = do

  describe "Formatting works properly for Dodo" $ do

    it "0: simple text" $ do
      qTest (D.text "pre") `shouldEqual` "pre"

    it "1: only formatted text" $ do
      qTest (F.bold $ D.text "bold") `shouldEqual` "**bold**"
      qTest (F.underline $ D.text "under") `shouldEqual` "__under__"

    it "2: formatted text after usual text" $ do
      qTest (D.text "smth" <> (F.bold $ D.text "bold")) `shouldEqual` "smth**bold**"
      qTest (D.text "smth" <> (F.underline $ D.text "under")) `shouldEqual` "smth__under__"

    it "3: formatted text before usual text" $ do
      qTest ((F.bold $ D.text "bold") <> D.text "smth") `shouldEqual` "**bold**smth"
      qTest ((F.underline $ D.text "under") <> D.text "smth") `shouldEqual` "__under__smth"

    it "4: formatted inside formatted" $ do
      qTest (F.bold $ F.underline $ D.text "bold&under") `shouldEqual` "**__bold&under__**"
      qTest (F.underline $ F.bold $ D.text "bold&under") `shouldEqual` "__**bold&under**__"

    it "5: formatted inside formatted, extended" $ do
      qTest (F.bold      (D.text "bold-start"  <> (F.underline $ D.text "bold&under") <> D.text "bold-end") ) `shouldEqual` "**bold-start__bold&under__bold-end**"
      qTest (F.underline (D.text "under-start" <> (F.bold      $ D.text "bold&under") <> D.text "under-end")) `shouldEqual` "__under-start**bold&under**under-end__"

    it "4: complex test A" $ do
      qTest testA `shouldEqual` "pre **bold __bold&under__ bold2** post"

    it "5: complex test B" $ do
      qTest testB `shouldEqual` """<span style="color:#ff0000">~~This is <span style="color:#0000ff">**blue and bold**</span> __underlined text.__ The end.~~</span>"""

    it "6: complex test C" $ do
      qTest testC `shouldEqual` """Line with no style
<span style="background-color:#00ffff">**~~strikethrough~~
<span style="color:#ff0000">  Red
  Lines
  And bold</span>**</span>"""