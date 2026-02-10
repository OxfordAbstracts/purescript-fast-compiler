module Test.Main where

import Prelude

import Data.ObjectMap (ObjectMap)
import Data.ObjectMap as OM
import Data.ObjectMap.ST as STOM
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

sample :: ObjectMap Int String
sample = OM.empty
  # OM.insert 2 "2"
  # OM.insert 3 "3"
  # OM.insert 1 "1"

main :: Effect Unit
main = launchAff_ $ runSpec [ consoleReporter ] do
  describe "insertion" do
    it "keeps order" do
      OM.empty
        # OM.insert "b" 2
        # OM.insert "c" 3
        # OM.insert "a" 1
        # OM.toArray
        # shouldEqual
            [ "b" /\ 2
            , "c" /\ 3
            , "a" /\ 1
            ]
  describe "bulk insertion with numbers" do
    it "keeps order" do
      OM.fromArray
        [ 2 /\ 2
        , 3 /\ 3
        , 1 /\ 1
        ]
        # OM.toArray
        # shouldEqual
            [ 2 /\ 2
            , 3 /\ 3
            , 1 /\ 1
            ]

  describe "build an object map via ST" do
    it "keeps order" do
      let m' = STOM.run (do
            m <- STOM.new
            _ <- STOM.poke 2 3 m
            _ <- STOM.poke 3 3 m
            _ <- STOM.poke 1 1 m
            pure m
      )
      OM.toArray m' # shouldEqual
            [ 2 /\ 3
            , 3 /\ 3
            , 1 /\ 1
            ]