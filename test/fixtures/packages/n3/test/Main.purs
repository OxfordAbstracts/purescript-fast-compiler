module Test.Main where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (launchAff_, try)
import Effect.Class (liftEffect)
import Effect.Console (errorShow, logShow)
import N3 (Format(..), parse)

main :: Effect Unit
main = launchAff_ do
  quadsOrError <- try $ parse "http://example.org/" Turtle "<#a> <#p> ."
  case quadsOrError of 
    Left error -> liftEffect $ errorShow error
    Right quads -> liftEffect $ logShow quads
