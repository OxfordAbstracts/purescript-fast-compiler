module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_)
import Webb.Test.Prelude (runSpecs)

main :: Effect Unit
main = do launchAff_ (runSpecs ".*Spec")

