module Test.Main where

import Prelude

import Effect (Effect)
import Webb.Monad.Prelude (launch_)
import Webb.Test.Prelude (runSpecs)

main :: Effect Unit
main = do launch_ $ runSpecs ".*Spec"

