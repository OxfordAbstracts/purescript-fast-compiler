module Test.Formatting.Utils where

import Prelude

import Data.Tuple.Nested ((/\), type (/\))

import Test.Spec (Spec)
import Test.Spec.Assertions (shouldEqual)

import Test.Utils (helper) as U


helper :: forall a. { title :: Int -> a /\ String -> String, render :: a -> String } -> Array (a /\ String) -> Spec Unit
helper { title, render } =
    U.helper
        { title : \idx pair -> "works for sample " <> title idx pair
        , spec : \(tag /\ expected) ->
            render tag `shouldEqual` expected
        }