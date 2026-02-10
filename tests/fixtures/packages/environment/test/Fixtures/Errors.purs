module Test.Fixtures.Errors where

import Prelude

import Data.Either (Either, blush)
import Data.Maybe (Maybe)
import Effect.Aff (message)
import Effect.Exception (Error)

read ∷ ∀ a. Either Error a → Maybe String
read = map message <<< blush
