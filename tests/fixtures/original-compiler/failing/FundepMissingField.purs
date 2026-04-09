-- @shouldFailWith PropertyIsMissing
module FundepMissingField where

import Prelude
import Control.Monad.State.Class as St
import Control.Monad.State.Trans (StateT)

type TestState = { a :: Int, b :: Boolean }

test :: forall m. StateT TestState m Unit
test = do 
  { a, b, notAPropertyOnState } <- St.modify \st -> st
    { a = 1
    , b = true
    }
  pure unit