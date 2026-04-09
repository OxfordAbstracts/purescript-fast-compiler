-- @shouldFailWith PropertyIsMissing
module FundepMissingFieldMiddleChain where

import Prelude
import Control.Monad.State.Class as St
import Control.Monad.State.Trans (StateT)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.Writer.Trans (WriterT)

type TestState = { a :: Int, b :: Boolean }

test :: forall m. WriterT Unit (ReaderT Unit (ReaderT Unit (StateT TestState (ReaderT Unit m)))) Unit
test = do 
  { a, b, notAPropOnState } <- parent 1
  pure unit
  where 
  parent n = action n
  action n = St.modify \st -> st
    { a = n
    , b = true
    }
