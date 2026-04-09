-- @shouldFailWith PropertyIsMissing
module FundepMissingFieldDeeper where

import Prelude
import Control.Monad.State.Class as St
import Control.Monad.State.Trans (StateT)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.Writer.Trans (WriterT)

type TestState = { a :: Int, b :: Boolean }

test :: forall m. WriterT Unit (ReaderT Unit (ReaderT Unit (StateT TestState m))) Unit
test = do 
  { a, b, notAPropOnState } <- St.modify \st -> st
    { a = 1
    , b = true
    }
  pure unit