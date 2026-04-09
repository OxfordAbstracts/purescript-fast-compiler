-- @shouldFailWith PropertyIsMissing
module FundepMissingField where

import Prelude

class MonadState s m | m -> s where
  modify :: (s -> s) -> m s

type State =
  { count :: Int
  , name :: String
  , loading :: Boolean
  }

data MyM a = MyM a

instance Functor MyM where
  map f (MyM a) = MyM (f a)

instance Apply MyM where
  apply (MyM f) (MyM a) = MyM (f a)

instance Applicative MyM where
  pure a = MyM a

instance Bind MyM where
  bind (MyM a) f = f a

instance Monad MyM

instance MonadState State MyM where
  modify f = MyM (f { count: 0, name: "", loading: false })

component :: MyM Unit
component = test
  where
  test :: MyM Unit
  test = do
    result <- runSolver 1 "hello"
    pure unit
    where
    runSolver stage_id params = do
      { count, notAProperty } <- modify \st -> st
        { loading = true
        , count = st.count + 1
        }
      pure unit
