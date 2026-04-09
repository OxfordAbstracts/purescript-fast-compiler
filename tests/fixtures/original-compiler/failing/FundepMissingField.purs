-- @shouldFailWith PropertyIsMissing
module FundepMissingField where

import Prelude

-- Simulates H.modify :: forall s m. MonadState s m => (s -> s) -> m s
-- The return type `m s` means the result has type `s`, determined by fundep.
-- Destructuring the result with a field that doesn't exist on State should
-- be caught as a type error.

class MonadState s m | m -> s where
  modify :: (s -> s) -> m s

type State = { count :: Int, name :: String }

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
  modify f = MyM (f { count: 0, name: "" })

test :: MyM Unit
test = do
  -- notAProperty does not exist on State — this should fail
  { count, notAProperty } <- modify \st -> st { count = st.count + 1 }
  pure unit
