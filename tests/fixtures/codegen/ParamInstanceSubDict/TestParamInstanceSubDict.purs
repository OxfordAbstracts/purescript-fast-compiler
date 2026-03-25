module TestParamInstanceSubDict where

-- Bug 1 (argonaut-codecs/routing-duplex): Parameterized instance used in
-- a where clause. The hoisted module-level instance var is correct, but
-- a second usage site emits the raw unapplied instance function.

class MyMonad m where
  myPure :: forall a. a -> m a
  myBind :: forall a b. m a -> (a -> m b) -> m b

data Identity a = Identity a

runIdentity :: forall a. Identity a -> a
runIdentity (Identity a) = a

instance myMonadIdentity :: MyMonad Identity where
  myPure a = Identity a
  myBind (Identity a) f = f a

class MyState s m where
  myState :: forall a. (s -> { value :: a, state :: s }) -> m a

newtype StateT s m a = StateT (s -> m { value :: a, state :: s })

runStateT :: forall s m a. StateT s m a -> s -> m { value :: a, state :: s }
runStateT (StateT f) s = f s

instance myStateStateT :: MyMonad m => MyState s (StateT s m) where
  myState f = StateT (\s -> myPure (f s))

-- Module-level usage (should hoist instance correctly)
getVal :: StateT String Identity String
getVal = myState (\s -> { value: s, state: s })

-- Where-clause usage (bug: may use raw unapplied instance)
transform :: StateT String Identity String
transform = StateT go
  where
  go s = let StateT f = myState (\s' -> { value: s', state: s' }) in f s

test :: String
test = let Identity r = runStateT transform "hello" in r.value
-- TEST: "hello"
