module TestPointFreeParamInstance where

-- Bug 2 (spec): Point-free definition where the resolved instance dict
-- is stored as DictExpr::Var(instanceName) without applying sub-dicts.
-- Pattern from Options.Applicative.Internal: exitContext = P $ lift $ modify_ $ Array.drop 1
-- The point-free body with polymorphic m means the sub-dict is unresolved.

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
  myModify :: (s -> s) -> m s

newtype StateT s m a = StateT (s -> m { value :: a, state :: s })

runStateT :: forall s m a. StateT s m a -> s -> m { value :: a, state :: s }
runStateT (StateT f) s = f s

instance myStateStateT :: MyMonad m => MyState s (StateT s m) where
  myModify f = StateT (\s -> let s' = f s in myPure { value: s', state: s' })

-- Polymorphic: m is a type variable, not concrete.
-- The MyMonad m constraint must be threaded through to myStateStateT.
mySetState :: forall m. MyMonad m => String -> StateT String m String
mySetState val = myModify (\_ -> val)

-- Concrete call site: m = Identity
test :: String
test = let Identity r = runStateT (mySetState "hello") "world" in r.value
-- TEST: "hello"
