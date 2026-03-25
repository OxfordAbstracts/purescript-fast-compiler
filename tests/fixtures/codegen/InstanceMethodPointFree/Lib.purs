module Lib where

-- Minimal MonadState + StateT + ReaderT stack to reproduce Bug 2 (spec).
-- exitContext is a point-free instance method; enterContext has binders.

class MyMonad m where
  myPure :: forall a. a -> m a
  myBind :: forall a b. m a -> (a -> m b) -> m b

class MyMonad m <= MyState s m where
  myModify :: (s -> s) -> m Unit2

data Unit2 = Unit2

data Identity a = Identity a

instance myMonadIdentity :: MyMonad Identity where
  myPure a = Identity a
  myBind (Identity a) f = f a

newtype StateT s m a = StateT (s -> m { value :: a, state :: s })

instance myMonadStateT :: MyMonad m => MyMonad (StateT s m) where
  myPure a = StateT (\s -> myPure { value: a, state: s })
  myBind (StateT fa) f = StateT (\s ->
    myBind (fa s) (\r -> let StateT fb = f r.value in fb r.state))

instance myStateStateT :: MyMonad m => MyState s (StateT s m) where
  myModify f = StateT (\s -> myPure { value: Unit2, state: f s })

newtype ReaderT r m a = ReaderT (r -> m a)

instance myMonadReaderT :: MyMonad m => MyMonad (ReaderT r m) where
  myPure a = ReaderT (\_ -> myPure a)
  myBind (ReaderT fa) f = ReaderT (\r ->
    myBind (fa r) (\a -> let ReaderT fb = f a in fb r))

class MyMonadP m where
  enterCtx :: String -> m Unit2
  exitCtx :: m Unit2

-- P wraps ReaderT over StateT — like the spec's P monad
newtype P a = P (ReaderT Unit2 (StateT (Array String) Identity) a)

runP :: forall a. P a -> { value :: a, state :: Array String }
runP (P (ReaderT f)) = let StateT g = f Unit2 in let Identity r = g [] in r

liftState :: forall a. StateT (Array String) Identity a -> P a
liftState s = P (ReaderT (\_ -> s))

-- Instance with two methods: enterCtx has binder, exitCtx is point-free.
-- Bug: exitCtx drops the monadIdentity sub-dict on myStateStateT.
instance myMonadPP :: MyMonadP P where
  enterCtx name = liftState (myModify (\arr -> [name]))
  exitCtx = liftState (myModify (\arr -> [] :: Array String))
