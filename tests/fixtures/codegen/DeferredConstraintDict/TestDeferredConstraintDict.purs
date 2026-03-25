module TestDeferredConstraintDict where

import Prelude
import WriterTrans (WriterT(..), runWriterT)
import WriterClass (class MonadTell, tell)

-- Bug 5 (hyrule): tell(monadTellWriterT) missing sub-dicts.
-- tell, monadTellWriterT, and pending are in separate modules,
-- creating ModuleAccessor patterns in JS.

newtype SpecT m a = SpecT (WriterT (Array String) m a)

-- pending has forall m. Monad m =>
-- tell needs WriterClass.monadTellWriterT(monoidArray)(dictMonad)
-- Bug: codegen may emit tell(monadTellWriterT) without sub-dicts
pending :: forall m. Monad m => String -> SpecT m Unit
pending name = SpecT (tell [name])

data Identity a = Identity a

runIdentity :: forall a. Identity a -> a
runIdentity (Identity a) = a

instance functorIdentity :: Functor Identity where
  map f (Identity a) = Identity (f a)

instance applyIdentity :: Apply Identity where
  apply (Identity f) (Identity a) = Identity (f a)

instance applicativeIdentity :: Applicative Identity where
  pure a = Identity a

instance bindIdentity :: Bind Identity where
  bind (Identity a) f = f a

instance monadIdentity :: Monad Identity

test :: Array String
test = let SpecT w = pending "hello" in let Identity r = runWriterT w in r.log
-- TEST: ["hello"]
