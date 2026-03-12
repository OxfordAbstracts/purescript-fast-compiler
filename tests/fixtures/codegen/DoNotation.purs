module DoNotation where

class MyBind m where
  myBind :: forall a b. m a -> (a -> m b) -> m b

class MyPure m where
  myPure :: forall a. a -> m a

-- Simple do block simulation via bind chains
bindChain :: forall m a. MyBind m => MyPure m => m a -> m a
bindChain x = myBind x (\a -> myPure a)
