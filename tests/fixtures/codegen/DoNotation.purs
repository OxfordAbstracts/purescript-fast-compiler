module DoNotation where

-- Bind class (needed for do notation desugaring)
class Bind m where
  bind :: forall a b. m a -> (a -> m b) -> m b

-- Pure/Applicative for pure in do blocks
class Pure m where
  pure :: forall a. a -> m a

-- discard is needed for do-notation statements without <-
discard :: forall f a. Bind f => f a -> (a -> f a) -> f a
discard = bind

-- Simple do block with bind
doSimple :: forall m a. Bind m => m a -> (a -> m a) -> m a
doSimple x f = do
  a <- x
  f a

-- Do block with multiple binds
doChain :: forall m. Bind m => Pure m => m Int -> m Int
doChain x = do
  a <- x
  b <- pure a
  pure b

-- Do block with discard (statement without <-)
doDiscard :: forall m. Bind m => m Int -> m Int -> m Int
doDiscard x y = do
  x
  y
