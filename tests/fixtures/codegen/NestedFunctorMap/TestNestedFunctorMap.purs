module TestNestedFunctorMap where

import Prelude

data Pair a b = Pair a b

instance functorPair :: Functor (Pair a) where
  map f (Pair a b) = Pair a (f b)

data Box a = Box a

instance functorBox :: Functor Box where
  map f (Box a) = Box (f a)

-- Simulate WriterT: newtype wrapping m (Pair r w)
newtype MyT w m a = MyT (m (Pair a w))

runMyT :: forall w m a. MyT w m a -> m (Pair a w)
runMyT (MyT ma) = ma

mapMyT :: forall w1 w2 m1 m2 a b. (m1 (Pair a w1) -> m2 (Pair b w2)) -> MyT w1 m1 a -> MyT w2 m2 b
mapMyT f (MyT ma) = MyT (f ma)

-- Simulate SpecT: another newtype layer
newtype SpecT a m r = SpecT (MyT (Array a) m r)

-- This pattern matches mapSpecTree: over SpecT $ mapMyT $ g >>> map (map $ map f)
-- The Tuple/Pair type is NOT explicit - it comes from mapMyT's type signature.
-- Bug: middle map uses dictFunctor instead of functorPair.
mapSpecTree :: forall m a r. Functor m => (m (Pair r (Array a)) -> m (Pair r (Array a))) -> (a -> a) -> SpecT a m r -> SpecT a m r
mapSpecTree g f (SpecT (MyT inner)) = SpecT (MyT (g (map (map (map f)) inner)))

showPair :: Pair Int (Array Int) -> String
showPair (Pair a bs) = show a <> ":" <> show bs

unbox :: forall a. Box a -> a
unbox (Box a) = a

-- If middle map is wrong, this will fail at runtime
test = showPair (unbox (map (map (map (_ + 10))) (Box (Pair 1 [2, 3]))))
-- TEST: "1:[12,13]"
