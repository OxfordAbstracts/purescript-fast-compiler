module SuperclassAccessorTest where

class MySemigroup a where
  myAppend :: a -> a -> a

class MySemigroup a <= MyMonoid a where
  myMempty :: a

instance mySemigroupString :: MySemigroup String where
  myAppend a b = a

instance myMonoidString :: MyMonoid String where
  myMempty = ""

-- Uses the Monoid dict and accesses its Semigroup superclass
useMonoid :: forall a. MyMonoid a => a -> a
useMonoid x = myAppend x x

test = useMonoid "hello"

-- TEST: "hello"
