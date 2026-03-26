module SuperclassAccessor where

-- Minimal reproduction of the superclass accessor thunk bug.
-- When a function has a MyMonoid constraint and uses myAppend (from MySemigroup),
-- the compiler must generate code that:
-- 1. Takes a MyMonoid dictionary parameter
-- 2. Calls dictMyMonoid.MySemigroup0() to get the MySemigroup dict
-- 3. Uses the semigroup dict to call myAppend
--
-- The bug: our compiler doesn't emit Semigroup0 as a thunk in the dict.

class MySemigroup a where
  myAppend :: a -> a -> a

class MySemigroup a <= MyMonoid a where
  myMempty :: a

instance mySemigroupString :: MySemigroup String where
  myAppend a b = a

instance myMonoidString :: MyMonoid String where
  myMempty = ""

-- This function takes a MyMonoid constraint but uses myAppend (from MySemigroup).
-- The generated JS must access the superclass: dictMyMonoid.MySemigroup0().myAppend
foldish :: forall a. MyMonoid a => a -> a -> a
foldish x y = myAppend (myAppend x y) myMempty

test :: String
test = foldish "hello" "world"
