module TestSuperclassWrapper where

-- Minimal reproduction: superclass accessor in parameterized instance
-- must apply the correct wrapper function, not just return the raw parent dict

class MySemigroup a where
  myAppend :: a -> a -> a

class MySemigroup a <= MyMonoid a where
  myMempty :: a

instance mySemigroupString :: MySemigroup String where
  myAppend a b = a

instance myMonoidString :: MyMonoid String where
  myMempty = ""

-- Parameterized instance: MySemigroup/MyMonoid for functions
instance mySemigroupFn :: MySemigroup b => MySemigroup (a -> b) where
  myAppend f g = \x -> myAppend (f x) (g x)

instance myMonoidFn :: MyMonoid b => MyMonoid (a -> b) where
  myMempty = \_ -> myMempty

-- POLYMORPHIC function that accesses superclass through dict at runtime
-- This is the pattern that triggers the bug: dictMyMonoid.MySemigroup0()
-- must return mySemigroupFn(parent.MySemigroup0()), not the raw parent Semigroup dict
useMonoid :: forall a. MyMonoid a => a -> a -> a
useMonoid x y = myAppend x (myAppend y myMempty)

-- Call with a function type to trigger the parameterized instance path
applyFnMonoid :: (Int -> String) -> (Int -> String) -> Int -> String
applyFnMonoid f g n = useMonoid f g n

-- TEST: "hello"
test = applyFnMonoid (\_ -> "hello") (\_ -> "world") 0
