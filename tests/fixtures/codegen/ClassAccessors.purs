module ClassAccessors where

data Box a = Box a

class MyApply f where
  myApply :: forall a b. f (a -> b) -> f a -> f b

class MyApply f <= MyApplicative f where
  myPure :: forall a. a -> f a

instance myApplyBox :: MyApply Box where
  myApply (Box f) (Box a) = Box (f a)

instance myApplicativeBox :: MyApplicative Box where
  myPure a = Box a

-- Constrained function using superclass method
liftA :: forall f a b. MyApplicative f => (a -> b) -> f a -> f b
liftA f a = myApply (myPure f) a

unbox :: forall a. Box a -> a
unbox (Box a) = a

test = unbox (liftA (\x -> x) (Box 42))

-- TEST: 42
