module ClassAccessors where

class MyApply f where
  myApply :: forall a b. f (a -> b) -> f a -> f b

class MyApply f <= MyApplicative f where
  myPure :: forall a. a -> f a

-- Class method accessor: myPure should become function(dict) { return dict.myPure; }
-- Constrained function: liftA should get a dict parameter
liftA :: forall f a b. MyApplicative f => (a -> b) -> f a -> f b
liftA f a = myApply (myPure f) a
