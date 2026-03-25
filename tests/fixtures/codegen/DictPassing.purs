module DictPassing where

class MyFunctor f where
  myMap :: forall a b. (a -> b) -> f a -> f b

data MyMaybe a = MyNothing | MyJust a

instance myFunctorMyMaybe :: MyFunctor MyMaybe where
  myMap fn (MyJust x) = MyJust (fn x)
  myMap _  _          = MyNothing

-- Constrained function: must take a dict param and thread it to myMap
liftF :: forall f a b. MyFunctor f => (a -> b) -> f a -> f b
liftF f x = myMap f x

unwrap :: forall a. MyMaybe a -> a
unwrap (MyJust a) = a
unwrap MyNothing = unwrap MyNothing

test = unwrap (liftF (\x -> x) (MyJust 42))

-- TEST: 42
