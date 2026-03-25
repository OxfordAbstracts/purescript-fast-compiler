module MyBind where

-- A simple Bind-like class
class MyBind f where
  myBind :: forall a b. f a -> (a -> f b) -> f b

-- A simple type with a non-parameterized instance
data MyProxy a = MyProxy

instance myBindProxy :: MyBind MyProxy where
  myBind _ _ = MyProxy
