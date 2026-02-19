module TestOperator where

class MyAppend a where
  myAppend :: a -> a -> a

infixr 5 myAppend as <>

instance myAppendInt :: MyAppend Int where
  myAppend x _ = x

joined :: forall a. MyAppend a => a -> a -> a
joined x y = x <> y
