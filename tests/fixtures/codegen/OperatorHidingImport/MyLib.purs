module MyLib where

class MyAppend a where
  myAppend :: a -> a -> a

infixr 5 myAppend as <>

unused :: Int
unused = 0
