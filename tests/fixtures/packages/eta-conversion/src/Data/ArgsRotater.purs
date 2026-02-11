module Data.ArgsRotater where

class ArgsRotater input tail output | input -> output, output -> input where
  rotate :: input -> tail -> output

instance args9 :: ArgsRotater
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> ret)
  a9
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> ret)
  where
  rotate f a9 a1 a2 a3 a4 a5 a6 a7 a8 = f a1 a2 a3 a4 a5 a6 a7 a8 a9
else
instance args8 :: ArgsRotater
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> ret)
  a8
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> ret)
  where
  rotate f a8 a1 a2 a3 a4 a5 a6 a7 = f a1 a2 a3 a4 a5 a6 a7 a8
else
instance args7 :: ArgsRotater
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> ret)
  a7
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> ret)
  where
  rotate f a7 a1 a2 a3 a4 a5 a6 = f a1 a2 a3 a4 a5 a6 a7
else
instance args6 :: ArgsRotater
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> ret)
  a6
  (a1 -> a2 -> a3 -> a4 -> a5 -> ret)
  where
  rotate f a6 a1 a2 a3 a4 a5 = f a1 a2 a3 a4 a5 a6
else
instance args5 :: ArgsRotater
  (a1 -> a2 -> a3 -> a4 -> a5 -> ret)
  a5
  (a1 -> a2 -> a3 -> a4 -> ret)
  where
  rotate f a5 a1 a2 a3 a4 = f a1 a2 a3 a4 a5
else
instance args4 :: ArgsRotater
  (a1 -> a2 -> a3 -> a4 -> ret)
  a4
  (a1 -> a2 -> a3 -> ret)
  where
  rotate f a4 a1 a2 a3 = f a1 a2 a3 a4
else
instance args3 :: ArgsRotater
  (a1 -> a2 -> a3 -> ret)
  a3
  (a1 -> a2 -> ret)
  where
  rotate f a3 a1 a2 = f a1 a2 a3
else
instance args2 :: ArgsRotater
  (a1 -> a2 -> ret)
  a2
  (a1 -> ret)
  where
  rotate f a2 a1 = f a1 a2

infixr 9 rotate as <^
infixl 9 rotate as <<^
