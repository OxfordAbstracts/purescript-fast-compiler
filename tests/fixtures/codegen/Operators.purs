module Operators where

add :: Int -> Int -> Int
add a b = a

infixl 6 add as +

useOp :: Int -> Int
useOp x = x + x

applyFn :: forall a b. (a -> b) -> a -> b
applyFn f x = f x

infixr 0 applyFn as $

useDollar :: Int -> Int
useDollar x = useOp $ x

test = useDollar 5

-- TEST: 5
