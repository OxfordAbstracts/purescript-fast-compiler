module WhereBindings where

-- Simple where clause
useWhere :: Int -> Int
useWhere x = y
  where
    y = x

-- Where with function binding
applyTwice :: forall a. (a -> a) -> a -> a
applyTwice f x = f (f x)

withHelper :: Int -> Int
withHelper x = helper x
  where
    helper n = n

-- Nested where
compute :: Int -> Int -> Int
compute x y = inner x
  where
    offset = y
    inner n = offset
