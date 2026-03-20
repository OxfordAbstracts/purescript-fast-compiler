module RecordWildcards where

-- Record construction
mkPoint :: Int -> Int -> { x :: Int, y :: Int }
mkPoint x y = { x, y }

-- Record access
getX :: { x :: Int, y :: Int } -> Int
getX p = p.x

-- Record update
setX :: Int -> { x :: Int, y :: Int } -> { x :: Int, y :: Int }
setX newX p = p { x = newX }

-- Nested records
type Inner = { val :: Int }
type Outer = { inner :: Inner, label :: String }

mkOuter :: Int -> String -> Outer
mkOuter v l = { inner: { val: v }, label: l }

getInnerVal :: Outer -> Int
getInnerVal o = o.inner.val
