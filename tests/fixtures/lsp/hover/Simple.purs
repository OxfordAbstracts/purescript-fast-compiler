module Simple where

import Simple.Lib (class Cl, member, times2, addOne, Effect, class MyFunctor, myMap)

-- | The answer to everything
x = 42

fn :: Int -> Int
fn n = times2 n

data Color = Red | Green | Blue

data Box a = MkBox a

boxed = MkBox x

colorFn c = case c of
  Red -> 1
  Green -> 2
  Blue -> 3

class MyShow a where
  myShow :: a -> String

instance MyShow Int where
  myShow _ = "int"

shown = myShow 42

-- | Wraps a value in an identity
newtype Identity a = Identity a

-- | An alias for Int
type Age = Int

-- | A foreign-imported function
foreign import myFfi :: Int -> String

foreign import data MyOpaque :: Type

useAddOne = addOne 1

useMember :: forall a. Cl a => a -> a
useMember a = member a

useEffect :: Effect Int -> Int
useEffect _ = 0

useMap :: forall f a b. MyFunctor f => f a -> f b
useMap = myMap

withLet :: Int
withLet = let y = 10 in y

withWhere :: Int -> Int
withWhere q = r
  where r = q

-- Format: line:col (name) => hover: <expected_type_substring>
-- Use "null" for expected null result
-- Use "doc: <text>" to also check doc-comment content
--
-- Line 5: x = 42
-- 5:0 (x) => hover: Int | doc: The answer to everything
--
-- Line 7: fn :: Int -> Int
-- 7:0 (fn) => hover: Int -> Int
--
-- Line 8: fn n = times2 n
-- 8:7 (times2) => hover: times2
--
-- Line 10: data Color = Red | Green | Blue
-- 10:5 (Color) => hover: Type
--
-- Line 14: boxed = MkBox x
-- 14:0 (boxed) => hover: Box Int
-- 14:14 (x) => hover: Int
--
-- Line 16: colorFn c = case c of
-- 16:0 (colorFn) => hover: Color -> Int
--
-- Line 21: class MyShow a where
-- 21:6 (MyShow) => hover: Type -> Constraint
--
-- Line 22: myShow :: a -> String
-- 22:2 (myShow) => hover: myShow
--
-- Line 27: shown = myShow 42
-- 27:0 (shown) => hover: String
-- 27:8 (myShow) => hover: myShow
--
-- Line 30: newtype Identity a = Identity a
-- 30:8 (Identity) => hover: Type | doc: Wraps a value in an identity
--
-- Line 33: type Age = Int
-- 33:5 (Age) => hover: Type | doc: An alias for Int
--
-- Line 36: foreign import myFfi :: Int -> String
-- 36:15 (myFfi) => hover: Int -> String | doc: A foreign-imported function
--
-- Line 38: foreign import data MyOpaque :: Type
-- 38:20 (MyOpaque) => hover: Type
--
-- Line 40: useAddOne = addOne 1
-- 40:0 (useAddOne) => hover: Int
-- 40:12 (addOne) => hover: addOne
--
-- Line 42: useMember :: forall a. Cl a => a -> a
-- 42:0 (useMember) => hover: useMember
-- 42:23 (Cl) => hover: Type -> Constraint | doc: This is a class
--
-- Line 45: useEffect :: Effect Int -> Int
-- 45:13 (Effect) => hover: Type -> Type | doc: Opaque effect type
--
-- Line 48: useMap :: forall f a b. MyFunctor f => f a -> f b
-- 48:24 (MyFunctor) => hover: (Type -> Type) -> Constraint | doc: Custom functor
--
-- Local variable: function parameter n (definition)
-- 8:3 (n) => hover: Int
-- Local variable: function parameter n (reference)
-- 8:14 (n) => hover: Int
--
-- Local variable: case binder c (definition)
-- 16:8 (c) => hover: Color
--
-- Local variable: let binding y (definition and reference)
-- 52:14 (y) => hover: Int
-- 52:24 (y) => hover: Int
--
-- Local variable: function parameter q and where binding r
-- 55:10 (q) => hover: Int
-- 55:14 (r) => hover: Int
-- 56:8 (r) => hover: Int
--
-- Line 2: import Simple.Lib (class Cl, member, ...)
-- 2:29 (member) => hover: member
-- 2:53 (Effect) => hover: Type -> Type | doc: Opaque effect type
-- 2:45 (addOne) => hover: addOne | doc: Adds one to a number
-- 2:67 (MyFunctor) => hover: (Type -> Type) -> Constraint | doc: Custom functor
--
-- Line 1: empty line
-- 1:0 (ws) => hover: null
