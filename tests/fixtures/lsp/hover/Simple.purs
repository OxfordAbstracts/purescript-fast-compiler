module Simple where

import Simple.Lib (class Cl, member, times2, addOne, Effect, class MyFunctor, myMap)
import Simple.Lib as Lib

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

myRecord = { name: "hello", age: 42 }

getName = myRecord.name

-- Qualified name usage
qualTimes2 = Lib.times2 5
qualAddOne = Lib.addOne 10
qualMember :: forall a. Lib.Cl a => a -> a
qualMember a = Lib.member a

-- Format: line:col (name) => hover: <expected_type_substring>
-- Use "null" for expected null result
-- Use "doc: <text>" to also check doc-comment content
--
-- 6:0 (x) => hover: Int | doc: The answer to everything
-- 8:0 (fn) => hover: Int -> Int
-- 9:7 (times2) => hover: times2
-- 11:5 (Color) => hover: Type
-- 15:0 (boxed) => hover: Box Int
-- 15:14 (x) => hover: Int
-- 17:0 (colorFn) => hover: Color -> Int
-- 22:6 (MyShow) => hover: Type -> Constraint
-- 23:2 (myShow) => hover: myShow
-- 28:0 (shown) => hover: String
-- 28:8 (myShow) => hover: myShow
-- 31:8 (Identity) => hover: Type | doc: Wraps a value in an identity
-- 34:5 (Age) => hover: Type | doc: An alias for Int
-- 37:15 (myFfi) => hover: Int -> String | doc: A foreign-imported function
-- 39:20 (MyOpaque) => hover: Type
-- 41:0 (useAddOne) => hover: Int
-- 41:12 (addOne) => hover: addOne
-- 43:0 (useMember) => hover: useMember
-- 43:23 (Cl) => hover: Type -> Constraint | doc: This is a class
-- 46:13 (Effect) => hover: Type -> Type | doc: Opaque effect type
-- 49:24 (MyFunctor) => hover: (Type -> Type) -> Constraint | doc: Custom functor
--
-- Local variables
-- 9:3 (n) => hover: Int
-- 9:14 (n) => hover: Int
-- 17:8 (c) => hover: Color
-- 53:14 (y) => hover: Int
-- 53:24 (y) => hover: Int
-- 56:10 (q) => hover: Int
-- 56:14 (r) => hover: Int
-- 57:8 (r) => hover: Int
--
-- Import line hover
-- 2:7 (Simple.Lib) => hover: module Simple.Lib | doc: Utility functions and classes for Simple
-- 2:29 (member) => hover: member
-- 2:53 (Effect) => hover: Type -> Type | doc: Opaque effect type
-- 2:45 (addOne) => hover: addOne | doc: Adds one to a number
-- 2:67 (MyFunctor) => hover: (Type -> Type) -> Constraint | doc: Custom functor
--
-- Record literal labels
-- 59:13 (name) => hover: String
-- 59:28 (age) => hover: Int
--
-- Record access
-- 61:19 (name) => hover: String
--
-- Qualified names
-- 64:13 (Lib.times2) => hover: times2
-- 65:13 (Lib.addOne) => hover: addOne | doc: Adds one to a number
-- 67:15 (Lib.member) => hover: member
--
-- Empty line
-- 1:0 (ws) => hover: null
