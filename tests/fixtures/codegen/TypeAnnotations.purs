module TypeAnnotations where

-- Primitive types
anInt :: Int
anInt = 1

aNumber :: Number
aNumber = 1.0

aString :: String
aString = "hello"

aBool :: Boolean
aBool = true

-- Function types
id :: forall a. a -> a
id x = x

const :: forall a b. a -> b -> a
const x _ = x

-- Record types
type Person = { name :: String, age :: Int }

mkPerson :: String -> Int -> Person
mkPerson n a = { name: n, age: a }

getName :: Person -> String
getName p = p.name

-- Array types
nums :: Array Int
nums = [1, 2, 3]

strs :: Array String
strs = ["a", "b"]

-- Nested types
nested :: Array (Array Int)
nested = [[1], [2, 3]]

test = getName (mkPerson "hi" anInt)

-- TEST: "hi"
