module RecordOps where

type Person = { name :: String, age :: Int }

mkPerson :: String -> Int -> Person
mkPerson n a = { name: n, age: a }

getName :: Person -> String
getName p = p.name

getAge :: Person -> Int
getAge p = p.age

updateAge :: Person -> Int -> Person
updateAge p newAge = p { age = newAge }

emptyRecord :: {}
emptyRecord = {}

nestedRecord :: { inner :: { x :: Int } }
nestedRecord = { inner: { x: 42 } }

accessNested :: { inner :: { x :: Int } } -> Int
accessNested r = r.inner.x
