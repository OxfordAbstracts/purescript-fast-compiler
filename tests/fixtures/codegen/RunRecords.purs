module RunRecords where

type Person = { name :: String, age :: Int }

mkPerson :: String -> Int -> Person
mkPerson n a = { name: n, age: a }

getName :: Person -> String
getName p = p.name

getAge :: Person -> Int
getAge p = p.age
