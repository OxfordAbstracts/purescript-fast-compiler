module NewtypeErasure where

newtype Name = Name String

newtype Wrapper a = Wrapper a

mkName :: String -> Name
mkName s = Name s

unwrapName :: Name -> String
unwrapName (Name s) = s

wrapInt :: Int -> Wrapper Int
wrapInt n = Wrapper n

unwrapWrapper :: forall a. Wrapper a -> a
unwrapWrapper (Wrapper x) = x
