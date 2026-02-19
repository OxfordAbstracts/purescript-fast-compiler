module RunNewtype where

newtype Name = Name String

mkName :: String -> Name
mkName s = Name s

unwrapName :: Name -> String
unwrapName (Name s) = s
