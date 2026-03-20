-- | Utility functions and classes for Simple
module Simple.Lib where

import Prelude

-- | This is a class
class Classy a where
  classMember :: a -> a

data LibType
  = LibCon1
  | LibCon2

type LibAlias = Int

infixr 5 append as <>

libValue :: Int -> Int
libValue n = n * 2

-- | Opaque effect type
foreign import data Effect :: Type -> Type
