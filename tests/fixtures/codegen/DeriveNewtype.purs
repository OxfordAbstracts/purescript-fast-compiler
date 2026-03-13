module DeriveNewtype where

import Data.Newtype (class Newtype)

newtype Name = Name String

derive instance newtypeName :: Newtype Name _

newtype Wrapper a = Wrapper a

derive instance newtypeWrapper :: Newtype (Wrapper a) _
