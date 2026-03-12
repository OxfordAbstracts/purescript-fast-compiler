module DeriveNewtype where

class Newtype t a | t -> a where
  wrap :: a -> t
  unwrap :: t -> a

newtype Name = Name String

derive instance newtypeName :: Newtype Name _

newtype Wrapper a = Wrapper a

derive instance newtypeWrapper :: Newtype (Wrapper a) _
