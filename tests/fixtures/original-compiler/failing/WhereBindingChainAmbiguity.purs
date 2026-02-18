-- @shouldFailWith NoInstanceFound
module Main where

data Proxy :: forall k. k -> Type
data Proxy a = Proxy

foreign import data Peano :: Type
foreign import data Z :: Peano
foreign import data S :: Peano -> Peano

class TLShow :: forall k. k -> Constraint
class TLShow i where
  tlShow :: Proxy i -> String

instance TLShow (S (S Z)) where
  tlShow _ = "2"
else instance TLShow Z where
  tlShow _ = "0"
else instance TLShow x => TLShow (S x) where
  tlShow _ = "S"

peano :: Int -> String
peano = go (Proxy :: Proxy Z)
  where
  go :: forall i. TLShow i => Proxy i -> Int -> String
  go p 0 = tlShow p
  go _ n = go (Proxy :: Proxy (S i)) (n - 1)
