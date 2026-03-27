-- | Core module: defines the wrapper type and its alias (like Routing.Duplex)
module Core where

-- The underlying type (like RouteDuplex a b)
newtype RD a b = RD (a -> b)

-- Type alias (like RouteDuplex' a = RouteDuplex a a)
type RD' a = RD a a

-- A sub-class (like GRouteDuplexCtr)
class Sub a b | a -> b where
  sub :: RD' a -> RD' b

instance subAll :: Sub a a where
  sub x = x

-- Some concrete values using the alias (like segment, rest)
rdString :: RD' String
rdString = RD (\s -> s)

rdInt :: RD' Int
rdInt = RD (\_ -> 0)
