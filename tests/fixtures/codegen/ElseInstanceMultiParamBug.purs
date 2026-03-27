-- | MRE for routing-duplex gsep bug:
-- | Multiple else-instances of a multi-param class share the same head type constructor.
-- | When calling the class method with concrete args that select the last instance
-- | (which has a sub-constraint), the wrong instance or an un-applied constrained
-- | instance is emitted.
-- |
-- | Expected: op(opWW(subInstWW))(w1)(w2) where subInstWW is the concrete sub-dict
-- | Bug:      op(opStringW)(w1)(w2) -- wrong instance, missing sub-dict application
-- TEST: "product"
module ElseInstanceMultiParamBug where

-- Simple wrapper type (like RouteDuplex a a)
newtype W a = W a

-- Sub-class (like GRouteDuplexCtr)
class Sub a b | a -> b where
  sub :: W a -> W b

instance subString :: Sub String String where
  sub x = x

else instance subAll :: Sub a a where
  sub x = x

-- Multi-param class with else-instance chain (like GSep a b c | a b -> c)
class Op a b c | a b -> c where
  op :: a -> b -> c

-- Op String (W a) String: first arg is String (like gsepStringRoute)
instance opStringW :: Sub a b => Op String (W a) String where
  op _ _ = "stringW"

-- Op (W a) String String: first arg is W (like gsepRouteString)
else instance opWString :: Sub a b => Op (W a) String String where
  op _ _ = "wString"

-- Op (W a) (W b) String: first arg is W (like gsepProduct) -- the one we want
else instance opWW :: Sub a b => Op (W a) (W b) String where
  op _ _ = "product"

-- Call that should pick opWW
-- Both args are W, so it should use opWW(subAll)
test :: String
test = op (W "hello") (W "world")
