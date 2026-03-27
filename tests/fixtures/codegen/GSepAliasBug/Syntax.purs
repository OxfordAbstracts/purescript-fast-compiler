-- | Syntax module: defines the multi-param class with else-instance chain
-- | (like Routing.Duplex.Generic.Syntax with class GSep)
module Syntax where

import Core (class Sub, RD, RD', sub, rdString)

-- Multi-param class with FD (like GSep a b c | a b -> c)
class Op a b c | a b -> c where
  op :: a -> b -> c

-- First instance: Op String (RD a a) String (like gsepStringRoute)
instance opStringRD :: Sub a b => Op String (RD a a) String where
  op _ _ = "stringRD"

-- Second instance: Op (RD a a) String String (like gsepRouteString)
else instance opRDString :: Sub a b => Op (RD a a) String String where
  op _ _ = "rdString"

-- Third instance: Op (RD a a) (RD b b) String (like gsepProduct)
else instance opRDRD :: Sub b c => Op (RD a a) (RD b b) String where
  op _ _ = "rdrd"

infixr 1 op as //
