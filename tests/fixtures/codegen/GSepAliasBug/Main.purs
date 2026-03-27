-- | Main module: uses the alias type through the operator
-- | This mirrors Test.Main using segment :: RouteDuplex' String with gsep
-- |
-- | The bug: when resolving `rdString // rdInt`, the typechecker stores
-- | rdString's type as RD' String (alias not expanded). Instance matching
-- | for Op then fails to match opRDRD (which expects RD a a not RD' a),
-- | and the fallback returns opStringRD (wrong instance) from the registry.
-- |
-- TEST: "rdrd"
module Main where

import Prelude (class Show, show)
import Core (RD', rdString, rdInt)
import Syntax ((//) )

-- The call that should use opRDRD(subAll)
-- Both args are RD' String and RD' Int (type alias for RD a a)
test :: String
test = rdString // rdInt
