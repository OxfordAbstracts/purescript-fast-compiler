module MyLib where

import Prelude (class Semigroup, class Monoid, (<>), mempty)

-- Function with Monoid dict constraint + value args.
-- Like Data.Array.intercalate: takes Monoid dict, then separator, then two values.
myConcat :: forall a. Monoid a => a -> a -> a -> a
myConcat sep a b = a <> sep <> b
