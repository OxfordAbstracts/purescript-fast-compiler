module Typisch.Row
  ( class Lacks
  , class Cons
  , class Cons2
  , class Cons3
  , class Changes
  , class Replaces
  , module Prim.Row
  ) where

import Prim.Row as Row
import Prim.Row (class Nub, class Union)
import Data.Symbol (class IsSymbol)

-- | A version of `Prim.Row.Lacks` that infers `Data.Symbol.IsSymbol`
-- | for you to ease record modification.
class
  ( IsSymbol label
  , Row.Lacks label row
  ) <= Lacks (label :: Symbol) (row :: Row Type)

instance lacks ::
  ( IsSymbol label
  , Row.Lacks label row
  ) => Lacks label row

-- | A version of `Prim.Row.Cons` that infers `Data.Symbol.IsSymbol`
-- | and `Prim.Row.Lacks` for you to ease record modification.
class
  ( Lacks label tail
  , Row.Cons label a tail row
  ) <= Cons
       (label :: Symbol)
       (a     :: Type)
       (tail  :: Row Type)
       (row   :: Row Type)
       | label a tail -> row
       , label row    -> a tail

instance cons ::
  ( Lacks label tail
  , Row.Cons label a tail row
  ) => Cons label a tail row

-- | `Cons`, but for two items.
class
  ( Lacks labelB base
  , Cons labelA a base rowA
  , Cons labelB b rowA rowAB
  ) <= Cons2
       (labelA :: Symbol)
       (a      :: Type)
       (labelB :: Symbol)
       (b      :: Type)
       (base   :: Row Type)
       (rowA   :: Row Type) -- base + a
       (rowAB  :: Row Type) -- base + a + b
       | labelA a base  -> rowA
       , labelB b rowA  -> rowAB
       , labelB b rowAB -> rowA
       , labelA a rowA  -> base

instance cons2 ::
  ( Lacks labelB base
  , Cons labelA a base rowA
  , Cons labelB b rowA rowAB
  ) => Cons2 labelA a labelB b base rowA rowAB

-- | `Cons`, but for threeitems.
class
  ( Lacks labelB base
  , Lacks labelC base
  , Cons labelA a base rowA
  , Cons labelB b rowA rowAB
  , Cons labelC c rowAB rowABC
  ) <= Cons3
       (labelA :: Symbol)
       (a      :: Type)
       (labelB :: Symbol)
       (b      :: Type)
       (labelC :: Symbol)
       (c      :: Type)
       (base   :: Row Type)
       (rowA   :: Row Type) -- base + a
       (rowAB  :: Row Type) -- base + a + b
       (rowABC :: Row Type) -- base + a + b + c
       | labelA a base   -> rowA
       , labelB b rowA   -> rowAB
       , labelC c rowAB  -> rowABC
       , labelC c rowABC -> rowAB
       , labelB b rowAB  -> rowA
       , labelA a rowA   -> base

instance cons3 ::
  ( Lacks labelB base
  , Lacks labelC base
  , Cons labelA a base rowA
  , Cons labelB b rowA rowAB
  , Cons labelC c rowAB rowABC
  ) => Cons3 labelA a labelB b labelC c base rowA rowAB rowABC

-- | A class that represents changing the type of a label in a row.
class
  ( Cons label a tail rowA
  , Cons label b tail rowB
  ) <= Changes
       (label :: Symbol)
       (a     :: Type)
       (b     :: Type)
       (tail  :: Row Type)
       (rowA  :: Row Type)
       (rowB  :: Row Type)
       | label a tail -> rowA
       , label b tail -> rowB
       , label rowA -> a tail
       , label rowB -> b tail

instance changes ::
  ( Cons label a tail rowA
  , Cons label b tail rowB
  ) => Changes label a b tail rowA rowB

-- | A class that represents replacing a row entry with another one.
class
  ( Cons labelA a tail rowA
  , Cons labelB b tail rowB
  ) <= Replaces
       (labelA :: Symbol)
       (a      :: Type)
       (labelB :: Symbol)
       (b      :: Type)
       (tail   :: Row Type)
       (rowA   :: Row Type)
       (rowB   :: Row Type)
       | labelA a tail -> rowA
       , labelB b tail -> rowB
       , labelA rowA -> a tail
       , labelB rowB -> b tail

instance replaces ::
  ( Cons labelA a tail rowA
  , Cons labelB b tail rowB
  ) => Replaces labelA a labelB b tail rowA rowB
