module MVC.Util
  ( FnMapProp(..)
  , class MapProp
  , mapProp
  ) where

import Data.Symbol (class IsSymbol)
import Heterogeneous.Mapping (class HMap, class Mapping, hmap)
import Prim.Row as Row
import Record as Record
import Type.Proxy (Proxy)

--------------------------------------------------------------------------------
--- MapProp
--------------------------------------------------------------------------------

class
  MapProp
    (sym :: Symbol)
    (ri :: Row Type)
    (ro :: Row Type)
  | sym ri -> ro
  where
  mapProp :: Proxy sym -> { | ri } -> { | ro }

instance
  ( HMap (FnMapProp sym) (Record ri) (Record ro)
  ) =>
  MapProp sym ri ro
  where
  mapProp :: Proxy sym -> Record ri -> Record ro
  mapProp sym = hmap (FnMapProp sym)

data FnMapProp (k :: Symbol) = FnMapProp (Proxy k)

instance (IsSymbol k, Row.Cons k a rx r) => Mapping (FnMapProp k) { | r } a
  where
  mapping :: FnMapProp k -> Record r -> a
  mapping (FnMapProp k) = Record.get k
