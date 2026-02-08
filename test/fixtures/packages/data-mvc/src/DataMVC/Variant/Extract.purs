module DataMVC.Variant.Extract
  ( class ExtractVariant
  , extractVariant
  , class ExtractVariantRL
  , extractVariantRL
  ) where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant)
import Data.Variant as V
import DataMVC.Types.DataPath (DataPathSegment(..))
import DataMVC.Types.DataError (DataResult, scopeOpt)
import MVC.Variant.Types (VariantState(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
--- ExtractVariant
--------------------------------------------------------------------------------

class
  ExtractVariant (extracts :: Row Type) (rsta :: Row Type) (r :: Row Type)
  | extracts -> rsta r
  where
  extractVariant :: Record extracts -> VariantState rsta -> DataResult (Variant r)

instance
  ( ExtractVariantRL rl extracts rsta r
  , RowToList extracts rl
  ) =>
  ExtractVariant extracts rsta r
  where
  extractVariant :: Record extracts -> VariantState rsta -> DataResult (Variant r)
  extractVariant extracts (VariantState va) =
    extractVariantRL prxRl extracts va

    where
    prxRl :: Proxy rl
    prxRl = Proxy

--------------------------------------------------------------------------------
--- ExtractVariantRL
--------------------------------------------------------------------------------

class
  ExtractVariantRL
    (rl :: RowList Type)
    (extracts :: Row Type)
    (rsta :: Row Type)
    (r :: Row Type)
  | rl extracts -> rsta r
  where
  extractVariantRL :: Proxy rl -> Record extracts -> Variant rsta -> DataResult (Variant r)

instance ExtractVariantRL RL.Nil extracts () r
  where
  extractVariantRL :: Proxy RL.Nil -> Record extracts -> Variant () -> DataResult (Variant r)
  extractVariantRL _ _ = V.case_

instance
  ( ExtractVariantRL rl' extracts rsta' r
  , Row.Cons sym (sta -> DataResult a) extractsx extracts
  , Row.Cons sym sta rsta' rsta
  , Row.Cons sym a rx r
  , IsSymbol sym
  ) =>
  ExtractVariantRL (RL.Cons sym x rl') extracts rsta r
  where
  extractVariantRL :: Proxy (RL.Cons sym x rl') -> Record extracts -> Variant rsta -> DataResult (Variant r)
  extractVariantRL _ extracts =
    tail
      # V.on prxSym head

    where
    head :: sta -> DataResult (Variant r)
    head = extract >>> map (V.inj prxSym)

    pathSeg :: DataPathSegment
    pathSeg = SegCase (reflectSymbol prxSym)

    extract :: sta -> DataResult a
    extract = Record.get prxSym extracts >>> scopeOpt pathSeg

    tail :: Variant rsta' -> DataResult (Variant r)
    tail = extractVariantRL prxRl' extracts

    prxRl' :: Proxy rl'
    prxRl' = Proxy

    prxSym :: Proxy sym
    prxSym = Proxy
