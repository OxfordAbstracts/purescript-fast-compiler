module DataMVC.Record.Extract
  ( class ExtractRecord
  , extractRecord
  , class ExtractRecordRL
  , extractRecordRL
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import DataMVC.Types.DataPath (DataPathSegment(..), DataPathSegmentField(..))
import DataMVC.Types.DataError (DataResult, scopeOpt)
import MVC.Record (RecordState(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
--- ExtractRecord
--------------------------------------------------------------------------------

class
  ExtractRecord
    (extracts :: Row Type)
    (rsta :: Row Type)
    (r :: Row Type)
  | extracts -> rsta r
  where
  extractRecord :: Record extracts -> RecordState rsta -> DataResult (Record r)

instance
  ( RowToList extracts rl
  , ExtractRecordRL rl extracts rsta r
  ) =>
  ExtractRecord extracts rsta r
  where
  extractRecord :: Record extracts -> RecordState rsta -> DataResult (Record r)
  extractRecord = extractRecordRL prxRl
    where
    prxRl :: Proxy rl
    prxRl = Proxy

--------------------------------------------------------------------------------
--- ExtractRecordRL
--------------------------------------------------------------------------------

class
  ExtractRecordRL
    (rl :: RowList Type)
    (extracts :: Row Type)
    (rsta :: Row Type)
    (r :: Row Type)
  | rl extracts -> rsta r
  where
  extractRecordRL :: Proxy rl -> Record extracts -> RecordState rsta -> DataResult (Record r)

instance ExtractRecordRL RL.Nil extracts rsta ()
  where
  extractRecordRL :: Proxy RL.Nil -> Record extracts -> RecordState rsta -> DataResult (Record ())
  extractRecordRL _ _ _ = Right {}

instance
  ( ExtractRecordRL rl' extracts rsta r'
  , Row.Cons sym (sta -> DataResult a) extractsx extracts
  , Row.Cons sym sta rstax rsta
  , Row.Cons sym a r' r
  , Row.Lacks sym r'
  , IsSymbol sym
  ) =>
  ExtractRecordRL (RL.Cons sym x rl') extracts rsta r
  where
  extractRecordRL :: Proxy (RL.Cons sym x rl') -> Record extracts -> RecordState rsta -> DataResult (Record r)
  extractRecordRL _ extracts (RecordState states) =
    case head, tail of
      Left errors1, Left errors2 ->
        Left (errors1 <> errors2)

      Left errors, Right _ ->
        Left errors

      Right _, Left errors ->
        Left errors

      Right x, Right xs ->
        Right $ Record.insert prxSym x xs

    where
    tail :: DataResult (Record r')
    tail = extractRecordRL prxRl' extracts (RecordState states)

    head :: DataResult a
    head = extract state # scopeOpt pathSeg

    pathSeg :: DataPathSegment
    pathSeg = SegField $ SegStaticKey (reflectSymbol prxSym)

    extract :: sta -> DataResult a
    extract = Record.get prxSym extracts

    state :: sta
    state = Record.get prxSym states

    prxRl' :: Proxy rl'
    prxRl' = Proxy

    prxSym :: Proxy sym
    prxSym = Proxy

