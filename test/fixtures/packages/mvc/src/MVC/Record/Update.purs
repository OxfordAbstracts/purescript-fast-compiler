module MVC.Record.Update
  ( class UpdateRecord
  , class UpdateRecordRL
  , updateRecord
  , updateRecordRL
  ) where

import Prelude

import Data.Symbol (class IsSymbol)
import Data.Variant (Variant)
import Data.Variant as V
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))
import MVC.Record.Types (RecordMsg(..), RecordState(..))

--------------------------------------------------------------------------------
--- UpdateRecord
--------------------------------------------------------------------------------

class
  UpdateRecord
    (updates :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  | updates -> rmsg rsta
  where
  updateRecord
    :: Record updates
    -> (RecordMsg rmsg -> RecordState rsta -> RecordState rsta)

instance
  ( RowToList rsta rl
  , UpdateRecordRL rl rsta rmsg updates
  ) =>
  UpdateRecord updates rmsg rsta
  where
  updateRecord :: Record updates -> RecordMsg rmsg -> RecordState rsta -> RecordState rsta
  updateRecord updates (SetField v) state =
    updateRecordRL (Proxy :: _ rl) updates state v

--------------------------------------------------------------------------------
--- UpdateRecordRL
--------------------------------------------------------------------------------

class
  UpdateRecordRL
    (rl :: RowList Type)
    (rs :: Row Type)
    (rm :: Row Type)
    (updates :: Row Type)
  | rl -> rs rm updates
  where
  updateRecordRL
    :: Proxy rl
    -> Record updates
    -> (RecordState rs -> Variant rm -> RecordState rs)

instance UpdateRecordRL RL.Nil rs () ()
  where
  updateRecordRL :: Proxy RL.Nil -> Record () -> (RecordState rs -> Variant () -> RecordState rs)
  updateRecordRL _ _ _ = V.case_

instance
  ( IsSymbol sym
  , UpdateRecordRL rl' rs rm' updates'
  , Row.Cons sym sta rsx rs
  , Row.Cons sym msg rm' rm
  , Row.Cons sym (msg -> sta -> sta) updates' updates
  , Row.Lacks sym rm'
  , Row.Lacks sym rsx
  , Row.Lacks sym updates'
  ) =>
  UpdateRecordRL (RL.Cons sym x rl') rs rm updates
  where
  updateRecordRL
    :: Proxy (RL.Cons sym x rl')
    -> Record updates
    -> (RecordState rs -> Variant rm -> RecordState rs)
  updateRecordRL _ updates (RecordState r) =
    tail
      # V.on prxSym
          ( \msg ->
              let
                updateFn = Record.get prxSym updates
              in
                RecordState $ Record.modify prxSym (updateFn msg) r
          )
    where
    tail :: Variant rm' -> RecordState rs
    tail =
      updateRecordRL prxRL'
        (Record.delete prxSym updates)
        (RecordState r)

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRL' :: Proxy rl'
    prxRL' = Proxy
