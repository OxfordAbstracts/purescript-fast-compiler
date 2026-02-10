module DataMVC.Record.Init
  ( class InitRecord
  , initRecord
  , class InitRecordRL
  , initRecordRL
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Symbol (class IsSymbol)
import MVC.Record (RecordState(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
--- InitRecord
--------------------------------------------------------------------------------

class
  InitRecord
    (inits :: Row Type)
    (r :: Row Type)
    (rsta :: Row Type)
  | inits -> r rsta
  where
  initRecord :: Record inits -> Maybe (Record r) -> RecordState rsta

instance
  ( InitRecordRL rl inits r rsta
  , RowToList inits rl
  ) =>
  InitRecord inits r rsta
  where
  initRecord :: Record inits -> Maybe (Record r) -> RecordState rsta
  initRecord inits =
    initRecordRL prxRl inits
    where
    prxRl :: Proxy rl
    prxRl = Proxy

--------------------------------------------------------------------------------
--- InitRecordRL
--------------------------------------------------------------------------------

class
  InitRecordRL
    (rl :: RowList Type)
    (inits :: Row Type)
    (r :: Row Type)
    (rsta :: Row Type)
  | rl inits -> r rsta
  where
  initRecordRL :: Proxy rl -> Record inits -> Maybe (Record r) -> RecordState rsta

instance InitRecordRL RL.Nil inits r ()
  where
  initRecordRL :: Proxy RL.Nil -> Record inits -> Maybe (Record r) -> RecordState ()
  initRecordRL _ _ _ = RecordState {}

instance
  ( InitRecordRL rl' inits r rsta'
  , Row.Cons sym (Maybe a -> sta) initsx inits
  , Row.Cons sym a rx r
  , Row.Cons sym sta rsta' rsta
  , Row.Lacks sym rsta'
  , IsSymbol sym
  ) =>
  InitRecordRL (RL.Cons sym x rl') inits r rsta
  where
  initRecordRL :: Proxy (RL.Cons sym x rl') -> Record inits -> Maybe (Record r) -> RecordState rsta
  initRecordRL _ inits optRec =
    overRecordState update tail

    where
    update :: Record rsta' -> Record rsta
    update = Record.insert prxSym head

    overRecordState :: (Record rsta' -> Record rsta) -> RecordState rsta' -> RecordState rsta
    overRecordState f (RecordState rec) = RecordState $ f rec

    head :: sta
    head = init (map (Record.get prxSym) optRec)

    tail :: RecordState rsta'
    tail = initRecordRL prxRl' inits optRec

    init :: Maybe a -> sta
    init = Record.get prxSym inits

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRl' :: Proxy rl'
    prxRl' = Proxy
