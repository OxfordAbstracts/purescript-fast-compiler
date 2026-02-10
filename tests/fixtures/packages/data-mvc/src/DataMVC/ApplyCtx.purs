module DataMVC.ApplyCtx
  ( class ApplyCtx
  , mapApplyCtx
  , class ApplyCtxRL
  , mapApplyCtxRL
  ) where

import Data.Symbol (class IsSymbol)
import DataMVC.Types.DataUI (DataUI, DataUICtx, DataUiInterface, applyWrap, runDataUi)
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
--- ApplyCtx
--------------------------------------------------------------------------------

class
  ApplyCtx
    (a :: Type)
    (datauis :: Row Type)
    (uis :: Row Type)
  | datauis -> uis a
  where
  mapApplyCtx :: a -> { | datauis } -> { | uis }

instance
  ( ApplyCtxRL rl a datauis uis
  , RowToList datauis rl
  ) =>
  ApplyCtx a datauis uis
  where
  mapApplyCtx :: a -> Record datauis -> Record uis
  mapApplyCtx = mapApplyCtxRL prxRl
    where
    prxRl :: Proxy rl
    prxRl = Proxy

--------------------------------------------------------------------------------
--- ApplyCtxRL
--------------------------------------------------------------------------------

class
  ApplyCtxRL
    (rl :: RowList Type)
    (a :: Type)
    (datauis :: Row Type)
    (uis :: Row Type)
  | datauis -> uis a where
  mapApplyCtxRL :: Proxy rl -> a -> { | datauis } -> { | uis }

instance ApplyCtxRL RL.Nil a datauis ()
  where
  mapApplyCtxRL :: Proxy RL.Nil -> a -> { | datauis } -> { | () }
  mapApplyCtxRL _ _ _ = {}

instance
  ( ApplyCtxRL rl' (DataUICtx srf fm fs) datauis uis'
  , Row.Cons sym (DataUiInterface srf (fm msg) (fs sta) a) uis' uis
  , Row.Cons sym (DataUI srf fm fs msg sta a) datauisx datauis
  , IsSymbol sym
  , Row.Lacks sym uis'
  ) =>
  ApplyCtxRL (RL.Cons sym x rl') (DataUICtx srf fm fs) datauis uis
  where
  mapApplyCtxRL :: Proxy (RL.Cons sym x rl') -> DataUICtx srf fm fs -> { | datauis } -> { | uis }
  mapApplyCtxRL _ ctx datauis =
    Record.insert prxSym ui tail

    where
    dataui :: DataUI srf fm fs msg sta a
    dataui = Record.get prxSym datauis

    dataui' :: DataUI srf fm fs (fm msg) (fs sta) a
    dataui' = applyWrap dataui

    ui :: DataUiInterface srf (fm msg) (fs sta) a
    ui = runDataUi dataui' ctx

    tail :: { | uis' }
    tail = mapApplyCtxRL (Proxy :: Proxy rl') ctx datauis

    prxSym :: Proxy sym
    prxSym = Proxy

