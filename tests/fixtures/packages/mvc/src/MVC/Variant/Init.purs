module MVC.Variant.Init
  ( class InitVariant
  , initVariant
  ) where

import Prelude

import Data.Symbol (class IsSymbol)
import Data.Variant as V
import MVC.Variant.Types (VariantState(..))
import Prim.Row as Row
import Record as Record
import Type.Proxy (Proxy)

class
  InitVariant
    (sym :: Symbol)
    (initstates :: Row Type)
    (rsta :: Row Type)
  where
  initVariant :: Proxy sym -> Record initstates -> VariantState rsta

instance
  ( Row.Cons sym sta initstatesx initstates
  , Row.Cons sym sta rstax rsta
  , IsSymbol sym
  ) =>
  InitVariant sym initstates rsta
  where
  initVariant :: Proxy sym -> Record initstates -> VariantState rsta
  initVariant prxSym initStates =
    VariantState $ V.inj prxSym state
    where
    state :: sta
    state = Record.get prxSym initStates

