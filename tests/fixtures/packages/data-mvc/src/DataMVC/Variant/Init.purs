module DataMVC.Variant.Init
  ( class InitVariant
  , initVariant
  , class InitVariantRL
  , initVariantRL
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol)
import Data.Variant (Variant)
import Data.Variant as V
import MVC.Variant.Types (VariantState(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
--- InitVariant
--------------------------------------------------------------------------------

class
  InitVariant
    (inits :: Row Type)
    (initsym :: Symbol)
    (r :: Row Type)
    (rsta :: Row Type)
  | inits initsym -> r rsta
  where
  initVariant :: Record inits -> Proxy initsym -> Maybe (Variant r) -> VariantState rsta

instance
  ( Row.Cons initsym (Maybe a -> sta) initsx inits
  , Row.Cons initsym sta rstax rsta
  , IsSymbol initsym
  , RowToList inits rl
  , InitVariantRL rl inits r rsta
  ) =>
  InitVariant inits initsym r rsta where

  initVariant :: Record inits -> Proxy initsym -> Maybe (Variant r) -> VariantState rsta
  initVariant inits _ = case _ of
    Nothing -> VariantState $ V.inj prxInitSym state
    Just va -> initVariantRL prxRl inits va

    where
    state :: sta
    state = init Nothing

    init :: Maybe a -> sta
    init = Record.get prxInitSym inits

    prxInitSym :: Proxy initsym
    prxInitSym = Proxy

    prxRl :: Proxy rl
    prxRl = Proxy

--------------------------------------------------------------------------------
--- InitVariantRL
--------------------------------------------------------------------------------

class
  InitVariantRL
    (rl :: RowList Type)
    (inits :: Row Type)
    (r :: Row Type)
    (rsta :: Row Type)
  | rl inits -> r rsta
  where
  initVariantRL :: Proxy rl -> Record inits -> Variant r -> VariantState rsta

instance InitVariantRL RL.Nil inits () rsta
  where
  initVariantRL :: Proxy RL.Nil -> Record inits -> Variant () -> VariantState rsta
  initVariantRL _ _ = V.case_

instance
  ( InitVariantRL rl' inits r' rsta
  , Row.Cons sym a r' r
  , Row.Cons sym (Maybe a -> sta) initsx inits
  , Row.Cons sym sta rstax rsta
  , IsSymbol sym
  ) =>
  InitVariantRL (RL.Cons sym x rl') inits r rsta
  where

  initVariantRL :: Proxy (RL.Cons sym x rl') -> Record inits -> Variant r -> VariantState rsta
  initVariantRL _ inits =
    tail
      # V.on prxSym (Just >>> init >>> V.inj prxSym >>> VariantState)

    where
    init :: Maybe a -> sta
    init = Record.get prxSym inits

    tail :: Variant r' -> VariantState rsta
    tail = initVariantRL prxRl' inits

    prxRl' :: Proxy rl'
    prxRl' = Proxy

    prxSym :: Proxy sym
    prxSym = Proxy
