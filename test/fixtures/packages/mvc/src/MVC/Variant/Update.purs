module MVC.Variant.Update
  ( class MatchCase
  , matchCase
  , class MatchCaseRL
  , matchCaseRL
  , class UpdateVariant
  , updateVariant
  , class UpdateVariantRL
  , updateVariantRL
  ) where

import Prelude

import Data.Symbol (class IsSymbol)
import Data.Variant (Variant)
import Data.Variant as V
import MVC.Variant.Types (VariantMsg(..), VariantState(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
--- UpdateVariant
--------------------------------------------------------------------------------

class
  UpdateVariant
    (initstates :: Row Type)
    (updates :: Row Type)
    (rcase :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  where
  updateVariant
    :: Record initstates
    -> Record updates
    -> (VariantMsg rcase rmsg -> VariantState rsta -> VariantState rsta)

instance
  ( UpdateVariantRL rl updates rmsg rsta
  , RowToList updates rl
  , MatchCase rcase initstates rsta
  ) =>
  UpdateVariant initstates updates rcase rmsg rsta
  where
  updateVariant
    :: Record initstates
    -> Record updates
    -> (VariantMsg rcase rmsg -> VariantState rsta -> VariantState rsta)
  updateVariant initVariantStates updates msg (VariantState vsta) =
    case msg of
      ChildCaseMsg vmsg ->
        VariantState $ updateVariantRL prxRl updates vmsg vsta

      ChangeCase vcase ->
        VariantState $ matchCase initVariantStates vcase

      ErrMsg _ ->
        VariantState vsta

    where
    prxRl :: Proxy rl
    prxRl = Proxy

--------------------------------------------------------------------------------
--- UpdateVariantRL
--------------------------------------------------------------------------------

class
  UpdateVariantRL
    (rl :: RowList Type)
    (updates :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  | rl -> rsta
  where
  updateVariantRL
    :: Proxy rl
    -> Record updates
    -> (Variant rmsg -> Variant rsta -> Variant rsta)

instance UpdateVariantRL RL.Nil updates rmsg ()
  where
  updateVariantRL
    :: Proxy RL.Nil
    -> Record updates
    -> (Variant rmsg -> Variant () -> Variant ())
  updateVariantRL _ _ _ = V.case_

instance
  ( Row.Cons sym (msg -> sta -> sta) updatesx updates
  , Row.Cons sym msg rmsgx rmsg
  , Row.Cons sym sta rsta' rsta

  , Row.Lacks sym rsta'
  , Row.Lacks sym updatesx

  , UpdateVariantRL rl' updates rmsg rsta'
  , IsSymbol sym
  , Row.Union rsta' rstax rsta
  , RowToList rsta msgRL
  ) =>
  UpdateVariantRL (RL.Cons sym x rl') updates rmsg rsta
  where
  updateVariantRL
    :: Proxy (RL.Cons sym x rl')
    -> Record updates
    -> (Variant rmsg -> Variant rsta -> Variant rsta)
  updateVariantRL _ updates vmsg =
    tail'
      # V.on prxSym
          \sta -> V.inj prxSym $
            ( V.default sta
                # V.on prxSym (\msg -> updateFn msg sta)
            ) vmsg
    where

    tail :: Variant rsta' -> Variant rsta'
    tail = updateVariantRL prxRl' updates vmsg

    tail' :: Variant rsta' -> Variant rsta
    tail' = tail >>> V.expand

    updateFn :: msg -> sta -> sta
    updateFn = Record.get prxSym updates

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRl' :: Proxy rl'
    prxRl' = Proxy

--------------------------------------------------------------------------------
--- MatchCase
--------------------------------------------------------------------------------

class
  MatchCase
    (rcase :: Row Type)
    (initstates :: Row Type)
    (rsta :: Row Type)
  where
  matchCase :: Record initstates -> Variant rcase -> Variant rsta

instance
  ( MatchCaseRL rl rcase initstates rsta
  , RowToList initstates rl
  ) =>
  MatchCase rcase initstates rsta
  where
  matchCase :: Record initstates -> Variant rcase -> Variant rsta
  matchCase = matchCaseRL (Proxy :: Proxy rl)

--------------------------------------------------------------------------------
--- MatchCaseRL
--------------------------------------------------------------------------------

class
  MatchCaseRL
    (rl :: RowList Type)
    (rcase :: Row Type)
    (initstates :: Row Type)
    (rsta :: Row Type)
  | rl -> rcase
  where
  matchCaseRL :: Proxy rl -> Record initstates -> Variant rcase -> Variant rsta

instance MatchCaseRL RL.Nil () initstates rsta
  where
  matchCaseRL :: Proxy RL.Nil -> Record initstates -> Variant () -> Variant rsta
  matchCaseRL _ _ = V.case_

instance
  ( Row.Cons sym sta rstax rsta
  , Row.Cons sym sta initstatesx initstates
  , Row.Cons sym Unit rcase' rcase
  , Row.Lacks sym rcase'
  , MatchCaseRL rl' rcase' initstates rsta
  , IsSymbol sym
  ) =>
  MatchCaseRL (RL.Cons sym x rl') rcase initstates rsta
  where
  matchCaseRL :: Proxy (RL.Cons sym x rl') -> Record initstates -> Variant rcase -> Variant rsta
  matchCaseRL _ initVariantStates =
    tail
      # V.on prxSym (\_ -> V.inj prxSym $ initVariantState)

    where
    initVariantState :: sta
    initVariantState = Record.get prxSym initVariantStates

    tail :: Variant rcase' -> Variant rsta
    tail = matchCaseRL prxRl' initVariantStates

    prxRl' :: Proxy rl'
    prxRl' = Proxy

    prxSym :: Proxy sym
    prxSym = Proxy

