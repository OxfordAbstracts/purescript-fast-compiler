module MVC.Record.View
  ( ViewRecordProps
  , ViewResult
  , class ViewRecord
  , class ViewRecordRL
  , viewRecord
  , viewRecordRL
  ) where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant as V
import MVC.Record.Types (RecordMsg(..), RecordState(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

type ViewResult :: (Type -> Type) -> Type -> Type
type ViewResult html msg = { key :: String, viewValue :: html msg }

type ViewRecordProps html msg =
  { viewEntries :: Array (ViewResult html msg) -> html msg
  }

--------------------------------------------------------------------------------
--- ViewRecord
--------------------------------------------------------------------------------

class
  ViewRecord
    (html :: Type -> Type)
    (views :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  where
  viewRecord
    :: Record views
    -> ViewRecordProps html (RecordMsg rmsg)
    -> (RecordState rsta -> html (RecordMsg rmsg))

instance
  ( RowToList views rl
  , ViewRecordRL html views rl rmsg rsta
  ) =>
  ViewRecord html views rmsg rsta
  where
  viewRecord
    :: Record views
    -> ViewRecordProps html (RecordMsg rmsg)
    -> RecordState rsta
    -> html (RecordMsg rmsg)
  viewRecord fieldViews props = viewRecordRL prxRL fieldViews <#> props.viewEntries
    where
    prxRL :: Proxy rl
    prxRL = Proxy

--------------------------------------------------------------------------------
--- ViewRecordRL
--------------------------------------------------------------------------------

class
  ViewRecordRL
    (html :: Type -> Type)
    (views :: Row Type)
    (rl :: RowList Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  | rl -> rmsg rsta views
  where
  viewRecordRL
    :: Proxy rl
    -> Record views
    -> (RecordState rsta -> Array (ViewResult html (RecordMsg rmsg)))

instance ViewRecordRL html () RL.Nil () () where
  viewRecordRL
    :: Proxy RL.Nil
    -> Record ()
    -> (RecordState () -> Array (ViewResult html (RecordMsg ())))
  viewRecordRL _ _ _ = []

instance
  ( Functor html
  , IsSymbol sym
  , ViewRecordRL html views' rl' rmsg' rsta'

  , Row.Cons sym sta rsta' rsta
  , Row.Cons sym msg rmsg' rmsg
  , Row.Cons sym (sta -> html msg) views' views

  , Row.Lacks sym rsta'
  , Row.Lacks sym rmsg'
  , Row.Lacks sym views'

  , Row.Union rmsg' rx rmsg
  ) =>
  ViewRecordRL html views (RL.Cons sym x rl') rmsg rsta
  where
  viewRecordRL
    :: Proxy (RL.Cons sym x rl')
    -> Record views
    -> RecordState rsta
    -> Array (ViewResult html (RecordMsg rmsg))
  viewRecordRL _ views (RecordState states) =
    [ head' ] <> tail'
    where
    head :: ViewResult html msg
    head =
      { key: reflectSymbol prxSym
      , viewValue: Record.get prxSym views state
      }

    state :: sta
    state = Record.get prxSym states

    head' :: ViewResult html (RecordMsg rmsg)
    head' =
      { key: head.key
      , viewValue: map (SetField <<< V.inj prxSym) head.viewValue
      }

    tail :: Array (ViewResult html (RecordMsg rmsg'))
    tail = viewRecordRL prxRL'
      (Record.delete prxSym views)
      (RecordState (Record.delete prxSym states))

    tail' :: Array (ViewResult html (RecordMsg rmsg))
    tail' = map (\x -> x { viewValue = map (\(SetField x') -> SetField $ V.expand x') x.viewValue }) tail

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRL' :: Proxy rl'
    prxRL' = Proxy

