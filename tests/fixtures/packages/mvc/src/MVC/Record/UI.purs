module MVC.Record.UI
  ( UIRecordProps
  , class UIRecord
  , uiRecord
  ) where

import MVC.Record (class UpdateRecord, class ViewRecord, ViewResult, updateRecord, viewRecord)
import MVC.Record.Init (class InitRecord, initRecord)
import MVC.Record.Types (RecordMsg, RecordState)
import MVC.Types (UI)
import MVC.Util (class MapProp, mapProp)
import Type.Proxy (Proxy(..))

type UIRecordProps :: (Type -> Type) -> Type -> Type -> Type
type UIRecordProps srf msg sta =
  { viewEntries :: Array (ViewResult srf msg) -> srf msg
  }

class
  UIRecord
    (uis :: Row Type)
    (srf :: Type -> Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  | uis -> srf rmsg rsta
  where
  uiRecord
    :: Record uis
    -> UIRecordProps srf (RecordMsg rmsg) (RecordState rsta)
    -> UI srf (RecordMsg rmsg) (RecordState rsta)

instance
  ( MapProp "init" uis inits
  , MapProp "update" uis updates
  , MapProp "view" uis views
  , InitRecord inits rsta
  , UpdateRecord updates rmsg rsta
  , ViewRecord srf views rmsg rsta
  ) =>
  UIRecord uis srf rmsg rsta
  where
  uiRecord
    :: Record uis
    -> UIRecordProps srf (RecordMsg rmsg) (RecordState rsta)
    -> UI srf (RecordMsg rmsg) (RecordState rsta)
  uiRecord uis props =
    { init: initRecord inits
    , update: updateRecord updates
    , view: viewRecord views { viewEntries: props.viewEntries }
    }
    where
    --- Records

    inits :: Record inits
    inits = mapProp prxInit uis

    updates :: Record updates
    updates = mapProp prxUpdate uis

    views :: Record views
    views = mapProp prxView uis

    -- Proxies

    prxInit :: Proxy "init"
    prxInit = Proxy

    prxUpdate :: Proxy "update"
    prxUpdate = Proxy

    prxView :: Proxy "view"
    prxView = Proxy
