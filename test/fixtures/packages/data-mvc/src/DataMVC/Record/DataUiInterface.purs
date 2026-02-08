module DataMVC.Record.DataUiInterface
  ( FnRecordGet
  , class DataUiInterfaceRecord
  , dataUiInterfaceRecord
  , class MapProp
  , mapProp
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Newtype as NT
import Data.Symbol (class IsSymbol)
import Heterogeneous.Mapping (class HMap, class Mapping, hmap)
import DataMVC.Record.Extract (class ExtractRecord, extractRecord)
import DataMVC.Record.Init (class InitRecord, initRecord)
import DataMVC.Types.DataUI (DataUiInterface(..))
import DataMVC.Types.DataError (DataResult)
import MVC.Record (class UpdateRecord, class ViewRecord, RecordMsg, RecordState, updateRecord, viewRecord)
import MVC.Record.UI (UIRecordProps)
import Prim.Row as Row
import Record as Record
import Type.Proxy (Proxy(..))

class
  DataUiInterfaceRecord
    (uis :: Row Type)
    (srf :: Type -> Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
    (r :: Row Type)
  where
  dataUiInterfaceRecord
    :: UIRecordProps srf (RecordMsg rmsg) (RecordState rsta)
    -> Record uis
    -> DataUiInterface srf (RecordMsg rmsg) (RecordState rsta) (Record r)

instance
  ( MapProp "extract" uis extracts
  , MapProp "init" uis inits
  , MapProp "update" uis updates
  , MapProp "view" uis views

  , InitRecord inits r rsta
  , UpdateRecord updates rmsg rsta
  , ViewRecord srf views rmsg rsta
  , ExtractRecord extracts rsta r
  ) =>
  DataUiInterfaceRecord uis srf rmsg rsta r
  where
  dataUiInterfaceRecord
    :: UIRecordProps srf (RecordMsg rmsg) (RecordState rsta)
    -> Record uis
    -> DataUiInterface srf (RecordMsg rmsg) (RecordState rsta) (Record r)
  dataUiInterfaceRecord props uis = DataUiInterface { init, update, view, extract, name }

    where
    -- Fields

    init :: Maybe (Record r) -> RecordState rsta
    init = initRecord inits

    update :: RecordMsg rmsg -> RecordState rsta -> RecordState rsta
    update = updateRecord updates

    view :: RecordState rsta -> srf (RecordMsg rmsg)
    view = viewRecord views { viewEntries: props.viewEntries }

    extract :: RecordState rsta -> DataResult (Record r)
    extract = extractRecord extracts

    name :: String
    name = "Record"

    -- Records

    inits :: Record inits
    inits = mapProp prxInit uis

    updates :: Record updates
    updates = mapProp prxUpdate uis

    views :: Record views
    views = mapProp prxView uis

    extracts :: Record extracts
    extracts = mapProp prxExtract uis

    -- Proxies

    prxInit :: Proxy "init"
    prxInit = Proxy

    prxUpdate :: Proxy "update"
    prxUpdate = Proxy

    prxView :: Proxy "view"
    prxView = Proxy

    prxExtract :: Proxy "extract"
    prxExtract = Proxy

-------------------------------------------------------------------------------
--- MapProp
-------------------------------------------------------------------------------

class
  MapProp
    (sym :: Symbol)
    (ri :: Row Type)
    (ro :: Row Type)
  | sym ri -> ro where
  mapProp :: Proxy sym -> { | ri } -> { | ro }

instance
  ( HMap (FnRecordGet sym) (Record ri) (Record ro)
  ) =>
  MapProp sym ri ro
  where
  mapProp :: Proxy sym -> Record ri -> Record ro
  mapProp sym = hmap (FnRecordGet sym)

data FnRecordGet :: Symbol -> Type
data FnRecordGet sym = FnRecordGet (Proxy sym)

instance
  ( Row.Cons sym a rx r
  , IsSymbol sym
  , Newtype nt (Record r)
  ) =>
  Mapping (FnRecordGet sym) nt a
  where
  mapping :: FnRecordGet sym -> nt -> a
  mapping (FnRecordGet prxSym) =
    Record.get prxSym <<< NT.unwrap

