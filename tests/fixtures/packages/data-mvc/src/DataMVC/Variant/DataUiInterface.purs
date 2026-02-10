module DataMVC.Variant.DataUiInterface
  ( DataUiInterfaceVariantProps
  , FnConvertInit(..)
  , FnRecordGet
  , class DataUiInterfaceVariant
  , class MapInits
  , class MapProp
  , dataUiInterfaceVariant
  , mapInits
  , mapProp
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Newtype as NT
import Data.Symbol (class IsSymbol)
import Data.Variant (Variant)
import Heterogeneous.Mapping (class HMap, class Mapping, hmap)
import DataMVC.Types.DataUI (DataUiInterface(..))
import DataMVC.Types.DataError (DataResult)
import DataMVC.Variant.Extract (class ExtractVariant, extractVariant)
import DataMVC.Variant.Init (class InitVariant, initVariant)
import MVC.Variant.Types (VariantMsg, VariantState)
import MVC.Variant.Update (class UpdateVariant, updateVariant)
import MVC.Variant.View (class ViewVariant, ViewArgs, viewVariant)
import Prim.Row as Row
import Record as Record
import Type.Proxy (Proxy(..))

type DataUiInterfaceVariantProps :: (Type -> Type) -> Symbol -> Type
type DataUiInterfaceVariantProps srf initsym =
  { view :: forall msg. ViewArgs srf msg -> srf msg
  }

-------------------------------------------------------------------------------
--- DataUiInterfaceVariant
-------------------------------------------------------------------------------

class
  DataUiInterfaceVariant
    (uis :: Row Type)
    (srf :: Type -> Type)
    (initsym :: Symbol)
    (rcase :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
    (r :: Row Type)
  | uis srf initsym rcase -> rmsg rsta r
  where
  dataUiInterfaceVariant
    :: Record uis
    -> Proxy initsym
    -> DataUiInterfaceVariantProps srf initsym
    -> DataUiInterface srf (VariantMsg rcase rmsg) (VariantState rsta) (Variant r)

instance
  ( MapProp "extract" uis extracts
  , MapProp "init" uis inits
  , MapProp "update" uis updates
  , MapProp "view" uis views

  , InitVariant inits initsym r rsta
  , UpdateVariant inits' updates rcase rmsg rsta
  , ViewVariant srf views rcase rmsg rsta
  , ExtractVariant extracts rsta r

  , MapInits inits inits'
  ) =>
  DataUiInterfaceVariant uis srf initsym rcase rmsg rsta r
  where
  dataUiInterfaceVariant
    :: Record uis
    -> Proxy initsym
    -> DataUiInterfaceVariantProps srf initsym
    -> DataUiInterface srf (VariantMsg rcase rmsg) (VariantState rsta) (Variant r)
  dataUiInterfaceVariant uis prxInitSym props =
    DataUiInterface
      { init, update, view, extract, name }

    where
    -- Fields

    init :: Maybe (Variant r) -> VariantState rsta
    init = initVariant inits prxInitSym

    update :: VariantMsg rcase rmsg -> VariantState rsta -> VariantState rsta
    update = updateVariant inits' updates

    view :: VariantState rsta -> srf (VariantMsg rcase rmsg)
    view = viewVariant { view: props.view } views

    extract :: VariantState rsta -> DataResult (Variant r)
    extract = extractVariant extracts

    name :: String
    name = "Variant"

    -- Records

    inits' :: Record inits'
    inits' = mapInits inits

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
  | sym ri -> ro
  where
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

-------------------------------------------------------------------------------
--- MapInits
-------------------------------------------------------------------------------

class
  MapInits (inits :: Row Type) (inits' :: Row Type)
  | inits -> inits'
  where
  mapInits :: Record inits -> Record inits'

instance
  ( HMap FnConvertInit { | inits } { | inits' }
  ) =>
  MapInits inits inits'
  where
  mapInits :: Record inits -> Record inits'
  mapInits = hmap FnConvertInit

data FnConvertInit = FnConvertInit

instance Mapping FnConvertInit (Maybe a -> b) b
  where
  mapping :: FnConvertInit -> (Maybe a -> b) -> b
  mapping _ f = f Nothing