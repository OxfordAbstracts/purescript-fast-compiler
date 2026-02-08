module MVC.Variant.UI
  ( UIVariantProps
  , class UIVariant
  , uiVariant
  ) where

import MVC.Types (UI)
import MVC.Util (class MapProp, mapProp)
import MVC.Variant.Init (class InitVariant, initVariant)
import MVC.Variant.Types (VariantMsg, VariantState)
import MVC.Variant.Update (class UpdateVariant, updateVariant)
import MVC.Variant.View (class ViewVariant, ViewArgs, viewVariant)
import Type.Proxy (Proxy(..))

type UIVariantProps :: (Type -> Type) -> Symbol -> Type
type UIVariantProps srf initsym =
  { view :: forall msg. ViewArgs srf msg -> srf msg
  , initCase :: Proxy initsym
  }

--------------------------------------------------------------------------------
--- UIVariant
--------------------------------------------------------------------------------

class
  UIVariant
    (uis :: Row Type)
    (srf :: Type -> Type)
    (initsym :: Symbol)
    (rcase :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  | uis -> srf initsym rmsg rsta
  where
  uiVariant
    :: Record uis
    -> UIVariantProps srf initsym
    -> UI srf (VariantMsg rcase rmsg) (VariantState rsta)

instance
  ( MapProp "init" uis inits
  , MapProp "update" uis updates
  , MapProp "view" uis views
  , InitVariant initsym inits rsta
  , UpdateVariant inits updates rcase rmsg rsta
  , ViewVariant srf views rcase rmsg rsta
  ) =>
  UIVariant uis srf initsym rcase rmsg rsta where
  uiVariant
    :: Record uis
    -> UIVariantProps srf initsym
    -> UI srf (VariantMsg rcase rmsg) (VariantState rsta)
  uiVariant uis props =
    { init
    , update
    , view
    }

    where
    -- Fields

    init :: VariantState rsta
    init = initVariant props.initCase inits

    update :: VariantMsg rcase rmsg -> VariantState rsta -> VariantState rsta
    update = updateVariant inits updates

    view :: VariantState rsta -> srf (VariantMsg rcase rmsg)
    view = viewVariant { view: props.view } views

    -- Records

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
