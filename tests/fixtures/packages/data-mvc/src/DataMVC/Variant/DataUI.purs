module DataMVC.Variant.DataUI
  ( class DataUiVariant
  , dataUiVariant
  ) where

import Data.Variant (Variant)
import DataMVC.ApplyCtx (class ApplyCtx, mapApplyCtx)
import DataMVC.Types.DataUI (DataUI(..), DataUICtx)
import DataMVC.Variant.DataUiInterface (class DataUiInterfaceVariant, DataUiInterfaceVariantProps, dataUiInterfaceVariant)
import MVC.Variant.Types (VariantMsg, VariantState)
import Type.Proxy (Proxy)

class
  DataUiVariant
    (datauis :: Row Type)
    (fm :: Type -> Type)
    (fs :: Type -> Type)
    (srf :: Type -> Type)
    (initsym :: Symbol)
    (rcase :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
    (r :: Row Type)
  | datauis -> fm fs srf initsym rcase rmsg rsta r
  where
  dataUiVariant
    :: Record datauis
    -> Proxy initsym
    -> DataUiInterfaceVariantProps srf initsym
    -> DataUI srf fm fs (VariantMsg rcase rmsg) (VariantState rsta) (Variant r)

instance
  ( ApplyCtx (DataUICtx srf fm fs) datauis uis
  , DataUiInterfaceVariant uis srf initsym rcase rmsg rsta r
  ) =>
  DataUiVariant datauis fm fs srf initsym rcase rmsg rsta r
  where
  dataUiVariant
    :: Record datauis
    -> Proxy initsym
    -> DataUiInterfaceVariantProps srf initsym
    -> DataUI srf fm fs (VariantMsg rcase rmsg) (VariantState rsta) (Variant r)
  dataUiVariant datauis prxInitSym props =
    DataUI \ctx ->
      let
        uis :: Record uis
        uis = mapApplyCtx ctx datauis
      in
        dataUiInterfaceVariant uis prxInitSym props
