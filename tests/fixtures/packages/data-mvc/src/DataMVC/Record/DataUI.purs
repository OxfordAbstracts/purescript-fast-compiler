module DataMVC.Record.DataUI
  ( class DataUiRecord
  , dataUiRecord
  ) where

import DataMVC.ApplyCtx (class ApplyCtx, mapApplyCtx)
import DataMVC.Record.DataUiInterface (class DataUiInterfaceRecord, dataUiInterfaceRecord)
import DataMVC.Types.DataUI (DataUI(..), DataUICtx)
import MVC.Record (RecordMsg, RecordState)
import MVC.Record.UI (UIRecordProps)

class
  DataUiRecord
    (datauis :: Row Type)
    (fm :: Type -> Type)
    (fs :: Type -> Type)
    (srf :: Type -> Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
    (r :: Row Type)
  | datauis -> fm fs srf rmsg rsta r
  where
  dataUiRecord
    :: UIRecordProps srf (RecordMsg rmsg) (RecordState rsta)
    -> Record datauis
    -> DataUI srf fm fs (RecordMsg rmsg) (RecordState rsta) (Record r)

instance
  ( ApplyCtx (DataUICtx srf fm fs) datauis uis
  , DataUiInterfaceRecord uis srf rmsg rsta r
  ) =>
  DataUiRecord datauis fm fs srf rmsg rsta r
  where
  dataUiRecord
    :: UIRecordProps srf (RecordMsg rmsg) (RecordState rsta)
    -> Record datauis
    -> DataUI srf fm fs (RecordMsg rmsg) (RecordState rsta) (Record r)
  dataUiRecord props datauis = DataUI \ctx ->
    let
      uis :: Record uis
      uis = mapApplyCtx ctx datauis
    in
      dataUiInterfaceRecord props uis

