module DataMVC.Types.DataUI
  ( DataUI(..)
  , DataUICtx(..)
  , DataUICtxImpl
  , DataUiInterface(..)
  , RefineDataResults
  , applyDataUi
  , applyWrap
  , dataUiInterfaceToUI
  , refineDataUi
  , runDataUi
  , runDataUiFinal
  , unDataUICtx
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Newtype as NT
import Data.Profunctor (lcmap)
import DataMVC.Types.DataError (DataResult)
import MVC.Types as MVC

newtype DataUI srf fm fs msg sta a =
  DataUI
    (DataUICtx srf fm fs -> DataUiInterface srf msg sta a)

newtype DataUiInterface srf msg sta a =
  DataUiInterface
    { init :: Maybe a -> sta
    , update :: msg -> sta -> sta
    , view :: sta -> srf msg
    , extract :: sta -> DataResult a
    , name :: String
    }

newtype DataUICtx html fm fs =
  DataUICtx (DataUICtxImpl html fm fs)

type DataUICtxImpl html fm fs =
  { wrap ::
      forall msg sta a
       . DataUiInterface html msg sta a
      -> DataUiInterface html (fm msg) (fs sta) a
  }

type Extract sta a = sta -> DataResult a

type Update msg sta = msg -> sta -> sta

type Init sta a = Maybe a -> sta

type View :: (Type -> Type) -> Type -> Type -> Type
type View srf msg sta = sta -> srf msg

--------------------------------------------------------------------------------
--- 
--------------------------------------------------------------------------------

runDataUi
  :: forall srf fm fs msg sta a
   . DataUI srf fm fs msg sta a
  -> DataUICtx srf fm fs
  -> DataUiInterface srf msg sta a
runDataUi (DataUI dataUi) ctx = dataUi ctx

runDataUiFinal
  :: forall srf fm fs msg sta a
   . DataUI srf fm fs msg sta a
  -> DataUICtx srf fm fs
  -> DataUiInterface srf (fm msg) (fs sta) a
runDataUiFinal dataUi ctx = runDataUi (applyWrap dataUi) ctx

applyWrap
  :: forall srf fm fs msg sta a
   . DataUI srf fm fs msg sta a
  -> DataUI srf fm fs (fm msg) (fs sta) a
applyWrap (DataUI mkDataUi) = DataUI \c@(DataUICtx ctx) ->
  ctx.wrap $ mkDataUi c

applyDataUi
  :: forall html fm fs msg1 msg2 sta1 sta2 a1 a2
   . { extract :: Extract sta1 a1 -> Extract sta2 a2
     , init :: Init sta1 a1 -> Init sta2 a2
     , name :: String
     , update :: Update msg1 sta1 -> Update msg2 sta2
     , view :: View html msg1 sta1 -> View html msg2 sta2
     }
  -> DataUI html fm fs msg1 sta1 a1
  -> DataUI html fm fs msg2 sta2 a2
applyDataUi r ui1 = DataUI \ctx -> DataUiInterface
  { name: r.name
  , view:
      r.view (NT.unwrap $ runDataUi ui1 ctx).view
  , extract:
      r.extract (NT.unwrap $ runDataUi ui1 ctx).extract
  , update:
      r.update (NT.unwrap $ runDataUi ui1 ctx).update
  , init:
      r.init (NT.unwrap $ runDataUi ui1 ctx).init
  }

type RefineDataResults a b =
  { typeName :: String
  , refine :: a -> DataResult b
  , unrefine :: b -> a
  }

refineDataUi :: forall srf fm fs msg sta a b. RefineDataResults a b -> DataUI srf fm fs msg sta a -> DataUI srf fm fs msg sta b
refineDataUi { typeName, refine, unrefine } (DataUI mkDataUi) = DataUI \ctx ->
  let
    DataUiInterface dataUi = mkDataUi ctx
  in
    DataUiInterface
      { extract: dataUi.extract >=> refine
      , init: lcmap (map unrefine) dataUi.init
      , name: typeName
      , update: dataUi.update
      , view: dataUi.view
      }

dataUiInterfaceToUI :: forall html msg sta a. DataUiInterface html msg sta a -> MVC.UI html msg sta
dataUiInterfaceToUI (DataUiInterface dataUi) =
  { init: dataUi.init Nothing
  , update: dataUi.update
  , view: dataUi.view
  }

unDataUICtx :: forall html fm fs. DataUICtx html fm fs -> DataUICtxImpl html fm fs
unDataUICtx (DataUICtx impl) = impl

--------------------------------------------------------------------------------
--- Instances
--------------------------------------------------------------------------------

derive instance Newtype (DataUI srf fm fs msg sta a) _

derive instance Newtype (DataUiInterface srf msg sta a) _

