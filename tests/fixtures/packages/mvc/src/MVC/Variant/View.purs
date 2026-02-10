module MVC.Variant.View
  ( ViewArgs
  , ViewVariantProps
  , caseKeyToVariant
  , caseKeyToVariantRL
  , class CaseKeyToVariant
  , class CaseKeyToVariantRL
  , class GetKeys
  , class GetSym
  , class GetSymRL
  , class ViewVariant
  , class ViewVariantRL
  , getKeys
  , getSym
  , getSymRL
  , viewVariant
  , viewVariantRL
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant)
import Data.Variant as V
import MVC.Variant.Types (CaseKey(..), VariantMsg(..), VariantState(..))
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Type.Proxy (Proxy(..))

type ViewArgs src msg =
  { viewCase :: src msg
  , mkMsg :: CaseKey -> msg
  , caseKey :: CaseKey
  , caseKeys :: Array CaseKey
  }

type ViewVariantProps html =
  { view :: forall msg. ViewArgs html msg -> html msg
  }

--------------------------------------------------------------------------------
--- ViewVariant
--------------------------------------------------------------------------------

class
  ViewVariant
    (html :: Type -> Type)
    (views :: Row Type)
    (rcase :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  where
  viewVariant
    :: ViewVariantProps html
    -> (Record views -> VariantState rsta -> html (VariantMsg rcase rmsg))

instance
  ( ViewVariantRL rl html views rmsg rsta
  , RowToList views rl
  , CaseKeyToVariant rcase
  , Functor html
  , GetKeys rl
  , GetSym rsta
  ) =>
  ViewVariant html views rcase rmsg rsta
  where
  viewVariant
    :: ViewVariantProps html
    -> (Record views -> VariantState rsta -> html (VariantMsg rcase rmsg))
  viewVariant d views (VariantState rsta) = viewUser'
    where
    viewCases :: html (Variant rmsg)
    viewCases = viewVariantRL prxRl views rsta

    viewCases' :: html (VariantMsg rcase rmsg)
    viewCases' = viewCases # map ChildCaseMsg

    caseKeyToVariantMsg :: CaseKey -> VariantMsg rcase rmsg
    caseKeyToVariantMsg = caseKeyToVariant >>> case _ of
      Nothing -> ErrMsg "Invalid case provided by user view"
      Just vcase -> ChangeCase vcase

    viewUser' :: html (VariantMsg rcase rmsg)
    viewUser' = d.view
      { viewCase: viewCases'
      , mkMsg: caseKeyToVariantMsg
      , caseKey: CaseKey $ getSym rsta
      , caseKeys: CaseKey <$> getKeys prxRl
      }

    prxRl :: Proxy rl
    prxRl = Proxy

--------------------------------------------------------------------------------
--- CaseKeyToVariant
--------------------------------------------------------------------------------

class
  CaseKeyToVariant
    (rcase :: Row Type)
  where
  caseKeyToVariant :: CaseKey -> Maybe (Variant rcase)

instance
  ( CaseKeyToVariantRL rl rcase
  , RowToList rcase rl
  ) =>
  CaseKeyToVariant rcase
  where
  caseKeyToVariant :: CaseKey -> Maybe (Variant rcase)
  caseKeyToVariant = caseKeyToVariantRL (Proxy :: Proxy rl)

--------------------------------------------------------------------------------
--- CaseKeyToVariantRL
--------------------------------------------------------------------------------

class
  CaseKeyToVariantRL
    (rl :: RowList Type)
    (rcase :: Row Type)
  | rl -> rcase
  where
  caseKeyToVariantRL :: Proxy rl -> CaseKey -> Maybe (Variant rcase)

instance CaseKeyToVariantRL RL.Nil ()
  where
  caseKeyToVariantRL :: Proxy RL.Nil -> CaseKey -> Maybe (Variant ())
  caseKeyToVariantRL _ _ = Nothing

instance
  ( CaseKeyToVariantRL rl' rcase'
  , Row.Cons sym Unit rcase' rcase
  , Row.Lacks sym rcase'
  , IsSymbol sym
  , Row.Union rcase' rcasex rcase
  ) =>
  CaseKeyToVariantRL (RL.Cons sym x rl') rcase
  where
  caseKeyToVariantRL :: Proxy (RL.Cons sym x rl') -> CaseKey -> Maybe (Variant rcase)
  caseKeyToVariantRL _ givenKey =
    if caseKey == givenKey then
      head
    else
      tail'

    where
    caseKey = CaseKey $ reflectSymbol prxSym

    head :: Maybe (Variant rcase)
    head = Just $ V.inj prxSym unit

    tail :: Maybe (Variant rcase')
    tail = caseKeyToVariantRL prxRl' givenKey

    tail' :: Maybe (Variant rcase)
    tail' = tail # map V.expand

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRl' :: Proxy rl'
    prxRl' = Proxy

--------------------------------------------------------------------------------
--- ViewVariantRL
--------------------------------------------------------------------------------

class
  ViewVariantRL
    (rl :: RowList Type)
    (html :: Type -> Type)
    (views :: Row Type)
    (rmsg :: Row Type)
    (rsta :: Row Type)
  | rl -> rmsg rsta
  where
  viewVariantRL :: Proxy rl -> Record views -> Variant rsta -> html (Variant rmsg)

instance ViewVariantRL RL.Nil html views () () where
  viewVariantRL :: Proxy RL.Nil -> Record views -> Variant () -> html (Variant ())
  viewVariantRL _ _ = V.case_

instance
  ( ViewVariantRL rl' html views rmsg' rsta'
  , Row.Cons sym msg rmsg' rmsg
  , Row.Cons sym sta rsta' rsta
  , Row.Cons sym (sta -> html msg) viewsx views
  , Row.Lacks sym rmsg'
  , Row.Lacks sym rsta'
  , Functor html
  , IsSymbol sym
  , Row.Union rmsg' rmsgx rmsg
  ) =>
  ViewVariantRL (RL.Cons sym x rl') html views rmsg rsta
  where
  viewVariantRL :: Proxy (RL.Cons sym x rl') -> Record views -> Variant rsta -> html (Variant rmsg)
  viewVariantRL _ views =
    tail'
      # V.on prxSym viewFn'

    where
    tail :: Variant rsta' -> html (Variant rmsg')
    tail = viewVariantRL prxRl' views

    tail' :: Variant rsta' -> html (Variant rmsg)
    tail' = tail >>> map V.expand

    viewFn :: sta -> html msg
    viewFn = Record.get prxSym views

    viewFn' :: sta -> html (Variant rmsg)
    viewFn' = viewFn >>> map (V.inj prxSym)

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRl' :: Proxy rl'
    prxRl' = Proxy

--------------------------------------------------------------------------------
-- GetKeys
--------------------------------------------------------------------------------

class GetKeys (rl :: RowList Type) where
  getKeys :: Proxy rl -> Array String

instance GetKeys RL.Nil where
  getKeys :: Proxy RL.Nil -> Array String
  getKeys _ = []

instance (IsSymbol sym, GetKeys rl') => GetKeys (RL.Cons sym a rl') where
  getKeys :: Proxy (RL.Cons sym a rl') -> Array String
  getKeys _ = [ head ] <> tail
    where
    head :: String
    head = reflectSymbol prxSym

    tail :: Array String
    tail = getKeys prxRl'

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRl' :: Proxy rl'
    prxRl' = Proxy

--------------------------------------------------------------------------------
-- GetSym
--------------------------------------------------------------------------------

class GetSym (r :: Row Type) where
  getSym :: Variant r -> String

instance
  ( RowToList r rl
  , GetSymRL rl r
  ) =>
  GetSym r
  where
  getSym :: Variant r -> String
  getSym = getSymRL (Proxy :: Proxy rl)

--------------------------------------------------------------------------------
--- GetSymRL
--------------------------------------------------------------------------------

class
  GetSymRL
    (rl :: RowList Type)
    (r :: Row Type)
  | rl -> r
  where
  getSymRL :: Proxy rl -> Variant r -> String

instance GetSymRL RL.Nil () where
  getSymRL :: Proxy RL.Nil -> Variant () -> String
  getSymRL _ = V.case_

instance
  ( GetSymRL rl' r'
  , Row.Cons sym a r' r
  , IsSymbol sym
  , Row.Lacks sym r'
  , Row.Union r' rx r
  ) =>
  GetSymRL (RL.Cons sym a rl') r
  where
  getSymRL :: Proxy (RL.Cons sym a rl') -> Variant r -> String
  getSymRL _ =
    getSymRL prxRl'
      # V.on prxSym getSym'

    where
    getSym' :: a -> String
    getSym' _ = reflectSymbol prxSym

    prxSym :: Proxy sym
    prxSym = Proxy

    prxRl' :: Proxy rl'
    prxRl' = Proxy
