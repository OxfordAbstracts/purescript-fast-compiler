module MVC.Variant.Types
  ( CaseKey(..)
  , VariantMsg(..)
  , VariantState(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Show.Generic (genericShow)
import Data.Variant (class VariantEqs, class VariantShows, Variant)
import Data.Variant.Internal (class VariantTags)
import Prim.RowList (class RowToList)

newtype VariantState r = VariantState (Variant r)

data VariantMsg rcase rmsg
  = ChildCaseMsg (Variant rmsg)
  | ChangeCase (Variant rcase)
  | ErrMsg String

newtype CaseKey = CaseKey String

-----------------------------------------------------------
--- Instances
-----------------------------------------------------------

derive instance Eq CaseKey

derive instance Newtype CaseKey _

derive instance Newtype (VariantState r) _

derive instance Generic (VariantMsg rcase rmsg) _

derive instance Generic (VariantState r) _

instance
  ( RowToList rcase rlcase
  , RowToList rmsg rlmsg
  , VariantTags rlcase
  , VariantTags rlmsg
  , VariantShows rlcase
  , VariantShows rlmsg
  ) =>
  Show (VariantMsg rcase rmsg) where
  show = genericShow

derive instance
  ( RowToList rcase rlcase
  , RowToList rmsg rlmsg
  , VariantTags rlcase
  , VariantTags rlmsg
  , VariantEqs rlcase
  , VariantEqs rlmsg
  ) =>
  Eq (VariantMsg rcase rmsg)

instance
  ( RowToList r rl
  , VariantTags rl
  , VariantShows rl
  ) =>
  Show (VariantState r) where
  show = genericShow

derive instance
  ( RowToList r rl
  , VariantTags rl
  , VariantEqs rl
  ) =>
  Eq (VariantState r)