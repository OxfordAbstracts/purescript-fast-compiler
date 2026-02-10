module MVC.Record.Types
  ( RecordMsg(..)
  , RecordState(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Variant (class VariantEqs, class VariantShows, Variant)
import Data.Variant.Internal (class VariantTags)
import Prim.RowList (class RowToList)

newtype RecordState r = RecordState (Record r)

newtype RecordMsg r = SetField (Variant r)

derive instance Generic (RecordMsg r) _

derive newtype instance (RowToList r rl, VariantTags rl, VariantEqs rl) => Eq (RecordMsg r)

instance (RowToList r rl, VariantTags rl, VariantShows rl) => Show (RecordMsg r) where
  show = genericShow

derive instance Generic (RecordState r) _

derive newtype instance (Eq (Record r)) => Eq (RecordState r)

instance (Show (Record r)) => Show (RecordState r) where
  show = genericShow