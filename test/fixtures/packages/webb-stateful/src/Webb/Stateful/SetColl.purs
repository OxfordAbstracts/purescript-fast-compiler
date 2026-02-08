module Webb.Stateful.SetColl where

import Prelude
import Webb.State.Prelude

import Data.Set as S
import Data.Traversable (for)
import Effect.Class (class MonadEffect)
import Webb.Stateful (defaultCompare, defaultEq)


newtype SetColl a = SC (ShowRef (S.Set a))

derive newtype instance Show a => Show (SetColl a)
derive newtype instance Refer (S.Set a) (SetColl a)

instance Eq a => Eq (SetColl a) where
  eq = defaultEq
  
instance Ord a => Ord (SetColl a) where
  compare = defaultCompare
  
newSet :: forall a m. MonadEffect m => m (SetColl a)
newSet = do
  ref <- newShowRef S.empty
  pure $ SC ref

newSet' :: forall a m. Ord a => MonadEffect m => Array a -> m (SetColl a)
newSet' arr = do
  ref <- newShowRef $ S.fromFoldable arr
  pure $ SC ref

insert :: forall a m. Ord a => MonadEffect m => SetColl a -> a -> m Unit
insert coll a = do S.insert a :> coll

delete :: forall a m. Ord a => MonadEffect m => SetColl a -> a -> m Unit
delete coll a = do S.delete a :> coll

member :: forall a m. Ord a => MonadEffect m => SetColl a -> a -> m Boolean
member coll a = do S.member a <: coll

forEach :: forall a b m. Ord a => Ord b => MonadEffect m => 
  SetColl a -> (a -> m b) -> m (S.Set b)
forEach coll f = do
  set <- aread coll
  let arr = S.toUnfoldable set :: Array _
  arr' <- for arr f
  pure $ S.fromFoldable arr'

forEach_ :: forall a b m. Ord a => Ord b => MonadEffect m => 
  SetColl a -> (a -> m b) -> m Unit
forEach_ coll f = void $ forEach coll f

length :: forall a m. MonadEffect m => SetColl a -> m Int
length coll = areads S.size coll