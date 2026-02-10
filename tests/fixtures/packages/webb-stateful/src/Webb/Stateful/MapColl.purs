module Webb.Stateful.MapColl where

import Prelude
import Webb.State.Prelude

import Data.Array as A
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Traversable (for)
import Data.Tuple (Tuple)
import Effect.Class (class MonadEffect)
import Webb.Stateful (defaultCompare, defaultEq)

newtype MapColl k v = MC (ShowRef (Map k v))

derive newtype instance (Show k, Show v) => Show (MapColl k v)
derive newtype instance Refer (Map k v) (MapColl k v)

instance (Eq k, Eq v) => Eq (MapColl k v) where
  eq = defaultEq

instance (Ord k, Ord v) => Ord (MapColl k v) where
  compare = defaultCompare
  
newMap :: forall k v m. MonadEffect m => m (MapColl k v)
newMap = do
  ref <- newShowRef M.empty
  pure $ MC ref

newMap' :: forall k v m. Ord k => MonadEffect m => 
  Array (Tuple k v) -> m (MapColl k v)
newMap' arr = do
  ref <- newShowRef $ M.fromFoldable arr
  pure $ MC ref
  
insert :: forall k v m. Ord k => MonadEffect m =>
  MapColl k v -> k -> v -> m Unit
insert coll k v = M.insert k v :> coll

delete :: forall k v m. Ord k => MonadEffect m =>
  MapColl k v -> k -> m Unit
delete coll k = M.delete k :> coll

lookup :: forall k v m. Ord k => MonadEffect m =>
  MapColl k v -> k -> m (Maybe v)
lookup coll k = M.lookup k <: coll

member :: forall k v m. Ord k => MonadEffect m =>
  MapColl k v -> k -> m Boolean
member coll k = M.member k <: coll

update :: forall k v m . Ord k => MonadEffect m =>
  MapColl k v -> k -> v -> (v -> v) -> m Unit
update coll k default f = do
  M.alter alter k :> coll
  where
  alter mval = case mval of
    Nothing -> pure default
    Just val -> pure $ f val

keys :: forall k v m. MonadEffect m =>
  MapColl k v -> m (Set k)
keys coll = M.keys <: coll

values :: forall k v m. MonadEffect m =>
  MapColl k v -> m (Array v)
values coll = do 
  vals <- M.values <: coll
  pure $ A.fromFoldable vals
  
toUnfoldable :: forall k v m. MonadEffect m =>
  MapColl k v -> m (Array (Tuple k v))
toUnfoldable coll = do M.toUnfoldable <: coll

forEach :: forall k v b m. MonadEffect m =>
  MapColl k v -> (v -> m b) -> m (Map k b)
forEach coll f = do
  map <- aread coll
  for map f

forEach_ :: forall k v b m. MonadEffect m =>
  MapColl k v -> (v -> m b) -> m Unit
forEach_ coll f = void $ forEach coll f

length :: forall k v m. MonadEffect m =>
  MapColl k v -> m Int
length coll = M.size <: coll