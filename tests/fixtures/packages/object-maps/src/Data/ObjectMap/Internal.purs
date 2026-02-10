module Data.ObjectMap.Internal where

import Prelude

import Data.Argonaut.Core (stringify)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldl, foldr, foldMap)
import Data.FoldableWithIndex (class FoldableWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex)
import Data.Lens (lens)
import Data.Lens.AffineTraversal (affineTraversal)
import Data.Lens.At (class At)
import Data.Lens.Index (class Index)
import Data.Maybe (Maybe, maybe, maybe')
import Data.Traversable (class Traversable, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, traverseWithIndex)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Data.Tuple.Nested ((/\))
import Foreign.Object (Object)
import Foreign.Object as Obj

newtype ObjectMap k v = ObjectMap (Object (Tuple k v))

fromArray :: forall k v. EncodeJson k => Array (Tuple k v) -> ObjectMap k v
fromArray xs = xs
  <#> (\kv -> toJsonStr (fst kv) /\ kv)
  # Obj.fromFoldable
  # ObjectMap

toArray :: forall k v. ObjectMap k v -> Array (Tuple k v)
toArray (ObjectMap obj) = Obj.values obj

empty :: forall k v. ObjectMap k v
empty = ObjectMap $ Obj.empty

isEmpty :: forall k v. ObjectMap k v -> Boolean
isEmpty (ObjectMap obj) = Obj.isEmpty obj

size :: forall k v. ObjectMap k v -> Int
size (ObjectMap obj) = Obj.size obj

member :: forall k v. EncodeJson k => k -> ObjectMap k v -> Boolean
member key (ObjectMap obj) = Obj.member (toJsonStr key) obj

insert :: forall k v. EncodeJson k => k -> v -> ObjectMap k v -> ObjectMap k v
insert key val (ObjectMap obj) = ObjectMap $
  Obj.insert (toJsonStr key) (Tuple key val) obj

delete :: forall k v. EncodeJson k => k -> ObjectMap k v -> ObjectMap k v
delete key (ObjectMap obj) = ObjectMap $ Obj.delete (toJsonStr key) obj

lookup :: forall k v. EncodeJson k => k -> ObjectMap k v -> Maybe v
lookup key (ObjectMap obj) = Obj.lookup (toJsonStr key) obj <#> snd

-- | Insert, remove or update a value for a key in a map
alter :: forall k v. EncodeJson k => (Maybe v -> Maybe v) -> k -> ObjectMap k v -> ObjectMap k v
alter f key (ObjectMap obj) = ObjectMap $ Obj.alter f' (toJsonStr key) obj
  where
  f' v = (key /\ _) <$> f (snd <$> v)

-- | Remove or update a value for a key in a map
update :: forall k v. EncodeJson k => (v -> Maybe v) -> k -> ObjectMap k v -> ObjectMap k v
update f key (ObjectMap obj) = ObjectMap $ Obj.update f' (toJsonStr key) obj
  where
  f' v = (key /\ _) <$> f (snd v)

instance Functor (ObjectMap k) where
  map f (ObjectMap m) = ObjectMap $ m <#> \(k /\ v) -> k /\ f v

instance FunctorWithIndex k (ObjectMap k) where
  mapWithIndex f (ObjectMap m) = ObjectMap $ m <#> \(k /\ v) -> k /\ f k v

instance Foldable (ObjectMap k) where
  foldl f z (ObjectMap obj) = foldl (\y v -> f y (snd v)) z obj
  foldr f z (ObjectMap obj) = foldr (\v y -> f (snd v) y) z obj
  foldMap f (ObjectMap obj) = foldMap (f <<< snd) obj

instance FoldableWithIndex k (ObjectMap k) where
  foldlWithIndex f z (ObjectMap obj) = foldl (\y (k /\ v) -> f k y v) z obj
  foldrWithIndex f z (ObjectMap obj) = foldr (\(k /\ v) y -> f k v y) z obj
  foldMapWithIndex f (ObjectMap obj) = foldMap (uncurry f) obj

instance Traversable (ObjectMap k) where
  traverse = traverseWithIndex <<< const
  sequence = traverse identity

instance TraversableWithIndex k (ObjectMap k) where
  traverseWithIndex f (ObjectMap obj) = ObjectMap <$> traverse (\(k /\ v) -> (k /\ _) <$> f k v) obj

instance EncodeJson k => Index (ObjectMap k v) k v where
  ix k = affineTraversal set pre
    where
    set :: ObjectMap k v -> v -> ObjectMap k v
    set s b = insert k b s

    pre :: ObjectMap k v -> Either (ObjectMap k v) v
    pre s = maybe (Left s) Right $ lookup k s

instance EncodeJson k => At (ObjectMap k v) k v where
  at k =
    lens (lookup k) \m ->
      maybe' (\_ -> delete k m) \v -> insert k v m

toJsonStr :: forall a. EncodeJson a => a -> String
toJsonStr = encodeJson >>> stringify >>> enforceJsString

enforceJsString :: String -> String
enforceJsString x = ticks <> x <> ticks
  where
  ticks = "\""