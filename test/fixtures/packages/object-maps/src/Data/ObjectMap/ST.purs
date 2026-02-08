module Data.ObjectMap.ST
  ( STObjectMap
  , delete
  , freeze
  , new
  , peek
  , poke
  , modify
  , run
  , thaw
  , unsafeFreeze
  ) where

import Prelude

import Control.Monad.ST (ST)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Maybe (Maybe(..))
import Data.ObjectMap.Internal as OM
import Data.Tuple (Tuple, snd)
import Data.Tuple.Nested ((/\))
import Foreign.Object as O
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STO
import Foreign.Object.ST.Unsafe as STOU
import Unsafe.Coerce (unsafeCoerce)

newtype STObjectMap r k v = STObjectMap (STObject r (Tuple k v))

-- | Create a new, empty mutable map
new :: forall r k v. ST r (STObjectMap r k v)
new = STObjectMap <$> STO.new

-- | Get the value for a key in a mutable map
peek :: forall r k v. EncodeJson k => k -> STObjectMap r k v -> ST r (Maybe v)
peek k (STObjectMap m) = map snd <$> STO.peek (OM.toJsonStr k) m

-- | Update the value for a key in a mutable map
poke :: forall r k v. EncodeJson k => k -> v -> STObjectMap r k v -> ST r (STObjectMap r k v)
poke k v (STObjectMap m) = STObjectMap <$> STO.poke (OM.toJsonStr k) (k /\ v) m

-- | Remove a key and the corresponding value from a mutable map
delete :: forall r k v. EncodeJson k => k -> STObjectMap r k v -> ST r (STObjectMap r k v)
delete k (STObjectMap m) = STObjectMap <$> STO.delete (OM.toJsonStr k) m

-- | Similar to alter but for mutable maps
modify :: forall r k v. EncodeJson k => k -> (Maybe v -> Maybe v) -> STObjectMap r k v -> ST r (STObjectMap r k v)
modify key f m = do
  mv <- f <$> peek key m
  case mv of
    Nothing -> delete key m
    Just v -> poke key v m

-- | Convert an immutable map into a mutable map
thaw :: forall r k v. OM.ObjectMap k v -> ST r (STObjectMap r k v)
thaw (OM.ObjectMap m) = STObjectMap <$> O.thawST m

run :: forall k v. (forall r. ST r (STObjectMap r k v)) -> OM.ObjectMap k v
run = unsafeCoerce O.runST

-- | Convert a mutable map into an immutable map
freeze :: forall r k v. STObjectMap r k v -> ST r (OM.ObjectMap k v)
freeze (STObjectMap m) = OM.ObjectMap <$> O.freezeST m

-- | Unsafely get the map out of ST without copying it
unsafeFreeze :: forall r k v. STObjectMap r k v -> ST r (OM.ObjectMap k v)
unsafeFreeze (STObjectMap m) = OM.ObjectMap <$> STOU.unsafeFreeze m