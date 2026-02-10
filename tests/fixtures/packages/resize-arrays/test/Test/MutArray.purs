module Test.MutArray where

import Prelude

import Data.Function.Uncurried (Fn2, mkFn2)
import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)

foreign import data MutArray :: Type -> Type

foreign import fromArrayImpl :: forall a. EffectFn1 (Array a) (MutArray a)

foreign import toArrayImpl :: forall a. EffectFn1 (MutArray a) (Array a)

foreign import shiftImpl :: forall a. EffectFn1 (MutArray a) Unit

foreign import unshiftImpl :: forall a. EffectFn2 a (MutArray a) Unit

foreign import popImpl :: forall a. EffectFn1 (MutArray a) Unit

foreign import pushImpl :: forall a. EffectFn2 a (MutArray a) Unit

foreign import foldlImpl :: forall a b. EffectFn3 (Fn2 b a b) b (MutArray a) b

foreign import foldrImpl :: forall a b. EffectFn3 (Fn2 a b b) b (MutArray a) b

foreign import lengthImpl :: forall a. MutArray a -> Int

foreign import mapImpl :: forall a b. EffectFn2 (a -> b) (MutArray a) (MutArray b)

foreign import lookupImpl :: forall a. EffectFn2 Int (MutArray a) (Nullable a)

fromArray :: forall a. Array a -> Effect (MutArray a)
fromArray = runEffectFn1 fromArrayImpl

toArray :: forall a. MutArray a -> Effect (Array a)
toArray = runEffectFn1 toArrayImpl

shift :: forall a. MutArray a -> Effect Unit
shift = runEffectFn1 shiftImpl

unshift :: forall a. a -> MutArray a -> Effect Unit
unshift = runEffectFn2 unshiftImpl

pop :: forall a. MutArray a -> Effect Unit
pop = runEffectFn1 popImpl

push :: forall a. a -> MutArray a -> Effect Unit
push = runEffectFn2 pushImpl

foldl :: forall a b. (b -> a -> b) -> b -> MutArray a -> Effect b
foldl f acc items = runEffectFn3 foldlImpl (mkFn2 f) acc items

foldr :: forall a b. (a -> b -> b) -> b -> MutArray a -> Effect b
foldr f acc items = runEffectFn3 foldrImpl (mkFn2 f) acc items

length :: forall a. MutArray a -> Int
length = lengthImpl

map :: forall a b. (a -> b) -> MutArray a -> Effect (MutArray b)
map = runEffectFn2 mapImpl

lookup :: forall a. Int -> MutArray a -> Effect (Maybe a)
lookup n items = do
  a <- runEffectFn2 lookupImpl n items
  pure $ toMaybe a
