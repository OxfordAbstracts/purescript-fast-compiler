module GoJS.Collection where

import Prelude

import Data.Foldable (class Foldable, foldl, foldr, foldMap)
import Data.List.Lazy (List, cons, nil)
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)

foreign import data Iterator_ :: Type -> Type
foreign import data Set_ :: Type -> Type
foreign import data List_ :: Type -> Type
foreign import data Map_ :: Type -> Type -> Type

foreign import iterate_ :: forall n. Iterator_ n -> Nullable n
foreign import toIterator_ :: forall iterator n. iterator n -> Iterator_ n
foreign import setFirst_ :: forall n. Set_ n -> Nullable n
foreign import insertAt_ :: forall n. Int -> n -> List_ n -> Effect Unit

-- GoJS provides no way of *constructing* an iterator, which is needed for foldable instances,
-- so we convert them to a lazy list and use that instance instead, since there's a conceptual similarity.
-- This is not the most efficient solution (especially for Sets) but it provides a sensible interface for now.
iteratorToList :: forall a. Iterator_ a -> List a
iteratorToList i = case toMaybe $ iterate_ i of
  Just x -> cons x (iteratorToList i)
  Nothing -> nil

instance iteratorFoldable :: Foldable Iterator_ where
  foldl f acc = foldl f acc <<< iteratorToList
  foldr f acc = foldr f acc <<< iteratorToList
  foldMap f = foldMap f <<< iteratorToList

instance setFoldable :: Foldable Set_ where
  foldl f acc = foldl f acc <<< toIterator_
  foldr f acc = foldr f acc <<< toIterator_
  foldMap f = foldMap f <<< toIterator_

instance listFoldable :: Foldable List_ where
  foldl f acc = foldl f acc <<< toIterator_
  foldr f acc = foldr f acc <<< toIterator_
  foldMap f = foldMap f <<< toIterator_

setFirst :: forall a. Set_ a -> Maybe a
setFirst = toMaybe <<< setFirst_