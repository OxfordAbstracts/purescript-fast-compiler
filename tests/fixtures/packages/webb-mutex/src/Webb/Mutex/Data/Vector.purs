module Webb.Mutex.Data.Vector where

import Prelude

import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.Maybe (Maybe, isJust)
import Data.Newtype (class Newtype, unwrap, wrap, modify)


{- Provide proper language for the inner operations we want to perform. It is NOT 
  best-provided by the Array, since we may want to vary the actual type in the end.
-}

newtype Vector a = V (Array a)

derive newtype instance (Eq a) => Eq (Vector a)
derive newtype instance (Ord a) => Ord (Vector a)
derive newtype instance Show a => Show (Vector a)
derive newtype instance Semigroup (Vector a)
derive newtype instance Monoid (Vector a)
derive newtype instance Functor Vector
derive newtype instance Apply Vector
derive newtype instance Applicative Vector
derive newtype instance Bind Vector
derive newtype instance Monad Vector
derive instance Newtype (Vector a) _

fromArray :: forall a. Array a -> Vector a
fromArray = wrap

toArray :: forall a. Vector a -> Array a
toArray = unwrap

fromFoldable :: forall a f. Foldable f => f a -> Vector a
fromFoldable = fromArray <<< Array.fromFoldable

addLast :: forall a. a -> Vector a -> Vector a
addLast a = unwrap >>> flip Array.snoc a >>> wrap

addAllLast :: forall a f. Foldable f => f a -> Vector a -> Vector a
addAllLast items vec = vec <> (fromFoldable items)

addFirst :: forall a. a -> Vector a -> Vector a
addFirst a = unwrap >>> Array.cons a >>> wrap

addAllFirst :: forall a f. Foldable f => f a -> Vector a -> Vector a
addAllFirst items vec = (fromFoldable items) <> vec

drop :: forall a. Int -> Vector a -> Vector a
drop n = unwrap >>> Array.drop n >>> wrap

dropEnd :: forall a. Int -> Vector a -> Vector a
dropEnd n = unwrap >>> Array.dropEnd n >>> wrap

take :: forall a. Int -> Vector a -> Vector a
take n = unwrap >>> Array.take n >>> wrap

takeEnd :: forall a. Int -> Vector a -> Vector a
takeEnd n = unwrap >>> Array.takeEnd n >>> wrap

first :: forall a. Vector a -> Maybe a
first = unwrap >>> Array.head

tail :: forall a. Vector a -> Maybe (Vector a)
tail = unwrap >>> Array.tail >>> (wrap <$> _)

init :: forall a. Vector a -> Maybe (Vector a)
init = unwrap >>> Array.init >>> (wrap <$> _)

last :: forall a. Vector a -> Maybe a
last = unwrap >>> Array.last

reverse :: forall a. Vector a -> Vector a
reverse = unwrap >>> Array.reverse >>> wrap

empty :: forall a. Vector a
empty = wrap []

isEmpty :: forall a. Vector a -> Boolean
isEmpty = size >>> (_ <= 0)

size :: forall a. Vector a -> Int
size = unwrap >>> Array.length

find :: forall a. (a -> Boolean) -> Vector a -> Maybe a
find f = unwrap >>> Array.find f

canFind :: forall a. (a -> Boolean) -> Vector a -> Boolean
canFind f vec = isJust (find f vec)

findEq :: forall a. Eq a => a -> Vector a -> Maybe a
findEq a vec = find (_ == a) vec

canFindEq :: forall a. Eq a => a -> Vector a -> Boolean
canFindEq a vec = isJust (findEq a vec)

filter :: forall a. (a -> Boolean) -> Vector a -> Vector a
filter f = modify $ Array.filter f

reject :: forall a. (a -> Boolean) -> Vector a -> Vector a
reject f vec = filter (not <<< f) vec