module Data.ResizeArray
  ( ResizeArray
  , cons
  , debug
  , drop
  , dropEnd
  , dropEndWhile
  , dropWhile
  , empty
  , emptyAt
  , fromArray
  , fromArrayAt
  , head
  , index
  , isEmpty
  , last
  , length
  , reindex
  , snoc
  , toArray
  , toList
  , toListWithIndices
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Foldable (class Foldable, foldMapDefaultL, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndexDefaultL, foldlWithIndex, foldrWithIndex)
import Data.List (List)
import Data.List as List
import Data.HashMap (HashMap)
import Data.HashMap as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))

type Map a b = HashMap a b

newtype ResizeArray a = ResizeArray
  { items :: Map Int a
  , anchorIndex :: Int -- The index before the head element
  }

isEmpty :: forall a. ResizeArray a -> Boolean
isEmpty (ResizeArray { items }) = Map.isEmpty items

length :: forall a. ResizeArray a -> Int
length (ResizeArray { items }) = Map.size items

index :: forall a. ResizeArray a -> Int -> Maybe a
index (ResizeArray { items }) idx = do
  Map.lookup idx items

getHeadIndex :: forall a. ResizeArray a -> Maybe Int
getHeadIndex ra@(ResizeArray { anchorIndex }) =
  if isEmpty ra then
    Nothing
  else
    Just (anchorIndex + 1)

getLastIndex :: forall a. ResizeArray a -> Maybe Int
getLastIndex ra@(ResizeArray { anchorIndex }) =
  if isEmpty ra then
    Nothing
  else
    Just (anchorIndex + length ra)

getNextHeadIndex :: forall a. ResizeArray a -> Int
getNextHeadIndex ra@(ResizeArray { anchorIndex }) =
  if isEmpty ra then
    anchorIndex + 1
  else
    anchorIndex

getNextLastIndex :: forall a. ResizeArray a -> Int
getNextLastIndex ra@(ResizeArray { anchorIndex }) =
  if isEmpty ra then
    anchorIndex + 1
  else
    anchorIndex + 1 + length ra

debug :: forall a. ResizeArray a -> (Int /\ Array (Int /\ a))
debug ra@(ResizeArray { anchorIndex }) =
  anchorIndex /\ List.toUnfoldable (toListWithIndices ra)

emptyAt :: forall a. Int -> ResizeArray a
emptyAt idx = ResizeArray { items: Map.empty, anchorIndex: idx - 1 }

empty :: forall a. ResizeArray a
empty = emptyAt 0

fromArrayAt :: forall a. Int -> Array a -> ResizeArray a
fromArrayAt idx arr =
  foldl snoc (emptyAt idx) arr

fromArray :: forall a. Array a -> ResizeArray a
fromArray = fromArrayAt 0

instance Show a => Show (ResizeArray a) where
  show ra@(ResizeArray { anchorIndex }) =
    let
      arr :: Array a
      arr = List.toUnfoldable (toList ra)

      at = anchorIndex + 1
    in
      "(fromArrayAt " <> show at <> " " <> show arr <> ")"

derive instance Eq a => Eq (ResizeArray a)

derive instance Functor ResizeArray

instance FoldableWithIndex Int ResizeArray where
  foldrWithIndex f z ra = case getLastIndex ra of
    Nothing -> z
    Just lastIndex ->
      mkFoldWithIndex { start: lastIndex, step: (_ - 1) } f z ra

  foldlWithIndex f z ra = case getHeadIndex ra of
    Nothing -> z
    Just headIndex ->
      mkFoldWithIndex { start: headIndex, step: (_ + 1) } (\idx -> flip $ f idx) z ra

  foldMapWithIndex = foldMapWithIndexDefaultL

mkFoldWithIndex :: forall a b. { start :: Int, step :: Int -> Int } -> (Int -> a -> b -> b) -> b -> ResizeArray a -> b
mkFoldWithIndex { start, step } f z (ResizeArray { items }) = tailRec go { idx: start, acc: z }
  where
  go { idx, acc } = case Map.lookup idx items of
    Just val -> Loop { idx: step idx, acc: f idx val acc }
    Nothing -> Done acc

instance Foldable ResizeArray where
  foldMap = foldMapDefaultL
  foldr f z = foldrWithIndex (\_ val acc -> f val acc) z
  foldl f z = foldlWithIndex (\_ acc val -> f acc val) z

toListWithIndices :: forall a. ResizeArray a -> List (Tuple Int a)
toListWithIndices ra = foldrWithIndex (\ix val -> List.Cons (Tuple ix val)) List.Nil ra

toList :: forall a. ResizeArray a -> List a
toList ra = foldr (\val acc -> List.Cons val acc) List.Nil ra

toArray :: forall a. ResizeArray a -> Array a
toArray = List.toUnfoldable <<< toList

snoc :: forall a. ResizeArray a -> a -> ResizeArray a
snoc ra@(ResizeArray { items, anchorIndex }) item =
  let
    nextLastIndex = getNextLastIndex ra
  in
    ResizeArray
      { items: Map.insert nextLastIndex item items
      , anchorIndex
      }

cons :: forall a. a -> ResizeArray a -> ResizeArray a
cons item ra@(ResizeArray { items }) =
  let
    nextHeadIndex = getNextHeadIndex ra
  in
    ResizeArray
      { items: Map.insert nextHeadIndex item items
      , anchorIndex: nextHeadIndex - 1
      }

reindex :: forall a. Int -> ResizeArray a -> ResizeArray a
reindex idx ra =
  foldl snoc (fromArrayAt idx []) (toList ra)

deleteHead :: forall a. ResizeArray a -> ResizeArray a
deleteHead ra@(ResizeArray { items, anchorIndex }) =
  case getHeadIndex ra of
    Nothing -> ra
    Just headIndex -> ResizeArray
      { items: Map.delete headIndex items
      , anchorIndex: anchorIndex + 1
      }

deleteLast :: forall a. ResizeArray a -> ResizeArray a
deleteLast ra@(ResizeArray { items, anchorIndex }) =
  case getLastIndex ra of
    Nothing -> ra
    Just lastIndex ->
      ResizeArray
        { items: Map.delete lastIndex items
        , anchorIndex
        }

drop :: forall a. Int -> ResizeArray a -> ResizeArray a
drop n ra = tailRec go { n, ra }
  where
  go acc | acc.n == 0 = Done acc.ra
  go acc = Loop { n: acc.n - 1, ra: deleteHead acc.ra }

dropEnd :: forall a. Int -> ResizeArray a -> ResizeArray a
dropEnd n ra = tailRec go { n, ra }
  where
  go acc | acc.n == 0 = Done acc.ra
  go acc = Loop { n: acc.n - 1, ra: deleteLast acc.ra }

head :: forall a. ResizeArray a -> Maybe a
head ra = case getHeadIndex ra of
  Just headIndex -> index ra headIndex
  Nothing -> Nothing

last :: forall a. ResizeArray a -> Maybe a
last ra = case getLastIndex ra of
  Just lastIndex -> index ra lastIndex
  Nothing -> Nothing

dropWhile :: forall a. (a -> Boolean) -> ResizeArray a -> ResizeArray a
dropWhile f ra = tailRec go ra
  where
  go acc = case head acc of
    Just headVal | f headVal -> Loop (drop 1 acc)
    _ -> Done acc

dropEndWhile :: forall a. (a -> Boolean) -> ResizeArray a -> ResizeArray a
dropEndWhile f ra = tailRec go ra
  where
  go acc = case last acc of
    Just lastVal | f lastVal -> Loop (deleteLast acc)
    _ -> Done acc

