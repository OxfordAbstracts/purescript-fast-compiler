module Data.Foldable.Extra
  ( partitionMaybe
  , mapMaybeAny
  , mapEither
  , occurrences
  , occurrencesMap
  , sameElements
  , groupMaybe
  , groupMaybeMap
  , allPredicate
  , anyPredicate
  ) where

import Control.Applicative (pure)
import Data.Array (findIndex, snoc, modifyAt)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Eq (class Eq, (/=), (==))
import Data.Foldable (all, elem, length, null, and, or)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Monoid (mempty, (<>))
import Data.Ord (class Ord)
import Data.Semiring ((+))
import Data.Traversable (class Foldable, foldl)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)


-- | Try to make a projection from an array. Return an array with the projection and the original array with the elements removed.
-- |
-- | ```purescript
-- | partitionMaybe (\x -> if x == "dog" then Just "cat" else Nothing) ["apple", "dog", "kiwi"] == { no: ["apple", "kiwi"], yes: ["cat"] }
-- | ```
partitionMaybe :: forall a b f. Foldable f => (a -> Maybe b) -> f a -> { no :: Array a, yes :: Array b }
partitionMaybe f xs = foldl go {yes: [], no: []} xs
  where go rec@{yes, no} x =
          case f x of
            Nothing -> rec {no  = no <> [x]}
            Just b  -> rec {yes = yes <> [b]}

-- | Map an array conditionally, only return the array when at least one element was mapped.
-- | Elements that are not mapped will keep the old value.
-- |
-- | ```purescript
-- | mapMaybeAny (\_ -> Nothing) [1,2,3] == Nothing
-- | mapMaybeAny (\x -> if x == 2 then Just 99 else Nothing) [1,2,3] == Just [1,99,3]
-- | ```
mapMaybeAny :: forall f a. Foldable f => (a -> Maybe a) -> f a -> Maybe (Array a)
mapMaybeAny f xs =
  let go (Tuple acc replaced) x = case f x of
          Nothing -> Tuple (acc <> pure x) replaced
          Just y  -> Tuple (acc <> pure y) true

      Tuple acc replaced = foldl go (Tuple mempty false) xs

  in  if replaced then
        Just acc
      else
        Nothing

-- | Map with a function that yields `Either`. Only succeeding when all elements where mapped to `Right`.
-- | Hint: if you don't care about collecting all the Left's (error conditions) and you are looking for a function like
-- | `forall a b c. (a -> Either c b) -> Array a -> Either c (Array b)` then use `traverse` from `Data.Traversable`.
mapEither :: forall a b c f. Foldable f => (a -> Either c b) -> f a -> Either (Array c) (Array b)
mapEither f foldable =
  let {lefts, rights} = foldl (g f) {lefts: [], rights: []} foldable
  in  if null lefts then
          Right rights
        else
          Left lefts
  where g :: forall q r s. (q -> Either s r) -> {lefts :: Array s, rights :: Array r} -> q -> {lefts :: Array s, rights :: Array r}
        g f2 {lefts, rights} elem = case f2 elem of
          Left l -> {lefts: lefts <> [l], rights}
          Right r -> {lefts, rights: rights <> [r]}

-- | Count the amount of times a value occurs in an array.
-- | Mostly useful for when you can not define an Ord instance
-- |
-- | ```purescript
-- | occurrences ["A", "B", "B"] == [Tuple "A" 1, Tuple "B" 2]
-- | ```
occurrences :: forall a f. Eq a => Foldable f => f a -> Array (Tuple a Int)
occurrences xs = foldl go [] xs
  where go acc x = modifyOrSnoc (\(Tuple k _) -> k == x) (\(Tuple k v) -> Tuple k (v + 1)) acc (Tuple x 1)

-- | Count the amount of times a value occurs in an array.
-- | Requires an Ord instance for Map. This function should be faster than `occurrences`
-- |
-- | ```purescript
-- | occurrencesMap ["A", "B", "B"] == Map.fromList [Tuple "A" 1, Tuple "B" 2]
-- | ```
occurrencesMap :: forall a f. Foldable f => Ord a => f a -> Map a Int
occurrencesMap xs = foldl go Map.empty xs
  where go acc x = Map.insertWith (\old _ -> old + 1) x 1 acc

-- | Checks if two arrays have exactly the same elements.
-- | The order of elements does not matter.
-- |
-- | ```purescript
-- | sameElements ["A", "B", "B"] ["B", "A", "B"] == true
-- | sameElements ["A", "B", "B"] ["A", "B"] == false
-- | ```
sameElements :: forall a f. Foldable f => Eq a => f a -> f a -> Boolean
sameElements a b =
  let l_a = length a :: Int
      l_b = length b :: Int
  in  if l_a /= l_b then false else
        let occ_a = occurrences a
            occ_b = occurrences b
            go :: Tuple a Int -> Boolean
            go x = x `elem` occ_b
        in  all go occ_a

-- | Similar to `group`, adds the ability to group by a projection.
-- | The projection is returned as the first argument of the Tuple.
-- |
-- | ```purescript
-- | groupMaybe (\x -> Just $ if even x then "even" else "odd") [1,2,3] == [(Tuple "odd" [1,3]), (Tuple "even" [2])]
-- | ```
groupMaybe :: forall f a b. Foldable f => Eq b => (a -> Maybe b) -> f a -> Array (Tuple b (NonEmptyArray a))
groupMaybe f xs =
  let g :: Array (Tuple b (NonEmptyArray a)) -> a -> Array (Tuple b (NonEmptyArray a))
      g acc x = case f x of
        Nothing -> acc
        Just v  -> modifyOrSnoc (\(Tuple acc_b _) -> acc_b == v) (\(Tuple acc_b nea) -> Tuple acc_b (NEA.snoc nea x)) acc (Tuple v (NEA.singleton x))
  in  foldl g [] xs

-- | Similar to `groupMaybe`, adds the ability to map over the thing being grouped.
-- | Useful for removing data that was only there to do the grouping.
-- |
-- | ```purescript
-- | groupMaybeMap (\x -> Just $ if even x then "even" else "odd") (*3) [1,2,3] == [(Tuple "odd" [3,9]), (Tuple "even" [6])]
-- | groupMaybeMap f identity xs = groupMaybe f xs
-- | ```
groupMaybeMap :: forall a b c f. Foldable f => Eq b => (a -> Maybe b) -> (a -> c) -> f a -> Array (Tuple b (NonEmptyArray c))
groupMaybeMap f g xs =
  let h :: Array (Tuple b (NonEmptyArray c)) -> a -> Array (Tuple b (NonEmptyArray c))
      h acc x = case f x of
        Nothing -> acc
        Just v  -> modifyOrSnoc (\(Tuple acc_b _) -> acc_b == v) (\(Tuple acc_b nea) -> Tuple acc_b (NEA.snoc nea (g x))) acc (Tuple v (NEA.singleton (g x)))
  in  foldl h [] xs

-- | Combines multiple predicates into one. All have to match.
-- | This function is an alias for `Foldable.and`, since HeytingAlgebras lift over functions.
-- |
-- | ```purescript
-- | let preds = allPredicate [(_ > 5), (_ > 10)]
-- | all preds [10,20] == true
-- | all preds [5,10,20] == false
-- | any preds [1,5,10] == true
-- | any preds [1,5] == false
-- | ```
allPredicate :: forall f a. Foldable f => f (a -> Boolean) -> (a -> Boolean)
allPredicate = and

-- | Combines multiple predicates into one. Only one has to match.
-- | This function is an alias for `Foldable.or`, since HeytingAlgebras lift over functions.
-- |
-- | ```purescript
-- | let preds = anyPredicate [(_ > 5), (_ > 10)]
-- | all preds [5,10] == true
-- | all preds [1,5,10] == false
-- | any preds [1,5] == true
-- | any preds [1] == false
-- | ```
anyPredicate :: forall f a. Foldable f => f (a -> Boolean) -> (a -> Boolean)
anyPredicate = or

-- Not exported
modifyOrSnoc :: forall a. (a -> Boolean) -> (a -> a) -> Array a -> a -> Array a
modifyOrSnoc f modifier xs x = case findIndex f xs of
  Nothing  -> snoc xs x
  Just idx -> unsafePartial (fromJust (modifyAt idx modifier xs))
