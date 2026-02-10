-- | This module provides various adapters and other such utilities
-- | for `Unfoldable1`.

module Data.Unfoldable1.Trivial1
  ( module Reexports
  , refoldl1
  , refoldr1
  , refoldMap1
  , refold1
  , foldEnum
  , unfoldrInf
  , iterate
  , repeat
  , head1
  , last1
  , take1
  , index1
  , append1
  , append1'
  ) where

import Data.Unfoldable1.Trivial1.Internal
  ( Trivial1
  , trivial1
  , turbofish1
  , (::<+>)
  , uncons1) as Reexports

import Prelude

import Data.Unfoldable1.Trivial1.Internal
  ( Trivial1
  , (::<+>)
  , untrivial1
  , runTrivial1
  , Generator1
  )
import Data.Unfoldable.Trivial.Internal
  ( Trivial
  , untrivial
  , Generator
  )


import Data.Unfoldable1 (class Unfoldable1, unfoldr1)
import Data.Semigroup.Foldable (foldl1, foldr1, foldMap1, fold1)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..), note)
import Data.Enum (class BoundedEnum, upFromIncluding)
import Data.Tuple (fst)
import Data.Tuple.Nested ((/\), type (/\))
import Data.Newtype (un)
import Data.Semigroup.Last (Last(..))

-- | Returns the first element.
head1 :: forall a. Trivial1 a -> a
head1 = untrivial1 eHead1
  where eHead1 :: forall b. Generator1 a b -> b -> a
        eHead1 f seed = fst $ f seed

-- | Returns the last element.
last1 :: forall a. Trivial1 a -> a
last1 = un Last <<< foldMap1 Last

-- | Keep only a strictly positive number of elements from the start.
take1 :: forall a u. Unfoldable1 u => Int -> Trivial1 a -> u a
take1 n = untrivial1 eTake1
  where eTake1 :: forall b. Generator1 a b -> b -> u a
        eTake1 f seed = unfoldr1 taker $ n /\ seed
          where taker :: Generator1 a (Int /\ b)
                taker (m /\ b)
                  | m <= 1 = Nothing <$ f b
                  | otherwise = map ((/\) (m - 1)) <$> f b

-- | Get the element at the specified *modular* 0-index, i.e. the element
-- | at that 0-index in the elements infinitely extended left and right.
-- |
-- | Will loop infinitely if given an infinite `Unfoldable1` and a negative index.
-- | Will not loop infinitely if given an infinite `Unfoldable1` and a nonnegative index;
-- | computes the length for itself as it iterates. Iterates twice when resolving an out of
-- | bounds index; does not store any intermediate results. In general, this function is
-- | not supposed to be *used for modular indexing*, because modular indexing just happens
-- | to be a simple and sensible way to guarantee an output, and there's no point in this
-- | existing without a guaranteed output (just use `index`).
-- | If you want modular indexing for the mod, please use an actual container.
-- TODO: something that actually does collect the last n in one pass? either a function like this or a straight up newtype. actually no that's stupid because if you do a normal list it can just get GCed anyways :p or wait no it can't because no tail recursion modulo cons huh
index1 :: forall a. Trivial1 a -> Int -> a
index1 t i = untrivial1 eIndex1 t
  where eIndex1 :: forall b. Generator1 a b -> b -> a
        eIndex1 f seed = index1' 0 $ f seed
          where index1' :: Int -> a /\ Maybe b -> a
                index1' n (a /\ _)
                  | n == i = a
                index1' n (_ /\ Nothing) = index1 t $ mod i $ n + 1
                index1' n (_ /\ Just b) = index1' (n + 1) $ f b

-- | `foldl1` specialized to `Trivial1`. "Re-fold" a polymorphic `Unfoldable1`.
-- | Usually cleaner and more convenient than `turbofish`, when applicable.
refoldl1 :: forall a. (a -> a -> a) -> Trivial1 a -> a
refoldl1 = foldl1

-- | `foldr1` specialized to `Trivial1`. "Re-fold" a polymorphic `Unfoldable1`.
-- | Usually cleaner and more convenient than `turbofish`, when applicable.
refoldr1 :: forall a. (a -> a -> a) -> Trivial1 a -> a
refoldr1 = foldr1

-- | `foldMap` specialized to `Trivial1`. "Re-fold" a polymorphic `Unfoldable1`.
-- | Usually cleaner and more convenient than `turbofish1`, when applicable.
refoldMap1 :: forall a c. Semigroup c => (a -> c) -> Trivial1 a -> c
refoldMap1 = foldMap1

-- | `fold` specialized to `Trivial1`. "Re-fold" a polymorphic `Unfoldable1`.
-- | Usually cleaner and more convenient than `turbofish1`, when applicable.
refold1 :: forall a. Semigroup a => Trivial1 a -> a
refold1 = fold1

-- | Map each element of a `BoundedEnum` into a semigroup,
-- | and combine the results through `refold1`.
foldEnum :: forall a b. BoundedEnum a => Semigroup b => (a -> b) -> b
foldEnum = flip foldMap1 ::<+> upFromIncluding bottom

-- | Unfold an infinite `Unfoldable1`.
-- | Analogous to `unfold1` and `unfold`, but with no way to signal termination;
-- | `unfoldInf f b` consists of `fst $ f b` appended to `unfoldInf f $ snd $ f b`.
-- |
-- | This should only be used to produce either lazy types (like lazy `List`s) or
-- | types with truncating `Unfoldable1` instances (like `Maybe`).
unfoldrInf :: forall a b u. Unfoldable1 u => (b -> a /\ b) -> b -> u a
unfoldrInf = unfoldr1 <<< (map Just <<< _)

-- | Create an infinite `Unfoldable1` by repeated application of a function to a seed value. 
-- | Analogous to `iterateN`, but with no iteration limit.
-- |
-- | This should only be used to produce either lazy types (like lazy `List`s) or
-- | types with truncating `Unfoldable1` instances (like `Maybe`).
iterate :: forall a u. Unfoldable1 u => (a -> a) -> a -> u a
iterate f seed = unfoldr1 (map \a -> Just (f a /\ f a)) $ seed /\ seed

-- | Create an infinite `Unfoldable1` by repeating a single element.
repeat :: forall a u. Unfoldable1 u => a -> u a
repeat = runTrivial1 <<< pure

-- | Concatenate an `Unfoldable1` with a possibly-empty `Unfoldable`.
-- |
-- | Do not use this to create a data structure. Please use Data.List.Lazy instead.
append1 :: forall a u. Unfoldable1 u => Trivial1 a -> Trivial a -> u a
append1 t1 = untrivial (untrivial1 eAppend1 t1)
  where eAppend1 :: forall b b'. Generator1 a b -> b -> Generator a b' -> b' -> u a
        eAppend1 f seed f' seed' = unfoldr1 appended $ Right seed
          where appended :: Either (a /\ b') b -> a /\ Maybe (Either (a /\ b') b)
                appended (Right b)
                  | a /\ mnb <- f b = a /\ case mnb of
                      Just nb -> Just $ Right nb
                      Nothing -> Left <$> f' seed'
                appended (Left (a /\ b')) = a /\ (Left <$> f' b')

-- | Concatenate a possibly-empty `Unfoldable` with an `Unfoldable1`.
-- |
-- | Do not use this to create a data structure. Please use Data.List.Lazy instead.
append1' :: forall a u. Unfoldable1 u => Trivial a -> Trivial1 a -> u a
append1' t = untrivial1 (untrivial eAppend1' t)
  where eAppend1' :: forall b b'. Generator a b -> b -> Generator1 a b' -> b' -> u a
        eAppend1' f seed f' seed'
          | Just p <- f seed = unfoldr1 appended $ Right p
          where appended :: Either b' (a /\ b) -> a /\ Maybe (Either b' (a /\ b))
                appended (Right (a /\ b)) = a /\ Just (note seed' $ f b)
                appended (Left b') = map Left <$> f' b'
          | otherwise = unfoldr1 f' seed'
