-- | This module provides the `Trivial` type as an existentially quantified
-- | dumb wrapper around `unfold`, which can be inspected and manipulated
-- | to implement various typeclasses and the utilities in Data.Unfoldable.Trivial.
-- | 
-- | This module also contains the implementations of utilities which rely on directly
-- | inspecting `Trivial` values and are re-exported by Data.Unfoldable.Trivial.
-- | Use this module directly only if you intend to directly inspect `Trivial` values yourself.

module Data.Unfoldable.Trivial.Internal
  ( Trivial
  , Generator
  , trivial
  , untrivial
  , turbofish
  , (::<*>)
  , unfoldr1Default
  , runTrivial
  ) where

import Prelude

import Data.Eq (class Eq1, eq1)
import Data.Ord (class Ord1, compare1)
import Data.Foldable (class Foldable, foldrDefault, foldMapDefaultL, intercalate)
import Data.Unfoldable
  (class Unfoldable
  , class Unfoldable1
  , unfoldr
  , none
  )
import Data.Tuple (uncurry, fst, snd)
import Data.Tuple.Nested ((/\), type (/\))
import Data.Maybe (Maybe(..), maybe')
import Data.Exists (Exists, mkExists, runExists)
import Data.Bifunctor (lmap)
import Data.Functor.Invariant (class Invariant, imapF)
import Data.Compactable (class Compactable, separateDefault)
import Data.Filterable
  ( class Filterable
  , partitionDefaultFilterMap
  , partitionMapDefault
  , filterMapDefault
  )
import Data.Either (Either(..), either)
import Control.Alternative (class Alt, class Plus, class Alternative, (<|>))
import Control.Lazy (class Lazy)
import Test.QuickCheck.Arbitrary (class Arbitrary, class Coarbitrary, arbitrary)
import Test.QuickCheck.Gen (sized)

-- | Alias for the generator function passed to `unfoldr`.
type Generator a b = b -> Maybe (a /\ b)

-- | A constructor taking the same arguments as `unfoldr`.
-- |
-- | Implementation detail. No longer part of the public API.
data UnfoldrCall a b = UnfoldrCall (Generator a b) b

-- | A type wrapping `unfoldr` calls, existentially quantified over the seed type
-- | so that it can be ignored in the type constructor. Its `Unfoldable` instance
-- | means that it can directly be constructed by calling `unfoldr`.
newtype Trivial a = Trivial (Exists (UnfoldrCall a))

-- | Specializes its argument to `Trivial`.
trivial :: forall a. Trivial a -> Trivial a
trivial = identity

-- | Function application specialized to a `Trivial` argument,
-- | at the same precedence as `($)`.
-- |
-- | Inspired by the Rust syntax of the same name, often used in the
-- | analogous context of collecting from an iterator.
turbofish :: forall a b. (Trivial a -> b) -> Trivial a -> b
turbofish = identity

infixr 0 turbofish as ::<*>

-- | Convenience function for inspecting `Trivial` values.
-- | Calls the function argument on the contents of the inner `Exists`.
untrivial :: forall a c. (forall b. Generator a b -> b -> c) -> Trivial a -> c
untrivial f (Trivial e) = runExists (\(UnfoldrCall g seed) -> f g seed) e

-- | Wraps both arguments to `unfoldr` in an `UnfoldrCall`.
instance trivialUnfoldable :: Unfoldable Trivial where
  unfoldr f seed = Trivial $ mkExists $ UnfoldrCall f seed

instance trivialUnfoldable1 :: Unfoldable1 Trivial where
  unfoldr1 = unfoldr1Default

instance trivialFunctor :: Functor Trivial where
  map :: forall a c. (a -> c) -> Trivial a -> Trivial c
  map f = untrivial eMap
    where eMap :: forall b. Generator a b -> b -> Trivial c
          eMap g seed = Trivial
                        $ mkExists
                        $ UnfoldrCall (
                          map (lmap f) <<< g
                        ) seed

instance trivialInvariant :: Invariant Trivial where
  imap = imapF

-- | Provides a default implementation of `unfoldr1` using `unfoldr` to satisfy
-- | the superclass bound on `Unfoldable`.
unfoldr1Default :: forall a b t. Unfoldable t => (b -> a /\ Maybe b) -> b -> t a
unfoldr1Default f = unfoldr (map f) <<< Just

-- | Converts to any other `Unfoldable`.
-- | Can also be seen as evaluating the inner `UnfoldrCall`.
-- | 
-- | This is only useful in implementing utility functions.
-- | In all other cases, simply use the desired type directly.
runTrivial :: forall a u. Unfoldable u => Trivial a -> u a
runTrivial = untrivial eRunTrivial
  where eRunTrivial :: forall b. Generator a b -> b -> u a
        eRunTrivial f seed = unfoldr f seed

-- | The *raison d'être* for `Trivial`.
-- | Allows folding polymorphic `Unfoldable`s as they generate.
-- |
-- | `foldr` uses a default implementation and may be inefficient.
-- | Note also that this enables the use of `sequence_`
-- | despite the lack of a `Traversable` instance, which is not provided because
-- | it would require forcing and accumulating every value, at which point
-- | any would-be user is better off with an actual container.
instance trivialFoldable :: Foldable Trivial where
  foldl :: forall a c. (c -> a -> c) -> c -> Trivial a -> c
  foldl f foldInit = untrivial eFoldl
    where eFoldl :: forall b. Generator a b -> b -> c
          eFoldl g unfoldSeed = lockstep unfoldSeed foldInit
            where lockstep :: b -> c -> c
                  lockstep seed acc
                    | Just (a /\ seed') <- g seed = lockstep seed' $ f acc a
                    | otherwise = acc

  foldr f = foldrDefault f
  foldMap f = foldMapDefaultL f

-- | Guaranteed finite.
instance trivialArbitrary :: (Arbitrary a, Coarbitrary a) => Arbitrary (Trivial a) where
  arbitrary = sized \size -> do
    (f :: a -> Maybe (a /\ a)) <- arbitrary 
    seed <- arbitrary
    pure $ unfoldr (uncurry \i b -> 
      if i >= size
      then Nothing
      else map ((i + 1) /\ _) <$> f b
    ) $ 0 /\ seed

instance trivialLazy :: Lazy (Trivial a) where
  defer = (#) unit

instance trivialCompactable :: Compactable Trivial where
  -- | Filters elements as they're produced
  compact :: forall a. Trivial (Maybe a) -> Trivial a
  compact = untrivial eCompact
    where eCompact :: forall b. Generator (Maybe a) b -> b -> Trivial a
          eCompact f seed = unfoldr filtering seed
            where filtering :: b -> Maybe (a /\ b)
                  filtering b
                    | Just (a /\ b') <- f b =
                        maybe'
                          (\_ -> filtering b')
                          (Just <<< (_ /\ b'))
                          a
                    | otherwise = Nothing
  -- | Default implementation, essentially running two separate filters.
  -- | Not great, but inherently can't do better without an intermediate container
  -- | (or emulating such with some massive thunk buildup)
  -- | -- which you probably do want at that point!
  separate t = separateDefault t

instance trivialFilterable :: Filterable Trivial where
  partitionMap p = partitionMapDefault p
  partition p = partitionDefaultFilterMap p
  filterMap p = filterMapDefault p
  filter :: forall a. (a -> Boolean) -> Trivial a -> Trivial a
  filter p = untrivial eFilter
    where eFilter :: forall b. Generator a b -> b -> Trivial a
          eFilter f seed = unfoldr filtering seed
            where filtering :: b -> Maybe (a /\ b)
                  filtering b
                    | Just (a /\ b') <- f b =
                        if p a
                        then Just (a /\ b')
                        else filtering b'
                    | otherwise = Nothing

-- | Concatenation.
-- |
-- | Do not use this to create a data structure. Please use Data.List.Lazy instead.
instance trivialSemigroup :: Semigroup (Trivial a) where
  append :: Trivial a -> Trivial a -> Trivial a
  append t = untrivial (untrivial eAlt t)
    where eAlt :: forall b b'. Generator a b -> b -> Generator a b' -> b' -> Trivial a
          eAlt f seed f' seed' = unfoldr appended $ Right seed
            where appended :: Either b' b -> Maybe (a /\ Either b' b)
                  appended = either
                    (map (map Left) <<< f')
                    (maybe'
                      (\_ -> map Left <$> f' seed')
                      (uncurry \a b -> Just (a /\ Right b))
                    <<< f)

instance trivialPlus :: Plus Trivial where
  empty = none

-- | **Not** concatenation! `(<|>)` clobbers a prefix of the right argument
-- | of the length of the left in order to satisfy the `Alternative` laws.
-- | (Thanks to @xgrommx's implementation in `ZipList`!)
instance trivialAlt :: Alt Trivial where
  alt :: forall a. Trivial a -> Trivial a -> Trivial a
  alt t = untrivial (untrivial eAlt t)
    where eAlt :: forall b b'. Generator a b -> b -> Generator a b' -> b' -> Trivial a
          eAlt f seed f' seed' = unfoldr smooshed $ Just seed /\ Just seed'
            where smooshed :: Maybe b /\ Maybe b' -> Maybe (a /\ Maybe b /\ Maybe b')
                  smooshed (b /\ b') = (map fst top <|> map fst me) <#> (_ /\ map snd top /\ map snd me)
                    where top = f =<< b
                          me = f' =<< b'

                    

instance trivialMonoid :: Monoid (Trivial a) where
  mempty = none

-- | Zipwith; chosen over the `Monad`-compatible
-- | nondet choice used for `Array` etc.
-- | because that would require effectively forcing one argument and either
-- | re-evaluating it constantly or storing its elements in a real container
-- | at which point please please please just do that without using `Trivial`.
-- | Length is the minimum of the arguments' lengths.
instance trivialApply :: Apply Trivial where
  apply :: forall a c. Trivial (a -> c) -> Trivial a -> Trivial c
  apply tg = untrivial (untrivial eApply tg)
    where eApply :: forall b b'. Generator (a -> c) b -> b -> Generator a b' -> b' -> Trivial c
          eApply f seed f' seed' = unfoldr (uncurry applied) $ seed /\ seed'
            where applied :: b -> b' -> Maybe (c /\ b /\ b')
                  applied b b' = do
                    g /\ nb <- f b
                    a /\ nb' <- f' b'
                    Just $ g a /\ nb /\ nb'

-- | Infinitely cycles to satisfy the Applicative laws!
-- | If you just want one element, use `singleton` instead.
instance trivialApplicative :: Applicative Trivial where
  pure a = unfoldr (const $ Just $ a /\ unit) unit

instance trivialAlternative :: Alternative Trivial

-- | Does not and cannot memoize the values being produced to compare.
-- | Please consider using Data.List.Lazy or your strict container of choice
-- | instead if you have any intention of using this for anything else.
instance trivialEq :: Eq a => Eq (Trivial a) where
  eq = eq1

instance trivialOrd :: Ord a => Ord (Trivial a) where
  compare = compare1

instance trivialEq1 :: Eq1 Trivial where
  eq1 :: forall a. Eq a => Trivial a -> Trivial a -> Boolean
  eq1 t = untrivial (untrivial eEq1 t)
    where eEq1 :: forall b b'. Generator a b -> b -> Generator a b' -> b' -> Boolean
          eEq1 f b f' b' =
            case f b /\ f' b' of
              Nothing /\ Nothing -> true
              Just (a /\ nb) /\ Just (a' /\ nb')
                | a == a' -> eEq1 f nb f' nb' -- && does short circuit but I don't want to count on it
              _ -> false

instance trivialOrd1 :: Ord1 Trivial where
  compare1 :: forall a. Ord a => Trivial a -> Trivial a -> Ordering
  compare1 t = untrivial (untrivial eCompare1 t)
    where eCompare1 :: forall b b'. Generator a b -> b -> Generator a b' -> b' -> Ordering
          eCompare1 f b f' b' =
            case f b /\ f' b' of
              Nothing /\ Nothing -> EQ
              Just (a /\ nb) /\ Just (a' /\ nb')
                | a == a' -> eCompare1 f nb f' nb'
                | otherwise -> a `compare` a'
              _ /\ Nothing -> GT
              _ /\ Just _ -> LT

instance trivialShow :: Show a => Show (Trivial a) where
  show t = "toUnfoldable [" <> intercalate ", " (show <$> t) <> "]"
