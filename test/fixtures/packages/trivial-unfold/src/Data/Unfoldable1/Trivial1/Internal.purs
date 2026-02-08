-- | This module provides the `Trivial1` type as an existentially quantified
-- | dumb wrapper around `unfold1`, which can be inspected and manipulated
-- | to implement various typeclasses and the utilities in Data.Unfoldable1.Trivia1.
-- | 
-- | This module also contains the implementations of utilities which rely on directly
-- | inspecting `Trivial1` values and are re-exported by Data.Unfoldable.Trivial1.
-- | Use this module directly only if you intend to directly inspect `Trivial1` values yourself.

module Data.Unfoldable1.Trivial1.Internal
  ( Trivial1
  , Generator1
  , untrivial1
  , trivial1
  , turbofish1
  , (::<+>)
  , uncons1
  , runTrivial1
  ) where

import Prelude

import Data.Eq (class Eq1, eq1)
import Data.Ord (class Ord1, compare1)
import Data.Foldable (class Foldable, foldrDefault, foldMapDefaultL, foldl, intercalate)
import Data.Semigroup.Foldable (class Foldable1, foldr1Default, foldMap1DefaultL)
import Data.Unfoldable1 (class Unfoldable1, unfoldr1)
import Data.Unfoldable (class Unfoldable, none)
import Data.These (These(..), these, maybeThese, theseLeft, theseRight)
import Data.Tuple (fst, snd, uncurry)
import Data.Tuple.Nested ((/\), type (/\))
import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..), note, either)
import Data.Exists (Exists, mkExists, runExists)
import Data.Functor.Invariant (class Invariant, imapF)
import Data.Bifunctor (lmap, bimap)
import Data.Profunctor.Strong ((&&&), (***))
import Control.Lazy (class Lazy)
import Control.Alternative (class Alt)
import Control.Apply (lift2)
import Control.Biapply (bilift2)
import Test.QuickCheck.Arbitrary (class Arbitrary, class Coarbitrary, arbitrary)
import Test.QuickCheck.Gen (sized)

import Data.Unfoldable.Trivial.Internal ((::<*>))

-- | Alias for the generator function passed to `unfoldr1`.
type Generator1 a b = b -> a /\ Maybe b

-- | A constructor taking the same arguments as `unfoldr1`.
-- |
-- | Implementation detail. No longer part of the public API.
data Unfoldr1Call a b = Unfoldr1Call (Generator1 a b) b

-- | A type wrapping `unfoldr1` calls, existentially quantified over the seed type
-- | so that it can be ignored in the type constructor. Its `Unfoldable1` instance
-- | means that it can directly be constructed by calling `unfoldr1`.
newtype Trivial1 a = Trivial1 (Exists (Unfoldr1Call a))

-- | Specializes its argument to `Trivial1`.
trivial1 :: forall a. Trivial1 a -> Trivial1 a
trivial1 = identity

-- | Function application specialized to a `Trivial1` argument,
-- | at the same precedence as `($)`.
-- |
-- | Inspired by the Rust syntax of the same name, often used in the
-- | analogous context of collecting from an iterator.
turbofish1 :: forall a b. (Trivial1 a -> b) -> Trivial1 a -> b
turbofish1 = identity

infixr 0 turbofish1 as ::<+>

-- | Convenience function for inspecting `Trivial` values.
-- | Calls the function argument on the contents of the inner `Exists`.
untrivial1 :: forall a c. (forall b. Generator1 a b -> b -> c) -> Trivial1 a -> c
untrivial1 f (Trivial1 e) = runExists (\(Unfoldr1Call g seed) -> f g seed) e

-- | Wraps both arguments to `unfoldr1` in an `Unfoldr1Call`.
instance trivial1Unfoldable1 :: Unfoldable1 Trivial1 where
  unfoldr1 f seed = Trivial1 $ mkExists $ Unfoldr1Call f seed

instance trivial1Functor :: Functor Trivial1 where
  map :: forall a c. (a -> c) -> Trivial1 a -> Trivial1 c
  map f = untrivial1 eMap
    where eMap :: forall b. Generator1 a b -> b -> Trivial1 c
          eMap g seed = Trivial1
                        $ mkExists
                        $ Unfoldr1Call (
                          lmap f <<< g
                        ) seed

instance trivial1Invariant :: Invariant Trivial1 where
  imap = imapF

-- | Converts to any other `Unfoldable1`.
-- | Can also be seen as evaluating the inner `Unfoldr1Call`.
-- | 
-- | This is only useful in implementing utility functions.
-- | In all other cases, simply use the desired type directly.
runTrivial1 :: forall a u. Unfoldable1 u => Trivial1 a -> u a
runTrivial1 = untrivial1 eRunTrivial1
  where eRunTrivial1 :: forall b. Generator1 a b -> b -> u a
        eRunTrivial1 f seed = unfoldr1 f seed

-- | Returns the first element, and an `Unfoldable` of the remaining elements.
uncons1 :: forall a u. Unfoldable u => Trivial1 a -> a /\ u a
uncons1 = untrivial1 eUncons1
  where eUncons1 :: forall b. Generator1 a b -> b -> a /\ u a
        eUncons1 f seed = f seed <#> maybe none (unfoldr1 f)

instance trivial1Foldable :: Foldable Trivial1 where
  foldl :: forall a c. (c -> a -> c) -> c -> Trivial1 a -> c
  foldl f foldInit = untrivial1 eFoldl
    where eFoldl :: forall b. Generator1 a b -> b -> c
          eFoldl g unfoldSeed = lockstep unfoldSeed foldInit
            where lockstep :: b -> c -> c
                  lockstep seed acc
                    | a /\ Just seed' <- g seed = lockstep seed' $ f acc a
                    | otherwise = f acc $ fst $ g seed

  foldr f = foldrDefault f
  foldMap f = foldMapDefaultL f

-- | The *raison d'être* for `Trivial1`.
-- | Allows folding polymorphic `Unfoldable1`s as they generate
-- | with no explicit starting value. In particular, `foldMap1`
-- | needs map only into a `Semigroup` rather than a `Monoid`.
-- |
-- | `foldr1` uses a default implementation and may be inefficient.
instance trivial1Foldable1 :: Foldable1 Trivial1 where
  -- I feel like there might be a cleaner way to do this that's still elegant but eh
  foldl1 :: forall a. (a -> a -> a) -> Trivial1 a -> a
  foldl1 f t = foldl f first ::<*> rest
    where first /\ rest = uncons1 t

  foldr1 f = foldr1Default f
  foldMap1 f = foldMap1DefaultL f

-- | Guaranteed finite.
instance trivial1Arbitrary :: (Arbitrary a, Coarbitrary a) => Arbitrary (Trivial1 a) where
  arbitrary = sized \size -> do
    (f :: a -> a /\ Maybe a) <- arbitrary 
    seed <- arbitrary
    pure $ unfoldr1 (uncurry \i b ->
      f b <#> \b' ->
        if i >= size
        then Nothing
        else ((i + 1) /\ _) <$> b'
    ) $ 0 /\ seed

instance trivial1Lazy :: Lazy (Trivial1 a) where
  defer = (#) unit

-- | Concatenation.
-- |
-- | Do not use this to create a data structure. Please use Data.List.Lazy instead.
instance trivial1Semigroup :: Semigroup (Trivial1 a) where
  append :: Trivial1 a -> Trivial1 a -> Trivial1 a
  append t1 = untrivial1 (untrivial1 eAlt t1)
    where eAlt :: forall b b'. Generator1 a b -> b -> Generator1 a b' -> b' -> Trivial1 a
          eAlt f seed f' seed' = unfoldr1 appended $ Right seed
            where appended :: Either b' b -> a /\ Maybe (Either b' b)
                  appended = either
                    (map (map Left) <<< f')
                    (map (Just <<< note seed') <<< f)

-- | Zipwith; chosen over the `Monad`-compatible nondet choice used for `Array` etc.
-- | because that would require effectively forcing one argument and either
-- | re-evaluating it constantly or storing its elements in a real container
-- | at which point please please please just do that without using `Trivial1`.
-- | Length is the minimum of the arguments' lengths.
instance trivial1Apply :: Apply Trivial1 where
  apply :: forall a c. Trivial1 (a -> c) -> Trivial1 a -> Trivial1 c
  apply tg = untrivial1 (untrivial1 eApply tg)
    where eApply :: forall b b'. Generator1 (a -> c) b -> b -> Generator1 a b' -> b' -> Trivial1 c
          eApply f seed f' seed' = unfoldr1 applied $ seed /\ seed'
            where applied :: b /\ b' -> c /\ Maybe (b /\ b')
                  applied = uncurry (bilift2 identity (lift2 (/\))) <<< bimap f f'

-- | Infinitely cycles to satisfy the Applicative laws!
-- | If you just want one element, use `singleton` instead.
instance trivial1Applicative :: Applicative Trivial1 where
  pure a = unfoldr1 (const $ a /\ Just unit) unit

-- | **Not** concatenation! `(<|>)` clobbers a prefix of the right argument
-- | of the length of the left for consistency with `Alternative Trivial`,
-- | although `Trivial1` itself fundamentally lacks a `Plus` instance.
instance trivial1Alt :: Alt Trivial1 where
  alt :: forall a. Trivial1 a -> Trivial1 a -> Trivial1 a
  alt t1 = untrivial1 (untrivial1 eAlt t1)
    where eAlt :: forall b b'. Generator1 a b -> b -> Generator1 a b' -> b' -> Trivial1 a
          eAlt f seed f' seed' = unfoldr1 smooshed $ Both seed seed'
            where smooshed :: These b b' -> a /\ Maybe (These b b')
                  smooshed =
                      bimap f f'
                    >>>
                      (bimap fst fst &&& bimap snd snd)
                    >>>
                      (
                        these identity identity const
                      ***
                        -- this SO feels like it should be a library feature
                        \x -> maybeThese (join $ theseLeft x) (join $ theseRight x)
                      )

-- | Does not and cannot memoize the values being produced to compare.
-- | Please consider using Data.List.Lazy or your strict container of choice
-- | instead if you have any intention of using this for anything else.
instance trivial1Eq :: Eq a => Eq (Trivial1 a) where
  eq = eq1

instance trivial1Ord :: Ord a => Ord (Trivial1 a) where
  compare = compare1

instance trivial1Eq1 :: Eq1 Trivial1 where
  eq1 :: forall a. Eq a => Trivial1 a -> Trivial1 a -> Boolean
  eq1 t1 = untrivial1 (untrivial1 eEq1 t1)
    where eEq1 :: forall b b'. Generator1 a b -> b -> Generator1 a b' -> b' -> Boolean
          eEq1 f b f' b' =
            case f b /\ f' b' of
              (a /\ Nothing) /\ a' /\ Nothing -> a == a'
              (a /\ Just nb) /\ a' /\ Just nb'
                | a == a' -> eEq1 f nb f' nb' -- && does short circuit but I don't want to count on it
              _ -> false

instance trivial1Ord1 :: Ord1 Trivial1 where
  compare1 :: forall a. Ord a => Trivial1 a -> Trivial1 a -> Ordering
  compare1 t1 = untrivial1 (untrivial1 eCompare1 t1)
    where eCompare1 :: forall b b'. Generator1 a b -> b -> Generator1 a b' -> b' -> Ordering
          eCompare1 f b f' b' =
            case f b /\ f' b' of
              (a /\ Nothing) /\ a' /\ Nothing -> a `compare` a'
              (a /\ Just nb) /\ a' /\ Just nb'
                | a == a' -> eCompare1 f nb f' nb'
                | otherwise -> a `compare` a'
              (a /\ _) /\ a' /\ _
                | a /= a' -> a `compare` a'
              _ /\ _ /\ Nothing -> GT
              _ /\ _ /\ Just _ -> LT

instance trivial1Show :: Show a => Show (Trivial1 a) where
  show t1 = "toUnfoldable (NonEmptyArray [" <> intercalate ", " (show <$> t1) <> "])"
