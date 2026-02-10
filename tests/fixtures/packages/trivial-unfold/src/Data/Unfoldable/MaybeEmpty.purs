module Data.Unfoldable.MaybeEmpty
  ( MaybeEmpty(..)
  , maybeEmpty
  , maybeEmpty'
  , justNonempty
  , distributeMaybes
  , distributeMaybesA
  , toAlternative
  , maybeOver
  ) where

import Prelude

import Data.Newtype (class Newtype, over, over2, unwrap)
import Data.Maybe (Maybe(..), maybe, maybe')
import Data.Tuple.Nested ((/\))
import Control.Apply (lift2)
import Control.Comonad (class Extend, (=>>))
import Data.Functor.Invariant (class Invariant, imapF)
import Data.Generic.Rep (class Generic)
import Data.Eq (class Eq1, eq1)
import Data.Ord (class Ord1, compare1)
import Test.QuickCheck.Arbitrary (class Arbitrary, class Coarbitrary)
import Control.Alternative (class Alt, class Plus, class Alternative, (<|>), empty)
import Data.Foldable (class Foldable, foldr, foldl, foldMap)
import Data.Traversable (class Traversable, traverse, sequence)
import Data.Unfoldable
  ( class Unfoldable1
  , class Unfoldable
  , unfoldr1
  , unfoldr
  , singleton
  )
import Data.Unfoldable.Trivial (cons)

-- | Lifts a nonempty container into a possibly-empty container by wrapping it in `Maybe`.
-- | such that an empty sequence corresponds to `Nothing` and a nonempty sequence
-- | corresponds to the nonempty container in a `Just`.
newtype MaybeEmpty :: forall k. (k -> Type) -> k -> Type
newtype MaybeEmpty f a = MaybeEmpty (Maybe (f a))

derive instance Newtype (MaybeEmpty f a) _
derive newtype instance Arbitrary (f a) => Arbitrary (MaybeEmpty f a)
derive newtype instance Coarbitrary (f a) => Coarbitrary (MaybeEmpty f a)
derive newtype instance Semigroup (f a) => Semigroup (MaybeEmpty f a)
derive newtype instance Semigroup (f a) => Monoid (MaybeEmpty f a)
derive newtype instance Bounded (f a) => Bounded (MaybeEmpty f a)
derive newtype instance Semiring (f a) => Semiring (MaybeEmpty f a)
derive instance Generic (MaybeEmpty f a) _
derive instance Eq1 f => Eq1 (MaybeEmpty f)
derive instance Ord1 f => Ord1 (MaybeEmpty f)

instance maybeEmptyShow :: (Show (f a)) => Show (MaybeEmpty f a) where
  show (MaybeEmpty m) = "(MaybeEmpty " <> show m <> ")"

instance maybeEmptyEq :: (Eq1 f, Eq a) => Eq (MaybeEmpty f a) where
  eq (MaybeEmpty Nothing) (MaybeEmpty Nothing) = true
  eq (MaybeEmpty x) (MaybeEmpty y) = (eq1 <$> x <*> y) == Just true

instance maybeEmptyOrd :: (Ord1 f, Ord a) => Ord (MaybeEmpty f a) where
  compare = compare1

instance maybeEmptyUnfoldable1 :: Unfoldable1 f => Unfoldable1 (MaybeEmpty f) where
  unfoldr1 = (<<<) (MaybeEmpty <<< Just) <<< unfoldr1

instance maybeEmptyUnfoldable :: Unfoldable1 f => Unfoldable (MaybeEmpty f) where
  unfoldr f seed
    | Just (a /\ seed') <- f seed = MaybeEmpty $ Just $ cons a $ unfoldr f seed'
    | otherwise = MaybeEmpty Nothing

instance maybeEmptyFunctor :: Functor f => Functor (MaybeEmpty f) where
  map = over MaybeEmpty <<< map <<< map

instance maybeEmptyApply :: Apply f => Apply (MaybeEmpty f) where
  apply (MaybeEmpty f) (MaybeEmpty a) = MaybeEmpty $ lift2 apply f a

instance maybeEmptyApplicative :: Applicative f => Applicative (MaybeEmpty f) where
  pure = MaybeEmpty <<< pure <<< pure

instance maybeEmptyBind :: (Bind f, Traversable f) => Bind (MaybeEmpty f) where
  bind (MaybeEmpty a) f = MaybeEmpty $ bind a $ map join <<< traverse (unwrap <<< f)

instance maybeEmptyMonad :: (Applicative f, Bind f, Traversable f) => Monad (MaybeEmpty f)

instance maybeEmptyInvariant :: Functor f => Invariant (MaybeEmpty f) where
  imap = imapF

-- | Composes `Alt Maybe` with `Alt f`.
-- | This does not seem likely to be particularly useful, but then again, what does?
-- |
-- | If you just want the first nonempty `MaybeEmpty f a`, `unwrap` or `toAlternative` it to `Maybe (f a)`.
instance maybeEmptyAlt :: Alt f => Alt (MaybeEmpty f) where
  alt (MaybeEmpty (Just a)) (MaybeEmpty (Just b)) = MaybeEmpty $ Just $ a <|> b
  alt a b = over2 MaybeEmpty (<|>) a b
  
-- | `empty = none`. Does not use `Plus f` if it exists--and given that
-- | this is all about wrapping guaranteed non-empty containers, it probably doesn't.
instance maybeEmptyPlus :: Alt f => Plus (MaybeEmpty f) where
  empty = MaybeEmpty Nothing

instance maybeEmptyAlternative :: (Applicative f, Alt f) => Alternative (MaybeEmpty f)

instance maybeEmptyExtend :: Extend f => Extend (MaybeEmpty f) where
  extend f (MaybeEmpty (Just x)) = MaybeEmpty $ Just $ x =>> (f <<< MaybeEmpty <<< Just)
  extend _ (MaybeEmpty Nothing) = MaybeEmpty Nothing

instance maybeEmptyFoldable :: Foldable f => Foldable (MaybeEmpty f) where
  foldr f b = foldl (foldr f) b <<< unwrap
  foldl f b = foldl (foldl f) b <<< unwrap
  foldMap f = foldMap (foldMap f) <<< unwrap

instance maybeEmptyTraversable :: Traversable f => Traversable (MaybeEmpty f) where
  traverse f = map MaybeEmpty <<< traverse (traverse f) <<< unwrap
  sequence   = map MaybeEmpty <<< traverse sequence <<< unwrap

-- | Convenience wrapper for `maybe` on the inner `Maybe`,
-- | to save you an `un` or `toAlternative`.
maybeEmpty :: forall f a b. b -> (f a -> b) -> MaybeEmpty f a -> b
maybeEmpty d f = maybe d f <<< unwrap

maybeEmpty' :: forall f a b. (Unit -> b) -> (f a -> b) -> MaybeEmpty f a -> b
maybeEmpty' d f = maybe' d f <<< unwrap

-- | Wrap an existing container into a `MaybeEmpty`.
justNonempty :: forall f a. f a -> MaybeEmpty f a
justNonempty = MaybeEmpty <<< Just

-- | Create an `f` containing a single `Nothing` if empty.
-- |
-- | Although Data.Unfoldable calls them "unfoldable functors", `Functor` isn't actually
-- | a superclass of `Unfoldable1`. On the off chance that you for some reason do in fact
-- | have an `Unfoldable1` type which is not a `Functor` but also want to use this,
-- | consider `emptyIfNone` from `Data.Unfoldable.Trivial` instead.
distributeMaybes :: forall f a. Unfoldable1 f => Functor f => MaybeEmpty f a -> f (Maybe a)
distributeMaybes (MaybeEmpty (Just x)) = Just <$> x
distributeMaybes (MaybeEmpty Nothing) = singleton Nothing

-- | Create an `f` containing `Nothing` if empty, using `pure` instead of `singleton`.
distributeMaybesA :: forall f a. Applicative f => MaybeEmpty f a -> f (Maybe a)
distributeMaybesA (MaybeEmpty (Just x)) = Just <$> x
distributeMaybesA (MaybeEmpty Nothing) = pure Nothing

-- | Unwrap and convert the inner `Maybe` into an alternative `Alternative`. *(ba dum tss)*
toAlternative :: forall u f a. Alternative f => MaybeEmpty u a -> f (u a)
toAlternative (MaybeEmpty (Just x)) = pure x
toAlternative (MaybeEmpty Nothing) = empty

-- | Apply a function to the inner container if present.
maybeOver :: forall f g a b. (f a -> g b) -> MaybeEmpty f a -> MaybeEmpty g b
maybeOver = over MaybeEmpty <<< map
