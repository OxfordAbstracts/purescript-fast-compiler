module ApplicativePhases
  ( Phases(..)
  , now
  , later
  , phase
  , foldPhases
  , cons
  , (:)
  , consFst
  , consSnd
  , cons'
  , index
  , index'
  , head
  , tail
  , head'
  , tail'
  , null
  , length
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))

data Phases f a
  = Nil a
  | Cons (∀ r. (∀ y z. (y → z → a) → f y → Phases f z → r) → r)

instance Functor (Phases f) where
  map f (Nil a) = Nil (f a)
  map f (Cons unwrap) = unwrap \c → cons' (\y z → f (c y z))

instance Apply f ⇒ Apply (Phases f) where
  apply (Nil f) a = f <$> a
  apply f (Nil a) = f <@> a
  apply (Cons unwrapF) (Cons unwrapA) =
    unwrapF \c1 f fs → unwrapA \c2 a as → cons'
      (\(Tuple f' a') (Tuple fs' as') → (c1 f' fs') (c2 a' as'))
      (Tuple <$> f <*> a)
      (Tuple <$> fs <*> as)

instance Apply f ⇒ Applicative (Phases f) where
  pure a = Nil a

-- | Append a computation to the start of a list, providing a combining
-- | function.
cons' ∷ ∀ @f @a @b @c. (a → b → c) → f a → Phases f b → Phases f c
cons' c f fs = Cons \res → res c f fs

-- | Append a computation to the start of a list, applying the result of the
-- | new computation to the result of the rest of the list.
cons ∷ ∀ @f @a @b. f (a → b) → Phases f a → Phases f b
cons = cons' ($)

infixr 6 cons as :

-- | Append a computation to the start of a list, keeping only the result of
-- | that first computation.
consFst ∷ ∀ @f @a @b. f a → Phases f b → Phases f a
consFst = cons' (\x _ → x)

-- | Append a computation to the start of a list, keeping only the result of
-- | the tail of the list.
consSnd ∷ ∀ @f @a @b. f a → Phases f b → Phases f b
consSnd = cons' (\_ x → x)

-- | Create a singleton list.
now ∷ ∀ @f @a. f a → Phases f a
now f = consFst f (Nil unit)

-- | Delay all of a list's computations by one phase.
later ∷ ∀ @f @a. Applicative f ⇒ Phases f a → Phases f a
later f = consSnd (pure unit) f

-- | Insert a computation at the given index/"phase". The first phase is 0,
-- | and providing a number lower than 0 also inserts at phase 0.
phase ∷ ∀ @f @a. Applicative f ⇒ Int → f a → Phases f a
phase i f
  | i <= 0 = now f
  | otherwise = later (phase (i - 1) f)

-- | Fold a list of computations into a single computation.
foldPhases ∷ ∀ @f. Applicative f ⇒ Phases f ~> f
foldPhases (Nil a) = pure a
foldPhases (Cons unwrap) = unwrap \c f fs → c <$> f <*> foldPhases fs

-- | Get the computation at a certain index.
index' ∷ ∀ @f @a. Functor f ⇒ Int → Phases f a → Maybe (f Unit)
index' _ (Nil _) = Nothing
index' i (Cons unwrap)
  | i < 0 = Nothing
  | i == 0 = unwrap \_ f _ → Just (void f)
  | otherwise = unwrap \_ _ fs → index' (i - 1) fs

-- | Get the computation at a certain index, returning `pure unit` if out of
-- | bounds.
index ∷ ∀ @f @a. Applicative f ⇒ Int → Phases f a → f Unit
index i = fromMaybe (pure unit) <<< index' i

-- | Get the first computation.
head' ∷ ∀ @f @a. Functor f ⇒ Phases f a → Maybe (f Unit)
head' (Nil _) = Nothing
head' (Cons unwrap) = unwrap \_ f _ → Just (void f)

-- | Get the first computation, returning `pure unit` if there isn't one.
head ∷ ∀ @f @a. Applicative f ⇒ Phases f a → f Unit
head = fromMaybe (pure unit) <<< head'

-- | Get all the computations except the first.
tail' ∷ ∀ @f @a. Phases f a → Maybe (Phases f Unit)
tail' (Nil _) = Nothing
tail' (Cons unwrap) = unwrap \_ _ fs → Just (void fs)

-- | Get all the computations except the first, returning an empty list if there
-- | are none.
tail ∷ ∀ @f @a. Applicative f ⇒ Phases f a → Phases f Unit
tail = fromMaybe (Nil unit) <<< tail'

-- | Check if a list is empty.
null ∷ ∀ @f @a. Phases f a → Boolean
null (Nil _) = true
null _ = false

-- | Find the length of a list.
length ∷ ∀ @f @a. Phases f a → Int
length (Nil _) = 0
length (Cons unwrap) = 1 + (unwrap \_ _ fs → length fs)
