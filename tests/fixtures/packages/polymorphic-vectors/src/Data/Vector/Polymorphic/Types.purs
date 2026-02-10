module Data.Vector.Polymorphic.Types where

import Prelude

import Control.Apply (lift2)
import Data.Distributive (class Distributive, collectDefault, distribute)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.Semigroup.Foldable (class Foldable1, foldMap1, foldl1Default, foldr1Default)
import Data.Semigroup.Traversable (class Traversable1, traverse1Default, traverse1, sequence1)
import Data.Traversable (class Traversable)

data Vector2 a = Vector2 a a

infix 2 Vector2 as ><

-- | Get the x value from a `Vector2`
getX ∷ ∀ a. Vector2 a → a
getX (x >< _) = x

-- | Get the y value from a `Vector2`
getY ∷ ∀ a. Vector2 a → a
getY (_ >< y) = y

derive instance Generic (Vector2 a) _
derive instance Eq a ⇒ Eq (Vector2 a)
derive instance Ord a ⇒ Ord (Vector2 a)

instance (Show a) ⇒ Show (Vector2 a) where
  show (a >< b) = "(" <> show a <> " >< " <> show b <> ")"

instance Functor Vector2 where
  map f (a >< b) = f a >< f b

instance Apply Vector2 where
  apply (f >< g) (x >< y) = f x >< g y

instance Applicative Vector2 where
  pure x = x >< x

instance Bind Vector2 where
  bind vec f = distribute f <*> vec

instance Monad Vector2

instance Semigroup a ⇒ Semigroup (Vector2 a) where
  append (a >< b) (a' >< b') = (a <> a') >< (b <> b')

instance Monoid a ⇒ Monoid (Vector2 a) where
  mempty = mempty >< mempty

instance Semiring a ⇒ Semiring (Vector2 a) where
  add = lift2 add
  zero = pure zero
  mul = lift2 mul
  one = pure one

instance Ring a ⇒ Ring (Vector2 a) where
  sub = lift2 sub

instance DivisionRing a ⇒ DivisionRing (Vector2 a) where
  recip = map recip

instance CommutativeRing a ⇒ CommutativeRing (Vector2 a)

instance EuclideanRing a ⇒ EuclideanRing (Vector2 a)
  where
  degree _ = 1
  div = lift2 div
  mod = lift2 mod

instance Foldable1 Vector2 where
  foldMap1 f (x >< y) = f x <> f y
  foldr1 f = foldr1Default f
  foldl1 f = foldl1Default f

instance Foldable Vector2 where
  foldr f z (x >< y) = x `f` (y `f` z)
  foldl f z (x >< y) = (z `f` x) `f` y
  foldMap = foldMap1

instance Traversable1 Vector2 where
  sequence1 (fx >< fy) = (><) <$> fx <*> fy
  traverse1 = traverse1Default

instance Traversable Vector2 where
  sequence = sequence1
  traverse = traverse1

instance Distributive Vector2 where
  distribute fvec = (><)
    do getX <$> fvec
    do getY <$> fvec
  collect = collectDefault

data Rect a = Rect (Vector2 a) (Vector2 a)

-- | Get the topleft position of a `Rect`
getPos ∷ ∀ a. Rect a → Vector2 a
getPos (Rect pos _) = pos

-- | Get the size of a `Rect`
getSize ∷ ∀ a. Rect a → Vector2 a
getSize (Rect _ size) = size

-- | Constructs a `Rect` from four values
makeRect ∷ ∀ a. a → a → a → a → Rect a
makeRect x y w h = Rect (x >< y) (w >< h)

derive instance Generic (Rect a) _
derive instance Eq a ⇒ Eq (Rect a)
derive instance Ord a ⇒ Ord (Rect a)

instance Show a ⇒ Show (Rect a) where
  show (Rect pos size) = "(Rect " <> show pos <> " " <> show size <> ")"

instance Functor Rect where
  map f (Rect xy wh) = Rect (map f xy) (map f wh)

instance Apply Rect where
  apply (Rect ab cd) (Rect xy wh) = Rect (apply ab xy) (apply cd wh)

instance Applicative Rect where
  pure x = Rect (pure x) (pure x)

instance Bind Rect where
  bind rect f = distribute f <*> rect

instance Monad Rect

instance Semigroup a ⇒ Semigroup (Rect a) where
  append (Rect a b) (Rect a' b') = Rect (a <> a') (b <> b')

instance Monoid a ⇒ Monoid (Rect a) where
  mempty = Rect mempty mempty

instance Semiring a ⇒ Semiring (Rect a) where
  add = lift2 add
  zero = pure zero
  mul = lift2 mul
  one = pure one

instance Foldable1 Rect where
  foldMap1 f (Rect (x >< y) (w >< h)) = f x <> f y <> f w <> f h
  foldr1 f = foldr1Default f
  foldl1 f = foldl1Default f

instance Foldable Rect where
  foldr f z (Rect (x >< y) (w >< h)) = x `f` (y `f` (w `f` (h `f` z)))
  foldl f z (Rect (x >< y) (w >< h)) = (((z `f` x) `f` y) `f` w) `f` h
  foldMap = foldMap1

instance Traversable1 Rect where
  sequence1 (Rect (fx >< fy) (fw >< fh)) = makeRect <$> fx <*> fy <*> fw <*> fh
  traverse1 = traverse1Default

instance Traversable Rect where
  sequence = sequence1
  traverse = traverse1

instance Distributive Rect where
  distribute fRect = makeRect
    do getX <<< getPos <$> fRect
    do getY <<< getPos <$> fRect
    do getX <<< getSize <$> fRect
    do getY <<< getSize <$> fRect
  collect = collectDefault
