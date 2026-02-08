module Data.Number.Dual where

import Prelude hiding (negate, add, mul, recip, div)
import Prelude (negate) as Ring
import Prelude (recip) as DivisionRing
import Prelude (div) as EuclideanRing

import Data.Number (acos, asin, atan, cos, exp, log, sin, sqrt) as Math
import Data.Tuple (fst, snd, uncurry)
import Data.Tuple.Nested ((/\), type (/\))
import Prim.Int (class Add)
import Type.Proxy (Proxy(..))

newtype Dual a b = D (a -> b /\ (a -> b))

class Monoidal k where
  cross ::
    forall a b c d.
    k a c ->
    k b d ->
    k (a /\ b) (c /\ d)

instance Monoidal (->) where
  cross f g = \(a /\ b) -> f a /\ g b

instance Monoidal Dual where
  cross (D f) (D g) = D $ \(a /\ b) ->
    let
      c /\ f' = f a
      d /\ g' = g b
    in
      (c /\ d) /\ cross f' g'

linearPropagation ::
  forall a b.
  (a -> b) ->
  (a -> b) ->
  Dual a b
linearPropagation f f' = D $ \a -> f a /\ f'

instance Semigroupoid Dual where
  compose (D g) (D f) = D $ \a ->
    let
      b /\ f' = f a
      c /\ g' = g b
    in
      c /\ compose g' f'

instance Category Dual where
  identity = linearPropagation identity identity

class Category k <= Cartesian k where
  exl :: forall a b. k (a /\ b) a
  exr :: forall a b. k (a /\ b) b
  dup :: forall a. k a (a /\ a)

instance Cartesian (->) where
  exl = fst
  exr = snd
  dup x = x /\ x

instance Cartesian Dual where
  exl = linearPropagation exl exl
  exr = linearPropagation exr exr
  dup = linearPropagation dup dup

class Space a where
  scale :: a -> (a -> a)
  accum :: (a /\ a) -> a

instance Semiring s => Space s where
  scale a = \da -> a * da
  accum = \(a /\ b) -> a + b

class RingCat k s where
  negate :: k s s
  add :: k (s /\ s) s
  mul :: k (s /\ s) s

instance Ring s => RingCat (->) s where
  negate = Ring.negate
  add = uncurry (+)
  mul = uncurry (*)

instance Ring s => RingCat Dual s where
  negate = linearPropagation negate negate
  add = linearPropagation add add
  mul = D $ \(a /\ b) ->
    (a * b) /\ (accum <<< cross (scale b) (scale a))

class DivisionRingCat k s where
  recip :: k s s
  div :: k (s /\ s) s

instance (DivisionRing s, EuclideanRing s) => DivisionRingCat (->) s where
  recip = DivisionRing.recip
  div = uncurry EuclideanRing.div

recipImpl :: forall b. EuclideanRing b => DivisionRing b => Dual b b
recipImpl = D \x -> recip x /\ (_ * (-(recip $ x * x)))

instance
  ( DivisionRing s
  , EuclideanRing s
  , RingCat Dual s
  ) =>
  DivisionRingCat Dual s where
  recip = recipImpl
  div = (exl .:. exr >>> recipImpl) >>> mul

expImpl :: Dual Number Number
expImpl = D \a -> Math.exp a /\ scale (Math.exp a)

lnImpl :: Dual Number Number
lnImpl = D \a -> Math.log a /\ scale (1.0 / a)

sinImpl :: Dual Number Number
sinImpl = D \a -> Math.sin a /\ scale (Math.cos a)

cosImpl :: Dual Number Number
cosImpl = D \a -> Math.cos a /\ scale (-Math.sin a)

sqrtImpl :: Dual Number Number
sqrtImpl = D \a -> Math.sqrt a /\ scale (0.5 / Math.sqrt a)

absImpl :: Dual Number Number
absImpl = dup >>> mul >>> sqrtImpl

atanImpl :: Dual Number Number
atanImpl = D \a -> Math.atan a /\ scale (1.0 / (1.0 + a * a))

coshImpl :: Dual Number Number
coshImpl = (dup >>> (exl >>> expImpl .:. exr >>> negate >>> expImpl) >>> add .:. cst 0.5) >>> mul

sinhImpl :: Dual Number Number
sinhImpl = (dup >>> (exl >>> expImpl .:. exr >>> negate >>> expImpl >>> negate) >>> add .:. cst 0.5) >>> mul

class NumCat k where
  exp :: k Number Number
  sqrt :: k Number Number
  sin :: k Number Number
  cos :: k Number Number
  tan :: k Number Number
  asin :: k Number Number
  acos :: k Number Number
  atan :: k Number Number
  sinh :: k Number Number
  cosh :: k Number Number
  tanh :: k Number Number
  asinh :: k Number Number
  acosh :: k Number Number
  atanh :: k Number Number
  ln :: k Number Number
  abs :: k Number Number
  sign :: k Number Number
  atan2 :: k (Number /\ Number) Number
  pow :: k (Number /\ Number) Number
  min :: k (Number /\ Number) Number
  max :: k (Number /\ Number) Number

instance NumCat Dual where
  exp = expImpl
  ln = lnImpl
  pow = (exl >>> lnImpl .:. exr) >>> mul >>> expImpl
  sqrt = sqrtImpl
  sin = sinImpl
  cos = cosImpl
  tan = dup >>> (exl >>> sinImpl .:. exr >>> cosImpl) >>> div
  asin = D \a -> Math.asin a /\ scale (1.0 / Math.sqrt (1.0 - a * a))
  acos = D \a -> Math.acos a /\ scale (-1.0 / Math.sqrt (1.0 - a * a))
  atan = atanImpl
  atan2 = div >>> atanImpl
  abs = absImpl
  sign = dup >>> (exl .:. exr >>> absImpl) >>> div
  min = ((add .:. (exl .:. exr >>> negate) >>> add >>> absImpl >>> negate) >>> add .:. cst 0.5) >>> mul
  max = ((add .:. (exl .:. exr >>> negate) >>> add >>> absImpl) >>> add .:. cst 0.5) >>> mul
  cosh = coshImpl
  sinh = sinhImpl
  tanh = dup >>> (exl >>> sinhImpl .:. exr >>> coshImpl) >>> div
  asinh = dup >>> (exl .:. (exr >>> dup >>> mul .:. cst 1.0) >>> add >>> sqrtImpl) >>> add >>> lnImpl
  acosh = dup >>> (exl .:. (exr >>> dup >>> mul .:. cst (-1.0)) >>> add >>> sqrtImpl) >>> add >>> lnImpl
  atanh =
    ( dup
        >>>
          ( (cst 1.0 .:. exl) >>> add .:. (cst 1.0 .:. exr >>> negate) >>> add
          )
        >>> div
        >>> lnImpl
        .:. cst 0.5
    ) >>> mul

-- | Generalized pairing operator
-- | such that
-- |            exl >>> f .:. exr >>> g
-- | is equivalent to
-- |            cross f g
pair ::
  forall a c d k.
  Cartesian k =>
  Monoidal k =>
  k a c ->
  k a d ->
  k a (c /\ d)
pair f g = cross f g <<< dup

infixr 6 pair as .:.

cst :: forall a s. Semiring s => s -> Dual a s
cst n = D $ const $ n /\ const zero

axes :: forall @n a. Axes n a => a
axes = axesImpl @n Proxy

class Axes :: Int -> Type -> Constraint
class Axes n a | n -> a where
  axesImpl :: Proxy n -> a

instance Axes 1 Number where
  axesImpl _ = 1.0
else instance Axes 2 ((Number /\ Number) /\ (Number /\ Number)) where
  axesImpl _ = (1.0 /\ 0.0) /\ (0.0 /\ 1.0)
else instance
  ( Axes n (h /\ t)
  , Add n 1 n1
  , Fmapable h (h /\ t) (Number /\ h) (h' /\ t')
  , Fmapable Number h Number h
  ) =>
  Axes n1 ((Number /\ h) /\ h' /\ t') where
  axesImpl _ = h'' /\ h' /\ t'
    where
    h /\ t = axesImpl (Proxy :: Proxy n)
    h' /\ t' =
      let
        D graph =
          fmap (dup >>> (cst 0.0 .:. exr) :: Dual h (Number /\ h))
        f /\ _ = graph (h /\ t)
      in
        f
    zeros =
      let
        D graph =
          fmap (cst 0.0 :: Dual Number Number)
        f /\ _ = graph h
      in
        f
    h'' = 1.0 /\ zeros

class Transposable a b | a -> b where
  transpose :: Dual a b

instance
  ( Transposable ((b /\ x) /\ (d /\ y)) e
  ) =>
  Transposable ((a /\ (b /\ x)) /\ (c /\ (d /\ y))) ((a /\ c) /\ e) where
  transpose = cross exl exl .:. cross exr exr >>> transpose
else instance Transposable ((a /\ b) /\ (c /\ d)) ((a /\ c) /\ (b /\ d)) where
  transpose = cross exl exl .:. cross exr exr
else instance Transposable a a where
  transpose = identity

class Cumulative c a where
  cumulate :: Dual c a

instance
  ( Ring a
  , Cumulative c a
  ) =>
  Cumulative (a /\ c) a where
  cumulate = cross identity cumulate >>> add

else instance Ring a => Cumulative (a /\ a) a where
  cumulate = add
else instance Cumulative a a where
  cumulate = identity

class Fmapable a c b k | b c -> k where
  fmap :: Dual a b -> Dual c k

instance Fmapable a a b b where
  fmap f = f

else instance
  ( Fmapable a c b k
  ) =>
  Fmapable a (a /\ c) b (b /\ k) where
  fmap f = cross f (fmap f)

minimize ::
  forall a c u t v axs.
  Fmapable a axs Number v =>
  Transposable (a /\ v) c =>
  Fmapable (Number /\ Number) c Number a =>
  Transposable (v /\ v) u =>
  Fmapable (Number /\ Number) u Number t =>
  Cumulative t Number =>
  axs ->
  Dual a Number ->
  Number ->
  Number ->
  a ->
  a

minimize axs (D cost) lambda epsilon z0 =
  let
    go z =
      let
        _ /\ f' = cost z
        fz =
          let
            D graph = fmap (linearPropagation f' (const 0.0) :: Dual a Number)
            f /\ _ = graph axs
          in
            f
        comb xs k ys =
          let
            D graph =
              transpose
                >>>
                  fmap
                    ( linearPropagation
                        (\(x /\ y) -> x + k * y)
                        (const 0.0) ::
                        Dual (Number /\ Number) Number
                    )
            f /\ _ = graph $ xs /\ ys
          in
            f
        _ /\ u' = cost $ comb z lambda fz

        fu =
          let
            D graph = fmap (linearPropagation u' (const 0.0) :: Dual a Number)
            f /\ _ = graph axs
          in
            f

        scal xs ys =
          let
            D graph =
              transpose
                >>>
                  fmap
                    ( linearPropagation
                        ( \(x /\ y) -> x * y
                        )
                        (const 0.0) ::
                        Dual (Number /\ Number) Number
                    )
                >>> cumulate
            f /\ _ = graph $ xs /\ ys
          in
            f
      in
        if scal fz fz < epsilon then z
        else
          let
            k = -scal fz fu / scal fu fu
          in
            go $ comb z k fz
  in
    go z0

distance2 ::
  forall a b c t.
  Transposable a b =>
  Fmapable (Number /\ Number) b (Number /\ Number) c =>
  Fmapable (Number /\ Number) c Number t =>
  Cumulative t Number =>
  Dual a Number

distance2 =
  transpose
    >>> fmap (cross identity negate :: Dual (Number /\ Number) (Number /\ Number))
    >>> fmap (add >>> dup >>> mul :: Dual (Number /\ Number) Number)
    >>> cumulate

norm2 ::
  forall a s t u v.
  Fmapable Number a Number s =>
  Transposable (a /\ s) t =>
  Fmapable (Number /\ Number) t (Number /\ Number) u =>
  Fmapable (Number /\ Number) u Number v =>
  Cumulative v Number =>
  Dual a Number

norm2 =
  dup >>> (exl .:. exr >>> fmap (cst 0.0 :: Dual Number Number)) >>> distance2

distance ::
  forall a b c t.
  Transposable a b =>
  Fmapable (Number /\ Number) b (Number /\ Number) c =>
  Fmapable (Number /\ Number) c Number (Number /\ t) =>
  Cumulative t Number =>
  Dual a Number
distance = distance2 >>> sqrt

