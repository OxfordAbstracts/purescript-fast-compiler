module Test.Main where

import Prelude hiding (negate, recip, add, mul, div, min, max)

import Data.Number (abs, sqrt, pi) as Number
import Data.Number.Dual
  ( Dual(..)
  , (.:.)
  , exl
  , exr
  , dup
  , cst
  , cross
  , scale
  , linearPropagation
  , negate
  , recip
  , add
  , mul
  , div
  , exp
  , sqrt
  , ln
  , pow
  , abs
  , sign
  , min
  , max
  , cos
  , sin
  , tan
  , acos
  , asin
  , atan
  , cosh
  , sinh
  , tanh
  , acosh
  , asinh
  , atanh
  , cumulate
  , fmap
  , transpose
  , distance2
  , norm2
  , distance
  , axes
  , minimize
  )

import Data.Tuple.Nested ((/\), type (/\))
import Effect (Effect)
import Test.Assert (assert')

class Simeq a where
  simeq :: a -> a -> Boolean

instance Simeq Number where
  simeq a b =
    a >= b - (Number.abs b + 0.000001) / 100.0
      && a <= b + (Number.abs b + 0.000001) / 100.0

instance (Simeq a, Simeq b) => Simeq (a /\ b) where
  simeq (a /\ b) (c /\ d) = simeq a c && simeq b d

infix 2 simeq as ~

main :: Effect Unit
main = do

  assert' "tuple manipulation" $
    let
      D graph =
        fmap
          ( linearPropagation
              ( \(x /\ y) -> (x + 1.0) * (y + 2.0)
              )
              (const 0.0) :: Dual (Number /\ Number) Number
          )
      f /\ _ = graph $ axes @2
    in
      f ~ 4.0 /\ 3.0

  assert' "x |-> |x^3 + 5| at -2" $
    let
      D graph =
        ( (identity .:. dup >>> mul) >>> mul
            .:. cst 5
        ) >>> add
          >>> fmap
            ( ( D \x ->
                  (if x < 0 then -x else x)
                    /\ (scale (if x < 0 then -1 else 1))
              ) :: Dual Int Int
            )
      f /\ f' = graph (-2)
    in
      f /\ f' 1 == 3 /\ -12

  assert' "x /\\ y |-> exp(-x^2 * y) at 0.3 /\\ 0.5" $
    let
      D graph =
        (exl >>> dup >>> mul >>> negate .:. exr)
          >>> mul
          >>> exp
      f /\ f' = graph $ 0.3 /\ 0.5
    in
      f /\ (f' $ 1.0 /\ 0.0) /\ (f' $ 0.0 /\ 1.0) ~ 0.956 /\ -0.2868 /\ -0.08604

  assert' "x /\\ y |-> 7 x / y at 2.0 /\\ 0.25" $
    let
      D graph =
        (div .:. cst 7.0) >>> mul
      f /\ f' = graph $ 2.0 /\ 0.25
    in
      f /\ (f' $ 1.0 /\ 0.0) /\ (f' $ 0.0 /\ 1.0) ~ 56.0 /\ 28.0 /\ -224.0

  assert' "x |-> sign (x) * tan (1 / x) at 2.0" $
    let
      D graph =
        dup >>> (exl >>> sign .:. exr >>> recip >>> tan) >>> mul
      f /\ f' = graph 2.0
    in
      f /\ f' 1.0 ~ 0.5463024898437905 /\ -0.3246116026023812

  assert' "x /\\ y |-> atan (sqrt (x*x + y*y)) at 0.3 /\\ 0.2" $
    let
      D graph =
        (exl >>> dup >>> mul .:. exr >>> dup >>> mul) >>> add >>> sqrt >>> atan
      f /\ f' = graph $ 0.3 /\ 0.2
      fx = f' $ 1.0 /\ 0.0
      fy = f' $ 0.0 /\ 1.0
    in
      f /\ fx /\ fy ~ 0.346047 /\ 0.7363277 /\ 0.49

  assert' "x /\\ y |-> -x / ln (x*x + y*y) at 0.3 /\\ 0.2" $
    let
      D graph =
        (exl >>> negate .:. (exl >>> dup >>> mul .:. exr >>> dup >>> mul) >>> add >>> ln) >>> div
      f /\ f' = graph $ 0.3 /\ 0.2
      fx = f' $ 1.0 /\ 0.0
      fy = f' $ 0.0 /\ 1.0
    in
      f /\ fx /\ fy ~ 0.147043 /\ 0.82278327 /\ 0.22176

  assert' "x /\\ y |-> x ^ y at 0.3 /\\ 0.2" $
    let
      D graph = pow
      f /\ f' = graph $ 0.3 /\ 0.2
      fx = f' $ 1.0 /\ 0.0
      fy = f' $ 0.0 /\ 1.0
    in
      f /\ fx /\ fy ~ 0.786 /\ 0.524 /\ -0.94632634

  assert' "x |-> cosh (acosh x) at 1.4" $
    let
      D graph = acosh >>> cosh
      f /\ f' = graph 1.4
    in
      f /\ f' 1.0 ~ 1.4 /\ 1.0

  assert' "other inverse trigonometric and hyperbolic functions" $
    let
      D graph =
        ( sin
            >>> asin
              .:. asin
            >>> sin
              .:. cos
            >>> acos
              .:. acos
            >>> cos
              .:. sinh
            >>> asinh
              .:. asinh
            >>> sinh
              .:. tanh
            >>> atanh
              .:. atanh
            >>> tanh
        )
          >>> cumulate
          >>> (identity .:. cst 8.0)
          >>> div
          >>> abs
      f /\ f' = graph 0.4
      fx = f' 1.0
    in
      f /\ fx ~ 0.4 /\ 1.0

  assert' "min and max functions" $
    let
      D graphn = min
      D graphx = max
      fn /\ fn' = graphn $ 3.14 /\ 2.72
      fx /\ fx' = graphx $ 3.14 /\ 2.72
      fnx = fn' $ 1.0 /\ 0.0
      fny = fn' $ 0.0 /\ 1.0
      fxx = fx' $ 1.0 /\ 0.0
      fxy = fx' $ 0.0 /\ 1.0
    in
      fn /\ fnx /\ fny /\ fx /\ fxx /\ fxy ~ 2.72 /\ 0.0 /\ 1.0 /\ 3.14 /\ 1.0 /\ 0.0

  assert' "simultaneous constraints : 2x+4y-7 == 0 and x-3y+2 == 0" $
    let
      l1 =
        ((identity .:. (cst 2.0 .:. cst 4.0)) >>> transpose >>> cross mul mul >>> add .:. (cst (-7.0))) >>> add
      l2 =
        ((identity .:. (cst 1.0 .:. cst (-3.0))) >>> transpose >>> cross mul mul >>> add .:. (cst 2.0)) >>> add
      graph = (l1 .:. l2) >>> cross dup dup >>> cross mul mul >>> add
    in
      minimize (axes @2) graph 1.0 1e-25 (0.0 /\ 0.0) ~ (13.0 / 10.0) /\ (11.0 / 10.0)

  assert' "x /\\ y equidistant to -4 /\\ 1, -1 /\\ -3 and 2 /\\ 2" $
    let
      d1 = (identity .:. cst (-4.0 /\ 1.0)) >>> distance
      d2 = (identity .:. cst (-1.0 /\ -3.0)) >>> distance
      d3 = (identity .:. cst (2.0 /\ 2.0)) >>> distance

      g1 = (d1 .:. d2 >>> negate) >>> add
      g2 = (d1 .:. d3 >>> negate) >>> add

      graph = (g1 .:. g2) >>> cross dup dup >>> cross mul mul >>> add
    in
      minimize (axes @2) graph 1.0 1e-25 (1.0 /\ 1.0) ~ (-43.0 / 54.0) /\ (5.0 / 18.0)

  assert' "x /\\ y minimizing the sum of distances to -4 /\\ 1, -1 /\\ -3 and 2 /\\ 2" $
    let
      d1 = (identity .:. cst (-4.0 /\ 1.0)) >>> distance
      d2 = (identity .:. cst (-1.0 /\ -3.0)) >>> distance
      d3 = (identity .:. cst (2.0 /\ 2.0)) >>> distance

      graph = ((d1 .:. d2) >>> add .:. d3) >>> add
    in
      minimize (axes @2) graph 1.0 1e-25 (1.0 /\ 1.0)
        ~
          ((-213.0 + 67.0 * Number.sqrt (3.0)) / 78.0) /\ ((-9.0 + Number.sqrt (3.0)) / 26.0)

  assert' "x /\\ y minimizing the sum of the square of distances to -4 /\\ 1, -1 /\\ -3 and 2 /\\ 2" $
    let
      d1 = (identity .:. cst (-4.0 /\ 1.0)) >>> distance2
      d2 = (identity .:. cst (-1.0 /\ -3.0)) >>> distance2
      d3 = (identity .:. cst (2.0 /\ 2.0)) >>> distance2

      graph = ((d1 .:. d2) >>> add .:. d3) >>> add
    in
      minimize (axes @2) graph 1.0 1e-20 (1.0 /\ 1.0) ~ -1.0 /\ 0.0

  assert' "tetrahedron mass center" $
    let
      a3D = -2.0 /\ 1.0 /\ -2.0
      b3D = -1.0 /\ -2.0 /\ 0.0
      c3D = 2.0 /\ 2.0 /\ 1.0
      d3D = -3.0 /\ -2.0 /\ 2.0

      d1 = (identity .:. cst a3D) >>> distance
      d2 = (identity .:. cst b3D) >>> distance
      d3 = (identity .:. cst c3D) >>> distance
      d4 = (identity .:. cst d3D) >>> distance

      g1 = (d1 .:. d2 >>> negate) >>> add
      g2 = (d2 .:. d3 >>> negate) >>> add
      g3 = (d3 .:. d4 >>> negate) >>> add

      graph = (g1 .:. g2 .:. g3) >>> norm2
    in
      minimize (axes @3) graph 1.1 1e-25 (1.0 /\ 0.0 /\ 0.0) ~ (-35.0 / 24.0) /\ (29.0 / 24.0) /\ (37.0 / 24.0)

  assert' "transcendant resolution : x == 2 - 2 exp (-x)" $
    let
      D graph =
        dup >>> cross ((cst 2.0 .:. negate) >>> add) (((negate >>> exp) .:. cst (-2.0)) >>> mul) >>> add >>> norm2
    in
      minimize (axes @1) (D graph) 1.0 1e-25 1.0 ~ 1.59362426

  assert' "pi approximation" $
    minimize (axes @1) ((cos .:. cst 1.0) >>> add) 1.0 1e-25 3.0 ~ Number.pi

