module Test.Main where

import Prelude

import Data.Array (head, any)
import Data.Array (length) as Array
import Data.Geometria
  ( class Analytic
  , circle
  , dot
  , halfline
  , length
  , line
  , meets
  , middle
  , normalTo
  , point
  , quadratic
  , segment
  , toCoordinates
  , vector
  , (<+|)
  , moveEllipse
  , Vector(..)
  )  
import Data.Maybe (fromMaybe)
import Data.Number (abs, sqrt)
import Data.Sparse.Polynomial (Polynomial, (^), (:.))
import Effect (Effect)
import Test.Assert (assert')

class Rougly a where
  roughly :: a -> a -> Boolean
  
instance Rougly Number where
  roughly a b = abs (b - a) < 1e-6
else instance Rougly (Polynomial Number) where
  roughly p q = (sqrt $ ((\x -> x*x) <$> (p - q)) :. 1.0) < 1e-6
else instance
  ( Analytic a
  ) => Rougly a where
  roughly a b = roughly (toCoordinates a) (toCoordinates b)

roughlyAmong :: forall a. Rougly a => a -> Array a -> Boolean
roughlyAmong x = any (_ `roughly` x)

main :: Effect Unit
main = do
  let
    confidentHead = head >>> fromMaybe (point zero)
    
    a = point $ 310.0^0 + 320.0^1
    b = point $ 100.0^0 + 210.0^1
    c = circle a (length $ vector a b)
    n = normalTo [vector b a]
    an = halfline a n
    e = confidentHead $ an `meets` c
    eb = segment e b
    i = middle eb
    f = confidentHead $ c `meets` (halfline a (vector b a))
    g = confidentHead $ (line a e) `meets` (line i f)
    h = confidentHead $ 
      (halfline b (vector b g)) `meets` (segment e f)
  assert' "elementary computations" $ 
    h `roughly` (point $ 470.0^0 + 270.0^1)
    && b `roughlyAmong` (c `meets` circle e (length $ vector e b))
  
  let
    perpendicularBisector p1 p2 = line m1 m2
      where
        m1 = middle $ segment p1 p2
        m2 = m1 <+| normalTo [vector p1 p2]
    
    j = point $ 2.0^0 + 2.0^1
    k = point $ 3.0^0 + 5.0^1
    l = point $ 4.0^1
    m = point $ -2.0^0 + 2.0^1
    p = point $ -3.0^0 - 1.0^1
    q = confidentHead $
      perpendicularBisector p m `meets` perpendicularBisector m j
    r = point $ (-3.0)^0 + (1.0/3.0)^1
    v = Vector $ 10.0^0 + 10.0^1
    ell = moveEllipse (-v) $ quadratic $ (_ <+| v) <$> [point zero, j, k, l, p]
    intersections = ell `meets` circle q (length $ vector q m)
  assert' "ellipse computations" $ 
    p `roughlyAmong` intersections &&
    j `roughlyAmong` intersections &&
    m `roughlyAmong` intersections &&
    r `roughlyAmong` intersections &&
    Array.length intersections == 4

  let
    s = point $ 2.0^0 + 7.0^1 + 17.0^2
    t = point $ 3.0^0 + 11.0^1 + 19.0^2
    u = point $ 5.0^0 + 13.0^1 + 23.0^2
    w = normalTo [vector s t, vector s u :: Vector 3]
    sw = vector (point zero) s `dot` w
  assert' "spatial computations" $
     sw `roughly` (vector (point zero) t `dot` w)
    && sw`roughly` (vector (point zero) u `dot` w)
        
  let
    x = Vector $ 12.0^0 + 2.0^1 + 3.0^2 + 4.0^3 + 14.0^4
    y = Vector $ 5.0^0 + 7.0^1 + 6.0^2 + 8.0^3 + 15.0^4
    z = Vector $ 1.0^0 + 10.0^1 + 11.0^2 + 9.0^3 + 13.0^4
    d = Vector $ 17.0^0 + 19.0^1 + 16.0^2 + 18.0^3 + 20.0^4
    o = normalTo [x, y, z, d :: Vector 5]
  assert' "hyeprspatial computations" $
    o `roughly` (Vector $ -1078.0^4 + 5753.0^3 + 1650.0^2 - 5577.0^1 - 143.0^0)
      && (o `dot` x) `roughly` 0.0
      && (o `dot` y) `roughly` 0.0
      && (o `dot` z) `roughly` 0.0
      && (o `dot` d) `roughly` 0.0

  pure unit
