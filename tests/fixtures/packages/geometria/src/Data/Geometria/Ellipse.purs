module Data.Geometria.Ellipse where

import Prelude

import Data.Array (uncons, filter, concat, zip, (..))
import Data.Complex 
  ( Cartesian(..)
  , imag
  , magnitudeSquared
  , normalize
  , pow
  , real
  )
import Data.Foldable (sum)
import Data.Geometria.Types
  ( class Intersectable
  , Circle(..)
  , HalfLine(..)
  , Line(..)
  , Point
  , Segment(..)
  , Vector(..)
  , circle
  , cosAngle
  , drain
  , halfline
  , immerse
  , index
  , length
  , line
  , meets
  , middle
  , normalized
  , normalTo
  , point
  , project
  , rotated
  , scale
  , segment
  , system
  , vector
  , (<+|)
  )
  
import Data.Geometria.Space (revolution)
import Data.Maybe (Maybe(..))
import Data.Number (cos, sin, atan, sqrt, atan2, acos)
import Data.Ord (abs)
import Data.Sparse.Matrix (Matrix(..), pluSolve, (!!)) 
import Data.Sparse.Polynomial (Polynomial, (^), (!))
import Data.Tuple.Nested ((/\), type (/\))
import Record.Studio.Map (mapRecord)

-- | 
-- | ```
-- |  --                                                        -- 
-- | | ;TLDR :                                                    |
-- | | ------                                                     |
-- | |                                                            |
-- | | e@                                                         |
-- | |   (                                                        |
-- | |     Ellipse                                                |
-- | |       { center                                             |
-- | |       , a                                                  |
-- | |       , b                                                  |
-- | |       , c                                                  |
-- | |       }                                                    |
-- | |   ) = ellipse center (radiusMax /\ radiusMin) alpha        |
-- | |                                                            |
-- | | represents the set of points (x/\y) satisfying:            |
-- | |                                                            |
-- | | a * (x - center.x)^2                                       |
-- | | + b * (y - center.y)^2                                     |
-- | | + c * (x - center.x) (y - center.y) - residualConstant(e)  |
-- | | = 0                                                        |
-- | |                                                            |
-- | |                                                            |
-- |  --                                                        --
-- | ```
-- |
-- | ## ELLIPSES
-- | 
-- | ### Implicit ellipse representations: 5 degrees of freedom
-- | 
-- | #### Level-set representation:
-- | `f(x,y) = ax2 + by2 + cxy + dx + ey = 1`
-- |
-- | #### Matrix equation representation:
-- | ```
-- |               _           _    _ _
-- |              | a   c/2 d/2 |  | x |
-- |      _    _  | c/2 b   e/2 |  | y |
-- |     | x y 1| | d/2 e/2 -1  |  | 1 | = X^TAX = 0
-- |      -    -   -           -    - -
-- | ```
-- | #### Centering (abandonment of degree-1 terms):
-- | Changes of variables: `x = X+h` and `y = Y+k` 
-- | such that `f(x,y) = g(X,Y) = aX2 + bY2 + cXY + L`
-- | => `[h; k] = [ec-2bd; cd-2ae] / (4ab-c2)`
-- | and `L = L(a,b,c,d,e,h,k) = ah2 + bk2 + chk + dh + ek`.
-- | Furthermore, `f(x,y) = 1` => `aX2 + bY2 + cXY = l = 1-L`.
-- | Then, ellipse representation can simply be:
-- | ```
-- |               _       _    _ _
-- |      _   _   | a   c/2 |  | x |
-- |     | x y |  | c/2 b   |  | y | = X^TBX = l
-- |      -   -    -       -    - -
-- | ```
-- | (cf. `ellipseInternal` and `residualConstant` functions)
-- | 
-- | #### Alinement (coupling term abandonment, after centering):
-- | `B` diagonalization, with `B` symmetric matrix: 
-- | * one diagonal matrix `D =[D00, 0; 0, D11]` : 2 degrees of freedom
-- | * one angle `t` : 1 degree of freedom
-- | => thus 5 degree of freedom with the 2 ones from centering.
-- | 
-- | (cf. `unCouple` function)
-- | 
-- | ### Ellipses explicit representations:
-- | Every point `(x,y)` of the unit circle is associated with
-- | a point `(X,Y)`from the `(h,k)`-centered ellipse thanks to 
-- | the affine transformation:
-- | ```
-- |  _ _   _ _   _              _  _                                 _  _ _
-- | | X | | h | | cos(t) -sin(t) || s0=sqrt(|l/D00|) 0                || x |
-- | | Y |=| k |+| sin(t)  cos(t) || 0                s1=sqrt(|l/D11|) || y |
-- |  - -   - -   -              -  -                                 -  - -
-- | ```
-- | whose linear part is like an SVD decomposition 
-- | (if, as it has been done here, `V` is chosen as the identity, meaning
-- | that the four cardinal points from the unit circle correspond 
-- | to the extreme points of the ellipse).
-- | This way, reciprocally, `t`, `s0` and `s1` parameters
-- | can be recovered, for every `T = USV'` matrix, by
-- | * diagonalizing `T'T`
-- | * orthonormalizing its eigen vectors
-- | * taking the square root of its eigen values.
-- |
-- | (cf. `ellipseDimensions`and `fromUnitCircle` functions)
-- | 

newtype Ellipse = 
  Ellipse 
    { center :: Point 2
    , a :: Number
    , b :: Number
    , c :: Number
    }

-- |
-- | Smart constructor computing the ellipse parameters from :
-- | * its center
-- | * the values of the two semi-axes
-- | * the value of the tilt
-- |
ellipse :: Point 2 -> Number /\ Number -> Number -> Ellipse
ellipse center (rx /\ rn) alpha = 
  Ellipse 
    { center
    , a
    , b
    , c
    }
    where
      h = center `index` 0
      k = center `index` 1
      xx = rx * rx
      nn = rn * rn
      cc = cos alpha * cos alpha
      ss = sin alpha * sin alpha 
      s2 = sin (2.0 * alpha)
      l = 
        1.0 /
          ( 1.0 
            - h*h*(cc/xx+ss/nn) 
            - h*k*s2*(1.0/xx-1.0/nn) 
            - k*k*(ss/xx+cc/nn)
          )
      a = l*(cc/xx+ss/nn)
      b = l*(ss/xx+cc/nn)
      c = s2*l*(1.0/xx-1.0/nn)

ellipseCenter :: Ellipse -> Point 2
ellipseCenter (Ellipse e) = e.center

ellipseInternal :: Ellipse -> Polynomial (Polynomial Number)
ellipseInternal (Ellipse e) = 
  (e.a)^0^0 + (e.c/2.0)^0^1
  + (e.c/2.0)^1^0 + (e.b)^1^1

-- |
-- | Value of the second member in the updated equation after centering.
-- |
residualConstant :: Ellipse -> Number
residualConstant (Ellipse el) = 
  let
    a = el.a
    b = el.b
    c = el.c
    h = el.center `index` 0
    k = el.center `index` 1
    d = -c*k-2.0*a*h
    e = -c*h-2.0*b*k
  in 1.0 - (a*h*h + b*k*k + c*h*k + d*h + e*k)

-- |
-- | Equivalent to the diagonalization of the symmetric input matrix :
-- | `t` est l'angle de rotation autour de l'origine tel que `c'=0` 
-- | dans la nouvelle representation:
-- | * `tan(2t) = c/(a-b)`
-- | * `vec` = matrice de rotation d'angle `t`
-- | * `val = recip vec * m * vec = [d00, 0; 0, d11]`
-- |
unCouple :: Ellipse -> Number /\ Number /\ Number
unCouple (Ellipse e) =
  let t = 0.5 * atan (e.c/ (e.a - e.b))
      a = e.a
      b = e.b
      c = e.c
      d00 = a*cos t*cos t + b*sin t*sin t + c*cos t*sin t
      d11 = a*sin t*sin t + b*cos t*cos t - c*cos t*sin t
  in t /\ d00 /\ d11

-- |
-- | Semi-axes of the ellipse
-- |
ellipseDimensions :: Ellipse -> Number /\ Number
ellipseDimensions e =
  let
    _ /\ d00 /\ d11 = unCouple e
    l = residualConstant e
  in sqrt (abs $ l / d00) /\ sqrt (abs $ l / d11) 

-- |
-- | Explicit construction of a point of the ellipse from a point
-- | of the unit circle such that the four cardinal circular points
-- | correspond to the extremities of the axes of the ellipse.
-- |
fromUnitCircle :: Ellipse -> Point 2 -> Point 2
fromUnitCircle ee@(Ellipse e) p =
  let
    dx /\ dy = ellipseDimensions ee
    t /\ _ = unCouple ee
  in e.center <+| 
    ( rotated t 
        $ vector 
          (point zero) 
          (point $ 
            (p `index` 0 * dx)^0
              +(p `index` 1 * dy)^1)
    )

-- |
-- | The 2 points `F0` and `F1` such that 
-- | `MF0 + MF1 = 2 * max(ellipseDimensions e)` for every `M` of the ellipse.
-- |
foci :: Ellipse -> Point 2 /\ Point 2
foci e =
  let
    a /\ b = ellipseDimensions e
    c = sqrt $ abs $ a*a - b*b
  in 
    if a > b
      then 
        fromUnitCircle e (point $ (-c/a)^0) 
          /\ fromUnitCircle e (point $ (c/a)^0)
      else 
        fromUnitCircle e (point $ (-c/b)^1) 
          /\ fromUnitCircle e (point $ (c/b)^1)

mkMatrix :: Array (Point 2) -> Matrix Number
mkMatrix ps =
  let  line :: Int /\ Point 2 -> _
       line (i /\ p) = (x*x)^i^0 + (y*y)^i^1 + (x*y)^i^2 + x^i^3 + y^i^4
        where
          x = p `index` 0
          y = p `index` 1
  in Matrix { height: 5
            , width: 5
            , coefficients:
                sum $ line <$> zip (0..4) ps
            }

-- |
-- | Extracts the relevant parts of an ellipse defined by 5 points
-- | (all different from the origin):
-- | symmetric 2X2 matrix /\ position of the center
-- |
-- | ### Computation of the parameters of an ellipse passing through the origin (`point zero`) CANNOT  be done with the `quadratic` function even if the five points are different from the origin. See in the test file how to make two translations to use it anyway. 
-- | 

quadratic :: Array (Point 2) -> Ellipse
quadratic arr =
  let 
    q = pluSolve (mkMatrix arr) $
      Matrix
        { coefficients: 1.0^0^0 + 1.0^1^0 + 1.0^2^0 + 1.0^3^0 + 1.0^4^0
        , height: 5
        , width: 1
        }
    a = q !! [0,0]
    b = q !! [1,0]
    c = q !! [2,0]
    d = q !! [3,0]
    e = q !! [4,0]
    h = (e*c - 2.0*b*d) / (4.0*a*b - c*c)
    k = (c*d - 2.0*a*e) / (4.0*a*b - c*c)
    t = 0.5 * atan (c/ (a - b))
    d00 = a*cos t*cos t + b*sin t*sin t + c*cos t*sin t
    d11 = a*sin t*sin t + b*cos t*cos t - c*cos t*sin t
    l = 1.0 - (a*h*h + b*k*k + c*h*k + d*h + e*k)

  in 
    ellipse 
      (point $ h^0 + k^1) 
      (sqrt (abs $ l / d00) /\ sqrt (abs $ l / d11)) 
      t

-- |
-- | The only ellipse tangent to the 5 sides of the polygon
-- | described by its ordered vertices.
-- |
brianchon :: Point 2 -> Point 2 -> Point 2 -> Point 2 -> Point 2 -> Ellipse
brianchon a b c d e =
  quadratic $ concat $ a' <> b' <> c' <> d' <> e'
    where
      a' = 
        let o = line b d `meets` line e c 
        in (\l -> line c d `meets` l) <$> line a <$> o
      b' = 
        let o = line c e `meets` line a d 
        in (\l -> line d e `meets` l) <$> line b <$> o
      c' = 
        let o = line d a `meets` line b e 
        in (\l -> line e a `meets` l) <$> line c <$> o
      d' = 
        let o = line e b `meets` line c a 
        in (\l -> line a b `meets` l) <$> line d <$> o
      e' = 
        let o = line a c `meets` line d b 
        in (\l -> line b c `meets` l) <$> line e <$> o

-- |
-- | Computes the relevant parts of an ellipse defined by :
-- | * its center
-- | * one of its cardinal points, (this sets the first semi-axis), and
-- | * the length of the other semi-axis.
-- | Could also be defined with 5 points :
-- | * the 4 cardinal points,
-- | * a fifth point defined as
-- |   the sum of two consecutive cardinal vectors, over `sqrt(2)`.
-- |
cardinal :: Point 2 -> Point 2 -> Number -> Ellipse
cardinal g a mb =
  ellipse g (length ga /\ mb) $ atan2 (ga `index` 1) (ga `index` 0)
    where
      ga = vector g a

-- |
-- | Biggest ellipse in a parallelogram defined by:
-- | * its center
-- | * the middle of one of its sides
-- | * the middle of the next side.
-- |
rytz :: Point 2 -> Point 2 -> Point 2 -> Ellipse
rytz g i j =
  cardinal g a mb where
    gj = vector g j
    k = g <+| normalTo [gj]
    l = middle $ segment i k
    radius = length $ vector l g
    ms = circle l radius `meets` line i k
    a /\ mb =
      case uncons ms of
        Just { head: a', tail: rest }
          -> case uncons rest of
              Just { head: b', tail: _ }
                -> (
                  g <+| 
                      (scale (length (vector i a')) $ normalized $ vector g b'
                      )
                    ) /\ length (vector i b')
              _ -> g /\ 0.0
        _ -> g /\ 0.0

-- |
-- | Biggest ellipse in a triangle.
-- | Could also be defined with 5 points :
-- | * the 3 segment's middles,
-- | * the intersection of a median and the symmetric of the opposite side
-- |   with respect to isobarycenter and
-- | * another intersection of a median and the symmetric of the opposite  
-- |   side with respect to isobarycenter.
-- |
steiner :: Point 2 -> Point 2 -> Point 2 -> Ellipse
steiner p1 p2 p3 =
  cardinal g e mf where
    affix p = Cartesian (p `index` 0) (p `index` 1)
    manifest z = point $ (real z)^0 + (imag z)^1
    zA = affix p1
    zB = affix p2
    zC = affix p3
    a = Cartesian 3.0 0.0
    b = Cartesian (-2.0) 0.0 * (zA + zB + zC)
    c = zA * zB + zA * zC + zB * zC
    delta = b * b - Cartesian 4.0 0.0 * a * c
    s = pow delta 0.5
    f1 = (-b + s) / Cartesian 2.0 0.0 / a
    f2 = (-b - s) / Cartesian 2.0 0.0 / a
    g = manifest $ (f1 + f2) / Cartesian 2.0 0.0
    det u v = u `index` 0 * v `index` 1 - u `index` 1 * v `index` 0
    i1 = 
      (
        magnitudeSquared (zA-zB) 
          + magnitudeSquared (zB-zC) 
          + magnitudeSquared (zC-zA)
      ) / 2.0
    i2 = abs $ sqrt 3.0 * det (vector p1 p2) (vector p2 p3)
    mf = (sqrt (i1 + i2) - sqrt (i1 - i2)) / 6.0
    me = Cartesian ((sqrt (i1 + i2) + sqrt (i1 - i2)) / 6.0) 0.0
    e = g <+| vector (point zero) (manifest $ me * normalize (f1 - f2))

-- |
-- | Translation adapted to the chosen representation of an ellipse.
-- |
moveEllipse :: Vector 2 -> Ellipse -> Ellipse
moveEllipse v e =
  let
    i = fromUnitCircle e (point $ 1.0^0)
    j = fromUnitCircle e (point $ 1.0^1)
    g = ellipseCenter e
  in cardinal (g <+| v) (i <+| v) (length $ vector g j)

-- |
-- | Rotation adapted to the chosen representation of an ellipse.
-- |
turnEllipse :: Number -> Ellipse -> Ellipse
turnEllipse t e =
  let
    i = fromUnitCircle e (point $ 1.0^0)
    j = fromUnitCircle e (point $ 1.0^1)
    g = ellipseCenter e
  in cardinal g (g <+| (rotated t $ vector g i)) (length $ vector g j)

-- |
-- | Scaling adapted to the chosen representation of an ellipse.
-- |
expandEllipse :: Number /\ Number -> Ellipse -> Ellipse
expandEllipse (kx /\ ky) e =
  let
    i = fromUnitCircle e (point $ 1.0^0)
    j = fromUnitCircle e (point $ 1.0^1)
    g = ellipseCenter e
  in cardinal g (g <+| scale kx (vector g i)) ((_ * ky) $ length $ vector g j)

roots2 :: Polynomial Number -> Array (Cartesian Number)
roots2 f =
  [ (-b - s) / n 2.0 / a
  , (-b + s) / n 2.0 / a
  ]
 where
    n x = Cartesian x 0.0
    a = n (f!2)
    b = n (f!1)
    c = n (f!0)
    s = pow (b*b - n 4.0 *a*c) 0.5
 
roots4 :: Polynomial Number -> Array (Cartesian Number)
roots4 f = 
  [ bb - s - pow (pp+q/s) 0.5 / n 2.0
  , bb - s + pow (pp+q/s) 0.5 / n 2.0
  , bb + s - pow (pp-q/s) 0.5 / n 2.0
  , bb + s + pow (pp-q/s) 0.5 / n 2.0
  ]
  where
    n x = Cartesian x 0.0
    a = n (f!4)
    b = n (f!3)
    c = n (f!2)
    d = n (f!1)
    e = n (f!0)
    d0 = c*c-n 3.0*b*d + n 12.0*a*e
    d1 = n 2.0*c*c*c - n 9.0*b*c*d + n 27.0 *b*b*e
      + n 27.0*a*d*d - n 72.0*a*c*e
    qq = 
      pow 
        (
          (d1 + pow (d1*d1-n 4.0 * d0*d0*d0) 0.5) / n 2.0
        ) (1.0/3.0)
    p = (n 8.0*a*c-n 3.0*b*b) / (n 8.0*a*a)
    q = (b*b*b-n 4.0*a*b*c+n 8.0*a*a*d) / (n 8.0*a*a*a)
    s = pow (n (-2.0/3.0) * p + (qq+d0/qq)/a/n 3.0) 0.5 / n 2.0
    bb = -b/a/n 4.0
    pp = -n 4.0 *s*s-n 2.0*p
      
canonicalEllipseCircle 
  :: Number -> Number -> Number -> Number -> Number -> Array (Point 2)
canonicalEllipseCircle a b h k r = arr
  where
    c = 1.0
    sq z = z*z
    p = 
      if abs k < 1e-9
         then (a-b)^2+(2.0*b*h)^1+(b*(r*r-h*h)-c)^0
         else
          (sq $ a-b)^4
          + (4.0*b*h*(a-b))^3
          + (2.0*(b*b*(3.0*h*h+k*k-r*r)-(a-b)*c+a*b*(r*r+k*k-h*h)))^2
          + (4.0*b*h*(b*(r*r-h*h-k*k)-c))^1
          + (b*b*sq(r*r-h*h-k*k)+2.0*b*c*(h*h-k*k-r*r)+c*c)^0
    xs = real <$> filter ((_ < 1e-4) <<< abs <<< imag) (roots4 p)
    arr = do
      x <- xs
      if abs k < 1e-9
         then do
           let y2 = r*r - sq (x-h)
           if y2 < 0.0
              then []
              else [point $ x^0+(sqrt y2)^1, point $ x^0-(sqrt y2)^1]
          else
            [point $ x^0+((k - (r*r-sq(x-h)+(a*x*x-c)/b) / k) / 2.0)^1]

canonicalEllipseLine 
  :: Number -> Number -> Number -> Number -> Number -> Array (Point 2)
canonicalEllipseLine a b r s t = arr
  where
    arr | abs r < 1e-9 = 
            do
              let
                y = - t / s
                x2 = (1.0 - b*y*y) / a
              if x2 < 0.0
                then []
                else [point $ (sqrt x2)^1+y^1, point $ -(sqrt x2)^0+y^1]
        | abs s < 1e-9 = 
            do
              let
                x = - t / r
                y2 = (1.0 - a*x*x) / b
              if y2 < 0.0
                then []
                else [point $ x^0+(sqrt y2)^1, point $ x^0-(sqrt y2)^1]
        | otherwise = 
            do
                x <- xs
                [point $ x^0-((t+r*x)/s)^1] 
            where
              p = (a*s*s+b*r*r)^2+(2.0*b*t*r)^1+(b*t*t-s*s)^0
              xs = real <$> filter ((_ < 1e-4) <<< abs <<< imag) (roots2 p)

instance Intersectable Ellipse Ellipse where
  meets e1 e2 = undo <$> canonicalEllipseCircle a b h k r where
    z = Vector $ 1.0^2 :: Vector 3
    a1 = fromUnitCircle e1 (point $ 1.0^0)
    b1 = fromUnitCircle e1 (point $ 1.0^1)
    c1 = ellipseCenter e1
    a2 = fromUnitCircle e2 (point $ 1.0^0)
    b2 = fromUnitCircle e2 (point $ 1.0^1)
    c2 = ellipseCenter e2
    
    scene = { a1, b1, c1, a2, b2, c2 }
    
    step0 = mapRecord (immerse :: Point 2 -> Point 3) scene
    vec0 = vector step0.c1 $ point zero
    
    step1 = 
      mapRecord 
        (
          (_ <+| vec0)
          >>> vector (point zero)
          :: Point 3 -> Vector 3
        ) step0
    
    major = if length step1.b1 > length step1.a1 then step1.b1 else step1.a1
    minor = if length step1.b1 < length step1.a1 then step1.b1 else step1.a1
    vec1 = normalized minor
    ang1 = acos $ length minor / length major
    
    step2 = mapRecord (revolution vec1 ang1 :: Vector 3 -> Vector 3) step1
    step3 = 
      mapRecord 
        ( project z z
        >>> (point zero <+| _) 
        >>> drain 
        :: Vector 3 -> Point 2
        ) step2

    e3 = rytz step3.c2 step3.a2 step3.b2
    vec3 = vector (ellipseCenter e3) $ point zero    
    ang3 /\ _ /\ _ = unCouple e3
    
    step4 = 
      mapRecord 
        (
          (_ <+| vec3) 
          >>> vector (point zero)
          >>> rotated (-ang3)
          >>> (point zero <+| _) 
          :: Point 2 -> Point 2
        ) step3
    i4 = ellipseInternal $ turnEllipse (-ang3) $ moveEllipse vec3 e3
    
    a = i4 !0!0
    b = i4 !1!1
    h = step4.c1 `index` 0
    k = step4.c1 `index` 1
    r = length $ vector step4.c1 step4.a1
    undo = 
      vector (point zero) 
        >>> rotated ang3
        >>> (_ - vec3)
        >>> (immerse :: Vector 2 -> Vector 3)
        >>> project (normalTo [step2.a1, step2.b1]) z
        >>> revolution vec1 (-ang1)
        >>> (_ - vec0)
        >>> (drain :: Vector 3 -> Vector 2)
        >>> (point zero <+| _)

instance Intersectable Ellipse (Line 2) where
 meets e1 (Line (a2 /\ b2)) = undo <$> canonicalEllipseLine a b r s t 
  where
    a1 = fromUnitCircle e1 (point $ 1.0^0)
    b1 = fromUnitCircle e1 (point $ 1.0^1)
    c1 = ellipseCenter e1
    
    scene = { a1, b1, c1, a2, b2 }
    
    vec0 = vector c1 $ point zero
    
    step0 = 
      mapRecord 
        (
          (_ <+| vec0)
          :: Point 2 -> Point 2
        ) scene
    
    ang1 /\ _ /\ _ = unCouple e1
    
    step1 = 
      mapRecord 
        (
          vector (point zero)
          >>> rotated (-ang1)
          >>> (point zero <+| _) 
          :: Point 2 -> Point 2
        ) step0
    i2 = ellipseInternal $ turnEllipse (-ang1) $ moveEllipse vec0 e1
    s2 = system (line step1.a2 step1.b2)
    
    a = i2 !0!0
    b = i2 !1!1
    r = s2 !0!0
    s = s2 !0!1
    t = s2 !0!2
    undo = 
      vector (point zero) 
        >>> rotated ang1
        >>> (_ - vec0)
        >>> (point zero <+| _)
      
instance Intersectable (Line 2) Ellipse where
  meets l e = meets e l

instance Intersectable Ellipse (HalfLine 2) where
  meets e (HalfLine (origin /\ direction)) =
    let l' = line origin (origin <+| direction)
     in filter (\p -> cosAngle (vector origin p) direction >= 0.0) $
         e `meets` l'
         
instance Intersectable (HalfLine 2) Ellipse where
  meets hl e = meets e hl

instance Intersectable Ellipse (Segment 2) where
  meets e (Segment (origin /\ extremity)) =
    let hl = halfline origin (vector origin extremity)
     in 
       filter 
        ( \p -> 
          cosAngle 
            (vector origin extremity) 
            (vector p extremity) >= 0.0
        ) $
         e `meets` hl
         
instance Intersectable (Segment 2) Ellipse where
  meets s e = meets e s

instance Intersectable Ellipse Circle where
  meets e1 (Circle (center /\ radius)) =  undo <$> canonicalEllipseCircle a b h k radius
    where
      a1 = fromUnitCircle e1 (point $ 1.0^0)
      b1 = fromUnitCircle e1 (point $ 1.0^1)
      c1 = ellipseCenter e1
    
      scene = { a1, b1, center }
    
      vec0 = vector c1 $ point zero
    
      step0 = 
        mapRecord 
          (
            (_ <+| vec0)
            :: Point 2 -> Point 2
          ) scene
    
      ang1 /\ _ /\ _ = unCouple e1
    
      step1 = 
        mapRecord 
          (
            vector (point zero)
            >>> rotated (-ang1)
            >>> (point zero <+| _) 
            :: Point 2 -> Point 2
          ) step0
      i2 = ellipseInternal $ turnEllipse (-ang1) $ moveEllipse vec0 e1
    
      a = i2 !0!0
      b = i2 !1!1
      c = step1.center
      h = c `index` 0
      k = c `index` 1
      undo = 
        vector (point zero) 
          >>> rotated ang1
          >>> (_ - vec0)
          >>> (point zero <+| _)
      
instance Intersectable Circle Ellipse where
  meets c e = meets e c
