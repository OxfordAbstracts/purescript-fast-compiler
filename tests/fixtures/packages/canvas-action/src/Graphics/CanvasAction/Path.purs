module Graphics.CanvasAction.Path
  ( PathData
  , Path2D
  , PathAction

  , getCursor
  , getSubpathStart

  , moveTo
  , closePath
  , lineTo
  , quadraticCurveTo
  , bezierCurveTo
  , ArcData
  , arcTo
  , arcTo_
  , ellipse
  , arc
  , rect
  , addPath
  , addPath'

  , FillRule(..)
  , runPath
  , fill
  , fillWith
  , stroke
  , strokeWith
  , clip

  , moveBy
  , lineBy
  , line
  , lines
  , polygon
  , circle
  , arcBy
  , arcBy_
  , abortSubpath
  ) where

import Prelude

import Control.Apply (lift2)
import Data.Array (fromFoldable, uncons)
import Data.Foldable (class Foldable, any, traverse_)
import Data.Maybe (Maybe(..))
import Data.Number (isFinite, isNaN, cos, sin, tau)
import Data.Tuple (Tuple(..))
import Data.Vector.Polymorphic (Vector2, convertRegion, length, (><))
import Data.Vector.Polymorphic.Class (class ToPos, class ToRegion, toPos)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Graphics.Canvas (Context2D, Rectangle)
import Graphics.CanvasAction (class CanvasStyle, class MonadCanvasAction, filled, getCtx, stroked)
import Graphics.CanvasAction.Transformation (DOMMatrix, rotate, toRecord, transformPoint, translate)

-- | A JavaScript `Path2D` Object
foreign import data JsPath2D ∷ Type

foreign import addPathImpl ∷ JsPath2D → DOMMatrix → JsPath2D → Effect Unit
foreign import closePathImpl ∷ JsPath2D → Effect Unit
foreign import moveToImpl ∷ Number → Number → JsPath2D → Effect Unit
foreign import lineToImpl ∷ Number → Number → JsPath2D → Effect Unit
foreign import bezierCurveToImpl
  ∷ Number → Number → Number → Number → Number → Number → JsPath2D → Effect Unit

foreign import quadraticCurveToImpl
  ∷ Number → Number → Number → Number → JsPath2D → Effect Unit

foreign import arcToImpl
  ∷ Number → Number → Number → Number → Number → JsPath2D → Effect Unit

foreign import ellipseImpl
  ∷ Number
  → Number
  → Number
  → Number
  → Number
  → Number
  → Number
  → Boolean
  → JsPath2D
  → Effect Unit

foreign import rectImpl
  ∷ Number → Number → Number → Number → JsPath2D → Effect Unit

-- | A record with data for the start of the current subpath and the location of
-- | the path cursor
type PathData =
  { subpathStart ∷ Maybe (Vector2 Number)
  , cursor ∷ Vector2 Number
  }

-- | A data type that contains a JavaScript `Path2D` object and `PathData`. The
-- | constructor is not exported because that would allow for desync between the
-- | JS `Path2D` and its data.
data Path2D = Path2D JsPath2D PathData

newtype PathAction a = PathAction (Path2D → Effect (Tuple PathData a))

instance Functor PathAction where
  map = liftM1

instance Apply PathAction where
  apply = ap

instance Applicative PathAction where
  pure a = PathAction \(Path2D _ pathData) → pure (Tuple pathData a)

instance Bind PathAction where
  bind (PathAction act) f = PathAction \path2d@(Path2D path _) → do
    Tuple pathData' a ← act path2d
    case f a of
      PathAction act' → act' (Path2D path pathData')

instance Monad PathAction

instance MonadEffect PathAction where
  liftEffect f = PathAction \(Path2D _ pathData) → Tuple pathData <$> f

instance Semigroup a ⇒ Semigroup (PathAction a) where
  append = lift2 append

instance Monoid a ⇒ Monoid (PathAction a) where
  mempty = pure mempty

isInfiniteOrNaN ∷ Number → Boolean
isInfiniteOrNaN n = not isFinite n || isNaN n

-- | Get the cursor position of the path
getCursor ∷ PathAction (Vector2 Number)
getCursor = PathAction
  \(Path2D _ pathData) → pure (Tuple pathData pathData.cursor)

-- | Get the start position of the current subpath
getSubpathStart ∷ PathAction (Maybe (Vector2 Number))
getSubpathStart = PathAction \(Path2D _ pathData) →
  pure (Tuple pathData pathData.subpathStart)

lineToHelper
  ∷ Boolean → (JsPath2D → Effect Unit) → Vector2 Number → PathAction Unit
lineToHelper invalid effect end = PathAction \(Path2D path pathData) →
  case invalid, pathData.subpathStart of
    true, _ → pure (Tuple pathData unit)
    false, Just _ → ado
      effect path
      in Tuple (pathData { cursor = end }) unit
    false, Nothing → ado
      effect path
      in Tuple (pathData { cursor = end, subpathStart = Just end }) unit

-- | Start a new sub-path at the given position
moveTo ∷ ∀ p. ToPos Number p ⇒ p → PathAction Unit
moveTo pos = PathAction \(Path2D path pathData) →
  if invalid then pure (Tuple pathData unit)
  else ado
    moveToImpl x y path
    in Tuple (pathData { cursor = p, subpathStart = Just p }) unit
  where
  p@(x >< y) = toPos pos
  invalid = any isInfiniteOrNaN p

-- | Draw a line from the current position to the starting position of the
-- | sub-path
closePath ∷ PathAction Unit
closePath = PathAction \(Path2D path pathData) → case pathData.subpathStart of
  Nothing → pure (Tuple pathData unit)
  Just start → Tuple (pathData { cursor = start }) <$> closePathImpl path

-- | Draw a line from the last point in the sub-path to the given position
lineTo ∷ ∀ p. ToPos Number p ⇒ p → PathAction Unit
lineTo pos = lineToHelper invalid (lineToImpl x y) p
  where
  p@(x >< y) = toPos pos
  invalid = any isInfiniteOrNaN p

-- | Adds a quadratic Bézier curve to the path. The first point is the control
-- | point and the second one is the end point.
quadraticCurveTo ∷ ∀ p. ToPos Number p ⇒ p → p → PathAction Unit
quadraticCurveTo cp' pos =
  lineToHelper invalid (quadraticCurveToImpl cpx cpy x y) p
  where
  p@(x >< y) = toPos pos
  cp@(cpx >< cpy) = toPos cp'
  invalid = any (any isInfiniteOrNaN) [ p, cp ]

-- | Adds a cubic Bézier curve to the path. The first two points are control
-- | points and the third one is the end point.
bezierCurveTo ∷ ∀ p. ToPos Number p ⇒ p → p → p → PathAction Unit
bezierCurveTo cp1' cp2' pos =
  lineToHelper invalid (bezierCurveToImpl cp1x cp1y cp2x cp2y x y) p
  where
  p@(x >< y) = toPos pos
  cp1@(cp1x >< cp1y) = toPos cp1'
  cp2@(cp2x >< cp2y) = toPos cp2'
  invalid = any (any isInfiniteOrNaN) [ p, cp1, cp2 ]

-- The following functions are for internal use, for calculating `ArcData`

-- | Given points a, b, and c, returns whether c is to the left when looking
-- | from a to b.
isLeftOf ∷ Vector2 Number → Vector2 Number → Vector2 Number → Boolean
isLeftOf (ax >< ay) (bx >< by) (cx >< cy) =
  (bx - ax) * (cy - ay) <= (by - ay) * (cx - ax)

-- | Returns whether the three given points are colinear
colinear ∷ Vector2 Number → Vector2 Number → Vector2 Number → Boolean
colinear (ax >< ay) (bx >< by) (cx >< cy) =
  (bx - ax) * (cy - ay) == (by - ay) * (cx - ax)

-- | Sets a Vector2's length to 1.0
normalize ∷ Vector2 Number → Vector2 Number
normalize vec = (_ / length vec) <$> vec

swap ∷ Vector2 Number → Vector2 Number
swap (x >< y) = (y >< x)

-- | Finds the intersection between two lines
intersect
  ∷ (Number → Vector2 Number) → (Number → Vector2 Number) → Vector2 Number
intersect l1 l2 = do
  let
    l1o@(x1 >< y1) = l1 0.0
    l2o@(x2 >< y2) = l2 0.0
    (xv1 >< yv1) = l1 1.0 - l1o
    (xv2 >< yv2) = l2 1.0 - l2o
    t1 = (xv2 * (y1 - y2) - yv2 * (x1 - x2)) / (xv1 * yv2 - xv2 * yv1)
  l1 t1

-- https://stackoverflow.com/questions/51223685/create-circle-tangent-to-two-lines-with-radius-r-geometry
getArcData
  ∷ Vector2 Number → Vector2 Number → Vector2 Number → Number → ArcData
getArcData p0 p1 p2 radius =
  if colinear p0 p1 p2 || radius == 0.0 then
    { start: p1, end: p1, center: p1, radius, nonZero: false }
  else do
    let
      rot90 = swap >>> ((identity >< negate) <*> _)
      p01Vel = normalize (p1 - p0)
      p01 t = p0 + map (t * _) p01Vel
      p21Vel = normalize (p1 - p2)
      p21 t = p2 + map (t * _) p21Vel
      p01shiftVector = rot90 (p01Vel * pure radius)
        # if isLeftOf p0 p1 p2 then identity else map negate
      p01shifted t = p01 t + p01shiftVector
      p21shiftVector = rot90 (p21Vel * pure radius)
        # if isLeftOf p2 p1 p0 then identity else map negate
      p21shifted t = p21 t + p21shiftVector
      center = intersect p01shifted p21shifted
    { start: center - p01shiftVector
    , end: center - p21shiftVector
    , center
    , radius
    , nonZero: true
    }

type ArcData =
  { start ∷ Vector2 Number
  , end ∷ Vector2 Number
  , center ∷ Vector2 Number
  , radius ∷ Number
  , nonZero ∷ Boolean
  }

arcTo ∷ ∀ p. ToPos Number p ⇒ p → p → Number → PathAction ArcData
arcTo p1' p2' radius = do
  p0 ← getCursor
  let arcData = getArcData p0 p1 p2 radius
  lineToHelper invalid (arcToImpl p1x p1y p2x p2y radius) arcData.end
  pure arcData
  where
  p1@(p1x >< p1y) = toPos p1'
  p2@(p2x >< p2y) = toPos p2'
  invalid = any isInfiniteOrNaN [ p1x, p1y, p2x, p2y, radius ] || radius < 0.0

arcTo_ ∷ ∀ p. ToPos Number p ⇒ p → p → Number → PathAction Unit
arcTo_ p1 p2 radius = void (arcTo p1 p2 radius)

ellipse
  ∷ ∀ p
  . ToPos Number p
  ⇒ p
  → Number
  → Number
  → Number
  → Number
  → Number
  → Boolean
  → PathAction Unit
ellipse center radiusX radiusY rotation startAngle endAngle anticlockwise =
  PathAction \(Path2D path pathData) →
    if invalid then pure (Tuple pathData unit)
    else ado
      ellipseImpl x y radiusX radiusY rotation
        startAngle
        endAngle
        anticlockwise
        path
      in Tuple (pathData { cursor = endPos }) unit
  where
  (x >< y) = toPos center
  invalid = any isInfiniteOrNaN
    [ x, y, radiusX, radiusY, rotation, startAngle, endAngle ]
  anglePoint angle = transformPoint (translate x y <> rotate rotation)
    (radiusX * cos angle >< radiusY * sin angle)
  endPos = anglePoint
    if anticlockwise then
      if endAngle - startAngle >= tau then startAngle else endAngle
    else if startAngle - endAngle >= tau then startAngle
    else endAngle

arc
  ∷ ∀ p
  . ToPos Number p
  ⇒ p
  → Number
  → Number
  → Number
  → Boolean
  → PathAction Unit
arc center radius = ellipse center radius radius 0.0

rect ∷ ∀ r. ToRegion Number r ⇒ r → PathAction Unit
rect region =
  if invalid then pure unit
  else do
    moveTo (x >< y)
    lineTo (x + width >< y)
    lineTo (x + width >< y + height)
    lineTo (x >< y + height)
    closePath
  where
  { x, y, width, height } = convertRegion region ∷ Rectangle
  invalid = any isInfiniteOrNaN [ x, y, width, height ]

-- | Add the contents of a `Path2D` to the current path
addPath ∷ Path2D → PathAction Unit
addPath = addPath' mempty

-- This doesn't follow the whatwg standard (https://html.spec.whatwg.org/multipage/canvas.html#dom-path2d-addpath),
-- which says to create a new subpath at the last point of the supplied path.
-- Instead, it does what all browsers seem to do, which is to inherit the start
-- and cursor positions of the last subpath of the supplied path.
-- | Add the contents of a `Path2D` to the current path, transforming it
-- | according to the provided `DOMMatrix`
addPath' ∷ DOMMatrix → Path2D → PathAction Unit
addPath' matrix (Path2D path2 { cursor, subpathStart }) =
  PathAction \(Path2D path pathData) →
    if invalid then pure (Tuple pathData unit)
    else ado
      addPathImpl path2 matrix path
      in Tuple pathData2' unit
  where
  { a, b, c, d, e, f } = toRecord matrix
  invalid = any isInfiniteOrNaN [ a, b, c, d, e, f ]
  pathData2' =
    { cursor: transformPoint matrix cursor
    , subpathStart: transformPoint matrix <$> subpathStart
    }

foreign import newPath2DImpl ∷ Effect JsPath2D
foreign import fillImpl ∷ Context2D → JsPath2D → String → Effect Unit
foreign import strokeImpl ∷ Context2D → JsPath2D → Effect Unit
foreign import clipImpl ∷ Context2D → JsPath2D → String → Effect Unit

-- | Enumerates the different fill rules
data FillRule = Nonzero | Evenodd

derive instance Eq FillRule

fillRuleToString ∷ FillRule → String
fillRuleToString Nonzero = "nonzero"
fillRuleToString Evenodd = "evenodd"

newPath2D ∷ ∀ m. MonadEffect m ⇒ m Path2D
newPath2D = ado
  jsPath ← liftEffect newPath2DImpl
  in Path2D jsPath { cursor: zero, subpathStart: Nothing }

-- | Create a `Path2D` from a `PathAction`
runPath ∷ ∀ m. MonadEffect m ⇒ PathAction Unit → m Path2D
runPath (PathAction action) = liftEffect do
  path@(Path2D jsPath _) ← newPath2D
  Tuple pathData _ ← action path
  pure (Path2D jsPath pathData)

-- | Fill a `Path2D`
fill ∷ ∀ m. MonadCanvasAction m ⇒ FillRule → Path2D → m Unit
fill rule (Path2D path _) = getCtx >>= \ctx →
  liftEffect (fillImpl ctx path (fillRuleToString rule))

-- | Fill a `Path2D` with the given style
fillWith
  ∷ ∀ m r. MonadCanvasAction m ⇒ CanvasStyle r ⇒ r → FillRule → Path2D → m Unit
fillWith style rule path = filled style (fill rule path)

-- | Stroke a `Path2D`
stroke ∷ ∀ m. MonadCanvasAction m ⇒ Path2D → m Unit
stroke (Path2D path _) = getCtx >>= \ctx → liftEffect (strokeImpl ctx path)

-- | Stroke a `Path2D` with the given style
strokeWith ∷ ∀ m r. MonadCanvasAction m ⇒ CanvasStyle r ⇒ r → Path2D → m Unit
strokeWith style path = stroked style (stroke path)

-- | Clip subsequent canvas drawings to a `Path2D`
clip ∷ ∀ m. MonadCanvasAction m ⇒ FillRule → Path2D → m Unit
clip rule (Path2D path _) = getCtx >>= \ctx →
  liftEffect (clipImpl ctx path (fillRuleToString rule))

-- | Move the cursor to a new position relative to its old position
moveBy ∷ ∀ p. ToPos Number p ⇒ p → PathAction Unit
moveBy pos = do
  cursor ← getCursor
  moveTo (cursor + p)
  where
  p = toPos pos

-- | Draw a line from the last point in the sub-path to the given position,
-- | measured relative to its old position
lineBy ∷ ∀ p. ToPos Number p ⇒ p → PathAction Unit
lineBy pos = do
  cursor ← getCursor
  lineTo (cursor + p)
  where
  p = toPos pos

-- | Move to the first point and draw a line to the second point
line ∷ ∀ p. ToPos Number p ⇒ p → p → PathAction Unit
line p1 p2 = moveTo p1 *> lineTo p2

-- | Append lines between all the specified points to the current subpath. First
-- | draws a line from the cursor position to the first point.
lines ∷ ∀ p f. ToPos Number p ⇒ Foldable f ⇒ f p → PathAction Unit
lines = traverse_ lineTo

-- | Draw a polygon with the specified points. Starts and ends on the first
-- | point.
polygon ∷ ∀ p f. ToPos Number p ⇒ Foldable f ⇒ f p → PathAction Unit
polygon = fromFoldable >>> uncons >>> case _ of
  Just { head, tail } → moveTo head *> traverse_ lineTo tail *> closePath
  Nothing → pure unit

-- | Draw a circle with the specified center and radius. Ends on the rightmost
-- | point of the circle.
circle ∷ ∀ p. ToPos Number p ⇒ p → Number → PathAction Unit
circle pos radius = do
  moveTo (x + radius >< y)
  arc pos radius 0.0 tau false
  where
  (x >< y) = toPos pos

-- | Like `arcTo`, but the first point is relative to the cursor position, and
-- | the second point is relative to the first point
arcBy ∷ ∀ p. ToPos Number p ⇒ p → p → Number → PathAction ArcData
arcBy pos1' pos2' radius = getCursor >>= \cursor →
  arcTo (cursor + pos1) (cursor + pos1 + pos2) radius
  where
  pos1 = toPos pos1'
  pos2 = toPos pos2'

-- | Like `arcTo_`, but the first point is relative to the cursor position, and
-- | the second point is relative to the first point
arcBy_ ∷ ∀ p. ToPos Number p ⇒ p → p → Number → PathAction Unit
arcBy_ pos1 pos2 radius = void (arcBy pos1 pos2 radius)

-- | Aborts the current subpath and starts a new one at the cursor position
abortSubpath ∷ PathAction Unit
abortSubpath = moveBy (0.0 >< 0.0)
