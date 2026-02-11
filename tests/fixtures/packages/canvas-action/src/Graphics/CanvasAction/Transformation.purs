module Graphics.CanvasAction.Transformation
  ( DOMMatrix
  , DOMMatrixRecord

  , multiplyDOMMatrix
  , invertDOMMatrix
  , fromRecord
  , fromNumbers
  , toRecord

  , transform
  , getTransform
  , setTransform
  , resetTransform
  , transformedBy
  , transformedTo
  , transformPoint

  , translate
  , scale
  , rotate
  , rotateAround
  , skew
  ) where

import Prelude

import Data.Vector.Polymorphic ((><))
import Data.Vector.Polymorphic.Class (class AsPosEndo, class ToPos, asPosEndo, toPos)
import Effect (Effect)
import Effect.Class (liftEffect)
import Graphics.Canvas as C
import Graphics.CanvasAction (class MonadCanvasAction, Context2D, getCtx)
import Data.Number as Number

foreign import data DOMMatrix ∷ Type

instance showDOMMatrix ∷ Show DOMMatrix where
  show m = "(fromRecord " <> show (toRecord m) <> ")"

instance Eq DOMMatrix where
  eq m1 m2 = eq (toRecord m1) (toRecord m2)

instance Semigroup DOMMatrix where
  append = multiplyDOMMatrix

instance Monoid DOMMatrix where
  mempty = fromRecord { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: 0.0, f: 0.0 }

type DOMMatrixRecord =
  { a ∷ Number
  , b ∷ Number
  , c ∷ Number
  , d ∷ Number
  , e ∷ Number
  , f ∷ Number
  }

toTransform ∷ DOMMatrix → C.Transform
toTransform = toRecord

foreign import multiplyDOMMatrix ∷ DOMMatrix → DOMMatrix → DOMMatrix

foreign import invertDOMMatrix ∷ DOMMatrix → DOMMatrix

foreign import fromRecord ∷ DOMMatrixRecord → DOMMatrix

fromNumbers ∷ Number → Number → Number → Number → Number → Number → DOMMatrix
fromNumbers a b c d e f = fromRecord { a, b, c, d, e, f }

foreign import toRecord ∷ DOMMatrix → DOMMatrixRecord

transform ∷ ∀ m. MonadCanvasAction m ⇒ DOMMatrix → m Unit
transform matrix = do
  ctx ← getCtx
  liftEffect (C.transform ctx (toTransform matrix))

foreign import getTransformImpl ∷ Context2D → Effect DOMMatrix

-- | Gets the current transformation matrix
getTransform ∷ ∀ m. MonadCanvasAction m ⇒ m DOMMatrix
getTransform = getCtx >>= map liftEffect getTransformImpl

-- | Sets the transformation matrix to the given DOMMatrix
setTransform ∷ ∀ m. MonadCanvasAction m ⇒ DOMMatrix → m Unit
setTransform matrix = do
  ctx ← getCtx
  liftEffect (C.setTransform ctx (toTransform matrix))

-- | Resets the transformation matrix
resetTransform ∷ ∀ m. MonadCanvasAction m ⇒ m Unit
resetTransform = setTransform mempty

-- | Applies the given transformation, runs the given action, and returns the
-- | transformation matrix to its previous state.
transformedBy ∷ ∀ m a. MonadCanvasAction m ⇒ DOMMatrix → m a → m a
transformedBy t action = do
  old ← getTransform
  transform t *> action <* setTransform old

-- | Sets the transformation matrix to the given DOMMatrix, runs the given
-- | action, and returns the transformation matrix to its previous state.
transformedTo ∷ ∀ m a. MonadCanvasAction m ⇒ DOMMatrix → m a → m a
transformedTo t action = do
  old ← getTransform
  setTransform t *> action <* setTransform old

-- | Applies a tranformation matrix to a point
transformPoint ∷ ∀ p. AsPosEndo Number p ⇒ DOMMatrix → p → p
transformPoint matrix = asPosEndo \(x >< y) → do
  let { a, b, c, d, e, f } = toRecord matrix
  (x * a + y * c + e >< b * x + y * d + f)

-- | Constructs a DOMMatrix that applies a translation
translate ∷ Number → Number → DOMMatrix
translate tx ty = fromNumbers 1.0 0.0 0.0 1.0 tx ty

-- | Constructs a DOMMatrix that applies a scaling
scale ∷ Number → Number → DOMMatrix
scale sx sy = fromNumbers sx 0.0 0.0 sy 0.0 0.0

-- | Constructs a DOMMatrix that applies a rotation
rotate ∷ Number → DOMMatrix
rotate theta = fromNumbers cos sin (-sin) cos 0.0 0.0
  where
  sin = Number.sin theta
  cos = Number.cos theta

-- | Constructs a DOMMatrix that applies a rotation around the specified point
rotateAround ∷ ∀ p. ToPos Number p ⇒ p → Number → DOMMatrix
rotateAround pos theta = translate x y <> rotate theta <> translate (-x) (-y)
  where
  (x >< y) = toPos pos

-- | Constructs a DOMMatrix that applies a skewing
skew ∷ Number → Number → DOMMatrix
skew sx sy = fromNumbers 1.0 sy sx 1.0 0.0 0.0
