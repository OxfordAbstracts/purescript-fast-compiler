module Data.Vector.Polymorphic.Class
  ( XY
  , WH
  , XYWH

  , class ToPos
  , class FromPos
  , class AsPosEndo
  , class AsPos
  , toPos
  , fromPos
  , asPosEndo
  , asPos

  , class ToSize
  , class FromSize
  , class AsSizeEndo
  , class AsSize
  , toSize
  , fromSize
  , asSizeEndo
  , asSize

  , class ToRegion
  , class FromRegion
  , class AsRegionEndo
  , class AsRegion
  , toRegion
  , fromRegion
  , asRegionEndo
  , asRegion
  ) where

import Prelude

import Data.Vector.Polymorphic.Types (Rect(..), Vector2, (><), makeRect)
import Prim.Row (class Nub)
import Record (disjointUnion, set)
import Safe.Coerce (coerce)
import Type.Equality (class TypeEquals)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

-- Internal
toRecord ∷ ∀ r1 r2. TypeEquals r1 r2 ⇒ Record r1 → Record r2
toRecord = coerce

fromRecord ∷ ∀ r1 r2. TypeEquals r1 r2 ⇒ Record r2 → Record r1
fromRecord = coerce

_x ∷ Proxy "x"
_x = Proxy

_y ∷ Proxy "y"
_y = Proxy

_width ∷ Proxy "width"
_width = Proxy

_height ∷ Proxy "height"
_height = Proxy

-- | Shorthand describing a row containing x and y fields
type XY ∷ ∀ k. k -> Row k -> Row k
type XY a r = (x ∷ a, y ∷ a | r)

-- | Shorthand describing a row containing width and height fields
type WH ∷ ∀ k. k -> Row k -> Row k
type WH a r = (width ∷ a, height ∷ a | r)

-- | Shorthand describing a row containing x, y, width and height fields
type XYWH ∷ ∀ k. k -> Row k -> Row k
type XYWH a r = XY a + WH a + r

-- | Class describing types which represent a position on a 2D plane and can be
-- | turned into a `Vector2 a`.
class ToPos a pa | pa → a where
  toPos ∷ pa → Vector2 a

instance ToPos a (Vector2 a) where
  toPos = identity

instance ToPos a (Rect a) where
  toPos (Rect pos _) = pos

instance TypeEquals r1 (XY a r) ⇒ ToPos a (Record r1) where
  toPos = toRecord >>> \{ x, y } → x >< y

-- | Class describing types which represent a position on a 2D plane and can be
-- | constructed from a `Vector2 a`.
class FromPos a pa | pa → a where
  fromPos ∷ Vector2 a → pa

instance FromPos a (Vector2 a) where
  fromPos = identity

instance Semiring a ⇒ FromPos a (Rect a) where
  fromPos pos = Rect pos zero

instance fromPosXY ∷
  ( TypeEquals r1 (XY a r)
  , Nub (XY a r) (XY a r)
  , Semiring (Record r)
  ) ⇒
  FromPos a (Record r1) where
  fromPos (x >< y) = fromRecord $ disjointUnion { x, y } zero

-- | Class describing types which represent a position on a 2D plane and can be
-- | modified by any function of type `Vector2 a → Vector2 a`.
-- |
-- | Instances must satisfy the following law:
-- |
-- | - Identity: `asPosEndo identity = identity`
class AsPosEndo a pa | pa → a where
  asPosEndo ∷ (Vector2 a → Vector2 a) → pa → pa

instance AsPosEndo a (Vector2 a) where
  asPosEndo = identity

instance AsPosEndo a (Rect a) where
  asPosEndo f (Rect pos size) = Rect (f pos) size

instance TypeEquals r1 (XY a r) ⇒ AsPosEndo a (Record r1) where
  asPosEndo f r1 = do
    let
      record@{ x, y } = toRecord r1
      (x' >< y') = f (x >< y)
    record
      # set _x x'
      # set _y y'
      # fromRecord

-- | Class describing types which represent a position on a 2D plane and can be
-- | modified by any function of type `Vector2 a → Vector2 b`.
-- |
-- | Instances must satisfy the following law:
-- |
-- | - Identity: `asPos identity = identity`
class AsPos a b pa pb | pa → a, pb → b, pa b → pb where
  asPos ∷ (Vector2 a → Vector2 b) → pa → pb

instance AsPos a b (Vector2 a) (Vector2 b) where
  asPos = identity

instance asPosXY ∷
  ( TypeEquals r1 (XY a r)
  , TypeEquals r2 (XY b r)
  ) ⇒
  AsPos a b (Record r1) (Record r2) where
  asPos f r1 = do
    let
      record@{ x, y } = toRecord r1
      (x' >< y') = f (x >< y)
    record
      # set _x x'
      # set _y y'
      # fromRecord

-- | Class describing types which represent a size on a 2D plane and can be
-- | turned into a `Vector2 a`.
class ToSize a sa | sa → a where
  toSize ∷ sa → Vector2 a

instance ToSize a (Vector2 a) where
  toSize = identity

instance ToSize a (Rect a) where
  toSize (Rect _ size) = size

instance TypeEquals r1 (WH a r) ⇒ ToSize a (Record r1) where
  toSize = toRecord >>> \{ width, height } → width >< height

-- | Class describing types which represent a size on a 2D plane and can be
-- | constructed from a `Vector2 a`.
class FromSize a sa | sa → a where
  fromSize ∷ Vector2 a → sa

instance FromSize a (Vector2 a) where
  fromSize = identity

instance Semiring a ⇒ FromSize a (Rect a) where
  fromSize size = Rect zero size

instance fromSizeWH ∷
  ( TypeEquals r1 (WH a r)
  , Semiring (Record r)
  , Nub (WH a r) (WH a r)
  ) ⇒
  FromSize a (Record r1) where
  fromSize (width >< height) =
    fromRecord $ disjointUnion { width, height } zero

-- | Class describing types which represent a size on a 2D plane and can be
-- | modified by any function of type `Vector2 a → Vector2 a`.
-- |
-- | Instances must satisfy the following law:
-- |
-- | - Identity: `asSizeEndo identity = identity`
class AsSizeEndo a sa | sa → a where
  asSizeEndo ∷ (Vector2 a → Vector2 a) → sa → sa

instance AsSizeEndo a (Vector2 a) where
  asSizeEndo = identity

instance AsSizeEndo a (Rect a) where
  asSizeEndo f (Rect pos size) = Rect pos (f size)

instance TypeEquals r1 (WH a r) ⇒ AsSizeEndo a (Record r1) where
  asSizeEndo f r1 = do
    let
      record@{ width, height } = toRecord r1
      (width' >< height') = f (width >< height)
    record
      # set _width width'
      # set _height height'
      # fromRecord

-- | Class describing types which represent a size on a 2D plane and can be
-- | modified by any function of type `Vector2 a → Vector2 b`.
-- |
-- | Instances must satisfy the following law:
-- |
-- | - Identity: `asSize identity = identity`
class AsSize a b sa sb | sa → a, sb → b, sa b → sb where
  asSize ∷ (Vector2 a → Vector2 b) → sa → sb

instance AsSize a b (Vector2 a) (Vector2 b) where
  asSize = identity

instance asSizeWH ∷
  ( TypeEquals r1 (WH a r)
  , TypeEquals r2 (WH b r)
  ) ⇒
  AsSize a b (Record r1) (Record r2) where
  asSize f r1 = do
    let
      record@{ width, height } = toRecord r1
      (width' >< height') = f (width >< height)
    record
      # set _width width'
      # set _height height'
      # fromRecord

-- | Class describing types which represent a rectangular region on a 2D plane
-- | and can be turned into a `Rect a`.
class ToRegion a ra | ra → a where
  toRegion ∷ ra → Rect a

instance Semiring a ⇒ ToRegion a (Vector2 a) where
  toRegion size = Rect zero size

instance ToRegion a (Rect a) where
  toRegion = identity

-- | With how the compiler works currently, it's not possible to have instances
-- | of `ToRegion` for both `WH a r` and `XYWH a r`, so you can't use a value
-- | like `{width: 50, height: 50}` for `toRegion`. If you want to use a record
-- | as a region the same way you would a `Vector2`, you can call `toSize` with
-- | it first:
-- | ```purs
-- | -- All these do the same thing
-- | outside (toSize { width: 50, height: 50 })
-- | outside { width: 50, height: 50, x: 0, y: 0 }
-- | outside (50 >< 50)
-- | ```
instance TypeEquals r1 (XYWH a r) ⇒ ToRegion a (Record r1) where
  toRegion =
    toRecord >>> \{ x, y, width, height } → makeRect x y width height

-- | Class describing types which represent a rectangular region on a 2D plane
-- | and can be constructed from a `Rect a`.
class FromRegion a ra | ra → a where
  fromRegion ∷ Rect a → ra

instance FromRegion a (Vector2 a) where
  fromRegion (Rect _ size) = size

instance FromRegion a (Rect a) where
  fromRegion = identity

instance fromRegionXYWH ∷
  ( TypeEquals r1 (XYWH a r)
  , Semiring (Record r)
  , Nub (XYWH a r) (XYWH a r)
  ) ⇒
  FromRegion a (Record r1) where
  fromRegion (Rect (x >< y) (width >< height)) =
    fromRecord $ disjointUnion { x, y, width, height } zero

-- | Class describing types which represent a rectangular region on a 2D plane
-- | and can be modified by any function of type `Rect a → Rect a`.
-- |
-- | Instances must satisfy the following law:
-- |
-- | - Identity: `asRegionEndo identity = identity`
class AsRegionEndo a ra | ra → a where
  asRegionEndo ∷ (Rect a → Rect a) → ra → ra

instance Semiring a ⇒ AsRegionEndo a (Vector2 a) where
  asRegionEndo f = fromRegion <<< f <<< toRegion

instance AsRegionEndo a (Rect a) where
  asRegionEndo = identity

instance asRegionEndoXYWH ∷
  TypeEquals r1 (XYWH a r) ⇒
  AsRegionEndo a (Record r1) where
  asRegionEndo f r1 = do
    let
      record@{ x, y, width, height } = toRecord r1
      (Rect (x' >< y') (width' >< height')) = f (makeRect x y width height)
    record
      # set _x x'
      # set _y y'
      # set _width width'
      # set _height height'
      # fromRecord

-- | Class describing types which represent a rectangular region on a 2D plane
-- | and can be modified by any function of type `Rect a → Rect b`.
-- |
-- | Instances must satisfy the following law:
-- |
-- | - Identity: `asRegion identity = identity`
class AsRegion a b ra rb | ra → a, rb → b, ra b → rb where
  asRegion ∷ (Rect a → Rect b) → ra → rb

instance Semiring a ⇒ AsRegion a b (Vector2 a) (Vector2 b)
  where
  asRegion f = fromRegion <<< f <<< toRegion

instance AsRegion a b (Rect a) (Rect b) where
  asRegion = identity

instance asRegionXYWH ∷
  ( TypeEquals r1 (XYWH a r)
  , TypeEquals r2 (XYWH b r)
  ) ⇒
  AsRegion a b (Record r1) (Record r2) where
  asRegion f r1 = do
    let
      record@{ x, y, width, height } = toRecord r1
      (Rect (x' >< y') (width' >< height')) = f (makeRect x y width height)
    record
      # set _x x'
      # set _y y'
      # set _width width'
      # set _height height'
      # fromRecord
