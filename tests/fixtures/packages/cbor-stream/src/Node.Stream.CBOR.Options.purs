module Node.Stream.CBOR.Options where

import Prelude

import Foreign (Foreign, unsafeToForeign)
import Prim.Row (class Nub, class Union)
import Record (merge, modify)
import Type.Prelude (Proxy(..))

data F32
  = F32Always
  | F32DecimalRound
  | F32DecimalFit
  | F32Never

derive instance Eq F32

foreign import data CBORStruct :: Type
foreign import f32ToConst :: {always :: F32 -> Boolean, round :: F32 -> Boolean, fit :: F32 -> Boolean} -> F32 -> Foreign

type Options r =
  ( useRecords :: Boolean
  , structures :: Array CBORStruct
  , structuredClone :: Boolean
  , mapsAsObject :: Boolean
  , useFloat32 :: F32
  , alwaysUseFloat :: Boolean
  , pack :: Boolean
  , variableMapSize :: Boolean
  , copyBuffers :: Boolean
  , bundleStrings :: Boolean
  , useTimestamp32 :: Boolean
  , largeBigIntToFloat :: Boolean
  , useTag259ForMaps :: Boolean
  , tagUint8Array :: Boolean
  , int64AsNumber :: Boolean
  | r
  )

prepareOptions
  :: forall @r @missing extra minimal minimalExtra
   . Union r missing (Options extra)
  => Union r (useFloat32 :: F32) minimal
  => Nub minimal (useFloat32 :: F32 | minimalExtra)
  => { | r }
  -> Foreign
prepareOptions a =
  unsafeToForeign
  $ modify (Proxy @"useFloat32") (f32ToConst {fit: eq F32DecimalFit, round: eq F32DecimalRound, always: eq F32Always})
  $ merge a {useFloat32: F32Never}
