module Node.Stream.CBOR.Decode where

import Prelude hiding (join)

import Data.Nullable (Nullable)
import Effect (Effect)
import Effect.Uncurried (mkEffectFn1)
import Foreign (Foreign)
import Foreign.Object (Object)
import Node.Buffer (Buffer)
import Node.EventEmitter (EventHandle(..))
import Node.EventEmitter.UtilTypes (EventHandle1)
import Node.Stream (Read, Stream, Write)
import Node.Stream.CBOR.Options (F32, Options, prepareOptions)
import Node.Stream.Object (Transform) as Object
import Prim.Row (class Nub, class Union)
import Unsafe.Coerce (unsafeCoerce)

data CBORDecode

-- | CBOR decoding transform stream
-- |
-- | Accepts unencoded `Buffer` chunks, and transforms them
-- | to JS values.
type CBORDecoder :: Row Type -> Type
type CBORDecoder r = Stream (read :: Read, write :: Write, cbor :: CBORDecode | r)

make
  :: forall r missing extra minimal minimalExtra
   . Union r missing (Options extra)
  => Union r (useFloat32 :: F32) minimal
  => Nub minimal (useFloat32 :: F32 | minimalExtra)
  => { | r }
  -> Effect (CBORDecoder ())
make = makeImpl <<< prepareOptions @r @missing

toObjectStream :: forall r. CBORDecoder r -> Object.Transform Buffer Foreign
toObjectStream = unsafeCoerce

-- | `data` event. Emitted when a CSV record has been parsed.
dataH :: forall a. EventHandle1 (CBORDecoder a) Foreign
dataH = EventHandle "data" mkEffectFn1

-- | FFI
foreign import makeImpl :: forall r. Foreign -> Effect (Stream r)

-- | FFI
foreign import readImpl :: forall r. Stream r -> Effect (Nullable Foreign)

-- | FFI
recordToForeign :: forall r. Record r -> Object Foreign
recordToForeign = unsafeCoerce
