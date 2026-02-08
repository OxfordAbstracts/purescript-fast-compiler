module Node.Stream.CBOR.Encode where

import Prelude

import Data.CBOR (class WriteCBOR, writeCBOR)
import Effect (Effect)
import Foreign (Foreign)
import Foreign.Object (Object)
import Node.Buffer (Buffer)
import Node.Stream (Read, Stream, Write)
import Node.Stream.CBOR.Options (F32, Options, prepareOptions)
import Node.Stream.Object (Transform) as Object
import Prim.Row (class Nub, class Union)
import Unsafe.Coerce (unsafeCoerce)

data CBOREncode

type CBOREncoder :: Row Type -> Type
type CBOREncoder r = Stream (read :: Read, write :: Write, csv :: CBOREncode | r)

foreign import makeImpl :: forall r. Foreign -> Effect (Stream r)
foreign import writeImpl :: forall r. Stream r -> Foreign -> Effect Unit

recordToForeign :: forall r. Record r -> Object Foreign
recordToForeign = unsafeCoerce

-- | Create a raw Transform stream that accepts chunks of `Array String`,
-- | and transforms them into string CSV rows.
-- |
-- | Requires an ordered array of column names.
make
  :: forall r missing extra minimal minimalExtra
   . Union r missing (Options extra)
  => Union r (useFloat32 :: F32) minimal
  => Nub minimal (useFloat32 :: F32 | minimalExtra)
  => { | r }
  -> Effect (CBOREncoder ())
make = makeImpl <<< prepareOptions @r @missing

-- | Convert the raw stream to a typed ObjectStream
toObjectStream :: CBOREncoder () -> Object.Transform Foreign Buffer
toObjectStream = unsafeCoerce

-- | Write a record to a CSVStringifier.
-- |
-- | The record will be emitted on the `Readable` end
-- | of the stream as a string chunk.
write :: forall a r. WriteCBOR a => CBOREncoder r -> a -> Effect Unit
write s a = writeImpl s $ writeCBOR a
