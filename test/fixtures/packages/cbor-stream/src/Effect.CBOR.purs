module Effect.CBOR where

import Prelude

import Control.Monad.Error.Class (liftEither)
import Control.Monad.Except (runExcept)
import Data.Bifunctor (lmap)
import Data.CBOR (class ReadCBOR, class WriteCBOR, readCBOR, writeCBOR)
import Effect (Effect)
import Effect.Exception (error)
import Foreign (Foreign)
import Node.Buffer (Buffer)

foreign import decodeImpl :: Buffer -> Effect Foreign
foreign import encodeImpl :: Foreign -> Effect Buffer

decode :: forall a. ReadCBOR a => Buffer -> Effect a
decode = (liftEither <<< lmap (error <<< show) <<< runExcept <<< readCBOR) <=< decodeImpl

encode :: forall a. WriteCBOR a => a -> Effect Buffer
encode = encodeImpl <<< writeCBOR
