module Pipes.CBOR where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, liftEither)
import Control.Monad.Except (runExcept)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Bifunctor (lmap)
import Data.CBOR (class ReadCBOR, class WriteCBOR, readCBOR, writeCBOR)
import Data.Maybe (Maybe)
import Data.Traversable (traverse)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error, error)
import Node.Buffer (Buffer)
import Node.Stream.CBOR.Decode as CBOR.Decode
import Node.Stream.CBOR.Encode as CBOR.Encode
import Pipes.Async (AsyncPipe, bindIO, mapIO)
import Pipes.Node.Stream as Pipes.Stream

-- | Transforms buffer chunks of a CBOR file to parsed values
-- | of type `a`.
decode
  :: forall m @a
   . MonadRec m
  => MonadAff m
  => MonadThrow Error m
  => ReadCBOR a
  => AsyncPipe (Maybe Buffer) (Maybe a) m Unit
decode = do
  let
    decoder = Pipes.Stream.fromTransformEffect $ CBOR.Decode.toObjectStream <$> CBOR.Decode.make {}
    parse = liftEither <<< lmap (error <<< show) <<< runExcept <<< readCBOR @a
  bindIO pure (traverse parse) decoder

-- | Encode purescript values as CBOR buffers
encode
  :: forall m a
   . MonadAff m
  => MonadThrow Error m
  => MonadRec m
  => WriteCBOR a
  => AsyncPipe (Maybe a) (Maybe Buffer) m Unit
encode =
  let
    p = Pipes.Stream.fromTransformEffect $ CBOR.Encode.toObjectStream <$> CBOR.Encode.make {}
  in
    mapIO (map writeCBOR) identity p
