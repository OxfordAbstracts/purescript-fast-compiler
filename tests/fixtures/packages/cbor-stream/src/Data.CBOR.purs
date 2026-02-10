module Data.CBOR where

import Prelude

import Control.Monad.Error.Class (liftMaybe, try)
import Control.Monad.Except (ExceptT(..), withExcept)
import Control.Monad.Except.Trans (runExceptT)
import Data.Array as Array
import Data.DateTime (DateTime)
import Data.Either (Either(..), isRight)
import Data.Foldable (class Foldable)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.JSDate (JSDate)
import Data.JSDate as JSDate
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Traversable (traverse)
import Foreign (F, Foreign, ForeignError(..), readArray, readNullOrUndefined, unsafeReadTagged, unsafeToForeign)
import Foreign.Index (readProp)
import JS.BigInt (BigInt)
import JS.Map (Map) as JS
import JS.Map as JS.Map
import Prim.Row as Row
import Prim.RowList (class RowToList, Cons, Nil, RowList)
import Record (get)
import Record.Builder (Builder)
import Record.Builder as Builder
import Simple.JSON (class ReadForeign, class WriteForeign, readImpl, writeImpl)
import Type.Prelude (Proxy(..))

class ReadCBOR :: Type -> Constraint
class ReadCBOR a where
  readCBOR :: Foreign -> F a

class WriteCBOR :: Type -> Constraint
class WriteCBOR a where
  writeCBOR :: a -> Foreign

instance ReadCBOR Foreign where
  readCBOR = pure
else instance (RowToList r rl, ReadCBORFields rl () r) => ReadCBOR (Record r) where
  readCBOR o = do
    flip Builder.build {} <$> getFields (Proxy @rl) o
else instance ReadCBOR BigInt where
  readCBOR = unsafeReadTagged "BigInt"
else instance ReadCBOR JSDate where
  readCBOR = unsafeReadTagged "Date"
else instance ReadCBOR DateTime where
  readCBOR a = do
    date :: JSDate <- readCBOR a
    liftMaybe (pure $ ForeignError $ "Invalid DateTime: " <> show date) $ JSDate.toDateTime date
else instance ReadCBOR a => ReadCBOR (Array a) where
  readCBOR a = do
    raws :: Array Foreign <- readArray a
    traverse readCBOR raws
else instance ReadCBOR a => ReadCBOR (Maybe a) where
  readCBOR a = do
    isNull <- isRight <$> try (readNullOrUndefined a)
    if isNull then
      pure Nothing
    else
      Just <$> readCBOR @a a
else instance (ReadCBOR v) => ReadCBOR (JS.Map String v) where
  readCBOR map = do
    map' :: JS.Map String Foreign <- unsafeReadTagged "Map" map
    foldlWithIndex (\k b v -> do
      map'' <- b
      v' <- readCBOR v
      pure $ JS.Map.insert k v' map''
    ) (pure JS.Map.empty) map'
else instance (ReadForeign a) => ReadCBOR a where
  readCBOR = readImpl

instance WriteCBOR Foreign where
  writeCBOR = identity
else instance (RowToList r rl, WriteCBORFields rl r () to) => WriteCBOR (Record r) where
  writeCBOR rec = unsafeToForeign $ Builder.build (writeImplFields (Proxy @rl) rec) {}
else instance WriteCBOR BigInt where
  writeCBOR = unsafeToForeign
else instance WriteCBOR JSDate where
  writeCBOR = unsafeToForeign
else instance WriteCBOR DateTime where
  writeCBOR = unsafeToForeign <<< JSDate.fromDateTime
else instance (WriteCBOR k, WriteCBOR v) => WriteCBOR (JS.Map k v) where
  writeCBOR = unsafeToForeign
else instance (WriteCBOR a) => WriteCBOR (Array a) where
  writeCBOR as = unsafeToForeign $ writeCBOR <$> as
else instance (Foldable f, WriteCBOR a) => WriteCBOR (f a) where
  writeCBOR as = unsafeToForeign $ writeCBOR $ Array.fromFoldable as
else instance (JS.Map.EncodeKey k, WriteCBOR k, WriteCBOR v) => WriteCBOR (Map k v) where
  writeCBOR map = writeCBOR $ foldlWithIndex (\k m v -> JS.Map.insert k v m) JS.Map.empty map
else instance (WriteForeign a) => WriteCBOR a where
  writeCBOR = writeImpl

applyEither :: forall e a b. Semigroup e => Either e (a -> b) -> Either e a -> Either e b
applyEither (Left e) (Right _) = Left e
applyEither (Left e1) (Left e2) = Left (e1 <> e2)
applyEither (Right _) (Left e) = Left e
applyEither (Right fun) (Right a) = Right (fun a)

exceptTApply :: forall a b e m. Semigroup e => Applicative m => ExceptT e m (a -> b) -> ExceptT e m a -> ExceptT e m b
exceptTApply fun a = ExceptT $ applyEither
  <$> runExceptT fun
  <*> runExceptT a

class ReadCBORFields (xs :: RowList Type) (from :: Row Type) (to :: Row Type)
  | xs -> from to where
  getFields :: Proxy xs
    -> Foreign
    -> F (Builder (Record from) (Record to))

instance readFieldsCons ::
  ( IsSymbol name
  , ReadCBOR ty
  , ReadCBORFields tail from from'
  , Row.Lacks name from'
  , Row.Cons name ty from' to
  ) => ReadCBORFields (Cons name ty tail) from to where
  getFields _ obj = (compose <$> first) `exceptTApply` rest
    where
      first = do
        value <- withExcept' (readCBOR =<< readProp name obj)
        pure $ Builder.insert nameP value
      rest = getFields tailP obj
      nameP = Proxy :: Proxy name
      tailP = Proxy :: Proxy tail
      name = reflectSymbol nameP
      withExcept' = withExcept <<< map $ ErrorAtProperty name

instance readFieldsNil ::
  ReadCBORFields Nil () () where
  getFields _ _ =
    pure identity

class WriteCBORFields (rl :: RowList Type) row (from :: Row Type) (to :: Row Type)
  | rl -> row from to where
  writeImplFields :: forall g. g rl -> Record row -> Builder (Record from) (Record to)

instance consWriteCBORFields ::
  ( IsSymbol name
  , WriteCBOR ty
  , WriteCBORFields tail row from from'
  , Row.Cons name ty whatever row
  , Row.Lacks name from'
  , Row.Cons name Foreign from' to
  ) => WriteCBORFields (Cons name ty tail) row from to where
  writeImplFields _ rec = result
    where
      namep = Proxy :: Proxy name
      value = writeCBOR $ get namep rec
      tailp = Proxy :: Proxy tail
      rest = writeImplFields tailp rec
      result = Builder.insert namep value <<< rest

instance nilWriteCBORFields ::
  WriteCBORFields Nil row () () where
  writeImplFields _ _ = identity
