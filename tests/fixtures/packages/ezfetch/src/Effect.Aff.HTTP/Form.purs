module Effect.Aff.HTTP.Form where

import Prelude

import Control.Monad.Error.Class (liftMaybe)
import Control.Monad.Except (runExcept)
import Control.Promise (Promise)
import Control.Promise as Promise
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Either (hush)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Generic.Rep (class Generic)
import Data.MIME (MIME)
import Data.MIME as MIME
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Show.Generic (genericShow)
import Data.Traversable (for)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (error)
import Foreign (Foreign, unsafeReadTagged, unsafeToForeign)
import Foreign.Object (Object)
import Foreign.Object as Object
import Simple.JSON (readImpl, unsafeStringify)
import Unsafe.Coerce (unsafeCoerce)
import Web.File.File (File)

type FileRecord = { filename :: String, mime :: String, buf :: ArrayBuffer }

foreign import data RawFormData :: Type
foreign import unsafeShowArrayBuffer :: ArrayBuffer -> String
foreign import unsafeEqArrayBuffer :: ArrayBuffer -> ArrayBuffer -> Boolean
foreign import unsafeMakeFile :: FileRecord -> Effect File
foreign import unsafeMakeFormData :: Object (Array Foreign) -> Effect RawFormData
foreign import unsafeUnmakeFormData :: RawFormData -> Effect (Promise (Object (Array Foreign)))

newtype Filename = Filename String

derive instance Generic Filename _
derive instance Newtype Filename _
instance Show Filename where
  show = genericShow

derive newtype instance Eq Filename
derive newtype instance Ord Filename

data Value
  = ValueString String
  | ValueFile Filename ArrayBuffer MIME

valueForeign :: Value -> Effect Foreign
valueForeign (ValueString s) = pure $ unsafeToForeign s
valueForeign (ValueFile filename buf mime) = unsafeToForeign <$> unsafeMakeFile { filename: unwrap filename, buf, mime: MIME.toString mime }

valueFromForeign :: Foreign -> Effect Value
valueFromForeign f = do
  let
    file :: Maybe { filename :: String, buf :: Foreign, mime :: String }
    file = hush $ runExcept $ readImpl f
    string = hush $ runExcept $ unsafeReadTagged "String" f

  case file of
    Just { filename, buf, mime } ->
      let
        buf' :: ArrayBuffer
        buf' = unsafeCoerce buf
      in
        pure $ ValueFile (wrap filename) buf' (MIME.fromString mime)
    Nothing -> do
      s <- liftMaybe (error $ "invalid form value " <> unsafeStringify f) string
      pure $ ValueString s

derive instance Generic Value _
instance Show Value where
  show (ValueString s) = "(ValueString " <> show s <> ")"
  show (ValueFile filename buf mime) = "(ValueFile (" <> show filename <> ") (ArrayBuffer " <> unsafeShowArrayBuffer buf <> ") (" <> show mime <> "))"

instance Eq Value where
  eq (ValueString a) (ValueString b) = a == b
  eq (ValueFile namea bufa mimea) (ValueFile nameb bufb mimeb)
    | namea /= nameb = false
    | mimea /= mimeb = false
    | otherwise = unsafeEqArrayBuffer bufa bufb
  eq _ _ = false

newtype Form = Form (Map String (Array Value))

derive instance Newtype Form _
derive newtype instance Show Form
derive newtype instance Eq Form

fromRaw :: forall m. MonadAff m => RawFormData -> m Form
fromRaw f = do
  obj <- liftAff $ Promise.toAffE $ unsafeUnmakeFormData f
  let
    formMap = Map.fromFoldableWithIndex obj
  map' <- liftEffect $ for formMap (\vs -> for vs valueFromForeign)
  pure $ Form map'

toRawFormData :: forall m. MonadEffect m => Form -> m RawFormData
toRawFormData =
  let
    collect k o vs = do
      o' <- o
      vs' <- for vs valueForeign
      pure $ Object.insert k vs' o'
  in
    liftEffect <<< flip bind unsafeMakeFormData <<< foldlWithIndex collect (pure Object.empty) <<< unwrap

