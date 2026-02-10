module Chameleon.Impl.ReactBasic.Html
  ( Config
  , ConfigOpt
  , ReactHtml(..)
  , defaultConfig
  , runReactHtml
  , simpleSplit
  , uppercaseStyleHack
  ) where

import Prelude

import Data.Array (mapMaybe)
import Data.Array as Arr
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), Replacement(..), toLower, toUpper)
import Data.String as Str
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, mkEffectFn1)
import Foreign (Foreign)
import Foreign.Object (Object)
import Foreign.Object as Obj
import React.Basic (JSX)
import React.Basic.DOM (text) as DOM
import Unsafe.Coerce (unsafeCoerce)
import Chameleon (class Html, class MapMaybe, ElemName(..), Key, Prop(..))

--------------------------------------------------------------------------------
--- ReactHtml
--------------------------------------------------------------------------------

type ConfigOpt =
  { cssStringToAttr :: String -> String /\ Foreign
  , key :: Maybe Key
  }

type Config a =
  { handler :: a -> Effect Unit
  }

defaultConfig :: ConfigOpt
defaultConfig =
  { cssStringToAttr: simpleSplit
  , key: Nothing
  }

class MaybeMsg html where
  fromMaybeMsg :: forall msg. html (Maybe msg) -> html msg

newtype ReactHtml a = ReactHtml (Config a -> ConfigOpt -> JSX)

instance MaybeMsg ReactHtml where
  fromMaybeMsg :: forall msg. ReactHtml (Maybe msg) -> ReactHtml msg
  fromMaybeMsg (ReactHtml mkJsx) = ReactHtml \env cfgOpt ->
    let
      env' :: Config (Maybe msg)
      env' =
        { handler: case _ of
            Nothing -> pure unit
            Just msg -> env.handler msg
        }
    in
      mkJsx env' cfgOpt

instance Functor ReactHtml where
  map f (ReactHtml mkJsx) = ReactHtml \env -> mkJsx env
    { handler = f >>> env.handler
    }

runReactHtml :: forall a. Config a -> ConfigOpt -> ReactHtml a -> JSX
runReactHtml cfg cfgOpt (ReactHtml f) =
  f cfg cfgOpt

instance MapMaybe ReactHtml where
  mapMaybe :: forall msg1 msg2. (msg1 -> Maybe msg2) -> ReactHtml msg1 -> ReactHtml msg2
  mapMaybe f (ReactHtml mkJsx) = ReactHtml \cfg opt ->
    let
      handler :: msg1 -> Effect Unit
      handler msg = f msg # case _ of
        Just msg' -> cfg.handler msg'
        Nothing -> pure unit

      cfg' :: Config msg1
      cfg' = { handler }
    in
      mkJsx cfg' opt

instance Html ReactHtml where
  elem (ElemName name) props1 children1 = ReactHtml $ \cfg cfgOpt ->
    let
      props2 = Obj.fromFoldable $ mapMaybe (mkProp cfg cfgOpt) $ props1
      children2 = (\jsx -> runReactHtml cfg cfgOpt { key = Nothing } jsx) <$> children1
    in
      if Arr.null children2 then
        createVoidElement name props2
      else
        createElement name props2 children2

  elemKeyed (ElemName name) props1 children1 = ReactHtml $ \cfg cfgOpt ->
    let
      props2 = Obj.fromFoldable $ mapMaybe (mkProp cfg cfgOpt) $ props1
      children2 = (\(key /\ jsx) -> runReactHtml cfg cfgOpt { key = Just key } jsx) <$> children1
    in
      if Arr.null children2 then
        createVoidElement name props2
      else
        createElement name props2 children2

  text str = ReactHtml $ \_ _ -> DOM.text str

mkProp :: forall a. Config a -> ConfigOpt -> Prop a -> Maybe (String /\ Foreign)
mkProp { handler } { cssStringToAttr } = case _ of
  Attr "style" v -> Just $ cssStringToAttr v
  Attr "" "" -> Nothing
  Attr k v | Str.stripPrefix (Pattern "data-") k /= Nothing -> Just (k /\ toForeign v)
  Attr k v -> Just $ (kebabToCamelCase $ Str.replace (Pattern ":") (Replacement "-") k) /\ toForeign v
  Event n f -> Just $  ("on" <> upperFirst n) /\ toForeign
    ( mkEffectFn1 \event -> case f event of
        Just action -> handler action
        Nothing -> pure unit
    )

-------------------------------------------------------------------------------
--- CSS Converter
-------------------------------------------------------------------------------

-- | This is a hack to provide styles as string to React
-- | It creates a warning in the console
uppercaseStyleHack :: String -> String /\ Foreign
uppercaseStyleHack str = "STYLE" /\ toForeign str

-- | This is a very simple parser for CSS strings
-- | It does not work for all cases, but it is enough for most of them
simpleSplit :: String -> String /\ Foreign
simpleSplit str =
  let
    entries :: Array (String /\ String)
    entries = simpleSplitCore str

    object :: Object String
    object = Obj.fromFoldable entries

    object' :: Object Foreign
    object' = map toForeign object
  in
    "style" /\ toForeign object'

simpleSplitCore :: String -> Array (String /\ String)
simpleSplitCore str =
  let
    decls :: Array String
    decls = Str.split (Pattern ";") str

  in
    map mkEntry decls

  where
  mkEntry :: String -> String /\ String
  mkEntry str' =
    let
      parts :: Array String
      parts = Str.split (Pattern ":") str'
    in
      case Array.uncons parts of
        Just { head, tail } ->
          Str.trim (kebabToCamelCase head) /\
            Str.trim (Str.joinWith ":" tail)
        _ -> "" /\ ""

--------------------------------------------------------------------------------
--- FFI
--------------------------------------------------------------------------------

foreign import createVoidElement :: String -> Object Foreign -> JSX

foreign import createElement :: String -> Object Foreign -> Array JSX -> JSX

--------------------------------------------------------------------------------
--- ToForeign
--------------------------------------------------------------------------------

class ToForeign a where
  toForeign :: a -> Foreign

instance ToForeign JSX where
  toForeign = unsafeCoerce

instance ToForeign a => ToForeign (Array a) where
  toForeign = unsafeCoerce <<< map toForeign

instance ToForeign String where
  toForeign = unsafeCoerce

instance ToForeign (Object Foreign) where
  toForeign = unsafeCoerce

instance ToForeign (EffectFn1 Foreign Unit) where
  toForeign = unsafeCoerce

--------------------------------------------------------------------------------
--- Utils
--------------------------------------------------------------------------------

upperFirst :: String -> String
upperFirst str =
  case str of
    "" -> ""
    _ -> toUpper (Str.take 1 str) <> Str.drop 1 str

lowerFirst :: String -> String
lowerFirst str =
  case str of
    "" -> ""
    _ -> toLower (Str.take 1 str) <> Str.drop 1 str

kebabToCamelCase :: String -> String
kebabToCamelCase str =
  let
    parts :: Array String
    parts = Str.split (Pattern "-") str

    parts' :: Array String
    parts' = map upperFirst parts
  in
    lowerFirst $ Str.joinWith "" parts'
