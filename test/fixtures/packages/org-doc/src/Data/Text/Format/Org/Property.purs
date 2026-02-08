module Data.Text.Format.Org.Property where

import Prelude

import Foreign (Foreign, F)

import Data.Array as Array
import Data.Maybe (Maybe (..))
import Data.Map (Map)
import Data.Map (empty, insert, size, fromFoldable, toUnfoldable, isEmpty) as Map
import Data.Newtype (class Newtype, wrap, unwrap)
import Data.Tuple (snd) as Tuple
import Data.Tuple.Nested ((/\), type (/\))
import Data.Either (Either(..))

import Yoga.JSON (class ReadForeign, readImpl, class WriteForeign, writeImpl)


data OrgProperty v
    = PNameValue String v
    | POnlyName String
    | PNameOptionalValue String v (Maybe v)
    | PAppend String (Maybe v)
    | PValueList String (Array v)

derive instance Functor OrgProperty

newtype OrgProperties v = OrgProperties (Array (OrgProperty v))

derive instance Newtype (OrgProperties v) _
derive instance Functor OrgProperties


type JsonPropertyRec v = Record (JsonPropertyRow v)

type JsonPropertyRow v =
    ( name :: String
    , value :: Maybe v
    , default :: Maybe v
    , append :: Boolean
    , vlist :: Array v
    )

newtype JsonProperties v = JsonProperties (Array (JsonPropertyRec v))

derive instance Newtype (JsonProperties v) _


instance WriteForeign (JsonProperties String) where
    writeImpl = unwrap >>> writeImpl

instance ReadForeign (JsonProperties String) where
    readImpl f = (readImpl f :: F (Array (JsonPropertyRec String))) <#> wrap


make :: forall v. Array (OrgProperty v) -> OrgProperties v
make = wrap


prop :: forall v. String -> v -> OrgProperty v
prop = PNameValue


propn :: forall v. String -> OrgProperty v
propn = POnlyName


propvlist :: forall v. String -> Array v -> OrgProperty v
propvlist = PValueList


propopt :: forall v. String -> v -> OrgProperty v
propopt name def = PNameOptionalValue name def Nothing


propoptv :: forall v. String -> v -> v -> OrgProperty v
propoptv name def = PNameOptionalValue name def <<< Just


propapp :: forall v. String -> v -> OrgProperty v
propapp name = PAppend name <<< Just


propappn :: forall v. String -> OrgProperty v -- FIXME: it's from example at https://orgmode.org/worg/dev/org-syntax-edited.html#Node_Properties, but it has no sense, appending nothing
propappn name = PAppend name Nothing


empty :: forall v. OrgProperties v
empty = wrap []


hasProperties :: forall v. OrgProperties v -> Boolean
hasProperties kws = Array.length (unwrap kws) > 0


isEmpty :: forall v. OrgProperties v -> Boolean
isEmpty = not hasProperties


snoc :: forall v. OrgProperties v -> OrgProperty v -> OrgProperties v
snoc props kv = unwrap props # flip Array.snoc kv # wrap


cons :: forall v. OrgProperty v -> OrgProperties v -> OrgProperties v
cons prop = unwrap >>> Array.cons prop >>> wrap


toRec :: forall v. OrgProperty v -> JsonPropertyRec v
toRec = case _ of
    PNameValue name value             -> { name, value : Just value, default : Nothing,  append : false, vlist : []     }
    POnlyName name                    -> { name, value : Nothing,    default : Nothing,  append : false, vlist : []     }
    PNameOptionalValue name opt mbVal -> { name, value : mbVal,      default : Just opt, append : false, vlist : []     }
    PAppend name mbAppend             -> { name, value : mbAppend,   default : Nothing,  append : true,  vlist : []     }
    PValueList name values            -> { name, value : Nothing,    default : Nothing,  append : false, vlist : values }


fromRec :: forall v. JsonPropertyRec v -> OrgProperty v
fromRec rec =
    if (Array.length rec.vlist > 0) then
        PValueList rec.name rec.vlist
    else
        if rec.append then
            PAppend rec.name rec.value
        else
            case rec.default of
                Just def ->
                    PNameOptionalValue rec.name def rec.value
                Nothing ->
                    case rec.value of
                        Just val -> PNameValue rec.name val
                        Nothing  -> POnlyName rec.name



fromJson :: forall v. JsonProperties v -> OrgProperties v
fromJson = wrap <<< map fromRec <<< unwrap


toJson :: forall v. OrgProperties v -> JsonProperties v
toJson = wrap <<< map toRec <<< unwrap
