module Data.Text.Format.Org.Keyword where

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

import Data.Text.Format.Org.Property (OrgProperty, JsonPropertyRec)
import Data.Text.Format.Org.Property as P


data OrgKeyword v
    = KWNameValue String v
    | KWOnlyName String
    | KWNameOptionalValue String v (Maybe v)
    | KWProperty (OrgProperty v)

derive instance Functor OrgKeyword

-- TODO: type OrgKeyword = Keyword String

newtype OrgKeywords v = OrgKeywords (Array (OrgKeyword v))

derive instance Newtype (OrgKeywords v) _

derive instance Functor OrgKeywords


type JsonKeywordRow v =
    ( name :: String
    , value :: Maybe v
    , default :: Maybe v
    )
type JsonKeywordRec v = Record (JsonKeywordRow v)

type JsonKeywordOrPropRec v = Either (JsonPropertyRec v) (JsonKeywordRec v)

newtype JsonKeywords v = JsonKeywords (Array (JsonKeywordOrPropRec v))

derive instance Newtype (JsonKeywords v) _


instance WriteForeign (JsonKeywords String) where
    writeImpl = unwrap >>> writeImpl

instance ReadForeign (JsonKeywords String) where
    readImpl f = (readImpl f :: F (Array (JsonKeywordOrPropRec String))) <#> wrap


{- instance (ReadForeign k, ReadForeign v) => ReadForeign (KeywordsOf k v)
    where readImpl f = (readImpl f :: F (Array (Int /\ (k /\ v)))) <#> toKeywords -}


make :: forall v. Array (OrgKeyword v) -> OrgKeywords v
make = wrap


kw :: forall v. String -> v -> OrgKeyword v
kw = KWNameValue


kwopt :: forall v. String -> v -> OrgKeyword v
kwopt name default = KWNameOptionalValue name default Nothing


kwoptv :: forall v. String -> v -> v -> OrgKeyword v
kwoptv name default = KWNameOptionalValue name default <<< Just


kwon :: forall v. String -> OrgKeyword v
kwon = KWOnlyName


-- TODO: Maybe value + maybe default
-- TODO: toKeywords converts to `Keyword`s instances


empty :: forall v. OrgKeywords v
empty = wrap []


hasKeywords :: forall v. OrgKeywords v -> Boolean
hasKeywords kws = Array.length (unwrap kws) > 0


isEmpty :: forall v. OrgKeywords v -> Boolean
isEmpty = not hasKeywords


snoc :: forall v. OrgKeywords v -> OrgKeyword v -> OrgKeywords v
snoc kws kv = unwrap kws # flip Array.snoc kv # wrap


cons :: forall v. OrgKeyword v -> OrgKeywords v -> OrgKeywords v
cons kv = unwrap >>> Array.cons kv >>> wrap


{-
qsnoc :: forall v. OrgKeywords v -> String -> v -> OrgKeywords v
qsnoc kws k v = snoc kws $ kw k v


qcons :: forall v. String -> v -> OrgKeywords v -> OrgKeywords v
qcons k v = cons $ kw k v


qpushopt :: forall v. Keywords v -> String -> v -> Keywords v
qpushopt kws k ov = push kws $ kwopt k ov


qpileopt :: forall v. String -> v -> Keywords v -> Keywords v
qpileopt k ov = pile $ kwopt k ov


qpushoptv :: forall v. Keywords v -> String -> v -> v -> Keywords v
qpushoptv kws k v ov = push kws $ kwoptv k v ov


qpileoptv :: forall v. String -> v -> v -> Keywords v -> Keywords v
qpileoptv k v ov = pile $ kwoptv k v ov


qpushon :: forall v. Keywords v -> String -> Keywords v
qpushon kws k = push kws $ kwon k


qpileon :: forall v. String -> Keywords v -> Keywords v
qpileon k = pile $ kwon k
-}


{-
insert' :: forall v. Int -> String -> v -> Keywords v -> Keywords v
insert' n k v = unwrap >>> Map.insert (n /\ k) (Just v) >>> wrap
-}


toRec :: forall v. OrgKeyword v -> JsonKeywordOrPropRec v
toRec = case _ of
    KWNameValue name value             -> Right { name, value : Just value, default : Nothing }
    KWOnlyName name                    -> Right { name, value : Nothing,    default : Nothing }
    KWNameOptionalValue name opt mbVal -> Right { name, value : mbVal,      default : Just opt }
    KWProperty orgprop                  -> Left $ P.toRec orgprop


fromRec :: forall v. JsonKeywordOrPropRec v -> OrgKeyword v
fromRec = case _ of
    Left orgprop -> KWProperty $ P.fromRec orgprop
    Right rec ->
        case rec.default of
            Just def ->
                KWNameOptionalValue rec.name def rec.value
            Nothing ->
                case rec.value of
                    Just val -> KWNameValue rec.name val
                    Nothing  -> KWOnlyName rec.name


fromJson :: forall v. JsonKeywords v -> OrgKeywords v
fromJson = wrap <<< map fromRec <<< unwrap


toJson :: forall v. OrgKeywords v -> JsonKeywords v
toJson = wrap <<< map toRec <<< unwrap


{-
-- t a (t b c) ->  t (t a b) c
_swap3 :: forall a b c. a /\ (b /\ c) -> (a /\ b) /\ c
_swap3 (a /\ (b /\ c)) = (a /\ b) /\ c


-- t (t a b) c ->  t a (t b c)
_bswap3 :: forall a b c. (a /\ b) /\ c -> a /\ (b /\ c)
_bswap3 ((a /\ b) /\ c) = a /\ (b /\ c)
-}
