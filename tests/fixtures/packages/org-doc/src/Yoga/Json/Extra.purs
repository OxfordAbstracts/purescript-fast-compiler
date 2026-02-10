module Yoga.Json.Extra where

import Prelude

import Prim.Row as Row
import Prim.RowList (class RowToList, RowList) as RL

import Type.Proxy (Proxy)

import Data.Either (Either(..))
import Data.Symbol (class IsSymbol)
import Data.Variant (Variant, class VariantMatchCases)
import Data.Variant (match, inj) as Variant
import Data.Tuple (curry, uncurry)
import Data.Tuple.Nested ((/\), type (/\))

import Control.Monad.Except (except)

import Foreign (F, Foreign, fail, ForeignError(..))

import Yoga.JSON (class ReadForeign, class WriteForeign, class ReadForeignVariant, readImpl, writeImpl)


data Case = Case -- a.k.a. Unit
data Case1 a = Case1 a
data Case2 a b = Case2 a b
data Case3 a b c = Case3 a b c
data Case4 a b c d = Case4 a b c d


instance ReadForeign Case where
    readImpl f = (readImpl f :: F String) >>= (\str -> case str of
        "." -> except $ Right Case
        _ -> fail $ ForeignError "No match")


instance ReadForeign a => ReadForeign (Case1 a) where
    readImpl f = (readImpl f :: F a) <#> Case1


instance (ReadForeign a, ReadForeign b) => ReadForeign (Case2 a b) where
    readImpl f = (readImpl f :: F { a :: a, b :: b }) <#> \r -> Case2 r.a r.b


instance (ReadForeign a, ReadForeign b, ReadForeign c) => ReadForeign (Case3 a b c) where
    readImpl f = (readImpl f :: F { a :: a, b :: b, c :: c }) <#> \r -> Case3 r.a r.b r.c


instance (ReadForeign a, ReadForeign b, ReadForeign c, ReadForeign d) => ReadForeign (Case4 a b c d) where
    readImpl f = (readImpl f :: F { a :: a, b :: b, c :: c, d :: d }) <#> \r -> Case4 r.a r.b r.c r.d


instance WriteForeign Case where
    writeImpl = const $ writeImpl "."


instance WriteForeign a => WriteForeign (Case1 a) where
    writeImpl (Case1 a) = writeImpl a


instance (WriteForeign a, WriteForeign b) => WriteForeign (Case2 a b) where
    writeImpl (Case2 a b) = writeImpl { a, b }


instance (WriteForeign a, WriteForeign b, WriteForeign c) => WriteForeign (Case3 a b c) where
    writeImpl (Case3 a b c) = writeImpl { a, b, c }


instance (WriteForeign a, WriteForeign b, WriteForeign c, WriteForeign d) => WriteForeign (Case4 a b c d) where
    writeImpl (Case4 a b c d) = writeImpl { a, b, c, d }


readMatchImpl
    :: forall
        (row :: Row Type)
        (rec :: Row Type)
        (a :: Type)
        (rl :: RL.RowList Type)
        (rl1 :: RL.RowList Type)
        (rl2 :: Row Type)
     . ReadForeignVariant rl row
    => RL.RowToList row rl
    => RL.RowToList rec rl1
    => VariantMatchCases rl1 rl2 (F a)
    => Row.Union rl2 () row
    => Proxy row -> Record rec -> Foreign -> F a
readMatchImpl _ rec f =
    (readImpl f :: F (Variant row))
        >>= Variant.match rec :: F a


select
    :: forall (label :: Symbol) (row' :: Row Type) (row ::Row Type)
     . Row.Cons label Case row' row ⇒ IsSymbol label
    => Proxy label → Variant row
select = flip Variant.inj Case


select1 :: forall (label :: Symbol) (row' :: Row Type) (row ::Row Type) a
     . Row.Cons label (Case1 a) row' row ⇒ IsSymbol label
    => Proxy label → a -> Variant row
select1 label = Variant.inj label <<< Case1


select2 :: forall (label :: Symbol) (row' :: Row Type) (row ::Row Type) a b
     . Row.Cons label (Case2 a b) row' row ⇒ IsSymbol label
    => Proxy label → a -> b -> Variant row
select2 label a b = Variant.inj label $ Case2 a b


select3 :: forall (label :: Symbol) (row' :: Row Type) (row ::Row Type) a b c
     . Row.Cons label (Case3 a b c) row' row ⇒ IsSymbol label
    => Proxy label → a -> b -> c -> Variant row
select3 label a b c = Variant.inj label $ Case3 a b c


select4 :: forall (label :: Symbol) (row' :: Row Type) (row ::Row Type) a b c d
     . Row.Cons label (Case4 a b c d) row' row ⇒ IsSymbol label
    => Proxy label → a -> b -> c -> d -> Variant row
select4 label a b c d = Variant.inj label $ Case4 a b c d


uncase :: forall a. a -> Case -> a
uncase = const


uncase1 :: forall a. Case1 a -> a
uncase1 (Case1 a) = a


uncase2 :: forall a b. Case2 a b -> a /\ b
uncase2 (Case2 a b) = a /\ b


uncase3 :: forall a b c. Case3 a b c -> a /\ b /\ c
uncase3 (Case3 a b c) = a /\ b /\ c


uncase4 :: forall a b c d. Case4 a b c d -> a /\ b /\ c /\ d
uncase4 (Case4 a b c d) = a /\ b /\ c /\ d


use :: forall a. a -> (Case -> F a)
use = const <<< except <<< Right


use1 :: forall a x. (a -> x) -> (Case1 a -> F x)
use1 f = except <<< Right <<< f <<< uncase1


use2 :: forall a b x. (a -> b -> x) -> (Case2 a b -> F x)
use2 f = except <<< Right <<< uncurry f <<< uncase2


use3 :: forall a b c x. (a -> b -> c -> x) -> (Case3 a b c -> F x)
use3 f = except <<< Right <<< (\(a /\ b /\ c) -> f a b c) <<< uncase3


use4 :: forall a b c d x. (a -> b -> c -> d -> x) -> (Case4 a b c d -> F x)
use4 f = except <<< Right <<< (\(a /\ b /\ c /\ d) -> f a b c d) <<< uncase4


todo :: forall a x. a -> (x -> F a)
todo = const <<< except <<< Right