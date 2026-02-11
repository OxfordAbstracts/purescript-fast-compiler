module Classless
  ( (~)
  , InitRecordField
  , InitSumField
  , MapProp
  , MapSumRecord
  , NoArgs(..)
  , ProductSpec(..)
  , class Init
  , class InitProduct
  , class InitRecord
  , class InitSum
  , class MapProduct
  , class MapSum
  , class MapSumProp
  , class SequenceProduct
  , class SequenceRecord
  , class SequenceRecordRL
  , init
  , initProduct
  , initRecord
  , initSum
  , mapProduct
  , mapSum
  , mapSumProp
  , sequenceProduct
  , sequenceRecord
  , sequenceRecordRL
  , noArgs
  , type (~)
  , pick
  ) where

import Prelude

import Data.Generic.Rep (Argument(..), NoArguments(..), Product(..))
import Data.Symbol (class IsSymbol)
import Heterogeneous.Folding (class FoldingWithIndex, class HFoldlWithIndex, hfoldlWithIndex)
import Heterogeneous.Mapping (class HMap, class Mapping, hmap, mapping)
import Prim.Row (class Cons, class Lacks, class Union)
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as R
import Record as Record
import Record.Builder (Builder)
import Record.Builder as Builder
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

--- Types

data ProductSpec a b = ProductSpec a b

infixr 6 type ProductSpec as ~

infixr 6 ProductSpec as ~

data NoArgs = NoArgs

noArgs :: NoArgs
noArgs = NoArgs

--- Init

class Init fn a where
  init :: fn -> a

--- InitProduct

class InitProduct f a where
  initProduct :: f -> a

instance (Init fn a, InitProduct fn b) => InitProduct fn (a ~ b) where
  initProduct fn = init fn ~ initProduct fn

else instance InitProduct fn NoArgs where
  initProduct _ = NoArgs

else instance (Init fn a) => InitProduct fn a where
  initProduct fn = init fn

--- InitSum

class InitSum f r where
  initSum :: f -> { | r }

instance (InitRecord (InitSumField f) r) => InitSum f r where
  initSum f = initRecord (InitSumField f)

data InitSumField f = InitSumField f

instance (InitProduct f a) => Init (InitSumField f) a where
  init (InitSumField f) = initProduct f

--- InitRecord

class InitRecord f r where
  initRecord :: f -> { | r }

instance
  ( RowToList r rl
  , HFoldlWithIndex (InitRecordField fn) {} (Proxy rl) { | r }
  ) =>
  InitRecord fn r where
  initRecord fn = hfoldlWithIndex (InitRecordField fn) {} (Proxy :: Proxy rl)

data InitRecordField a = InitRecordField a

instance
  ( IsSymbol sym
  , Lacks sym r
  , Cons sym a r rr
  , Init fn a
  ) =>
  FoldingWithIndex (InitRecordField fn) (Proxy sym) { | r } (Proxy a) { | rr } where
  foldingWithIndex (InitRecordField fn) s r _ = Record.insert s (init fn) r

--- MapProduct

class MapProduct mp a b where
  mapProduct :: mp -> a -> b

instance
  ( Mapping mp a a'
  , MapProduct mp b b'
  ) =>
  MapProduct mp (a ~ b) (a' ~ b') where
  mapProduct mp (a ~ b) = (mapping mp a) ~ (mapProduct mp b)

else instance MapProduct mp NoArgs NoArgs where
  mapProduct _ = identity

else instance (Mapping mp a a') => MapProduct mp a a' where
  mapProduct mp x = mapping mp x

--- MapSum

class MapSum (mp :: Type) (ri :: Row Type) (ro :: Row Type) | mp ri -> ro where
  mapSum :: mp -> { | ri } -> { | ro }

data MapSumRecord mp = MapSumRecord mp

instance (HMap (MapSumRecord mp) { | ri } { | ro }) => MapSum mp ri ro where
  mapSum mp = hmap (MapSumRecord mp)

instance (MapProduct mp a b) => Mapping (MapSumRecord mp) a b where
  mapping (MapSumRecord mp) = mapProduct mp

--- MapSumProp

class MapSumProp (k :: Symbol) (ri :: Row Type) (ro :: Row Type) | k ri -> ro where
  mapSumProp :: Proxy k -> { | ri } -> { | ro }

instance (IsSymbol k, MapSum (MapProp k) ri ro) => MapSumProp k ri ro where
  mapSumProp prx = mapSum (MapProp prx)

--- MapProp

data MapProp (k :: Symbol) = MapProp (Proxy k)

instance (IsSymbol k, Cons k a rx r) => Mapping (MapProp k) { | r } a where
  mapping (MapProp k) = Record.get k

--- SequenceProduct

class SequenceProduct specI specO (f :: Type -> Type) | specO f -> specI where
  sequenceProduct :: specI -> f specO

instance (Applicative f) => SequenceProduct NoArgs NoArguments f where
  sequenceProduct _ = pure NoArguments

instance (Applicative f) => SequenceProduct (f a) (Argument a) f where
  sequenceProduct x = ado
    x' <- x
    in Argument x'

instance
  ( Applicative f
  , SequenceProduct a a' f
  , SequenceProduct b b' f
  ) =>
  SequenceProduct (ProductSpec a b) (Product a' b') f where
  sequenceProduct (ProductSpec a b) = ado
    a' <- sequenceProduct a
    b' <- sequenceProduct b
    in Product a' b'

--- SequenceRecord

class SequenceRecord row row' m | row' -> row m where
  sequenceRecord :: Record row -> m (Record row')

instance
  ( RL.RowToList row' rl'
  , SequenceRecordRL rl' row () row' m
  ) =>
  SequenceRecord row row' m where
  sequenceRecord a = Builder.build <@> {} <$> builder
    where
    builder = sequenceRecordRL (Proxy :: _ rl') a

class
  Functor m <=
  SequenceRecordRL (rl :: RL.RowList Type) row from to m
  | rl row -> from to m
  where
  sequenceRecordRL :: Proxy rl -> Record row -> m (Builder { | from } { | to })

instance
  ( IsSymbol name
  , Row.Cons name (m ty) () row
  , Functor m
  , Row.Lacks name ()
  , Row.Cons name ty () to
  ) =>
  SequenceRecordRL (RL.Cons name ty RL.Nil) row () to m where
  sequenceRecordRL _ a =
    Builder.insert namep <$> valA
    where
    namep = Proxy :: _ name
    valA = R.get namep a

else instance
  ( IsSymbol name
  , Row.Cons name (m ty) row' row
  , Apply m
  , SequenceRecordRL tail row' from from' m
  , Row.Lacks name from'
  , Row.Lacks name row'
  , Row.Cons name ty from' to
  ) =>
  SequenceRecordRL (RL.Cons name ty tail) row from to m where
  sequenceRecordRL _ a =
    fn <$> valA <*> rest
    where
    namep = Proxy :: _ name
    valA = R.get namep a
    tailp = Proxy :: _ tail
    rest = sequenceRecordRL tailp (R.delete namep a)
    fn valA' rest' = Builder.insert namep valA' <<< rest'

instance Applicative m => SequenceRecordRL RL.Nil row () () m where
  sequenceRecordRL _ _ = pure identity

--- Util

pick :: forall r2 rx r1. Union r2 rx r1 => { | r1 } -> { | r2 }
pick = unsafeCoerce
