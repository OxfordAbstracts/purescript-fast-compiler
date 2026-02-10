module Classless.Arbitrary
  ( Arbitrary
  , additive
  , array
  , boolean
  , char
  , class Record
  , class Sum
  , conj
  , disj
  , dual
  , either
  , first
  , identity
  , int
  , last
  , list
  , maybe
  , multiplicative
  , nonEmptyArray
  , nonEmptyString
  , number
  , ordering
  , record
  , string
  , sum
  , tuple, record'
  , unit
  , class GetCases
  , getCases
  , MapInl(..)
  , MapInr(..)
  , MapRepToA(..)
  , class HomRecToNEA
  , homRecToNEA
  , ToNEA(..)
  ) where

import Prelude hiding (unit, identity)

import Classless (class SequenceProduct, class SequenceRecord, sequenceProduct, sequenceRecord)
import Control.Monad.Gen (chooseBool, sized)
import Control.Monad.Gen.Common as MGC
import Control.Monad.ST as ST
import Data.Array.NonEmpty as NEA
import Data.Array.NonEmpty.Internal (NonEmptyArray)
import Data.Array.ST as STA
import Data.Either (Either)
import Data.Enum (toEnumWithDefaults)
import Data.Generic.Rep (class Generic, Constructor(..), Sum(..), to)
import Data.Identity (Identity(..))
import Data.List (List)
import Data.Maybe (Maybe, fromJust)
import Data.Monoid.Additive (Additive(..))
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Monoid.Dual (Dual(..))
import Data.Monoid.Multiplicative (Multiplicative(..))
import Data.Semigroup.First (First(..))
import Data.Semigroup.Last (Last(..))
import Data.String.CodeUnits as Str
import Data.String.NonEmpty.CodeUnits as NESCU
import Data.String.NonEmpty.Internal (NonEmptyString)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Heterogeneous.Folding (class Folding, class HFoldl, hfoldl)
import Heterogeneous.Mapping (class HMap, class Mapping, hmap)
import Partial.Unsafe (unsafePartial)
import Prelude as P
import Prim.Row (class Cons, class Lacks, class Union)
import Record as R
import Record as Record
import Test.QuickCheck.Gen (Gen, frequency)
import Test.QuickCheck.Gen as Gen
import Type.Equality (class TypeEquals)
import Type.Proxy (Proxy(..))
import Type.Row.Homogeneous (class Homogeneous)
import Unsafe.Coerce (unsafeCoerce)

type Arbitrary a = Gen a

int :: Arbitrary Int
int = Gen.chooseInt (-1000000) 1000000

boolean :: Arbitrary Boolean
boolean = chooseBool

number :: Arbitrary Number
number = Gen.uniform

string :: Arbitrary String
string = Str.fromCharArray <$> array char

nonEmptyString :: Arbitrary NonEmptyString
nonEmptyString = NESCU.cons <$> char <*> string

char :: Arbitrary Char
char = toEnumWithDefaults bottom top <$> Gen.chooseInt 0 65536

unit :: Arbitrary Unit
unit = pure P.unit

ordering :: Arbitrary Ordering
ordering = Gen.elements $ unsafePartial fromJust $ NEA.fromArray [ LT, EQ, GT ]

array :: forall a. Arbitrary a -> Arbitrary (Array a)
array = Gen.arrayOf

nonEmptyArray :: forall a. Arbitrary a -> Arbitrary (NonEmptyArray a)
nonEmptyArray arb = do
  x <- arb
  xs <- array arb
  pure $ unsafePartial fromJust $ NEA.fromArray $ ST.run do
    mxs <- STA.unsafeThaw xs
    _ <- STA.push x mxs
    STA.unsafeFreeze mxs

first :: forall a. Arbitrary a -> Arbitrary (First a)
first x = First <$> x

last :: forall a. Arbitrary a -> Arbitrary (Last a)
last x = Last <$> x

additive :: forall a. Arbitrary a -> Arbitrary (Additive a)
additive x = Additive <$> x

conj :: forall a. Arbitrary a -> Arbitrary (Conj a)
conj x = Conj <$> x

multiplicative :: forall a. Arbitrary a -> Arbitrary (Multiplicative a)
multiplicative x = Multiplicative <$> x

disj :: forall a. Arbitrary a -> Arbitrary (Disj a)
disj x = Disj <$> x

dual :: forall a. Arbitrary a -> Arbitrary (Dual a)
dual x = Dual <$> x

tuple :: forall a b. Arbitrary a -> Arbitrary b -> Arbitrary (Tuple a b)
tuple x y = Tuple <$> x <*> y

maybe :: forall a. Arbitrary a -> Arbitrary (Maybe a)
maybe = MGC.genMaybe

either :: forall a b. Arbitrary a -> Arbitrary b -> Arbitrary (Either a b)
either = MGC.genEither

list :: forall a. Arbitrary a -> Arbitrary (List a)
list x = sized \n -> Gen.chooseInt zero n >>= flip Gen.listOf x

identity :: forall a. Arbitrary a -> Arbitrary (Identity a)
identity x = Identity <$> x

--- Record

class Record rspec r | r -> rspec where
  record :: Record rspec -> Arbitrary (Record r)

instance (SequenceRecord rspec r Gen) => Record rspec r where
  record = sequenceRecord

record' :: forall rspec r. (SequenceRecord rspec r Gen) => Record rspec -> Arbitrary (Record r) 
record' = sequenceRecord


--- Sum

class Sum ri a | a -> ri where
  sum :: { | ri } -> Gen a

instance
  ( Generic a rep
  , GetCases ri rep ro'
  , HMap (MapRepToA a) { | ro' } { | ro }
  , HomRecToNEA ro (Gen a)
  , Homogeneous ro (Gen a)
  , Homogeneous ro' (Gen rep)
  ) =>
  Sum ri a where
  sum sumSpec = homRecToNEA cases
    <#> (Tuple 1.0)
    # frequency
    where
    casesRep = getCases sumSpec (Proxy :: _ rep)
    cases = hmap (D $ Proxy :: _ a) casesRep

data MapRepToA (a :: Type) = D (Proxy a)

instance (Generic a rep, Functor f) => Mapping (MapRepToA a) (f rep) (f a) where
  mapping _ = map to

class GetCases (ri :: Row Type) (rep :: Type) (ro :: Row Type) | rep ri -> ro where
  getCases :: { | ri } -> Proxy rep -> { | ro }

instance
  ( Cons sym (Gen (Constructor sym genRep)) () ro
  , Cons sym prodSpec () ri
  , SequenceProduct prodSpec genRep Gen
  , IsSymbol sym
  ) =>
  GetCases ri (Constructor sym rep) ro where
  getCases r _ =
    Record.insert (Proxy :: _ sym) (Constructor <$> head) {}
    where
    head = r
      # Record.get (Proxy :: _ sym)
      # sequenceProduct

instance
  ( GetCases riA repA roA
  , GetCases riB repB roB
  , Cons sym y () riA
  , Cons sym y riB ri
  , Lacks sym riB
  , TypeEquals repA (Constructor sym x)
  , HMap MapInl { | roA } { | roA' }
  , HMap MapInr { | roB } { | roB' }
  , Union roA' roB' ro
  , IsSymbol sym
  , Union riA riB ri
  , Union riB riA ri
  ) =>
  GetCases ri (Sum repA repB) ro where
  getCases r _ =     
    Record.union
      (hmap MapInl xA)
      (hmap MapInr xB)
      where
      xA = getCases (pick r :: {| riA}) (Proxy :: _ repA) :: { | roA }
      xB = getCases (pick r :: {| riB}) (Proxy :: _ repB) :: { | roB }

pick :: forall r2 rx r1. Union r2 rx r1 =>  {| r1} -> {| r2}
pick = unsafeCoerce

-- 

class HomRecToNEA r a where
  homRecToNEA :: { | r } -> NonEmptyArray a

instance
  ( Homogeneous r a
  , HFoldl ToNEA Unit { | r } (NonEmptyArray a)
  ) =>
  HomRecToNEA r a where
  homRecToNEA r = hfoldl ToNEA P.unit r

data ToNEA = ToNEA

instance Folding ToNEA Unit a (NonEmptyArray a) where
  folding ToNEA _ = pure

instance Folding ToNEA (NonEmptyArray a) a (NonEmptyArray a) where
  folding ToNEA acc x = x `NEA.cons` acc

--

data MapInl = MapInl

instance Mapping MapInl (Gen a) (Gen (Sum a b)) where
  mapping MapInl = map Inl

data MapInr = MapInr

instance Mapping MapInr (Gen b) (Gen (Sum a b)) where
  mapping MapInr = map Inr