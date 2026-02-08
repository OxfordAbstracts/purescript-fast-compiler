-- # classless-arbitrary
-- ## Installation
-- ```
-- spago install classless
-- spago install classless-arbitrary
-- ```
--
-- ## Usage
-- ### Imports
-- For the examples in this document you'll need the following imports:

module Test.Classless.Arbitrary where

import Prelude

import Classless (class Init, class InitRecord, class InitSum, initRecord, initSum, noArgs, (~))
import Classless.Arbitrary as Arb
import Control.Alt ((<|>))
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Record as Record
import Test.QuickCheck.Gen (Gen, chooseInt)

-- ### Simple combinators
--
-- Let's assume we have the following somehow nested type:

type Items = Array
  ( Either
      String
      (Tuple Int Boolean)
  )

-- We can define a random generator of type `Gen Items` by reproducing the
-- nested structure with those primitives and combinators:

genItems'1 :: Gen Items
genItems'1 = Arb.array
  ( Arb.either
      Arb.string
      (Arb.tuple Arb.int Arb.boolean)
  )

-- The advantage of this approach is that we have full control over how each
-- piece of the type is generated. E.g. the `Arb.int` combinator will generate
-- Integers in some defined default range. But we can replace it with any other
-- generator of type `Gen Int`, maybe with one that can be configured to produce
-- values in a different range.  

customInt :: Gen Int
customInt = chooseInt 10 20

-- This library is using QuickCheck's `Gen` type, so you can use whatever
-- already exists for this type.
--
-- ### Record types
-- This works well for homogenous types like Arrays or Maybes. Things get a bit
-- more interesting when we like to write generators in this
-- style for heterogenous structures like Records. Let's say we'd like to
-- generate values for the following record type:

type User =
  { name :: String
  , age :: Int
  , loggedIn :: Boolean
  , coordinates :: Array { x :: Int, y :: Int }
  }

-- The least boilerplate we archive by using the generic `Arb.record` function
-- like below:

genUser'1 :: Gen User
genUser'1 = Arb.record
  { name: Arb.string
  , age: Arb.int
  , loggedIn: Arb.boolean
  , coordinates: Arb.array $ Arb.record
      { x: Arb.int
      , y: Arb.int
      }
  }

-- ### Generic Sum types
--
-- There's a similar construct for ADTs which have a generic instance. This
-- deserves a bit more explanation. Let's assume we have a `RemoteData` type. A
-- sum type with 4 constructors each having some or none positional arguments.

data RemoteData
  = NotAsked
  | Loading Int Int Int
  | Error String
  | Success
      { status :: Int
      , body :: String
      }

derive instance Generic RemoteData _

-- We can now use the `Arb.sum` function with a specification of how each field
-- in the type should be correlated with a generator. If there are no arguments,
-- we use `noArgs`. If we have a product of arguments we use the `~` operator to
-- list generators for the fields. The syntax is inspired by the [routing-duplex package](https://pursuit.purescript.org/packages/purescript-routing-duplex/0.4.1)

genRemoteData'1 :: Gen RemoteData
genRemoteData'1 = Arb.sum
  { "NotAsked": noArgs
  , "Loading": Arb.int ~ Arb.int ~ Arb.int
  , "Error": Arb.string
  , "Success": Arb.record
      { status: Arb.int
      , body: Arb.string
      }
  }

-- Of course, the above only compiles if all constructors are specified with the
-- correct labels and all the other types align to the target type.
--
--- ### Roll your own type class
--
-- At this moment we have some powerful combinators to create Generators for
-- most of the common data structures that we use in a program. And we have fine
-- grained control over how each piece of a type should be generated. The
-- downside of it is, that we have to manually write the Generators for each
-- type. As the name suggests, this "classless" package does not provide a
-- type class. But you can define a type class yourself. And the package is
-- designed to make this as boilerplate free as possible. The advantage of
-- defining the type class at your side is that you can write instances for every
-- type without the headache of orphan instances and Newtype wrappers.
--
-- Let's see how this works:

class MyArbitrary a where
  arbitrary :: Gen a

instance MyArbitrary Int where
  arbitrary = Arb.int

instance MyArbitrary String where
  arbitrary = Arb.string

instance MyArbitrary Boolean where
  arbitrary = Arb.boolean

instance (MyArbitrary a) => MyArbitrary (Array a) where
  arbitrary = Arb.array arbitrary

instance (MyArbitrary a) => MyArbitrary (Maybe a) where
  arbitrary = Arb.maybe arbitrary

instance (MyArbitrary a, MyArbitrary b) => MyArbitrary (Either a b) where
  arbitrary = Arb.either arbitrary arbitrary

instance (MyArbitrary a, MyArbitrary b) => MyArbitrary (Tuple a b) where
  arbitrary = Arb.tuple arbitrary arbitrary

-- So far this, should be quite familiar and not surprising. We defined instances
-- for a couple of concrete types like String or Boolean. As well as a couple of
-- combined types like `Array a` which refer to our instance to fill the values
-- of the generic type parameters. This does not work that easily for constructs
-- like records. Because they're completely heterogenous, meaning they can contain an
-- arbitrary amount of different types. Now we need a trick to "pass" our own
-- type class implementation to a generic function that traverses the record
-- fields. The concept that is used here is inspired by the [heterogeneous
-- package](https://github.com/thought2/purescript-heterogeneous) and is well
-- documented in the librarie's README.
--
-- We define a "dummy" data type and write an instance of the `Init` type class
-- for it:

data MyInit = MyInit

instance (MyArbitrary a) => Init MyInit (Gen a) where
  init _ = arbitrary

-- Now we have everything we need to define a type class instance for records
-- like this:

instance (Arb.Record r' r, InitRecord MyInit r') => MyArbitrary (Record r) where
  arbitrary = Arb.record $ initRecord MyInit

-- And for sum types we can define the following helper function which may be
-- familiar to you (see e.g. genericShow)

genericSum :: forall r' a. Arb.Sum r' a => InitSum MyInit r' => Gen a
genericSum = Arb.sum $ initSum MyInit

-- It does not matter if you have not fully understood the details of the
-- previous section. It's just important to note that we have created a type
-- class that is able to produce the three sample Generators we defined earlier
-- completely generically:

genItems'2 :: Gen Items
genItems'2 = arbitrary

genUser'2 :: Gen User
genUser'2 = arbitrary

genRemoteData'2 :: Gen RemoteData
genRemoteData'2 = genericSum

-- ### Combine both approaches to get the best of both worlds
--
-- This is very convenient but what we lose here is the ability to define
-- different generators for the same types that somewhere occur. Every integer
-- is generated in the same way and without Newtype wrappers there would be no way to
-- opt in for the `chooseInt` implementation that is explained above.
--
-- Depending on the use case we can chose the one or the other approach. But
-- wouldn't it be nice to have a combination of both somehow?
--
-- Let's try to write a Generator for the `User` record type above where every
-- field except one is derived by the type class.

genUser'3 :: Gen User
genUser'3 = Arb.record
  $ Record.union
      { age: chooseInt 0 100
      }
  $ initRecord MyInit

-- `initRecord` initializes the fields for us based on our type class. However,
-- before we pass field specification to the `Arb.record` function, we just
-- merge it with our manually defined subset of the spec and there we go.
-- The inference is optimized in such a way that this even works if the types
-- that you specify manually have no instances for your type class. As you can
-- see below, the integer is generated by the type class but for char there's no
-- instance so we have to merge it into the spec:

genAB :: Gen { a :: Int, b :: Char }
genAB = Arb.record
  $ Record.union
      { b: Arb.char
      }
  $ initRecord MyInit

-- The same patten works for sum types, too! Let's try to do the same with the
-- `RemoteData` sample. Let's say we only want a custom generator for the
-- `Error` case.

genRemoteData'3 :: Gen RemoteData
genRemoteData'3 = Arb.sum
  $ Record.union
      { "Error": pure "error one" <|> pure "error two"
      }
  $ initSum MyInit

-- We can even provide a Generator only for one field of a product:

genRemoteData'4 :: Gen RemoteData
genRemoteData'4 = Arb.sum
  $ Record.union
      { "Loading": arbitrary ~ arbitrary ~ chooseInt 0 100
      }
  $ initSum MyInit

-- And finally we can combine the sum and record mechanism. E.g. below we
-- generically retrieve everything except the `status` field in the `Success` case:

genRemoteData'5 :: Gen RemoteData
genRemoteData'5 = Arb.sum
  $ Record.union
      { "Success": Arb.record
          $ Record.union
              { status: chooseInt 200 500
              }
          $ initRecord MyInit
      }
  $ initSum MyInit

--
-- ## Documentation
-- Module documentation is [published on Pursuit](http://pursuit.purescript.org/packages/purescript-classless-arbitrary).