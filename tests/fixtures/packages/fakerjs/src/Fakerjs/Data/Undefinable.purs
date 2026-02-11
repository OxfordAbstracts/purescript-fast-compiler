-- | This module defines types and functions for working with undefinable types
-- | using the FFI.

-- TODO: WAIT https://github.com/ethul/purescript-undefinable/pull/8

module Fakerjs.Data.Undefinable
  ( Undefinable
  , undefined
  , notUndefined
  , toMaybe
  , toUndefinable
  ) where

import Prelude

import Data.Eq (class Eq1)
import Data.Function (on)
import Data.Function.Uncurried (Fn3, runFn3)
import Data.Maybe (Maybe(..), maybe)
import Data.Ord (class Ord1)
import Unsafe.Coerce (unsafeCoerce)

-- | A undefinable type. This type constructor is intended to be used for
-- | interoperating with JavaScript functions which accept or return undefined
-- | values.
-- |
-- | The runtime representation of `Undefinable T` is the same as that of `T`,
-- | except that it may also be `undefined`. For example, the JavaScript values
-- | `undefined`, `[]`, and `[1,2,3]` may all be given the type
-- | `Undefinable (Array Int)`. Similarly, the JavaScript values `[]`, `[undefined]`,
-- | and `[1,2,undefined,3]` may all be given the type `Array (Undefinable Int)`.
-- |
-- | There is one pitfall with `Undefinable`, which is that values of the type
-- | `Undefinable T` will not function as you might expect if the type `T` happens
-- | to itself permit `undefined` as a valid runtime representation.
-- |
-- | In particular, values of the type `Undefinable (Undefinable T)` will ‘collapse’,
-- | in the sense that the PureScript expressions `notUndefined undefined` and `undefined`
-- | will both leave you with a value whose runtime representation is just
-- | `undefined`. Therefore it is important to avoid using `Undefinable T` in
-- | situations where `T` itself can take `undefined` as a runtime representation.
-- | If in doubt, use `Maybe` instead.
-- |
-- | `Undefinable` does not permit lawful `Functor`, `Applicative`, or `Monad`
-- | instances as a result of this pitfall, which is why these instances are
-- | not provided.
foreign import data Undefinable :: Type -> Type

type role Undefinable representational

-- | The undefined value.
foreign import undefined :: forall a. Undefinable a

foreign import undefinable :: forall a r. Fn3 (Undefinable a) r (a -> r) r

-- | Wrap a non-undefined value.
notUndefined :: forall a. a -> Undefinable a
notUndefined = unsafeCoerce

-- | Takes `Nothing` to `undefined`, and `Just a` to `a`.
toUndefinable :: forall a. Maybe a -> Undefinable a
toUndefinable = maybe undefined notUndefined

-- | Represent `undefined` using `Maybe a` as `Nothing`. Note that this function
-- | can violate parametricity, as it inspects the runtime representation of
-- | its argument (see the warning about the pitfall of `Undefinable` above).
toMaybe :: forall a. Undefinable a -> Maybe a
toMaybe n = runFn3 undefinable n Nothing Just

instance showUndefinable :: Show a => Show (Undefinable a) where
  show = maybe "undefined" show <<< toMaybe

instance eqUndefinable :: Eq a => Eq (Undefinable a) where
  eq = eq `on` toMaybe

instance eq1Undefinable :: Eq1 Undefinable where
  eq1 = eq

instance ordUndefinable :: Ord a => Ord (Undefinable a) where
  compare = compare `on` toMaybe

instance ord1Undefinable :: Ord1 Undefinable where
  compare1 = compare
