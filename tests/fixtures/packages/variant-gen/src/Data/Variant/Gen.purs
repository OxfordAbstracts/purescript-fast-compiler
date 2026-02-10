module Data.Variant.Gen where

import Prelude

import Control.Monad.Gen (class MonadGen, frequency, oneOf)
import Data.List as L
import Data.NonEmpty (NonEmpty, (:|))
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant, inj)
import Prim.Row as Row
import Prim.RowList as RL
import Record as Record
import Type.Prelude (Proxy(..))

-- Generate a `Variant` with uniform probability given a record whose
-- generators' labels correspond to the `Variant`'s labels
--
-- ```purs
-- genMyVariant :: Gen (Variant (id :: String, unit :: Unit))
-- genMyVariant =
--   genVariantUniform
--     { id: genAlphaString
--     , unit: pure unit
--     }
-- ```
--
-- Inspired by https://github.com/JordanMartinez/purescript-veither/blob/9fb195b7bd97cfcf21bbd389b55002ca458f1bb4/src/Data/Veither.purs#L461
genVariantUniform
  :: forall genRows rowList variantRows m
   . MonadGen m
  => RL.RowToList genRows rowList
  => GenVariantUniformNonEmptyList rowList genRows variantRows m
  => Record genRows
  -> m (Variant variantRows)
genVariantUniform = oneOf <<< buildGenVariantUniformNonEmptyList (Proxy :: Proxy rowList)

-- For what functions we can use `NonEmpty List ...` as input? For now - only for `oneOf`
class
  GenVariantUniformNonEmptyList (rowList :: RL.RowList Type) (genRows :: Row Type) (variantRows :: Row Type) (m :: Type -> Type)
  | rowList -> genRows variantRows m
  where
  buildGenVariantUniformNonEmptyList :: Proxy rowList -> Record genRows -> NonEmpty L.List (m (Variant variantRows))

-- Instance for a list with at least one element
instance
  ( IsSymbol name
  , Row.Cons name (m a) genRows' genRows
  , Row.Cons name a variantRows' variantRows
  , GenVariantUniformList restRowList genRows variantRows m
  , MonadGen m
  ) =>
  GenVariantUniformNonEmptyList (RL.Cons name (m a) restRowList) genRows variantRows m where
  buildGenVariantUniformNonEmptyList _ rec =
    let
      nameProxy = Proxy :: Proxy name
      restProxy = Proxy :: Proxy restRowList
      (generator :: m a) = Record.get nameProxy rec
      (makeVariant :: m (Variant variantRows)) = map (inj nameProxy) generator
      tail = buildGenVariantUniformList restProxy rec
    in
      makeVariant :| tail

-- Class for handling the rest of the list
class
  GenVariantUniformList (rowList :: RL.RowList Type) (genRows :: Row Type) (variantRows :: Row Type) (m :: Type -> Type)
  | rowList -> genRows variantRows m
  where
  buildGenVariantUniformList :: Proxy rowList -> Record genRows -> L.List (m (Variant variantRows))

-- Instance for the rest of the list when it has elements
instance
  ( IsSymbol name
  , Row.Cons name (m a) genRows' genRows
  , Row.Cons name a variantRows' variantRows
  , GenVariantUniformList restRowList genRows variantRows m
  , MonadGen m
  ) =>
  GenVariantUniformList (RL.Cons name (m a) restRowList) genRows variantRows m where
  buildGenVariantUniformList _ rec =
    let
      nameProxy = Proxy :: Proxy name
      restProxy = Proxy :: Proxy restRowList
      (generator :: m a) = Record.get nameProxy rec
      (makeVariant :: m (Variant variantRows)) = map (inj nameProxy) generator
      rest = buildGenVariantUniformList restProxy rec
    in
      L.Cons makeVariant rest

-- Base case for rest of list
instance
  ( MonadGen m
  ) =>
  GenVariantUniformList RL.Nil genRows variantRows m where
  buildGenVariantUniformList _ _ = L.Nil

------------------------------------------------------------
-- Generate a `Variant` with uniform probability given a record whose
-- generators' labels correspond to the `Variant`'s labels
--
-- ```purs
-- genMyVariant :: Gen (Variant (id :: String, unit :: Unit))
-- genMyVariant =
--   genVariantFrequency
--     { id: Tuple 0.1 genAlphaString
--     , unit: Tuple 0.9 (pure unit)
--     }
-- ```
--
-- Inspired by https://github.com/JordanMartinez/purescript-veither/blob/9fb195b7bd97cfcf21bbd389b55002ca458f1bb4/src/Data/Veither.purs#L461
genVariantFrequency
  :: forall genRows rowList variantRows m
   . MonadGen m
  => RL.RowToList genRows rowList
  => GenVariantFrequencyNonEmptyList rowList genRows variantRows m
  => Record genRows
  -> m (Variant variantRows)
genVariantFrequency r = frequency $ buildGenVariantFrequencyNonEmptyList (Proxy :: Proxy rowList) r

-- For what functions we can use `NonEmpty List ...` as input? For now - only for `oneOf`
class
  GenVariantFrequencyNonEmptyList (rowList :: RL.RowList Type) (genRows :: Row Type) (variantRows :: Row Type) (m :: Type -> Type)
  | rowList -> genRows variantRows m
  where
  buildGenVariantFrequencyNonEmptyList :: Proxy rowList -> Record genRows -> NonEmpty L.List (Tuple Number (m (Variant variantRows)))

-- Instance for a list with at least one element
instance
  ( IsSymbol name
  , Row.Cons name (Tuple Number (m a)) genRows' genRows
  , Row.Cons name a variantRows' variantRows
  , GenVariantFrequencyList restRowList genRows variantRows m
  , MonadGen m
  ) =>
  GenVariantFrequencyNonEmptyList (RL.Cons name (Tuple Number (m a)) restRowList) genRows variantRows m where
  buildGenVariantFrequencyNonEmptyList _ rec =
    let
      nameProxy = Proxy :: Proxy name
      restProxy = Proxy :: Proxy restRowList
      (Tuple freq generator :: Tuple Number (m a)) = Record.get nameProxy rec
      head = Tuple freq (map (inj nameProxy) generator)
      tail = buildGenVariantFrequencyList restProxy rec
    in
      head :| tail

-- Class for handling the rest of the list
class
  GenVariantFrequencyList (rowList :: RL.RowList Type) (genRows :: Row Type) (variantRows :: Row Type) (m :: Type -> Type)
  | rowList -> genRows variantRows m
  where
  buildGenVariantFrequencyList :: Proxy rowList -> Record genRows -> L.List (Tuple Number (m (Variant variantRows)))

-- Instance for the rest of the list when it has elements
instance
  ( IsSymbol name
  , Row.Cons name (Tuple Number (m a)) genRows' genRows
  , Row.Cons name a variantRows' variantRows
  , GenVariantFrequencyList restRowList genRows variantRows m
  , MonadGen m
  ) =>
  GenVariantFrequencyList (RL.Cons name (Tuple Number (m a)) restRowList) genRows variantRows m where
  buildGenVariantFrequencyList _ rec =
    let
      nameProxy = Proxy :: Proxy name
      Tuple freq gen = Record.get nameProxy rec
      current = Tuple freq (map (inj nameProxy) gen)
      rest = buildGenVariantFrequencyList (Proxy :: Proxy restRowList) rec
    in
      L.Cons current rest

-- Base case for rest of list
instance
  ( MonadGen m
  ) =>
  GenVariantFrequencyList RL.Nil genRows variantRows m where
  buildGenVariantFrequencyList _ _ = L.Nil
