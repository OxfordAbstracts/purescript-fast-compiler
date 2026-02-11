module Internal.ForeignUtils where

import Data.Maybe (Maybe(..))
import Unsafe.Coerce (unsafeCoerce)

foreign import data PossiblyUndefined :: Type -> Type
foreign import undefined :: forall a. PossiblyUndefined a

toUndefined :: forall a. Maybe a -> PossiblyUndefined a
toUndefined Nothing = undefined
toUndefined (Just a) = unsafeCoerce a
