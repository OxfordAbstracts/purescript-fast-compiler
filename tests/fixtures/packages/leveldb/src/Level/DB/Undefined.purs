module Level.DB.Undefined where
import Data.Maybe (Maybe(..))
import Unsafe.Coerce (unsafeCoerce)

fromUndefined :: forall a . Undefined a -> Maybe a
fromUndefined u = if isUndefined u then Nothing else Just (unsafeCoerce u)

foreign import data Undefined :: Type -> Type

foreign import isUndefined :: forall a. Undefined a -> Boolean


