module GoJS.Unsafe.Method where

import Effect (Effect)

foreign import callUnsafe0 :: forall (obj :: Type) (output :: Type). String -> obj -> Effect output
foreign import callUnsafe1 :: forall (obj :: Type) (output :: Type) (arg1 :: Type). String -> arg1 -> obj -> Effect output
foreign import callUnsafe2 :: forall (obj :: Type) (output :: Type) (arg1 :: Type) (arg2 :: Type). String -> arg1 -> arg2 -> obj -> Effect output
foreign import callUnsafe3 :: forall (obj :: Type) (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type). String -> arg1 -> arg2 -> arg3 -> obj -> Effect output
foreign import callUnsafe4 :: forall (obj :: Type) (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type). String -> arg1 -> arg2 -> arg3 -> arg4 -> obj -> Effect output
foreign import callUnsafe5 :: forall (obj :: Type) (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type). String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> obj -> Effect output
foreign import callUnsafe6 :: forall (obj :: Type) (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type) (arg6 :: Type). String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> arg6 -> obj -> Effect output
foreign import callUnsafe7 :: forall (obj :: Type) (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type) (arg6 :: Type) (arg7 :: Type). String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> arg6 -> arg7 -> obj -> Effect output
foreign import callUnsafe8 :: forall (obj :: Type) (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type) (arg6 :: Type) (arg7 :: Type) (arg8 :: Type). String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> arg6 -> arg7 -> arg8 -> obj -> Effect output
