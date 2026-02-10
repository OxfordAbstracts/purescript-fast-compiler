module GoJS.Unsafe.Static where

import Effect (Effect)


foreign import callStatic0 :: forall (output :: Type). String -> String -> Effect output
foreign import callStatic1 :: forall (output :: Type) (arg1 :: Type). String -> String -> arg1 -> Effect output
foreign import callStatic2 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type). String -> String -> arg1 -> arg2 -> Effect output
foreign import callStatic3 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> Effect output
foreign import callStatic4 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> arg4 -> Effect output
foreign import callStatic5 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> Effect output


foreign import callStaticPure1 :: forall (output :: Type) (arg1 :: Type). String -> String -> arg1 -> output
foreign import callStaticPure2 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type). String -> String -> arg1 -> arg2 -> output
foreign import callStaticPure3 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> output
foreign import callStaticPure4 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> arg4 -> output
foreign import callStaticPure5 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> output
foreign import callStaticPure6 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type) (arg6 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> arg6 -> output
foreign import callStaticPure7 :: forall (output :: Type) (arg1 :: Type) (arg2 :: Type) (arg3 :: Type) (arg4 :: Type) (arg5 :: Type) (arg6 :: Type) (arg7 :: Type). String -> String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> arg6 -> arg7 -> output
