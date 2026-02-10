module GoJS.Unsafe.Get where

foreign import getAttrs :: forall d @a. Array String -> d -> a

getUnsafe :: forall d @t. Array String -> d -> t
getUnsafe = getAttrs