module Data.EtaConversionTransformer
  ( class EtaConversionTransformer
  , transform
  , (<<|)
  , transformFlipped
  , (|>>)
  , class WithInputEtaConversionTransformer
  , transformWith
  , (<<:)
  , transformWithFlipped
  , (:>>)
  ) where

import Prelude

class EtaConversionTransformer function return constructor |
  return -> constructor,
  constructor -> return
  where
  transform :: constructor -> function -> return

instance args9 :: EtaConversionTransformer
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> o)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 a3 a4 a5 a6 a7 a8 a9 = constructor $ function a1 a2 a3 a4 a5 a6 a7 a8 a9
else
instance args8 :: EtaConversionTransformer
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> o)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 a3 a4 a5 a6 a7 a8 = constructor $ function a1 a2 a3 a4 a5 a6 a7 a8
else
instance args7 :: EtaConversionTransformer
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> o)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 a3 a4 a5 a6 a7 = constructor $ function a1 a2 a3 a4 a5 a6 a7
else
instance args6 :: EtaConversionTransformer
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> o)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 a3 a4 a5 a6 = constructor $ function a1 a2 a3 a4 a5 a6
else
instance args5 :: EtaConversionTransformer
  (a1 -> a2 -> a3 -> a4 -> a5 -> o)
  (a1 -> a2 -> a3 -> a4 -> a5 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 a3 a4 a5 = constructor $ function a1 a2 a3 a4 a5
else
instance args4 :: EtaConversionTransformer
  (a1 -> a2 -> a3 -> a4 -> o)
  (a1 -> a2 -> a3 -> a4 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 a3 a4 = constructor $ function a1 a2 a3 a4
else
instance args3 :: EtaConversionTransformer
  (a1 -> a2 -> a3 -> o)
  (a1 -> a2 -> a3 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 a3 = constructor $ function a1 a2 a3
else
instance args2 :: EtaConversionTransformer
  (a1 -> a2 -> o)
  (a1 -> a2 -> ret)
  (o -> ret)
  where
  transform constructor function a1 a2 = constructor $ function a1 a2
else
instance args1 :: EtaConversionTransformer
  (a1 -> o)
  (a1 -> ret)
  (o -> ret) where
  transform constructor function a1 = constructor $ function a1


class WithInputEtaConversionTransformer function return constructor |
  return -> constructor,
  constructor -> return,
  return -> function
  where
  transformWith :: constructor -> function -> return

instance withInputArgs9 :: WithInputEtaConversionTransformer
  (i -> a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> o)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 a3 a4 a5 a6 a7 a8 a9 = constructor $ \i -> function i a1 a2 a3 a4 a5 a6 a7 a8 a9
else
instance withInputArgs8 :: WithInputEtaConversionTransformer
  (i -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> o))
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 a3 a4 a5 a6 a7 a8 = constructor $ \i -> function i a1 a2 a3 a4 a5 a6 a7 a8
else
instance withInputArgs7 :: WithInputEtaConversionTransformer
  (i -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> o))
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 a3 a4 a5 a6 a7 = constructor $ \i -> function i a1 a2 a3 a4 a5 a6 a7
else
instance withInputArgs6 :: WithInputEtaConversionTransformer
  (i -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> o))
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 a3 a4 a5 a6 = constructor $ \i -> function i a1 a2 a3 a4 a5 a6
else
instance withInputArgs5 :: WithInputEtaConversionTransformer
  (i -> (a1 -> a2 -> a3 -> a4 -> a5 -> o))
  (a1 -> a2 -> a3 -> a4 -> a5 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 a3 a4 a5 = constructor $ \i -> function i a1 a2 a3 a4 a5
else
instance withInputArgs4 :: WithInputEtaConversionTransformer
  (i -> (a1 -> a2 -> a3 -> a4 -> o))
  (a1 -> a2 -> a3 -> a4 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 a3 a4 = constructor $ \i -> function i a1 a2 a3 a4
else
instance withInputArgs3 :: WithInputEtaConversionTransformer
  (i -> (a1 -> a2 -> a3 -> o))
  (a1 -> a2 -> a3 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 a3 = constructor $ \i -> function i a1 a2 a3
else
instance withInputArgs2 :: WithInputEtaConversionTransformer
  (i -> (a1 -> a2 -> o))
  (a1 -> a2 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 a2 = constructor $ \i -> function i a1 a2
else
instance withInputArgs1 :: WithInputEtaConversionTransformer
  (i -> (a1 -> o))
  (a1 -> ret)
  ((i -> o) -> ret)
  where
  transformWith constructor function a1 = constructor $ \i -> function i a1

transformFlipped :: forall function return constructor. EtaConversionTransformer function return constructor => function -> constructor -> return
transformFlipped function constructor = transform constructor function

transformWithFlipped :: forall function return constructor. WithInputEtaConversionTransformer function return constructor => function -> constructor -> return
transformWithFlipped function constructor = transformWith constructor function

infixr 9 transform as <<|
infixr 9 transformWith as <<:
infixr 8 transformFlipped as |>>
infixr 8 transformWithFlipped as :>>