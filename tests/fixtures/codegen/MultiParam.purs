module MultiParam where

class MyConvert a b where
  myConvert :: a -> b

instance convertIntString :: MyConvert Int String where
  myConvert _ = "int"

doConvert :: forall a b. MyConvert a b => a -> b
doConvert x = myConvert x
