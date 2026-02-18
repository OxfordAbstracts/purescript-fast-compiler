module CallSiteDictPassing where

class MyShow a where
  myShow :: a -> String

myShowThing :: forall a. MyShow a => a -> String
myShowThing x = myShow x

-- Should pass dictMyShow to myShowThing at the call site
wrapper :: forall a. MyShow a => a -> String
wrapper x = myShowThing x
