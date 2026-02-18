module MyAlternative where

import MyApply (class MyApply)

class MyApply f <= MyAlternative f where
  myEmpty :: forall a. f a
