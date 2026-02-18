module MyPrelude (module MyFunctor, module MyApply, module MyAlternative) where

import MyFunctor (class MyFunctor, myMap, (<$>))
import MyApply (class MyApply, myApply, (<*>))
import MyAlternative (class MyAlternative, myEmpty)
