module TestSuperclass where

import MyFunctor (class MyFunctor, myMap)
import MyApply (class MyApply, myApply)

-- Uses myMap (MyFunctor method) through MyApply constraint.
-- Should extract the MyFunctor dict from dictMyApply via superclass accessor.
useBoth :: forall f a b. MyApply f => (a -> b) -> f a -> f b
useBoth f fa = myMap f fa
