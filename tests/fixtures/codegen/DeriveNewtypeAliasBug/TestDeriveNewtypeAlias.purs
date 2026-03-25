module TestDeriveNewtypeAlias where

import Prelude
import Data.Newtype (class Newtype)
import MyTrans (MyTrans(..), unMyTrans)
import MyAlias (MyAlias)

-- Newtype wrapping the alias from another module
newtype Wrapper a = Wrapper (MyAlias a)

derive instance newtypeWrapper :: Newtype (Wrapper a) _

-- Derive Functor through the cross-module alias:
-- should resolve to functorMyTrans (the actual type), not functorMyAlias (the alias)
derive newtype instance functorWrapper :: Functor Wrapper

unwrap :: forall a. Wrapper a -> Array a
unwrap (Wrapper x) = unMyTrans x

-- TEST: [2,3,4]
test = unwrap (map (_ + 1) (Wrapper (MyTrans [1, 2, 3])))
