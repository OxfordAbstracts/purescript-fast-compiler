-- Defines a multi-type-param Proxy and a parameterized Bind instance.
-- Mirrors: Pipes.Internal defining bindProxy :: Monad m => Bind (Proxy a' a b' b m)
-- The instance is HERE, not in MyBind's module.
module MyProxy where

import Prelude
import MyBind

-- Multi-type-param type, like Proxy a' a b' b m
data MyProxy (m :: Type -> Type) a = MyProxyCon | MyProxyPure a

-- Parameterized instance WITH CONSTRAINT: Monad m => MyBind (MyProxy m)
-- The constraint parameter is key — it's what triggers the wrong module hint
-- because resolution goes through the instance registry.
instance myBindMyProxy :: Monad m => MyBind (MyProxy m) where
  myBind MyProxyCon _ = MyProxyCon
  myBind (MyProxyPure a) f = f a
