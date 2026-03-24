-- Bug: when using myBind on MyProxy m (where the instance is parameterized
-- with Monad m =>), the codegen references MyBind.myBindMyProxy (the class
-- module) instead of MyProxy.myBindMyProxy (the instance definition module).
--
-- In the package tests this manifests as:
--   Control_Bind.bindProxy is not a function
-- because bindProxy is in Pipes.Internal, not Control.Bind.
module TestWrongModule where

import Prelude
import MyBind
import MyProxy

-- Function that uses MyBind on MyProxy within a Monad m context.
-- Mirrors Pipes.Core.composeResponse which uses bindProxy(dictMonad).
useProxy :: forall m a. Monad m => MyProxy m a -> (a -> MyProxy m a) -> MyProxy m a
useProxy p f = myBind p f

test = case (useProxy (MyProxyPure 42 :: MyProxy Array Int) (\x -> MyProxyPure x)) of
  MyProxyPure x -> x
  MyProxyCon -> 0

-- TEST: 42
