module Main where

import MethodConstraintGiven.Lib (class IxBind, class IxMonad, class IxApply, ibind, ipure)

-- Regression test: when an instance method has extra typeclass constraints
-- (beyond the instance head), those constraints should be treated as "given"
-- within the method body. Here, IxApply has superclasses IxBind and IxMonad,
-- so ibind and ipure should be available in the default implementation.

newtype Wrapper a = Wrapper a

instance IxBind Wrapper where
  ibind (Wrapper a) f = f a

instance IxMonad Wrapper where
  ipure = Wrapper

instance IxApply Wrapper where
  iapply (Wrapper f) (Wrapper a) = ipure (f a)
