module Types where

import Lib as R

-- Zero-param alias whose body is a qualified reference to a data type
-- with the SAME unqualified name, applied to concrete type arguments.
-- This must NOT cause an infinite expansion loop:
-- expanding T -> R.T A B C
-- must not re-expand R.T as the alias again.
type T = R.T R.A R.B R.C
