module ConstrainedInstance where
-- TEST: "int"

-- Reproduces routing-duplex gsep bug: constrained instance generated as
-- plain object instead of function taking dict parameter.

class MyConvert a b | a -> b where
  convert :: a -> b

instance convertIntString :: MyConvert Int String where
  convert _ = "int"

class MyWrap a where
  wrap :: a -> String

-- Constrained instance: should be function(dictMyConvert) { return {...}; }
-- Bug: generated as plain object { wrap: ... }
instance wrapWithConvert :: MyConvert a String => MyWrap a where
  wrap x = convert x

-- Should resolve to: wrapWithConvert(convertIntString).wrap(42)
-- Bug: generates wrap(42) — missing dict application entirely
test :: String
test = wrap 42
