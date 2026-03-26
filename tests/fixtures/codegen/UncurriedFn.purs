module UncurriedFn where
-- TEST: 99

-- | Minimal reproduction of the datetime-parsing / Parsing package bug:
-- | `TypeError: fn is not a function` at runFn5 call site.
-- |
-- | Pattern from Parsing.purs:
-- |   newtype ParserT s m a = ParserT (Fn5 state more lift throw done result)
-- |   bind (ParserT k1) next = ParserT (mkFn5 \s m l t d -> ...)
-- |   runParserT' state1 (ParserT k1) = ... runFn5 k1 state1 ...
-- |
-- | The reference compiler inlines mkFn2/mkFn5 calls when the argument is
-- | a lambda, generating multi-parameter JS functions directly:
-- |   function(a, b) { return body; }
-- | instead of:
-- |   mkFn2(function(a) { return function(b) { return body; }; })
-- |
-- | Using Fn2/mkFn2/runFn2 for simplicity (same pattern as Fn5).

-- Foreign data type for 2-arg uncurried functions
foreign import data Fn2 :: Type -> Type -> Type -> Type

-- Foreign mkFn2/runFn2 (same contract as Data.Function.Uncurried)
foreign import mkFn2 :: forall a b c. (a -> b -> c) -> Fn2 a b c
foreign import runFn2 :: forall a b c. Fn2 a b c -> a -> b -> c

-- Newtype wrapping an uncurried function (analogous to ParserT wrapping Fn5)
newtype Wrapper a = Wrapper (Fn2 Int Int a)

-- Construct wrapper with mkFn2 and a multi-param lambda.
-- Reference compiler output:  function(a, b) { return x; }
-- Current (buggy) output:     mkFn2(function(a) { return function(b) { return x; }; })
makeWrapper :: forall a. a -> Wrapper a
makeWrapper x = Wrapper (mkFn2 \a b -> x)

-- Unwrap and call via runFn2 (analogous to runParserT calling runFn5)
runWrapper :: forall a. Wrapper a -> Int -> Int -> a
runWrapper (Wrapper fn) = runFn2 fn

-- End-to-end test: build a Wrapper with mkFn2, then immediately call via runFn2.
test :: Int
test = runWrapper (makeWrapper 99) 1 2
