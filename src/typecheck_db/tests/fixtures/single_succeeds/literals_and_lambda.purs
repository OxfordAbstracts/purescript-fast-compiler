module Test.LiteralsAndLambda where

-- Integer / String / Char / Boolean / Float literals all infer
-- to their Prim counterparts.
anInt :: Int
anInt = 42

aNumber :: Number
aNumber = 1.5

aString :: String
aString = "hi"

aChar :: Char
aChar = 'x'

aBoolean :: Boolean
aBoolean = true

-- Identity function — the canonical polymorphic lambda.
identity :: forall a. a -> a
identity x = x

-- `const` — two-arg polymorphic function.
constFn :: forall a b. a -> b -> a
constFn x _ = x
