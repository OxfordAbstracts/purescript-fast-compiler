module ApplicativeDict where

-- Reproduces Bug 4: Applicative dict not passed to `pure` call.
-- When `myPure` (a class method) is used at a concrete type like Box,
-- the generated JS must resolve and pass the instance dictionary.
-- Reference compiler output: myPure(myApplicativeBox)(42)
-- Bug: generates myPure(42), treating 42 as the dict

class MyApplicative f where
  myPure :: forall a. a -> f a

data Box a = Box a

instance myApplicativeBox :: MyApplicative Box where
  myPure x = Box x

-- Constrained: should generate function(dictMyApplicative) { ... }
wrapIt :: forall f. MyApplicative f => f Int
wrapIt = myPure 42

-- Concrete: should resolve dict to myApplicativeBox
boxed :: Box Int
boxed = myPure 42
