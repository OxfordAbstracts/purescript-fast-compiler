module ModuleA where

class MyMonad m where
  myBind :: m Int -> (Int -> m Int) -> m Int

data Box a = Box a

instance myMonadBox :: MyMonad Box where
  myBind (Box a) f = f a

runIt :: forall m. MyMonad m => m Int -> m Int
runIt x = myBind x (\_ -> x)

unbox :: Box Int -> Int
unbox (Box a) = a
