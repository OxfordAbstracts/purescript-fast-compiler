module Webb.Mutex.Internal.Result where

import Prelude

import Effect (Effect)
import Effect.Aff (Error)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff, runEffectFn1)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Uncurried (EffectFn1)
import Webb.Monad.Prelude (launch_)


{-  Expresses the idea of a return value in an Aff context. In reality,
  the underlying value is just a Promise, but this is needed so that
  we can express an _interface_ using the algebraic data types, and not type classes; e.g.
  
  data Args = 
    F1 String Int (Result Int)
    F2 Number Boolean (Result Unit)
    
  By doing so, we can express a foreign interface as a simple function, which we can
  store in data types. If we wish to call any particular interface and receive the result
  value, we can write a function that constructs the Result object, passes it to the
  interface, and then waits for the Result to have a value.
  
  type Interface args = args -> Aff Unit
  
  call :: forall args a. Interface args -> (Result a -> args) -> Aff a
  call f args = 
    let result = Result :: Result a
    in do 
      f (args result)
      x <- await result
      
  While it's unfortunate that we have to introduce `await` syntax, it will be type-checked,
  and it will enable us to write interfaces much more quickly. Most of the time we will
  be able to hide the await syntax anyway.
-}

foreign import data Result :: Type -> Type
foreign import _result :: forall a. Effect (Result a)
foreign import _set :: forall a. Result a -> EffectFn1 a Unit
foreign import _get :: forall a. Result a -> EffectFnAff a
foreign import _error :: forall a. Result a -> EffectFn1 Error Unit

instance Show (Result a) where
  show _ = "Result"

newResult :: forall m a. MonadEffect m => m (Result a)
newResult = liftEffect do _result

-- Publish an error to the result
error :: forall m a. MonadEffect m => Result a -> Error -> m Unit
error result e =
  let err = _error result
  in liftEffect do runEffectFn1 err e

return :: forall m a. MonadEffect m => Result a -> a -> m Unit
return res val = liftEffect do
  let set = _set res
  runEffectFn1 set val

{- In an Aff context, wait for a result to be provided. -}
await :: forall m a. MonadAff m => Result a -> m a
await res = liftAff do
  let get = _get res
  fromEffectFnAff get
    
-- Yields based on a hidden result, forcing resumption on a Promise-schedule, since
-- a Promise underlies the Aff.
yield :: forall m. MonadAff m => m Unit
yield = do 
  result <- newResult
  launch_ do 
    return result unit
  await result
