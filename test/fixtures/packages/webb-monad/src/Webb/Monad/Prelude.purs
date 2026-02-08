module Webb.Monad.Prelude
( module P
, showEffect
, andM, orM, notM, (&&=), (||=), timesRepeat, timesRepeat_
, forceEither, forceMaybe, forceMaybe', onCancel, throwString
, launch, launch_, kill, _kill, delayInt
, expectSatisfy, expectSatisfyM, expectNotSatisfyM, expectM, spyM, expect
)
where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Error.Class as E
import Control.Monad.Loops as Loop
import Data.Array as A
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.List as List
import Data.Maybe (Maybe)
import Data.Newtype (wrap)
import Data.Traversable (for)
import Debug (trace)
import Debug as P
import Effect (Effect)
import Effect.Aff (Aff, Fiber, cancelWith, delay, killFiber, launchAff, launchAff_)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Effect.Unsafe (unsafePerformEffect)
import Prim.TypeError (class Warn, Text)


showEffect :: forall a. Show a => Effect a -> String
showEffect m = show $ unsafePerformEffect m

andM :: forall m. Monad m => m Boolean -> m Boolean -> m Boolean
andM a b = Loop.andM (List.fromFoldable [a, b])

orM :: forall m. Monad m => m Boolean -> m Boolean -> m Boolean
orM a b = Loop.orM (List.fromFoldable [a, b])

notM ::forall m. Functor m => m Boolean -> m Boolean
notM m = not <$> m

infixr 3 andM as &&=
infixr 2 orM as ||=

timesRepeat :: forall m a. Monad m => Int -> m a -> m (Array a)
timesRepeat n prog = do
  let attempts = A.replicate n unit
  arr <- for attempts \_ -> do prog
  pure arr

timesRepeat_ :: forall m. Monad m => Int -> m Unit -> m Unit
timesRepeat_ n prog = do void $ timesRepeat n prog

forceEither :: forall m a. MonadThrow Error m => Either String a -> m a
forceEither m = case m of 
  Left s -> do throwString s
  Right a -> pure a

forceMaybe :: forall m a. MonadThrow Error m => Maybe a -> m a
forceMaybe m = E.liftMaybe (error "Unexpected Nothing") m

forceMaybe' :: forall m a. MonadThrow Error m => String -> Maybe a -> m a
forceMaybe' str m = E.liftMaybe (error str) m

onCancel :: forall a. Aff Unit -> Aff a -> Aff a
onCancel cancel prog = cancelWith prog (wrap $ \_ -> cancel)

throwString :: forall a m. MonadThrow Error m => String -> m a
throwString s = throwError (error s)

launch :: forall a m. MonadEffect m => Aff a -> m (Fiber a)
launch prog = liftEffect (launchAff prog)

launch_ :: forall m. MonadEffect m => Aff Unit -> m Unit
launch_ prog = liftEffect (launchAff_ prog)

kill :: forall m a. MonadAff m => Fiber a -> m Unit
kill fiber = liftAff $ killFiber (error "killing fiber") fiber

_kill :: forall m a. MonadAff m => Fiber a -> m Unit
_kill = kill

delayInt :: forall m. MonadAff m => Int -> m Unit
delayInt ms = liftAff do delay (ms # toNumber >>> wrap)

expectSatisfyM :: forall m a. 
  MonadThrow Error m => Show a =>
  a -> (a -> m Boolean) -> String -> m Unit
expectSatisfyM a f msg = do
  success <- f a
  unless success do 
    throwString $ show a <> " failed: " <> msg

expectNotSatisfyM :: forall m a. 
  MonadThrow Error m => Show a =>
  a -> (a -> m Boolean) -> String -> m Unit
expectNotSatisfyM a f msg = expectSatisfyM a (f >>> notM) msg

expectSatisfy :: forall m a. 
  MonadThrow Error m => Show a =>
  a -> (a -> Boolean) -> String -> m Unit
expectSatisfy a f msg = do
  let success = f a
  unless success do 
    throwString $ show a <> " failed: " <> msg
    
expectM :: forall m.
  MonadEffect m => 
  m Boolean -> String -> m Unit
expectM match msg = unlessM match do 
  liftEffect do throwString msg

expect :: forall m.
  MonadEffect m => 
  Boolean -> String -> m Unit
expect match msg = unless match do 
  liftEffect do throwString msg
  
-- Trace a monadic item in any monadic effect by binding it before printing it.
-- It is thus transparent to the value.
spyM :: forall m a. Warn (Text "Debug function usage") =>
  Monad m => m a -> m a
spyM ma = do
  a <- ma
  let _ = (trace a \_ -> unit)
  pure a


