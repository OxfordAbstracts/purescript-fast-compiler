module Webb.Test.Prelude
( module P
, shouldEqualM
, shouldNotEqualM
, shouldSatisfyM
, shouldNotSatisfyM
, shouldSatisfyM_
, shouldNotSatisfyM_
, shouldSatisfyMFlipped
, shouldNotSatisfyMFlipped
, shouldSatisfyM_Flipped
, shouldNotSatisfyM_Flipped
, (?=), (!=), (?:), (!:), (?@), (!@), (===), (!==)
, runSpecs
)
where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Exception (Error, error)
import Test.Spec (Spec, describe, it, itOnly, describeOnly, parallel, sequential) as P
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy, shouldNotEqual, shouldNotSatisfy) as P
import Test.Spec.Discovery (discover)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

runSpecs :: forall m. MonadAff m => String -> m Unit
runSpecs rxString = do 
  specs <- discover rxString
  liftEffect $ runSpecAndExitProcess [consoleReporter] specs

throwString :: forall m a. MonadThrow Error m => String -> m a
throwString msg = do throwError (error msg)

shouldEqualM :: forall m a. 
  MonadThrow Error m => 
  Eq a => 
  Show a =>
  m a -> a -> m Unit
shouldEqualM ma b = do
  a <- ma
  shouldEqual a b

shouldNotEqualM :: forall m a. 
  MonadThrow Error m => 
  Eq a => 
  Show a =>
  m a -> a -> m Unit
shouldNotEqualM ma b = do
  a <- ma
  shouldNotEqual a b

shouldSatisfyM :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  a -> (a -> m Boolean) -> m Unit
shouldSatisfyM a f = do
  satisfied <- f a
  unless satisfied do
    throwString $ show a <> " failed to satisfy predicate"
    
shouldSatisfyM_ :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  m a -> (a -> Boolean) -> m Unit
shouldSatisfyM_ ma f = do
  a <- ma
  unless (f a) do
    throwString $ show a <> " failed to satisfy predicate"

shouldNotSatisfyM :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  a -> (a -> m Boolean) -> m Unit
shouldNotSatisfyM a f = do
  satisfied <- f a
  when satisfied do
    throwString $ show a <> " wrongly satisfied predicate"

shouldNotSatisfyM_ :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  m a -> (a -> Boolean) -> m Unit
shouldNotSatisfyM_ ma f = do
  a <- ma
  when (f a) do
    throwString $ show a <> " wrongly satisfied predicate"
    
shouldSatisfyMFlipped :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  (a -> m Boolean) -> a -> m Unit
shouldSatisfyMFlipped = flip shouldSatisfyM
    
shouldSatisfyM_Flipped :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  (a -> Boolean) -> m a -> m Unit
shouldSatisfyM_Flipped = flip shouldSatisfyM_

shouldNotSatisfyMFlipped :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  (a -> m Boolean) -> a -> m Unit
shouldNotSatisfyMFlipped = flip shouldNotSatisfyM

shouldNotSatisfyM_Flipped :: forall m a. 
  MonadThrow Error m => 
  Show a =>
  (a -> Boolean) -> m a -> m Unit
shouldNotSatisfyM_Flipped = flip shouldNotSatisfyM_
    
infix 1 shouldEqualM as ?=
infix 1 shouldNotEqualM as !=

infix 1 shouldSatisfyMFlipped as ?:
infix 1 shouldNotSatisfyMFlipped as !:

infix 1 shouldSatisfyM_Flipped as ?@
infix 1 shouldNotSatisfyM_Flipped as !@

infix 1 shouldEqual as ===
infix 1 shouldNotEqual as !==