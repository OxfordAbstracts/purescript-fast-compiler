module FRP.Event.Aff where

import Prelude

import Control.Monad.ST.Class (liftST)
import Control.Parallel (parSequence_)
import Data.Array.ST as STArray
import Effect.Aff (Aff, apathize, error, joinFiber, killFiber, launchAff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Effect.Uncurried (mkEffectFn1, runEffectFn1, runEffectFn2)
import FRP.Event (Event, makeEventO, subscribeO)

bindToAff :: forall a b. Event a -> (a -> Aff b) -> Event b
bindToAff e f = makeEventO $ mkEffectFn1 \k -> do
  fibRef <- launchAff (pure unit) >>= Ref.new
  u <- runEffectFn2 subscribeO e $ mkEffectFn1 \v -> do
    fib <- Ref.read fibRef
    newFib <- launchAff do
      apathize $ joinFiber fib
      o <- f v
      liftEffect $ runEffectFn1 k o
    Ref.write newFib fibRef
  pure do
    u
    fib <- Ref.read fibRef
    launchAff_ do
      killFiber (error "not an error") fib

bindToAffWithCancellation :: forall a b. Event a -> (a -> Aff b) -> Event b
bindToAffWithCancellation e f = makeEventO $ mkEffectFn1 \k -> do
  fibRef <- launchAff (pure unit) >>= Ref.new
  u <- runEffectFn2 subscribeO e $ mkEffectFn1 \v -> do
    fib <- Ref.read fibRef
    newFib <- launchAff do
      apathize $ killFiber (error "not an error") fib
      o <- f v
      liftEffect $ runEffectFn1 k o
    Ref.write newFib fibRef
  pure do
    u
    fib <- Ref.read fibRef
    launchAff_ do
      killFiber (error "not an error") fib

bindToAffParallel :: forall a b. Event a -> (a -> Aff b) -> Event b
bindToAffParallel e f = makeEventO $ mkEffectFn1 \k -> do
  fibsRef <- liftST $ STArray.new
  u <- runEffectFn2 subscribeO e $ mkEffectFn1 \v -> do
    newFib <- launchAff do
      o <- f v
      liftEffect $ runEffectFn1 k o
    void $ liftST $ STArray.push newFib fibsRef
  pure do
    u
    fibs <- liftST $ STArray.freeze fibsRef
    launchAff_ $ parSequence_ $ fibs <#> apathize <<< killFiber
      (error "not an error")