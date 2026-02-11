module Halogen.UseTrigger where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Ref as Ref
import Halogen.Hooks (class HookNewtype, type (<>), HookType, UseEffect, UseRef, UseState, captures, useRef, useState, useTickEffect)
import Halogen.Hooks as Hooks
import Halogen.UseTrigger.Internal (EvalTrigger, newEvalTrigger)

foreign import data UseTrigger :: (Type -> Type) -> HookType

type UseTrigger' m =
  UseState EvalTrigger
    <> UseRef (Array (TickHandler m))
    <> UseEffect
    <> Hooks.Pure

instance HookNewtype (UseTrigger m) (UseTrigger' m)

type TickHandler m = { continue :: Hooks.HookM m Unit } -> Hooks.HookM m Unit

type UseTriggerInterface m =
  { triggerEval :: Hooks.HookM m Unit
  , onNextTick :: TickHandler m -> Hooks.HookM m Unit
  }

useTrigger :: forall m. MonadEffect m => Hooks.Hook m (UseTrigger m) (UseTriggerInterface m)
useTrigger = Hooks.wrap hook
  where
  hook = Hooks.do
    _ /\ stateId <- useState (newEvalTrigger unit)
    _ /\ handlersRef <- useRef []

    captures {} useTickEffect $ do
      handlers <- liftEffect $ Ref.read handlersRef
      nextHandlersRef <- liftEffect $ Ref.new []
      for_ handlers \h -> do
        let
          continue :: Hooks.HookM m Unit
          continue = liftEffect $ Ref.modify_ (_ `Array.snoc` h) nextHandlersRef
        h { continue }
      liftEffect do
        hs <- Ref.read nextHandlersRef
        Ref.write hs handlersRef
      pure Nothing

    let
      triggerEval = Hooks.put stateId (newEvalTrigger unit)

      onNextTick f = liftEffect do
        Ref.modify_ (_ `Array.snoc` f) handlersRef

    Hooks.pure
      { triggerEval
      , onNextTick
      }