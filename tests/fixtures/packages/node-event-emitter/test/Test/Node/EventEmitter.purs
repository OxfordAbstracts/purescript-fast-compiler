module Test.Node.EventEmitter where

import Prelude

import Data.Foldable (for_)
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, EffectFn2, mkEffectFn1, runEffectFn1, runEffectFn2, runEffectFn3)
import Node.EventEmitter (EventEmitter, EventHandle(..), on, on_, once, once_, prependListener, prependListener_, prependOnceListener, prependOnceListener_, unsafeEmitFn)
import Node.EventEmitter as EventEmitter
import Node.EventEmitter.UtilTypes (EventHandle1)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

fooH :: EventHandle1 EventEmitter String
fooH = EventHandle "foo" mkEffectFn1

spec :: Spec Unit
spec = describe "event-emitter" do
  it "`new` does not throw" do
    liftEffect $ void $ EventEmitter.new
  it "`emit` does not throw" do
    liftEffect do
      ee <- EventEmitter.new
      void $ runEffectFn1 (unsafeEmitFn ee :: EffectFn1 String Boolean) "foo"
      void $ runEffectFn2 (unsafeEmitFn ee :: EffectFn2 String String Boolean) "foo" "baz"
      void $ runEffectFn1 (unsafeEmitFn ee) "foo"
      void $ runEffectFn2 (unsafeEmitFn ee) "foo" "bar"
      void $ runEffectFn3 (unsafeEmitFn ee) "foo" "bar" "baz"
  describe "standard functions" do
    let
      fns =
        [ "on_" /\ on_
        , "once_" /\ once_
        , "prependListener_" /\ prependListener_
        , "prependOnceListener_" /\ prependOnceListener_
        ]
    for_ fns \(fnName /\ fn) -> do
      it (fnName <> " works") do
        liftEffect do
          let expected = "bar"
          ref <- Ref.new ""
          ee <- EventEmitter.new
          ee # fn fooH \val -> do
            Ref.write val ref
          void $ runEffectFn2 (unsafeEmitFn ee) "foo" expected
          val <- Ref.read ref
          val `shouldEqual` expected

  describe "subscribe functions" do
    let
      fns =
        [ "onSubscribe" /\ on
        , "onceSubscribe" /\ once
        , "prependListenerSubscribe" /\ prependListener
        , "prependOnceListenerSubscribe" /\ prependOnceListener
        ]
    for_ fns \(fnName /\ fn) -> do
      it (fnName <> " - normal call works") do
        liftEffect do
          let expected = "bar"
          ref <- Ref.new ""
          ee <- EventEmitter.new
          void $ ee # fn fooH \val -> do
            Ref.write val ref
          void $ runEffectFn2 (unsafeEmitFn ee) "foo" expected
          val <- Ref.read ref
          val `shouldEqual` expected
    for_ fns \(fnName /\ fn) -> do
      it (fnName <> " - unsubscribing before call works") do
        liftEffect do
          ref <- Ref.new ""
          ee <- EventEmitter.new
          remove <- ee # fn fooH \val -> do
            Ref.write val ref
          remove
          void $ runEffectFn2 (unsafeEmitFn ee) "foo" "bar"
          val <- Ref.read ref
          val `shouldEqual` ""
