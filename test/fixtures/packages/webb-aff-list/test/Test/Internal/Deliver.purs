module Test.Internal.Deliver where

import Test.Prelude

import Effect.Aff (Aff)
import Webb.AffList.Internal.Deliver as Deliver



type DeliverProps = Unit

isOpen :: forall a. Deliver.Deliver a -> Boolean -> Aff Unit
isOpen d flag = do 
  Deliver.isOpen d ?= flag