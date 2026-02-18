module PartialRenamed where

import Prelude

partial ∷ Partial ⇒ Int → Int
partial n = case n of
  0 -> 0

unsafeOp ∷ Int → Int
unsafeOp = otherDischargePartial partial

foreign import _otherDischargePartial :: forall a b. a -> b

otherDischargePartial :: forall a. (Partial => a) -> a
otherDischargePartial = _otherDischargePartial


main = do
  let _ = unsafeOp 0
  log "Done"