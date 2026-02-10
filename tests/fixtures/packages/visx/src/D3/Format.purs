module D3.Format where

import Prelude
import Data.Int (toNumber)
import Data.JSDate (JSDate)
import Unsafe.Coerce (unsafeCoerce)

foreign import data D3Format ∷ Type

foreign import format ∷ String → D3Format

formatWhatever ∷ ∀ a. D3Format → a → String
formatWhatever formatFn s =
  (unsafeCoerce formatFn) (unsafeCoerce s)

formatNumber ∷ D3Format → Number → String
formatNumber formatFn n =
  ((unsafeCoerce formatFn) ∷ Number → String) n

formatInt ∷ D3Format → Int → String
formatInt formatFn i =
  ((unsafeCoerce formatFn) ∷ Number → String) (toNumber i)

formatDate ∷ D3Format → JSDate → String
formatDate formatFn i =
  ((unsafeCoerce formatFn) ∷ JSDate → String) i
