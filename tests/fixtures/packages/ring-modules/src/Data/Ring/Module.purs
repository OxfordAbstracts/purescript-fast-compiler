module Data.Ring.Module
  ( class LeftModule
  , mzeroL
  , maddL, (^+)
  , msubL, (^-)
  , mmulL, (^*)
  , mnegateL

  , class RightModule
  , mzeroR
  , maddR, (+^)
  , msubR, (-^)
  , mmulR, (*^)
  , mnegateR
  ) where

import Data.Ring (class Ring)
import Data.Unit (Unit, unit)

--------------------------------------------------------------------------------

-- | Left modules over rings.
-- |
-- | Instances must satisfy the following laws:
-- |
-- |  - Left distributivity: `r ^* (x ^+ y) = r ^* x ^+ r ^* y`
-- |  - Left distributivity: `(r + s) ^* x = r ^* x ^+ s ^* x`
-- |  - Left compatibility: `(r * s) ^* x = r ^* (s ^* x)`
-- |  - Left identity: `one ^* x = x`
class (Ring r) <= LeftModule x r | x -> r where
  mzeroL :: x
  maddL  :: x -> x -> x
  msubL  :: x -> x -> x
  mmulL  :: r -> x -> x

infixl 6 maddL as ^+
infixl 6 msubL as ^-
infixl 7 mmulL as ^*

instance leftModuleUnit :: (Ring a) => LeftModule Unit a where
  mzeroL = unit
  maddL _ _ = unit
  msubL _ _ = unit
  mmulL _ _ = unit

mnegateL :: ∀ x r. LeftModule x r => x -> x
mnegateL = (mzeroL ^- _)

--------------------------------------------------------------------------------

-- | Right modules over rings.
-- |
-- | Instances must satisfy the following laws:
-- |
-- |  - Right distributivity: `(x +^ y) *^ r = x *^ r +^ y *^ r`
-- |  - Right distributivity: `x *^ (r + s) = x *^ r +^ x *^ s`
-- |  - Right compatibility: `x *^ (r * s) = (x *^ r) *^ s`
-- |  - Right identity: `x *^ one = x`
class (Ring r) <= RightModule x r | x -> r where
  mzeroR :: x
  maddR  :: x -> x -> x
  msubR  :: x -> x -> x
  mmulR  :: x -> r -> x

infixl 6 maddR as +^
infixl 6 msubR as -^
infixl 7 mmulR as *^

instance rightModuleUnit :: (Ring a) => RightModule Unit a where
  mzeroR = unit
  maddR _ _ = unit
  msubR _ _ = unit
  mmulR _ _ = unit

mnegateR :: ∀ x r. RightModule x r => x -> x
mnegateR = (mzeroR -^ _)
