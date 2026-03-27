-- | MRE for the operator constraint origin bug.
-- |
-- | Root cause: value_origins pollution through wildcard imports.
-- | Chain:
-- |   1. Decoders exports getField (unconstrained). value_origins[getField] = Decoders.
-- |   2. Class does "import Decoders" (wildcard). Decoders's value_origins propagate
-- |      into Class's value_origins. Class.value_origins[getField] = Decoders.
-- |   3. Combinators defines constrained getField = D.getField decode.
-- |      Combinators.value_origins[getField] = Combinators (local def, correct).
-- |   4. Facade imports Class THEN Combinators.
-- |      - From Class: value_origins[getField] = Decoders (first, wins via or_insert).
-- |      - From Combinators: or_insert won't override → getField stays as Decoders.
-- |      - Facade.value_origins[getField] = Decoders (WRONG).
-- |   5. Test.Main imports from Facade, uses .! operator.
-- |      resolve_origin(getField, Facade.exports) = Decoders.
-- |      operator_targets[.!] = (Some(Decoders), getField).
-- |      Codegen: Decoders.getField(obj)(key) — obj passed as decoder!
-- |
-- | Bug:     Decoders.getField(obj)(key)      — obj treated as decoder fn, TypeError!
-- | Correct: Combinators.getField(dict)(obj)(key)
-- |
-- TEST: 99
module TestOperatorConstraintOrigin where

import Facade ((.!))

-- | Use .! with Int — should resolve Decode Int instance (decode n = n).
-- | Correct: Combinators.getField(decodeInt)(99)(0) = decode(99) = 99
-- | Bug:     Decoders.getField(99)(0) → tries to call 99 as a function → TypeError
test :: Int
test = (99 :: Int) .! (0 :: Int)
