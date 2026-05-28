-- A nullary capability class with no instances declared in a decl's
-- sig must be CARRIED into the inferred scheme rather than reported
-- as NoInstanceFound at the definer. The decl must take the
-- check_equation path (its sig carries an inner forall), so the
-- sig-pin records the capability constraint with no givens active
-- (check_equation has already popped them).
module Test where

class Cap

foreign import data T :: Type
foreign import mkT :: T

type Setup = { fetchPage :: forall m. m T }

useIt :: Cap => Setup -> T
useIt _ = mkT
