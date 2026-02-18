module GivenConstraintBareVar where

class Decode a where
  decode :: String -> a

class HasField (l :: Symbol) r a | l r -> a

-- When `Decode a` appears in the function signature and `a` is bare,
-- the chained-class ambiguity check should see it as "given" and not error.
decodeField :: forall a r. Decode a => HasField "value" r a => Record r -> a
decodeField _ = decode ""
