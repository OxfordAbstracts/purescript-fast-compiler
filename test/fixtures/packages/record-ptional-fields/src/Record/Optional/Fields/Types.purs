module Record.Optional.Fields.Types where

data Context

foreign import data Root :: Row Type -> Type -> Context

foreign import data AtProp :: (Type -> Context) -> Symbol -> Row Type -> Type -> Context

data ErrorDesc

foreign import data UnsupportedProp :: Symbol -> Row Type -> ErrorDesc

foreign import data UnexpectedType :: Type -> Type -> ErrorDesc

data TypeError :: Context -> ErrorDesc -> Type
data TypeError ctx err

class SetContextRow :: Row Type -> (Type -> Context) -> (Type -> Context) -> Constraint
class SetContextRow r ctx ctx' | r ctx -> ctx'

instance SetContextRow r (Root _1) (Root r)
else instance SetContextRow r (AtProp ctx prop _1) (AtProp ctx prop r)