module GoJS.Unsafe.Set where

import Prelude

import Effect (Effect)
import Prim.Row (class Cons, class Union)

foreign import setUnsafe :: forall r a. a -> Record r -> Effect Unit

class RecursiveUnion :: forall k1 k2 k3. Row k1 -> Row k2 -> Row k3 -> Constraint
class RecursiveUnion rIn rest union

instance
  ( --   Symbol              Row Type     Row Type   Row Type
    Cons someKeyHere (Record someRowHere) restOfThis totalOfThis
  , Cons someKeyHere (Record someRowThere) restOfThat totalOfThat
  , Union someRowHere someRowThere bothRowsTogether
  , Cons someKeyHere bothRowsTogether restOfSuperset union
  ) =>
  RecursiveUnion totalOfThis totalOfThat union

foreign import unsafeRecUnion :: forall r1 r2 r3. Record r1 -> Record r2 -> Record r3

recUnion :: forall rIn rest total. RecursiveUnion rIn rest total => Record rIn -> Record rest -> Record total
recUnion = unsafeRecUnion

-- TODO: Finish this and probably merge into some upstream. recursive record joins are basic wtf
-- x = recUnion {x: {nestedX: 10}} {x: {nestedY: 20}} -- `shouldEqual` {x: {nestedX: 10, nestedY: 20}}

