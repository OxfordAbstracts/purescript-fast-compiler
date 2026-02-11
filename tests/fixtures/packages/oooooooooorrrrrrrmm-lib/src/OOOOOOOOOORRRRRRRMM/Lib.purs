module OOOOOOOOOORRRRRRRMM.Lib where

import Prelude

import Data.Date (Date)
import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Data.Symbol (class IsSymbol)
import Foreign (Foreign)
import Prim.Row as R
import Prim.RowList (RowList)
import Prim.RowList as RL
import Record (get, insert)
import Type.Proxy (Proxy(..))
import Yoga.JSON (class WriteForeign, writeImpl)

class ToValues' :: RowList Type -> RowList Type -> Row Type -> Constraint
class ToValues' rl0 rl1 i where
  toValues' :: Proxy rl0 -> Proxy rl1 -> { | i } -> Array Foreign

class ToValues i where
  toValues :: { | i } -> Array Foreign

type AllRows = RL.Cons "$1" Unit (RL.Cons "$2" Unit (RL.Cons "$3" Unit (RL.Cons "$4" Unit (RL.Cons "$5" Unit (RL.Cons "$6" Unit (RL.Cons "$7" Unit (RL.Cons "$8" Unit (RL.Cons "$9" Unit (RL.Cons "$10" Unit (RL.Cons "$11" Unit (RL.Cons "$12" Unit (RL.Cons "$13" Unit (RL.Cons "$14" Unit (RL.Cons "$15" Unit (RL.Cons "$16" Unit (RL.Cons "$17" Unit (RL.Cons "$18" Unit (RL.Cons "$19" Unit (RL.Cons "$20" Unit (RL.Cons "$21" Unit (RL.Cons "$22" Unit (RL.Cons "$23" Unit (RL.Cons "$24" Unit (RL.Cons "$25" Unit (RL.Cons "$26" Unit (RL.Cons "$27" Unit (RL.Cons "$28" Unit (RL.Cons "$29" Unit (RL.Cons "$30" Unit (RL.Cons "$31" Unit (RL.Cons "$32" Unit (RL.Cons "$33" Unit (RL.Cons "$34" Unit (RL.Cons "$35" Unit (RL.Cons "$36" Unit (RL.Cons "$37" Unit (RL.Cons "$38" Unit (RL.Cons "$39" Unit (RL.Cons "$40" Unit (RL.Cons "$41" Unit (RL.Cons "$42" Unit (RL.Cons "$43" Unit (RL.Cons "$44" Unit (RL.Cons "$45" Unit (RL.Cons "$46" Unit (RL.Cons "$47" Unit (RL.Cons "$48" Unit (RL.Cons "$49" Unit (RL.Cons "$50" Unit (RL.Cons "$51" Unit (RL.Cons "$52" Unit (RL.Cons "$53" Unit (RL.Cons "$54" Unit (RL.Cons "$55" Unit (RL.Cons "$56" Unit (RL.Cons "$57" Unit (RL.Cons "$58" Unit (RL.Cons "$59" Unit (RL.Cons "$60" Unit (RL.Cons "$61" Unit (RL.Cons "$62" Unit (RL.Cons "$63" Unit (RL.Cons "$64" Unit (RL.Cons "$65" Unit (RL.Cons "$66" Unit (RL.Cons "$67" Unit (RL.Cons "$68" Unit (RL.Cons "$69" Unit (RL.Cons "$70" Unit (RL.Cons "$71" Unit (RL.Cons "$72" Unit (RL.Cons "$73" Unit (RL.Cons "$74" Unit RL.Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

instance (RL.RowToList i rl0, ToValues' rl0 AllRows i) => ToValues i where
  toValues = toValues' (Proxy :: Proxy rl0) (Proxy :: Proxy AllRows)

instance ToValues' RL.Nil rl i where
  toValues' _ _ _ = []

instance (WriteForeign v, IsSymbol k, R.Lacks k i', R.Cons k v i' i, ToValues' rl0 rl1 i) => ToValues' (RL.Cons k v rl0) (RL.Cons k Unit rl1) i where
  toValues' _ _ i = [ writeImpl $ get (Proxy :: _ k) i ] <> toValues' (Proxy :: Proxy rl0) (Proxy :: Proxy rl1) i

class UseMaybe i o | i -> o where
  useMaybe :: i -> o

instance UseMaybe Int Int where
  useMaybe = identity

instance UseMaybe Number Number where
  useMaybe = identity

instance UseMaybe String String where
  useMaybe = identity

instance UseMaybe Boolean Boolean where
  useMaybe = identity

instance UseMaybe Date Date where
  useMaybe = identity

instance UseMaybe i o => UseMaybe (Nullable i) (Maybe o) where
  useMaybe = map useMaybe <<< toMaybe

instance UseMaybe i o => UseMaybe (Array i) (Array o) where
  useMaybe = map useMaybe

class UseMaybeRow :: RowList Type -> Row Type -> Row Type -> Constraint
class UseMaybeRow rl i o | rl i -> o where
  useMaybeRow :: Proxy rl -> { | i } -> { | o }

instance (RL.RowToList i rl, UseMaybeRow rl i o) => UseMaybe (Record i) (Record o) where
  useMaybe = useMaybeRow (Proxy :: Proxy rl)

instance UseMaybeRow RL.Nil i () where
  useMaybeRow _ _ = {}

instance (IsSymbol k, UseMaybe v v', R.Lacks k i', R.Lacks k o', R.Cons k v i' i, R.Cons k v' o' o, UseMaybeRow rl i o') => UseMaybeRow (RL.Cons k v rl) i o where
  useMaybeRow _ i = insert (Proxy :: _ k) (useMaybe (get (Proxy :: _ k) i)) $ useMaybeRow (Proxy :: Proxy rl) i