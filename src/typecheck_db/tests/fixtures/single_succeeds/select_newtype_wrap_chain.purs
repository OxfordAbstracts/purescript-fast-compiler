module Test.SelectNewtypeWrapChain where

-- Minimal repro of the Puregres.Select cluster (Query.Event.*).
-- The real failing site is roughly:
--
--     wrapm $ runSelect $ selectEventColumns # from(...) # whereVal(...)
--
-- where:
--   - selectEventColumns has a 150-column chain of `++`s building a record row
--   - runSelect threads the gets row through `SelectFrom (ColCons head tail) gets table`
--   - wrapm wants `Newtype a b => f1 (f2 b) -> f1 (f2 a)`
--   - the sig pins `a = Event` and the chain pins `b = EventRec`
--
-- The solver hits its depth bound because `Newtype Unif Unif` and
-- `Coercible Unif Unif` wantings stay pending — unifs from
-- wrapm's instantiation never get pinned to Event / EventRec early
-- enough for the instance head match to succeed.

class Newtype a b | a -> b

class Functor f where
  fmap :: forall a b. (a -> b) -> f a -> f b

data Aff a = Aff a
instance Functor Aff where
  fmap f (Aff a) = Aff (f a)

data Array_ a = Array_ a
instance Functor Array_ where
  fmap f (Array_ a) = Array_ (f a)

foreign import wrapmImpl
  :: forall f1 f2 a b
   . f1 (f2 b) -> f1 (f2 a)

wrapm
  :: forall f1 f2 a b
   . Functor f1
  => Functor f2
  => Newtype a b
  => f1 (f2 b) -> f1 (f2 a)
wrapm = wrapmImpl

-- Mirror Puregres.Select's row machinery.
class Union :: Row Type -> Row Type -> Row Type -> Constraint
class Union a b c | a b -> c, a c -> b, b c -> a

data ColCons head tail = ColCons head tail
data ColNil = ColNil

data SelectStart gets head tail = SelectStart

foreign import selectImpl :: forall head r. head -> SelectStart { | r } head ColNil

select :: forall head r. head -> SelectStart { | r } head ColNil
select = selectImpl

foreign import andSelectImpl
  :: forall gets getsNew tail head newHead
   . SelectStart { | gets } head tail
  -> newHead
  -> SelectStart { | getsNew } newHead (ColCons head tail)

andSelect
  :: forall gets r getsNew tail head newHead
   . Union gets r getsNew
  => SelectStart { | gets } head tail
  -> newHead
  -> SelectStart { | getsNew } newHead (ColCons head tail)
andSelect = andSelectImpl

infixl 5 andSelect as ++

data SelectFrom heads gets table = SelectFrom

data EndQuery = EndQuery

foreign import fromImpl
  :: forall head tail table gets
   . (EndQuery -> table)
  -> SelectStart { | gets } head tail
  -> SelectFrom (ColCons head tail) { | gets } table

from
  :: forall head tail table gets
   . (EndQuery -> table)
  -> SelectStart { | gets } head tail
  -> SelectFrom (ColCons head tail) { | gets } table
from = fromImpl

foreign import runSelectImpl
  :: forall table head tail gets
   . SelectFrom (ColCons head tail) { | gets } table
  -> Aff (Array_ { | gets })

runSelect
  :: forall table head tail gets
   . SelectFrom (ColCons head tail) { | gets } table
  -> Aff (Array_ { | gets })
runSelect = runSelectImpl

-- Caller's target newtype.
type EventRec =
  ( id :: Int
  , name :: String
  , status :: Int
  , kind :: Int
  , owner :: Int
  , parent :: Int
  )

newtype Event = Event { | EventRec }
instance Newtype Event { | EventRec }

-- Mock columns + table.
data EventId = EventId
data EventName = EventName
data EventStatus = EventStatus
data EventKind = EventKind
data EventOwner = EventOwner
data EventParent = EventParent

data Events = Events
events :: EndQuery -> Events
events _ = Events

selectEventColumns :: SelectStart { | EventRec } EventParent _
selectEventColumns =
  select EventId
    ++ EventName
    ++ EventStatus
    ++ EventKind
    ++ EventOwner
    ++ EventParent

-- Pathological call: wrapm . runSelect . from . selectEventColumns.
-- Sig forces `a = Event`. Chain pins `b = { | EventRec }`.
-- The real cluster fails here with SolverDepthExceeded.
selectEventFromStageId :: Int -> Aff (Array_ Event)
selectEventFromStageId _ =
  wrapm (runSelect (from events selectEventColumns))
