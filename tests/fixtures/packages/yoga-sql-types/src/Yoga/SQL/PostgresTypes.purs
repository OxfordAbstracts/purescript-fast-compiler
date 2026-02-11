module Yoga.SQL.PostgresTypes where

import Prelude

import Control.Monad.Except.Trans (ExceptT, runExceptT)
import Data.Array as Array
import Data.Array.NonEmpty.Internal (NonEmptyArray)
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (intercalate)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Identity (Identity(..))
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe, fromJust)
import Data.Newtype (class Newtype, un)
import Data.Nullable (toNullable)
import Data.Reflectable (reflectType)
import Data.Semigroup.Foldable (intercalateMap)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Traversable (traverse)
import Data.Tuple.Nested (type (/\))
import Foreign (Foreign, ForeignError, readArray, readBoolean, readInt, readNull, readNumber, readString, renderForeignError, unsafeToForeign)
import Foreign.Object as Object
import Heterogeneous.Folding (class Folding, class FoldingWithIndex, class HFoldl, class HFoldlWithIndex, hfoldl, hfoldlWithIndex)
import Partial.Unsafe (unsafePartial)
import Prim.Coerce (class Coercible)
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RowList
import Record.Builder (Builder)
import Record.Builder as Builder
import Safe.Coerce (coerce)
import Type.Proxy (Proxy(..))
import Type.Row.Homogeneous (class Homogeneous)
import Unsafe.Coerce (unsafeCoerce)
import Yoga.JSON (unsafeStringify)
import Yoga.JSON.Error (renderHumanError)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Core SQL Query with Row Type Tracking
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A SQL query that tracks its parameters at the type level
-- | The row type `r` represents { paramName :: paramType, ... }
data SQLQuery :: Row Type -> Type
data SQLQuery rows = SQLQuery (Array String) String

sqlQueryToString :: forall r. SQLQuery r -> String
sqlQueryToString (SQLQuery _ q) = q

-- | Opaque SQL parameter type (database-specific)
foreign import data SQLParameter :: Type

-- | Opaque SQL result type (database-specific)
foreign import data SQLResult :: Type

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Converting PureScript Values to SQL Parameters
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class ToSQLParam a where
  toSQLParam :: a -> SQLParameter

instance ToSQLParam Int where
  toSQLParam = unsafeCoerce

else instance ToSQLParam String where
  toSQLParam = unsafeCoerce

else instance ToSQLParam Number where
  toSQLParam = unsafeCoerce

else instance ToSQLParam Boolean where
  toSQLParam = unsafeCoerce

else instance (ToSQLParam a) => ToSQLParam (Array a) where
  toSQLParam = unsafeCoerce

else instance (ToSQLParam a) => ToSQLParam (NonEmptyArray a) where
  toSQLParam = unsafeCoerce

else instance (ToSQLParam a) => ToSQLParam (Maybe a) where
  toSQLParam = map toSQLParam >>> toNullable >>> unsafeCoerce

else instance (ToSQLParam b, Newtype a b) => ToSQLParam a where
  toSQLParam = unsafeCoerce

else instance (Coercible a b, ToSQLParam b) => ToSQLParam b where
  toSQLParam = unsafeCoerce

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Converting SQL Results to PureScript Values
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

fromSQLValue :: forall @a. SQLFromForeign a => SQLResult -> Either String a
fromSQLValue param =
  (un Identity $ runExceptT $ fromSQLResultImpl (unsafeToForeign param))
    # lmap (intercalateMap ", " renderHumanError)

class SQLFromForeign a where
  fromSQLResultImpl :: Foreign -> ExceptT (NonEmptyList ForeignError) Identity a

instance SQLFromForeign Boolean where
  fromSQLResultImpl = readBoolean

instance SQLFromForeign Int where
  fromSQLResultImpl = readInt

instance SQLFromForeign String where
  fromSQLResultImpl = readString

instance SQLFromForeign Number where
  fromSQLResultImpl = readNumber

instance (SQLFromForeign a) => SQLFromForeign (Array a) where
  fromSQLResultImpl = readArray >=> traverse fromSQLResultImpl

instance (SQLFromForeign a) => SQLFromForeign (Maybe a) where
  fromSQLResultImpl = readNull >=> traverse fromSQLResultImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Result Array Parsing (for multiple return values)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

singleResult :: forall @a b. SQLFromForeign a => (a -> b) -> Array SQLResult -> Either String b
singleResult mk = case _ of
  [ x ] -> fromSQLValue @a x <#> mk
  x | len <- Array.length x -> Left $ "Expected exactly one result, got " <> show len

twoResults :: forall @a @b c. SQLFromForeign a => SQLFromForeign b => (a -> b -> c) -> Array SQLResult -> Either String c
twoResults mk = case _ of
  [ _1, _2 ] -> mk <$> fromSQLValue @a _1 <*> fromSQLValue @b _2
  x | len <- Array.length x -> Left $ "Expected exactly two results, got " <> show len

threeResults :: forall @a @b @c d. SQLFromForeign a => SQLFromForeign b => SQLFromForeign c => (a -> b -> c -> d) -> Array SQLResult -> Either String d
threeResults mk = case _ of
  [ _1, _2, _3 ] -> mk <$> fromSQLValue @a _1 <*> fromSQLValue @b _2 <*> fromSQLValue @c _3
  x | len <- Array.length x -> Left $ "Expected exactly three results, got " <> show len

fourResults :: forall @a @b @c @d e. SQLFromForeign a => SQLFromForeign b => SQLFromForeign c => SQLFromForeign d => (a -> b -> c -> d -> e) -> Array SQLResult -> Either String e
fourResults mk = case _ of
  [ _1, _2, _3, _4 ] -> mk <$> fromSQLValue @a _1 <*> fromSQLValue @b _2 <*> fromSQLValue @c _3 <*> fromSQLValue @d _4
  x | len <- Array.length x -> Left $ "Expected exactly four results, got " <> show len

fiveResults :: forall @a @b @c @d @e f. SQLFromForeign a => SQLFromForeign b => SQLFromForeign c => SQLFromForeign d => SQLFromForeign e => (a -> b -> c -> d -> e -> f) -> Array SQLResult -> Either String f
fiveResults mk = case _ of
  [ _1, _2, _3, _4, _5 ] -> mk <$> fromSQLValue @a _1 <*> fromSQLValue @b _2 <*> fromSQLValue @c _3 <*> fromSQLValue @d _4 <*> fromSQLValue @e _5
  x | len <- Array.length x -> Left $ "Expected exactly five results, got " <> show len

class FromResultArray fn a | fn -> a where
  fromResultArray :: fn -> Array SQLResult -> Either String a

instance (SQLFromForeign a, SQLFromForeign b, SQLFromForeign c, SQLFromForeign d, SQLFromForeign e) => FromResultArray (a -> b -> c -> d -> e -> f) f where
  fromResultArray = fiveResults

else instance (SQLFromForeign a, SQLFromForeign b, SQLFromForeign c, SQLFromForeign d) => FromResultArray (a -> b -> c -> d -> e) e where
  fromResultArray = fourResults

else instance (SQLFromForeign a, SQLFromForeign b, SQLFromForeign c) => FromResultArray (a -> b -> c -> d) d where
  fromResultArray = threeResults

else instance (SQLFromForeign a, SQLFromForeign b) => FromResultArray (a -> b -> c) c where
  fromResultArray = twoResults

else instance SQLFromForeign a => FromResultArray (a -> b) b where
  fromResultArray = singleResult

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Heterogeneous Folding for Parameter Extraction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

data TurnIntoSQLParam = TurnIntoSQLParam

instance (ToSQLParam n) => Folding TurnIntoSQLParam (Array SQLParameter) n (Array SQLParameter) where
  folding TurnIntoSQLParam acc a = Array.snoc acc (toSQLParam a)

instance
  ( ToSQLParam n
  , IsSymbol sym
  ) =>
  FoldingWithIndex TurnIntoSQLParam (Proxy sym) (Map String SQLParameter) n (Map String SQLParameter) where
  foldingWithIndex TurnIntoSQLParam sym acc a = Map.insert (reflectSymbol sym) (toSQLParam a) acc

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SQL Query Builder with Type-Level Parameter Tracking
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

newtype SQLBuilder r1 r2 = SQLBuilder (SQLQuery r1 -> SQLQuery r2)

class ToBuilder s r1 r2 | r1 -> r2, r2 -> r1 where
  toBuilder :: s -> SQLBuilder r1 r2

instance ToBuilder (SQLBuilder r1 r2) r1 r2 where
  toBuilder = identity

else instance ToBuilder String r r where
  toBuilder = nonArg

-- | Compose two builders
combineBuilders :: forall a b r1 r2 r3. ToBuilder a r2 r3 => ToBuilder b r1 r2 => a -> b -> SQLBuilder r1 r3
combineBuilders a b = SQLBuilder (f <<< g)
  where
  SQLBuilder f = toBuilder a
  SQLBuilder g = toBuilder b

infixl 8 combineBuilders as ^

-- | Create a SQL query from a builder
sql :: forall r. SQLBuilder () r -> SQLQuery r
sql (SQLBuilder builder) = builder (SQLQuery [] "")

-- | Add a typed parameter to the query (PostgreSQL $N format)
arg :: forall @a @sym r1 r2. IsSymbol sym => ToSQLParam a => Row.Cons sym a r1 r2 => SQLBuilder r1 r2
arg = SQLBuilder \(SQLQuery oldKeys oldQuery) ->
  let
    paramNum = Array.length oldKeys + 1
  in
    SQLQuery (Array.cons (reflectSymbol (Proxy :: Proxy sym)) oldKeys) ("$" <> show paramNum <> oldQuery)

-- | Add an Int parameter
int :: forall @sym r1 r2. IsSymbol sym => Row.Cons sym Int r1 r2 => SQLBuilder r1 r2
int = arg @Int @sym

-- | Add a String parameter
str :: forall @sym r1 r2. IsSymbol sym => Row.Cons sym String r1 r2 => SQLBuilder r1 r2
str = arg @String @sym

-- | Add a Boolean parameter
bool :: forall @sym r1 r2. IsSymbol sym => Row.Cons sym Boolean r1 r2 => SQLBuilder r1 r2
bool = arg @Boolean @sym

-- | Add a Number parameter
num :: forall @sym r1 r2. IsSymbol sym => Row.Cons sym Number r1 r2 => SQLBuilder r1 r2
num = arg @Number @sym

-- | Add a literal SQL string (no parameter)
nonArg :: forall r. String -> SQLBuilder r r
nonArg newQuery = SQLBuilder \(SQLQuery keys oldQuery) -> SQLQuery keys (newQuery <> oldQuery)

-- | Extract parameters from a record in the correct order
argsFor :: forall @params. HFoldlWithIndex TurnIntoSQLParam (Map String SQLParameter) { | params } (Map String SQLParameter) => SQLQuery params -> { | params } -> Array SQLParameter
argsFor (SQLQuery args _) params = do
  let theMap = hfoldlWithIndex TurnIntoSQLParam (Map.empty :: Map String SQLParameter) params
  -- Reverse the args array since we build it with cons (prepend)
  Array.reverse args <#> \positionedArg -> (unsafePartial $ fromJust $ Map.lookup positionedArg theMap)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Table Schema Definition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

newtype DatabaseColumns row = DatabaseColumns row

data SQLiteBaseType
  = TextColumn
  | IntColumn
  | RealColumn
  | BooleanColumn
  | BlobColumn
  | JsonBColumn
  | IntegerColumn
  | NumericColumn
  | NullColumn

renderBaseType :: SQLiteBaseType -> String
renderBaseType = case _ of
  TextColumn -> "TEXT"
  IntColumn -> "INT"
  RealColumn -> "REAL"
  BooleanColumn -> "BOOLEAN"
  BlobColumn -> "BLOB"
  JsonBColumn -> "JSONB"
  IntegerColumn -> "INTEGER"
  NumericColumn -> "NUMERIC"
  NullColumn -> "NULL"

data Constraint
  = Unique
  | PrimaryKey
  | NotNull
  | ForeignKey String
  | Check String
  | Default SQLParameter

renderConstraint :: Constraint -> String
renderConstraint = case _ of
  Unique -> "UNIQUE"
  PrimaryKey -> "PRIMARY KEY"
  NotNull -> "NOT NULL"
  ForeignKey ref -> "FOREIGN KEY (" <> ref <> ")"
  Check condition -> "CHECK (" <> condition <> ")"
  Default value -> "DEFAULT " <> unsafeStringify value

data SQLColumn = SQLColumn SQLiteBaseType (Array Constraint)

newtype TableName = TableName String

derive instance Newtype TableName _

newtype ColumnName = ColumnName String

derive instance Newtype ColumnName _

-- | A table with typed columns
data Table columns = Table TableName { | columns }

-- Helper for type inference
data MapRecord a b = MapRecord (String -> a -> b)

instance
  ( IsSymbol sym
  , Row.Lacks sym rb
  , Row.Cons sym b rb rc
  ) =>
  FoldingWithIndex
    (MapRecord a b)
    (Proxy sym)
    (Builder { | ra } { | rb })
    a
    (Builder { | ra } { | rc }) where
  foldingWithIndex (MapRecord f) prop rin a = (rin >>> Builder.insert prop (f (reflectSymbol prop) a))

mapRecordWithIndex
  :: forall @a @b @rin @rout
   . HFoldlWithIndex (MapRecord a b) (Builder {} {}) { | rin } (Builder {} { | rout })
  => (String -> a -> b)
  -> { | rin }
  -> { | rout }
mapRecordWithIndex f =
  Builder.buildFromScratch
    <<< hfoldlWithIndex
      (MapRecord f :: MapRecord a b)
      (identity :: Builder {} {})

-- | Create a table schema
table :: forall @cols. Homogeneous cols SQLColumn => TableName -> { | cols } -> Table cols
table = Table

-- | Extract column names from table schema
columnNamesOf
  :: forall cols colsRL out
   . RowToList cols colsRL
  => HFoldlWithIndex (MapRecord SQLColumn ColumnName)
       (Builder {} {})
       { | cols }
       (Builder {} { | out })
  => Table cols
  -> { | out }
columnNamesOf (Table _ cols) = cols # mapRecordWithIndex \key (_ :: SQLColumn) -> ColumnName key

newtype CreateTableStatement = CreateTableStatement String

derive instance Newtype CreateTableStatement _

-- | Generate CREATE TABLE statement from schema
createTable :: forall cols. Homogeneous cols SQLColumn => Table cols -> CreateTableStatement
createTable (Table (TableName tableName) tab) = CreateTableStatement $ "CREATE TABLE " <> tableName <> " (" <> cols <> ")"
  where
  toConstraint :: String -> SQLColumn -> String
  toConstraint key (SQLColumn baseType constraints) =
    key <> " " <> renderBaseType baseType <> " " <> (constraints <#> renderConstraint # intercalate " ")
  cols = (Object.fromHomogeneous tab) # mapWithIndex toConstraint # intercalate ", "
