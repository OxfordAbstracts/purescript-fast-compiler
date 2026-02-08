module DTS.Types
  ( OSet(..)
  , PropModifiers
  , TsDeclVisibility(..)
  , TsDeclaration(..)
  , TsFilePath(..)
  , TsFnArg(..)
  , TsImportPath(..)
  , TsModule(..)
  , TsModuleFile(..)
  , TsModulePath(..)
  , TsName(..)
  , TsProgram(..)
  , TsQualName(..)
  , TsRecordField(..)
  , TsType(..)
  , TsTypeArgs(..)
  , TsTypeArgsQuant(..)
  , mapQuantifier
  , printTsName
  ) where

import Prelude

import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Set.Ordered as OSet

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- | Represents a subset of TypeScript type declarations
data TsDeclaration
  = TsDeclTypeDef TsName TsDeclVisibility (OSet TsName) TsType
  | TsDeclValueDef TsName TsDeclVisibility TsType
  | TsDeclComments (Array String)

data TsDeclVisibility = Public | Private

-- | Represents a subset of TypeScript types
data TsType
  = TsTypeNumber
  | TsTypeString
  | TsTypeBoolean
  | TsTypeNull
  | TsTypeArray TsType
  | TsTypeReadonlyArray TsType
  | TsTypeIntersection (Array TsType)
  | TsTypeUnion (Array TsType)
  | TsTypeTuple (Array TsType)
  | TsTypeReadonlyTuple (Array TsType)
  | TsTypeRecord (Array TsRecordField)
  | TsTypeFunction TsTypeArgsQuant (Array TsFnArg) TsType
  | TsTypeConstructor TsQualName TsTypeArgs
  | TsTypeUniqueSymbol
  | TsTypeVar TsName
  | TsTypeTypelevelString String
  | TsTypeTypelevelNumber Number
  | TsTypeVoid

data TsModule = TsModule (Array TsDeclaration)

data TsModuleFile = TsModuleFile TsFilePath TsModule

-- | A collection of TypeScript modules
data TsProgram = TsProgram (Map TsFilePath TsModule)

data TsName = TsName String

data TsModulePath = TsModulePath String

data TsFilePath = TsFilePath String

data TsImportPath = TsImportPath String

data TsQualName = TsQualName (Maybe TsImportPath) TsName

newtype TsTypeArgsQuant = TsTypeArgsQuant (OSet TsName)

newtype TsTypeArgs = TsTypeArgs (Array TsType)

data TsFnArg = TsFnArg TsName TsType

data TsRecordField = TsRecordField String PropModifiers TsType

type PropModifiers =
  { readonly :: Boolean
  , optional :: Boolean
  }

newtype OSet a = OSet (OSet.OSet a)

newtype Statements a = Statements a

-------------------------------------------------------------------------------
-- TsName
-------------------------------------------------------------------------------

printTsName :: TsName -> String
printTsName (TsName n) = n

-------------------------------------------------------------------------------
-- TsType
-------------------------------------------------------------------------------

mapQuantifier :: (OSet TsName -> OSet TsName) -> TsType -> TsType
mapQuantifier f = case _ of
  TsTypeNumber -> TsTypeNumber
  TsTypeString -> TsTypeString
  TsTypeBoolean -> TsTypeBoolean
  TsTypeNull -> TsTypeNull
  TsTypeArray x -> TsTypeArray $ mapQuantifier f x
  TsTypeReadonlyArray x -> TsTypeReadonlyArray $ mapQuantifier f x
  TsTypeIntersection xs -> TsTypeIntersection
    (mapQuantifier f <$> xs)
  TsTypeUnion xs -> TsTypeUnion
    (mapQuantifier f <$> xs)
  TsTypeReadonlyTuple xs -> TsTypeReadonlyTuple
    (mapQuantifier f <$> xs)
  TsTypeTuple xs -> TsTypeTuple
    (mapQuantifier f <$> xs)
  TsTypeRecord x -> TsTypeRecord $ goTsRecordField <$> x
  TsTypeFunction x y z -> TsTypeFunction
    (goTsTypeArgsQuant x)
    (goTsFnArg <$> y)
    (mapQuantifier f z)
  TsTypeConstructor x y -> TsTypeConstructor
    (goTsQualName x)
    (goTsTypeArgs y)
  TsTypeUniqueSymbol -> TsTypeUniqueSymbol
  TsTypeVar x -> TsTypeVar $ goTsName x
  TsTypeVoid -> TsTypeVoid
  TsTypeTypelevelString x -> TsTypeTypelevelString x
  TsTypeTypelevelNumber x -> TsTypeTypelevelNumber x

  where
  goTsRecordField (TsRecordField x y z) = TsRecordField
    (goTsName x)
    (goPropModifiers y)
    (mapQuantifier f z)

  goTsTypeArgsQuant (TsTypeArgsQuant oset) = TsTypeArgsQuant $ f oset

  goTsTypeArgs (TsTypeArgs x) = TsTypeArgs $ mapQuantifier f <$> x

  goTsFnArg (TsFnArg x y) = TsFnArg (goTsName x) (mapQuantifier f y)

  goTsQualName = identity

  goTsName = identity

  goPropModifiers = identity

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

derive newtype instance Eq a => Semigroup (OSet a)

derive instance Eq TsRecordField
derive instance Eq TsFnArg
derive instance Eq TsTypeArgs
derive instance Eq TsQualName
derive instance Eq TsTypeArgsQuant
derive instance Eq TsImportPath
derive instance Eq TsDeclaration
derive instance Eq TsType
derive instance Eq TsName
derive instance Eq TsModulePath
derive instance Eq TsFilePath
derive instance Eq TsDeclVisibility

derive instance Ord TsFnArg
derive instance Ord TsRecordField
derive instance Ord TsTypeArgs
derive instance Ord TsQualName
derive instance Ord TsImportPath
derive instance Ord TsTypeArgsQuant
derive instance Ord TsDeclaration
derive instance Ord TsType
derive instance Ord TsName
derive instance Ord TsModulePath
derive instance Ord TsFilePath
derive instance Ord TsDeclVisibility

derive instance Newtype (OSet a) _

instance Show TsName where
  show (TsName name) = show name

instance Ord a => Ord (OSet a) where
  compare (OSet o1) (OSet o2) = toArray o1 `compare` toArray o2
    where
    toArray = OSet.toUnfoldable :: _ -> Array _

instance Eq a => Eq (OSet a) where
  eq (OSet o1) (OSet o2) = toArray o1 `eq` toArray o2
    where
    toArray = OSet.toUnfoldable :: _ -> Array _

instance Eq a => Monoid (OSet a) where
  mempty = OSet $ OSet.empty

