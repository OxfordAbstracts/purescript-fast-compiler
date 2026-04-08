module Simple where

import Prelude (add, ($))
import Simple.Lib (class Classy, classMember, LibType(LibCon1, LibCon2), LibAlias, libValue)
import Simple.Lib as SL

-- Data types
data MyData = MyConA | MyConB Int

-- Type alias
type MyAlias = Int

-- Values
myValue :: Int
myValue = 42

myOther :: Int -> Int
myOther n = n + 1

-- Constructors used in expression
useCon = MyConA

-- Type operator
infix 3 add as +++

-- Class
class MyClass a where
  myMethod :: a -> String

-- Usage sites for completion

-- Complete a data type name in a type signature (prefix "My")
typeSigData :: MyD
typeSigData = MyConA

-- Complete a type alias in a type signature (prefix "My")
typeSigAlias :: MyA
typeSigAlias = 42

-- Complete a value (prefix "myV")
useVal = myV

-- Complete a constructor (prefix "MyC")
useCtor = MyC

-- Complete a value operator (prefix "++")
useOp = 1 ++ 2

-- Complete a class name in a constraint (prefix "MyC")
classSig :: MyC a => a -> String
classSig = myMethod

-- Complete a class member (prefix "myM")
useMember = myM

-- Complete an imported data type (prefix "Lib")
importedType :: LibT
importedType = LibCon1

-- Complete an imported type alias (prefix "Lib")
importedAlias :: LibA
importedAlias = 42

-- Complete an imported value (prefix "lib")
useImportedVal = libV

-- Complete an imported constructor (prefix "LibC")
useImportedCtor = LibC

-- Complete an imported class (prefix "Cla")
importedClassSig :: Cla a => a -> a
importedClassSig = classMember

-- Complete an imported class member (prefix "class")
useImportedMember = classM

-- Complete a qualified value (prefix "SL.lib")
useQualified = SL.lib

-- Format: line:col (name) => contains: label1, label2
-- Lines are 0-indexed. Col is cursor position (after the prefix).
--
-- Line 32: typeSigData :: MyD
-- 32:18 (data type prefix MyD) => contains: MyData
--
-- Line 36: typeSigAlias :: MyA
-- 36:19 (type alias prefix MyA) => contains: MyAlias
--
-- Line 40: useVal = myV
-- 40:12 (value prefix myV) => contains: myValue
--
-- Line 43: useCtor = MyC
-- 43:13 (constructor prefix MyC) => contains: MyConA, MyConB
--
-- Line 46: useOp = 1 ++ 2
-- 46:12 (operator prefix ++) => contains: +++
--
-- Line 49: classSig :: MyC a => a -> String
-- 49:15 (class prefix MyC) => contains: MyClass
--
-- Line 53: useMember = myM
-- 53:15 (class member prefix myM) => contains: myMethod
--
-- Line 56: importedType :: LibT
-- 56:20 (imported data type prefix LibT) => contains: LibType
--
-- Line 60: importedAlias :: LibA
-- 60:21 (imported alias prefix LibA) => contains: LibAlias
--
-- Line 64: useImportedVal = libV
-- 64:21 (imported value prefix libV) => contains: libValue
--
-- Line 67: useImportedCtor = LibC
-- 67:22 (imported ctor prefix LibC) => contains: LibCon1, LibCon2
--
-- Line 70: importedClassSig :: Cla a => a -> a
-- 70:23 (imported class prefix Cla) => contains: Classy
--
-- Line 74: useImportedMember = classM
-- 74:26 (imported member prefix classM) => contains: classMember
--
-- Qualified completion tested by inline test: test_lsp_completion_qualified_values
