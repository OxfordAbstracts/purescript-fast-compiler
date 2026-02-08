module Text.Printf where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Prim.Symbol as Symbol
import Type.Proxy (Proxy(..))

class Printf (template :: Symbol) fn | template -> fn where
  printf :: Proxy template -> fn

instance (Parse "traverse" "" template "" spec, Format spec fn) => Printf template fn where
  printf _ = format (SProxy :: SProxy spec) ""

class Format (spec :: SList) fn | spec -> fn where
  format :: SProxy spec -> String -> fn

instance Format SNil String where
  format _ = identity

else instance (IsSymbol common, Format rest fn) => Format (SCons (Common common) rest) fn where
  format _ str = format (SProxy :: SProxy rest) (str <> reflectSymbol (Proxy :: Proxy common))

else instance (IsSymbol controls, Format rest fn) => Format (SCons (D controls) rest) (Int -> fn) where
  format _ str = \i -> format
    (SProxy :: SProxy rest)
    (str <> formatInt (reflectSymbol (Proxy :: Proxy controls)) i)

else instance (IsSymbol controls, Format rest fn) => Format (SCons (F controls) rest) (Number -> fn) where
  format _ str = \n -> format
    (SProxy :: SProxy rest)
    (str <> formatFloat (reflectSymbol (Proxy :: Proxy controls)) n)

else instance (IsSymbol controls, Format rest fn) => Format (SCons (S controls) rest) (String -> fn) where
  format _ str = \s -> format
    (SProxy :: SProxy rest)
    (str <> formatString (reflectSymbol (Proxy :: Proxy controls)) s)

class Parse (mode :: Symbol) (head :: Symbol) (tail :: Symbol) (acc :: Symbol) (spec :: SList) | mode head tail acc -> spec

instance (Symbol.Cons head' tail' tail, Parse "spec" head' tail' "" spec) => Parse "traverse" "%" tail acc (SCons (Common acc) spec)

else instance (Symbol.Append acc head acc') => Parse "traverse" head "" acc (SCons (Common acc') SNil)

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc head acc', Parse "traverse" head' tail' acc' spec) => Parse "traverse" head tail acc spec

else instance Parse "spec" "%" "" "" (SCons (Common "%") SNil)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec" "%" tail "" (SCons (Common "%") spec)

else instance (Symbol.Cons head' tail' tail, Parse "spec1" head' tail' "+" spec) => Parse "spec" "+" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec2" head' tail' "-" spec) => Parse "spec" "-" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec2'" head' tail' "'" spec) => Parse "spec" "'" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "0" spec) => Parse "spec" "0" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "1" spec) => Parse "spec" "1" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "2" spec) => Parse "spec" "2" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "3" spec) => Parse "spec" "3" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "4" spec) => Parse "spec" "4" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "5" spec) => Parse "spec" "5" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "6" spec) => Parse "spec" "6" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "7" spec) => Parse "spec" "7" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "8" spec) => Parse "spec" "8" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec3" head' tail' "9" spec) => Parse "spec" "9" tail "" spec

else instance (Symbol.Cons head' tail' tail, Parse "spec4" head' tail' "." spec) => Parse "spec" "." tail "" spec

else instance Parse "spec" "d" "" "" (SCons (D "") SNil)

else instance Parse "spec" "f" "" "" (SCons (F "") SNil)

else instance Parse "spec" "s" "" "" (SCons (S "") SNil)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec" "d" tail "" (SCons (D "") spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec" "f" tail "" (SCons (F "") spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec" "s" tail "" (SCons (S "") spec)

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "-" acc', Parse "spec2" head' tail' acc' spec) => Parse "spec1" "-" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "'" acc', Parse "spec2'" head' tail' acc' spec) => Parse "spec1" "'" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "0" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "0" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "1" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "1" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "2" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "2" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "3" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "3" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "4" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "4" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "5" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "5" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "6" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "6" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "7" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "7" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "8" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "8" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "9" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec1" "9" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "." acc', Parse "spec4" head' tail' acc' spec) => Parse "spec1" "." tail acc spec

else instance Parse "spec1" "d" "" acc (SCons (D acc) SNil)

else instance Parse "spec1" "f" "" acc (SCons (F acc) SNil)

else instance Parse "spec1" "s" "" acc (SCons (S acc) SNil)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec1" "d" tail acc (SCons (D acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec1" "f" tail acc (SCons (F acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec1" "s" tail acc (SCons (S acc) spec)

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "'" acc', Parse "spec2'" head' tail' acc' spec) => Parse "spec2" "'" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "0" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "0" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "1" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "1" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "2" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "2" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "3" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "3" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "4" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "4" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "5" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "5" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "6" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "6" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "7" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "7" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "8" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "8" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "9" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2" "9" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "." acc', Parse "spec4" head' tail' acc' spec) => Parse "spec2" "." tail acc spec

else instance Parse "spec2" "d" "" acc (SCons (D acc) SNil)

else instance Parse "spec2" "f" "" acc (SCons (F acc) SNil)

else instance Parse "spec2" "s" "" acc (SCons (S acc) SNil)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec2" "d" tail acc (SCons (D acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec2" "f" tail acc (SCons (F acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec2" "s" tail acc (SCons (S acc) spec)

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc any acc', Parse "spec3" head' tail' acc' spec) => Parse "spec2'" any tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "0" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "0" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "1" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "1" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "2" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "2" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "3" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "3" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "4" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "4" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "5" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "5" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "6" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "6" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "7" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "7" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "8" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "8" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "9" acc', Parse "spec3" head' tail' acc' spec) => Parse "spec3" "9" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "." acc', Parse "spec4" head' tail' acc' spec) => Parse "spec3" "." tail acc spec

else instance Parse "spec3" "d" "" acc (SCons (D acc) SNil)

else instance Parse "spec3" "f" "" acc (SCons (F acc) SNil)

else instance Parse "spec3" "s" "" acc (SCons (S acc) SNil)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec3" "d" tail acc (SCons (D acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec3" "f" tail acc (SCons (F acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec3" "s" tail acc (SCons (S acc) spec)

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "0" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "0" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "1" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "1" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "2" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "2" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "3" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "3" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "4" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "4" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "5" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "5" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "6" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "6" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "7" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "7" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "8" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "8" tail acc spec

else instance (Symbol.Cons head' tail' tail, Symbol.Append acc "9" acc', Parse "spec4" head' tail' acc' spec) => Parse "spec4" "9" tail acc spec

else instance Parse "spec4" "d" "" acc (SCons (D acc) SNil)

else instance Parse "spec4" "f" "" acc (SCons (F acc) SNil)

else instance Parse "spec4" "s" "" acc (SCons (S acc) SNil)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec4" "d" tail acc (SCons (D acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec4" "f" tail acc (SCons (F acc) spec)

else instance (Symbol.Cons head' tail' tail, Parse "traverse" head' tail' "" spec) => Parse "spec4" "s" tail acc (SCons (S acc) spec)

data Specifier

foreign import data Common :: Symbol -> Specifier
foreign import data D :: Symbol -> Specifier
foreign import data F :: Symbol -> Specifier
foreign import data S :: Symbol -> Specifier

data SList

data SProxy (s :: SList) = SProxy

foreign import data SNil :: SList
foreign import data SCons :: Specifier -> SList -> SList

foreign import formatInt :: String -> Int -> String

foreign import formatFloat :: String -> Number -> String

foreign import formatString :: String -> String -> String
