module Motsunabe where

import Prelude

import Data.Lazy (Lazy)
import Data.Lazy as Lazy
import Data.List (List(..), (:))
import Data.String as String
import Data.Tuple (Tuple(..))
import Unsafe.Coerce (unsafeCoerce)

-- | "a prettier printer" by wadler
-- originally implemented in format-nix (https://github.com/justinwoo/format-nix)
data Doc
  = DNil
  | DAppend Doc Doc
  | DNest Int Doc
  | DText String
  | DLine
  | DAlt Doc Doc

instance sgDoc :: Semigroup Doc where
  append = DAppend

instance mDoc :: Monoid Doc where
  mempty = DNil

data Print
  = PNil
  | PText String Print
  | PLine Int Print

group :: Doc -> Doc
group x = DAlt (flatten x) x

flatten :: Doc -> Doc
flatten DNil = DNil
flatten (DAppend x y) = DAppend (flatten x) (flatten y)
flatten (DNest i x) = DNest i (flatten x)
flatten (DText s) = DText s
flatten DLine = DText " "
flatten (DAlt x y) = flatten x

layout :: Print -> String
layout PNil = ""
layout (PText str x) = str <> layout x
layout (PLine i x) = "\n" <> indent i <> layout x

indent :: Int -> String
indent 0 = ""
indent 1 = "  "
indent n = "  " <> indent (n - 1)

best :: Int -> Int -> Doc -> Print
best w k x = be w k (pure (Tuple 0 x))

be :: Int -> Int -> List (Tuple Int Doc) -> Print
be w k Nil = PNil
be w k (Tuple i DNil : z) = be w k z
be w k (Tuple i (DAppend x y) : z) = be w k (Tuple i x : Tuple i y : z)
be w k (Tuple i (DNest j x) : z) = be w k ((Tuple (i + j) x) : z)
be w k (Tuple i (DText s) : z) = PText s (be w (k + String.length s) z)
be w k (Tuple i DLine : z) = PLine i (be w i z)
be w k (Tuple i (DAlt x y) : z) = better w k
  (Lazy.defer $ \_ -> be w k ((Tuple i x) : z))
  (Lazy.defer $ \_ -> be w k ((Tuple i y) : z))

better :: Int -> Int -> Lazy Print -> Lazy Print -> Print
better w k x' y' = do
  let x = Lazy.force x'
  if fits (w - k) x
    then x
    else Lazy.force y'

fits :: Int -> Print -> Boolean
fits w x | w < 0 = false
fits w PNil = true
fits w (PText s x) = fits (w - String.length s) x
fits w (PLine i x) = true

pretty :: Int -> Doc -> String
pretty w x = postProcess $ layout (best w 0 x) <> "\n"

prettyWithoutTrailing :: Int -> Doc -> String
prettyWithoutTrailing w x = postProcess $ layout (best w 0 x)

postProcess :: String -> String
postProcess s
  = String.joinWith "\n"
  $ map trimRight
  $ String.split (String.Pattern "\n") s

trimRight :: String -> String
trimRight s = s'.trimRight unit
  where s' = unsafeCoerce s :: { trimRight :: Unit -> String }
