module Data.Roman.Letters (LetterTriplet(..), fromLetters, toSymbols) where

import Prelude
import Data.Array (index, length, range)
import Data.Foldable (and)
import Data.Int (pow)
import Data.Map (fromFoldable)
import Data.Maybe (fromMaybe)
import Data.Roman.Symbols (SymbolsTable(..))
import Data.Tuple (Tuple(..))

infix 8 range as ..

data LetterTriplet
  = LetterTriplet String String String Int

instance eqLetterTriplet :: Eq LetterTriplet where
  eq (LetterTriplet o1 f1 t1 m1) (LetterTriplet o2 f2 t2 m2) =
    and
      [ eq o1 o2
      , eq f1 f2
      , eq t1 t2
      , eq m1 m2
      ]

instance showLetterTriplet :: Show LetterTriplet where
  show (LetterTriplet o f t m) =
    show
      $ fromFoldable
          [ Tuple "Units" o
          , Tuple "Fives" f
          , Tuple "Tens" t
          , Tuple "Magnitude" $ show m
          ]

fromLetters :: Array String -> Array LetterTriplet
fromLetters letters
  | length letters < 3 = []
  | otherwise = do
    i <- 0 .. ((length letters - 3) / 2)
    pure
      $ LetterTriplet
          (get letters (2 * i))
          (get letters (2 * i + 1))
          (get letters (2 * i + 2))
          (pow 10 i)
    where
    get arr x = fromMaybe "" $ index arr x

toSymbols :: LetterTriplet -> SymbolsTable
toSymbols (LetterTriplet o f t m) =
  SymbolsTable
    ( fromFoldable
        [ Tuple o (1 * m)
        , Tuple (o <> f) (4 * m)
        , Tuple f (5 * m)
        , Tuple (o <> t) (9 * m)
        , Tuple (t) (10 * m)
        ]
    )
