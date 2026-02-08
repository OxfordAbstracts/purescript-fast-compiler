module Data.Complex.FFT where

import Prelude

import Control.Monad.ST (ST, run, for)
import Data.Array (reverse, mapWithIndex, length, sortBy, (..), replicate, zipWith)
import Data.Array ((!!)) as Array
import Data.Array.ST (STArray, peek, poke, withArray)
import Data.Complex (Cartesian(..), conjugate)
import Data.Foldable (foldr)
import Data.Traversable (sequence)
import Data.Int (toStringAs, binary, fromStringAs, toNumber, round)
import Data.Int.Bits (shl)
import Data.Maybe (fromJust)
import Data.String (length) as String
import Data.String (toCodePointArray, singleton)
import Data.Number (sqrt, cos, atan2, pi, log)
import Partial.Unsafe (unsafePartial)

nth :: forall a. Array a -> Int -> a
nth xs i =  unsafePartial fromJust $ xs Array.!! i

infixl 6 nth as !!

type Complex = Cartesian Number

type Index = Int
type PowerOfTwo = Int
type ExponentOfTwo = Int

initialSort :: ExponentOfTwo -> Index -> Index
initialSort e2 i =
  let s2' = toStringAs binary i
      s2 =  foldr (<>) "" (replicate (e2 - String.length s2') "0") <> s2'
      c2 = singleton <$> (reverse $ toCodePointArray s2)
  in unsafePartial $ fromJust $ fromStringAs binary $ foldr (<>) "" c2

data Direction = Forward | Backward

trigTable :: forall h. PowerOfTwo -> STArray h Complex -> ST h Unit
trigTable n a =
  let csn = cos (pi / toNumber n)
      sn = sqrt (1.0 - csn * csn)
  in for 1 n \i -> do
        Cartesian x y <- unsafePeek (i-1) a
        poke i (Cartesian (x * csn - y * sn)
                          (y * csn + x * sn)) a

unsafePeek :: forall a. Int -> STArray a Complex -> ST a Complex
unsafePeek idx arr = do
  mz <- peek idx arr
  pure $ unsafePartial $ fromJust mz

process :: forall h. Direction -> ExponentOfTwo
                     -> Array Complex -> STArray h Complex -> ST h Unit
process dir b complexp a =
  for 0 b \ i -> do
    let count = shl 1 (b-i-1)
        step = shl 1 i
    for 0 count \j -> do
          for 0 step \k -> do
                  let idx = 2 * j * step + k
                  f0 <- unsafePeek idx a
                  fk <- unsafePeek (idx + step) a
                  let cexp = complexp !! (count * k)
                  let f1 = fk * (case dir of
                                    Forward -> conjugate cexp
                                    Backward -> cexp)
                  _ <- poke idx (f0+f1) a
                  poke (idx+step) (f0-f1) a

-- | U_i = fft Forward ((u_n))
-- | sr : sample rate
-- | Te : sampling period                               => Te = 1 / sr
-- | N : number of sample
-- | fe : frequency precision                           => fe = sr / (N - 1)
-- | T : signal duration
-- | u_n : sample at time t = n Te
-- | u_{N-1} : last sample at time t = T                => T = (N-1) Te = 1 / fe
-- | U_i : bin at frequency f = i fe                    => i  < (n-1) / 2
-- | U_{N/2-1} : last useful bin at frequency f = sr/2
fft :: Direction -> Array Complex -> Array Complex
fft dir zs =
  let n = toNumber $ length zs
      b = round $ log n / log 2.0
      n2 = (shl 1 b) `div` 2
      fs = (\i -> zs !! initialSort b i) <$> (0 .. (length zs-1))
      complexp = run (withArray (trigTable n2) (replicate n2 one))
   in (\z -> (_ / sqrt n) <$> z) <$> run (withArray (process dir b complexp) fs)

newtype ZipList a = ZipList (Array a)

derive newtype instance functorZipList :: Functor ZipList

instance applyZipList :: Apply ZipList where
  apply (ZipList fs) (ZipList xs) = ZipList (zipWith ($) fs xs)

instance applicativeZipList :: Applicative ZipList where
   pure = ZipList <<<  const []

transpose :: forall a. Array (Array a) -> Array (Array a)
transpose xs =
  let ZipList ys = sequence $ ZipList <$> xs
  in ys

fft2 :: Direction -> Array (Array Complex) -> Array (Array Complex)
fft2 dir zss = transpose $ fft dir <$> (transpose $ fft dir <$> zss)

type Freq = Int
type Bin = { re :: Number
           , im :: Number
           , freq :: Freq
           , mag :: Number
           , phase :: Number
           }

bin :: Freq -> Complex -> Bin
bin k (Cartesian re im) =
  { re
  , im
  , freq: k
  , mag: sqrt $ re * re + im * im
  , phase: atan2 im re
  }

sortByMagnitude :: Array Complex -> Array Bin
sortByMagnitude zs = sortBy (\a b -> compare b.mag a.mag) $
    (\{index, value} -> bin index value) <$> (
        mapWithIndex (\index value -> {index, value}) zs)
