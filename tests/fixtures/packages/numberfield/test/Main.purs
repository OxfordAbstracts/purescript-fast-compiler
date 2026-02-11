module Test.Main where

import Prelude

import Data.Algebraic.NumberField 
  ( Expression
  , build
  , element
  , framework
  , minimalPolynomial
  , run
  , toPrimitive
  )
import Data.Ratio (Ratio, (%))
import Data.Reflectable (reifyType)
import Data.Sparse.Polynomial ((^), display)
import Effect (Effect)
import JS.BigInt (BigInt, fromInt)
import Test.Assert (assert')

bigOne :: Ratio BigInt
bigOne = fromInt 1 % fromInt 1

main :: Effect Unit
main = do
  let 
    fw1 = 
      framework 
        (bigOne ^ 0) 
        [one ^ 2 - one ^ 1 - one ^ 0] -- minimal polynomial of phi
    
    test1 = display ["phi"] $ run $ reifyType fw1
      ( build 
        (
          ( const $
            let phi = element (bigOne ^ 1)
                toFrac n = element ((fromInt n % fromInt 1) ^ 0)
            in (phi + toFrac 2) * recip ((phi - toFrac 2) * (phi - toFrac 2))
          ) :: forall f. Expression f _ 
        )
      )
  assert' "1-element extension" $ test1 == "(11 % 1)×phi+7 % 1"
  
  let 
    fw2 = 
      framework 
        (bigOne ^ 0 ^ 0)
        [ one ^ 3 - (fromInt 2 % fromInt 1) ^ 0 -- minimal polynomial for cubicRoot(2)
        , one ^ 2 - (fromInt 3 % fromInt 1) ^ 0 -- minimal polynomial for sqrt(3)
        ]

    test2 = 
      display ["cr2", "sr3"] $ run $ reifyType fw2 
        ( build
          (
            ( const $
              let cbrt2 = element (bigOne ^ 0 ^ 1)
                  sqrt3 = element (bigOne ^ 1 ^ 0)
              in (recip $ cbrt2 * cbrt2 + cbrt2 - sqrt3)
            ) :: forall f. Expression f _ 
          )
        )

  assert' "sum-of-2-elements primitive minimal polynomial"  $ 
    show (minimalPolynomial fw2) == 
      "(1 % 1)×z^6+(-9 % 1)×z^4+(-4 % 1)×z^3+(27 % 1)×z^2+(-36 % 1)×z+(-23 % 1)"
  
  assert' "element expressions as functions of primitive" $
    show (toPrimitive fw2) ==
      "[(-2 % 51)×z^5+(-1 % 102)×z^4+(20 % 51)×z^3+(13 % 51)×z^2+(-38 % 51)×z+91 % 102,"
      <> "(2 % 51)×z^5+(1 % 102)×z^4+(-20 % 51)×z^3+(-13 % 51)×z^2+(89 % 51)×z+(-91 % 102)]"

  assert' "2-element extension" $ 
    test2 == "((1 % 3)×sr3+(-1 % 3))×cr2^2+(1 % 3)×cr2+(-1 % 3)×sr3+2 % 3"

  let 
    fw3 = 
      framework 
        (bigOne ^ 0 ^ 0 ^ 0)
        [ one ^ 2 - (fromInt 7 % fromInt 1) ^ 0 -- minimal polynomial for sqrt(7)
        , one ^ 2 - (fromInt 3 % fromInt 1) ^ 0 -- minimal polynomial for sqrt(3)
        , one ^ 2 - (fromInt 2 % fromInt 1) ^ 0 -- minimal polynomial for sqrt(2)
        ]

    test3 = 
      display ["sr7", "sr3", "sr2"] $ run $ reifyType fw3
        ( build
          (
            ( const $
              let sr7 = element (bigOne ^ 0 ^ 0 ^ 1)
                  r7 = recip sr7
                  sr3 = element (bigOne ^ 0 ^ 1 ^ 0)
                  sr2 = element (bigOne ^ 1 ^ 0 ^ 0)
                  r2 = recip sr2
                  q = (sr2 + sr3 * r7) * recip (sr3 + sr7 * r2) + sr2 * sr3
              in q * q
            ) :: forall f. Expression f _ 
          )
        )
  assert' "3-element extension" $ test3 == "64 % 7" 
