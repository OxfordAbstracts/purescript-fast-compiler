module Test.Pipes.CBOR where

import Prelude

import Control.Monad.Gen (chooseInt)
import Data.DateTime (DateTime)
import Data.List ((:))
import Data.List as List
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (wrap)
import Data.PreciseDateTime (fromRFC3339String, toDateTimeLossy)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.CBOR as CBOR
import Effect.Class (liftEffect)
import Node.Buffer (Buffer)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Partial.Unsafe (unsafePartial)
import Pipes (yield, (>->))
import Pipes.Async (debug, (>-/->))
import Pipes.CBOR as Pipes.CBOR
import Pipes.Collect as Pipes.Collect
import Pipes.Node.Stream as Pipes.Stream
import Pipes.Prelude (toListM) as Pipes
import Test.QuickCheck.Gen (randomSample')
import Test.Spec (Spec, before, describe, it)
import Test.Spec.Assertions (shouldEqual)

cborHex :: String
cborHex = "82b90002646e616d656568656e72796174c1fb41d990ee6d671aa0b90002646e616d65656a756c696f6174c1fbc1d756dad0bbb646"

cborBuf :: Effect Buffer
cborBuf = Buffer.fromString cborHex Hex

exp :: Array {name :: String, t :: DateTime}
exp =
  [{name: "henry", t: toDateTimeLossy $ unsafePartial fromJust $ fromRFC3339String $ wrap "2024-05-14T19:21:25.611Z"}
  ,{name: "julio", t: toDateTimeLossy $ unsafePartial fromJust $ fromRFC3339String $ wrap "1920-05-14T20:21:17.067Z"}
  ]


dt :: String -> DateTime
dt = toDateTimeLossy <<< unsafePartial fromJust <<< fromRFC3339String <<< wrap

spec :: Spec Unit
spec =
  describe "Pipes.CBOR" do
    it "encode" do
      bytes
        <- Pipes.Collect.toBuffer
          $ Pipes.Stream.withEOS (yield exp)
             >-/-> Pipes.CBOR.encode
             >-> Pipes.Stream.unEOS
      act <- liftEffect $ CBOR.decode bytes
      act `shouldEqual` exp

    describe "parse" do
      it "parses csv" do
        buf <- liftEffect $ cborBuf
        rows <- Pipes.toListM
          $ (yield (Just buf) *> yield Nothing)
              >-/-> debug "cbor" Pipes.CBOR.decode

        rows `shouldEqual` ((Just exp) : Nothing : List.Nil)
      before
        (do
          nums <- liftEffect $ randomSample' 100000 (chooseInt 0 9)
          let
            objs = (\n -> {id: n}) <$> nums
          bytes <-
            Pipes.Collect.toBuffer
            $ Pipes.Stream.withEOS (yield objs)
              >-/-> Pipes.CBOR.encode
              >-> Pipes.Stream.unEOS
          pure $ nums /\ bytes
        )
        $ it "parses large csv" \(nums /\ bytes) -> do
          rows <-
            Pipes.Collect.toArray
              $ Pipes.Stream.withEOS (yield bytes)
                  >-/-> Pipes.CBOR.decode @(Array {id :: Int})
                  >-> Pipes.Stream.unEOS

          rows `shouldEqual` [(\id -> { id }) <$> nums]
