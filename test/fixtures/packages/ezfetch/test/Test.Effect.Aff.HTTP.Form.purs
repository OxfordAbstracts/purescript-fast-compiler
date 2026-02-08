module Test.Effect.Aff.HTTP.Form where

import Prelude

import Data.MIME as MIME
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff.HTTP.Form (Form(..), RawFormData)
import Effect.Aff.HTTP.Form as Form
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

foreign import dummyForm :: Effect RawFormData

spec :: Spec Unit
spec = describe "Form" do
  it "fromRaw" do
    dummy <- liftEffect dummyForm
    f <- Form.fromRaw dummy
    buf <- Buffer.fromString "hello, world!" UTF8 >>= Buffer.toArrayBuffer # liftEffect
    f `shouldEqual` Form (Map.fromFoldable [ "foo" /\ [ Form.ValueString "bar" ], "baz" /\ [ Form.ValueFile (Form.Filename "foo.txt") buf MIME.Txt ] ])
  it "toRaw" do
    expect <- liftEffect dummyForm >>= Form.fromRaw
    buf <- Buffer.fromString "hello, world!" UTF8 >>= Buffer.toArrayBuffer # liftEffect
    let
      f = Form (Map.fromFoldable [ "foo" /\ [ Form.ValueString "bar" ], "baz" /\ [ Form.ValueFile (Form.Filename "foo.txt") buf MIME.Txt ] ])
    actual <- Form.toRawFormData f >>= Form.fromRaw
    expect `shouldEqual` actual
