module Test.Main where

import Prelude

import Data.Either (Either(..))
import Data.Enum (toEnum)
import Data.Foldable (for_)
import Data.Maybe (fromJust)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Web.Punycode (Error(..), decode, encode, toAscii, toUnicode)
import Partial.Unsafe (unsafePartial)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck ((===))

-- Test cases adapted from https://github.com/mathiasbynens/punycode.js/blob/main/tests/tests.js

type TestCase = { description :: String, decoded :: String, encoded :: String }

testData :: Array TestCase
testData =
  [
    -- Strings
    { description: "a single basic code point"
    , decoded: "Bach"
    , encoded: "Bach-"
    }
  , { description: "a single non-ASCII character"
    , decoded: "\xFC"
    , encoded: "tda"
    }
  , { description: "multiple non-ASCII characters"
    , decoded: "\xFC\xEB\xE4\xF6\x2665"
    , encoded: "4can8av2009b"
    }
  , { description: "mix of ASCII and non-ASCII characters"
    , decoded: "b\xFC" <> "cher"
    , encoded: "bcher-kva"
    }
  , { description: "long string with both ASCII and non-ASCII characters"
    , decoded: "Willst du die Bl\xFCthe des fr\xFChen, die Fr\xFC" <> "chte des sp\xE4teren Jahres"
    , encoded: "Willst du die Blthe des frhen, die Frchte des spteren Jahres-x9e96lkal"
    }
  ,
    -- https://tools.ietf.org/html/rfc3492#section-7.1
    { description: "Arabic (Egyptian)"
    , decoded: "\x0644\x064A\x0647\x0645\x0627\x0628\x062A\x0643\x0644\x0645\x0648\x0634\x0639\x0631\x0628\x064A\x061F"
    , encoded: "egbpdaj6bu4bxfgehfvwxn"
    }
  , { description: "Chinese (simplified)"
    , decoded: "\x4ED6\x4EEC\x4E3A\x4EC0\x4E48\x4E0D\x8BF4\x4E2d\x6587"
    , encoded: "ihqwcrb4cv8a8dqg056pqjye"
    }
  , { description: "Chinese (traditional)"
    , decoded: "\x4ED6\x5011\x7232\x4EC0\x9EBD\x4E0D\x8AAA\x4E2D\x6587"
    , encoded: "ihqwctvzc91f659drss3x8bo0yb"
    }
  , { description: "Czech"
    , decoded: "Pro\x010Dprost\x011Bnemluv\xED\x010D" <> "esky"
    , encoded: "Proprostnemluvesky-uyb24dma41a"
    }
  , { description: "Hebrew"
    , decoded: "\x05DC\x05DE\x05D4\x05D4\x05DD\x05E4\x05E9\x05D5\x05D8\x05DC\x05D0\x05DE\x05D3\x05D1\x05E8\x05D9\x05DD\x05E2\x05D1\x05E8\x05D9\x05EA"
    , encoded: "4dbcagdahymbxekheh6e0a7fei0b"
    }
  , { description: "Hindi (Devanagari)"
    , decoded: "\x092F\x0939\x0932\x094B\x0917\x0939\x093F\x0928\x094D\x0926\x0940\x0915\x094D\x092F\x094B\x0902\x0928\x0939\x0940\x0902\x092C\x094B\x0932\x0938\x0915\x0924\x0947\x0939\x0948\x0902"
    , encoded: "i1baa7eci9glrd9b2ae1bj0hfcgg6iyaf8o0a1dig0cd"
    }
  , { description: "Japanese (kanji and hiragana)"
    , decoded: "\x306A\x305C\x307F\x3093\x306A\x65E5\x672C\x8A9E\x3092\x8A71\x3057\x3066\x304F\x308C\x306A\x3044\x306E\x304B"
    , encoded: "n8jok5ay5dzabd5bym9f0cm5685rrjetr6pdxa"
    }
  , { description: "Korean (Hangul syllables)"
    , decoded: "\xC138\xACC4\xC758\xBAA8\xB4E0\xC0AC\xB78C\xB4E4\xC774\xD55C\xAD6D\xC5B4\xB97C\xC774\xD574\xD55C\xB2E4\xBA74\xC5BC\xB9C8\xB098\xC88B\xC744\xAE4C"
    , encoded: "989aomsvi5e83db1d2a355cv1e0vak1dwrv93d5xbh15a0dt30a5jpsd879ccm6fea98c"
    }
  , {-
  - As there's no way to do it in JavaScript, Punycode.js doesn't support
  - mixed-case annotation (which is entirely optional as per the RFC).
  - So, while the RFC sample string encodes to:
  - `b1abfaaepdrnnbgefbaDotcwatmq2g4l`
  - Without mixed-case annotation it has to encode to:
  - `b1abfaaepdrnnbgefbadotcwatmq2g4l`
  - https://github.com/mathiasbynens/punycode.js/issues/3
  -} { description: "Russian (Cyrillic)"
    , decoded: "\x043F\x043E\x0447\x0435\x043C\x0443\x0436\x0435\x043E\x043D\x0438\x043D\x0435\x0433\x043E\x0432\x043E\x0440\x044F\x0442\x043F\x043E\x0440\x0443\x0441\x0441\x043A\x0438"
    , encoded: "b1abfaaepdrnnbgefbadotcwatmq2g4l"
    }
  , { description: "Spanish"
    , decoded: "Porqu\xE9nopuedensimplementehablarenEspa\xF1ol"
    , encoded: "PorqunopuedensimplementehablarenEspaol-fmd56a"
    }
  , { description: "Vietnamese"
    , decoded: "T\x1EA1isaoh\x1ECDkh\xF4ngth\x1EC3" <> "ch\x1EC9n\xF3iti\x1EBFngVi\x1EC7t"
    , encoded: "TisaohkhngthchnitingVit-kjcr8268qyxafd2f1b9g"
    }
  , { description: ""
    , decoded: "3\x5E74" <> "B\x7D44\x91D1\x516B\x5148\x751F"
    , encoded: "3B-ww4c5e180e575a65lsy2b"
    }
  , { description: ""
    , decoded: "\x5B89\x5BA4\x5948\x7F8E\x6075-with-SUPER-MONKEYS"
    , encoded: "-with-SUPER-MONKEYS-pc58ag80a8qai00g7n9n"
    }
  , { description: ""
    , decoded: "Hello-Another-Way-\x305D\x308C\x305E\x308C\x306E\x5834\x6240"
    , encoded: "Hello-Another-Way--fc4qua05auwb3674vfr0b"
    }
  , { description: ""
    , decoded: "\x3072\x3068\x3064\x5C4B\x6839\x306E\x4E0B" <> "2"
    , encoded: "2-u9tlzr9756bt3uc0v"
    }
  , { description: ""
    , decoded: "Maji\x3067Koi\x3059\x308B" <> "5\x79D2\x524D"
    , encoded: "MajiKoi5-783gue6qz075azm5e"
    }
  , { description: ""
    , decoded: "\x30D1\x30D5\x30A3\x30FC" <> "de" <> "\x30EB\x30F3\x30D0"
    , encoded: "de-jg4avhby1noc0d"
    }
  , { description: ""
    , decoded: "\x305D\x306E\x30B9\x30D4\x30FC\x30C9\x3067"
    , encoded: "d9juau41awczczp"
    }
  , {-
  - This example is an ASCII string that breaks the existing rules for host
  - name labels. (It's not a realistic example for IDNA, because IDNA never
  - encodes pure ASCII labels.)
  -} { description: "ASCII string that breaks the existing rules for host-name labels"
    , decoded: "-> $1.00 <-"
    , encoded: "-> $1.00 <--"
    }
  ]

testDomains :: Array TestCase
testDomains =
  [ { description: ""
    , decoded: "ma\xF1" <> "ana.com"
    , encoded: "xn--maana-pta.com"
    }
  , { -- https://github.com/mathiasbynens/punycode.js/issues/17
      description: ""
    , decoded: "example.com."
    , encoded: "example.com."
    }
  , { description: ""
    , decoded: "b\xFC" <> "cher.com"
    , encoded: "xn--bcher-kva.com"
    }
  , { description: ""
    , decoded: "caf\xE9.com"
    , encoded: "xn--caf-dma.com"
    }
  , { description: ""
    , decoded: "\x2603-\x2318.com"
    , encoded: "xn----dqo34k.com"
    }
  , { description: ""
    , decoded: "\xD400\x2603-\x2318.com"
    , encoded: "xn----dqo34kn65z.com"
    }
  , { description: "Emoji"
    , decoded: "\xD83D\xDCA9.la"
    , encoded: "xn--ls8h.la"
    }
  , { description: "Non-printable ASCII"
    , decoded: "\x0\x01\x02foo.bar"
    , encoded: "\x0\x01\x02foo.bar"
    }
  , { description: "Email address"
    , decoded: "\x0434\x0436\x0443\x043C\x043B\x0430@\x0434\x0436p\x0443\x043C\x043B\x0430\x0442\x0435\x0441\x0442.b\x0440\x0444" <> "a"
    , encoded: "\x0434\x0436\x0443\x043C\x043B\x0430@xn--p-8sbkgc5ag7bhce.xn--ba-lmcq"
    }
  , { -- https://github.com/mathiasbynens/punycode.js/pull/115
      description: ""
    , decoded: "foo\x7F.example"
    , encoded: "foo\x7F.example"
    }
  ,
    -- separators
    { description: "Using U+002E as separator"
    , decoded: "ma\xF1" <> "ana\x2E" <> "com"
    , encoded: "xn--maana-pta.com"
    }
  , { description: "Using U+3002 as separator"
    , decoded: "ma\xF1" <> "ana\x3002" <> "com"
    , encoded: "xn--maana-pta.com"
    }
  , { description: "Using U+FF0E as separator"
    , decoded: "ma\xF1" <> "ana\xFF0E" <> "com"
    , encoded: "xn--maana-pta.com"
    }
  , { description: "Using U+FF61 as separator"
    , decoded: "ma\xF1" <> "ana\xFF61" <> "com"
    , encoded: "xn--maana-pta.com"
    }
  ]

createTest :: TestCase -> Spec Unit
createTest { description, decoded, encoded } =
  it description do
    decode encoded `shouldEqual` (Right decoded)
    encode decoded `shouldEqual` (Right encoded)

createDomainTest :: TestCase -> Spec Unit
createDomainTest { description, decoded, encoded } =
  it description do
    toAscii decoded `shouldEqual` (Right encoded)
    (toAscii =<< toUnicode encoded) `shouldEqual` (Right encoded)

createIdentityTest :: TestCase -> Spec Unit
createIdentityTest { description, decoded, encoded } =
  it description do
    toAscii encoded `shouldEqual` (Right encoded)
    toUnicode decoded `shouldEqual` (Right decoded)
    toUnicode encoded `shouldEqual` (Right encoded)

main :: Effect Unit
main = launchAff_ $ runSpec [ consoleReporter ] do
  describe "happy path" do
    for_ testData createTest

  describe "errors" do
    it "catches not-basic" do
      decode "\x81-" `shouldEqual` (Left (NotBasic $ unsafePartial $ fromJust $ toEnum 0x81))
      decode "\x81" `shouldEqual` (Left (NotBasic $ unsafePartial $ fromJust $ toEnum 0x81))
      decode "ls8h=" `shouldEqual` (Left (NotBasic $ unsafePartial $ fromJust $ toEnum 0x3D))

  describe "domains" do
    for_ testDomains createDomainTest

  describe "identity" do
    for_ testData createIdentityTest

  describe "inverse" do
    it "decode(encode(input)) == input" $
      quickCheck \s -> (decode =<< encode s) === Right s

    it "decode(decode(input)) == decode(input)" $
      quickCheck \s -> (decode =<< decode s) === decode s
