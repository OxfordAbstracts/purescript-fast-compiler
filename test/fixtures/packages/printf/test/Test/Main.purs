module Test.Main where

import Prelude

import Effect (Effect)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Text.Printf (printf)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Text.Printf" do
    describe "Basic formatting" do
      it "formats simple strings" do
        (printf (Proxy :: Proxy "Hello!")) `shouldEqual` "Hello!"

      it "formats integers with %d" do
        (printf (Proxy :: Proxy "Value: %d") 42) `shouldEqual` "Value: 42"
        (printf (Proxy :: Proxy "%d") (-123)) `shouldEqual` "-123"

      it "formats floats with %f" do
        (printf (Proxy :: Proxy "Pi: %f") 3.14159) `shouldEqual` "Pi: 3.14159"
        (printf (Proxy :: Proxy "%f") (-0.123)) `shouldEqual` "-0.123"

      it "formats strings with %s" do
        (printf (Proxy :: Proxy "Name: %s") "Alice") `shouldEqual` "Name: Alice"
        (printf (Proxy :: Proxy "%s") "") `shouldEqual` ""

    describe "Width specifications" do
      it "pads integers to specified width" do
        (printf (Proxy :: Proxy "%5d") 42) `shouldEqual` "   42"
        (printf (Proxy :: Proxy "%3d") 1234) `shouldEqual` "1234"

      it "pads floats to specified width" do
        (printf (Proxy :: Proxy "%8f") 3.14) `shouldEqual` "    3.14"
        (printf (Proxy :: Proxy "%6f") 12.345) `shouldEqual` "12.345"

      it "pads strings to specified width" do
        (printf (Proxy :: Proxy "%10s") "test") `shouldEqual` "      test"
        (printf (Proxy :: Proxy "%4s") "longer") `shouldEqual` "longer"

    describe "Alignment options" do
      it "left aligns with -" do
        (printf (Proxy :: Proxy "%-5d") 42) `shouldEqual` "42   "
        (printf (Proxy :: Proxy "%-8s") "test") `shouldEqual` "test    "
        (printf (Proxy :: Proxy "%-6f") 3.14) `shouldEqual` "3.14  "

    describe "Fill character options" do
      it "fills with specified character" do
        (printf (Proxy :: Proxy "%'_5d") 42) `shouldEqual` "___42"
        (printf (Proxy :: Proxy "%'#8s") "test") `shouldEqual` "####test"
        (printf (Proxy :: Proxy "%05d") 42) `shouldEqual` "00042"

    describe "Sign options" do
      it "handles + flag for positive numbers" do
        (printf (Proxy :: Proxy "%+d") 42) `shouldEqual` "+42"
        (printf (Proxy :: Proxy "%+f") 3.14) `shouldEqual` "+3.14"
        (printf (Proxy :: Proxy "%+d") (-42)) `shouldEqual` "-42"

    describe "Decimal precision" do
      it "handles decimal precision for floats" do
        (printf (Proxy :: Proxy "%.2f") 3.14159) `shouldEqual` "3.14"
        (printf (Proxy :: Proxy "%.3f") 1.23) `shouldEqual` "1.230"
        (printf (Proxy :: Proxy "%8.2f") 3.14159) `shouldEqual` "    3.14"

    describe "Complex combinations" do
      it "handles multiple format specifiers" do
        (printf (Proxy :: Proxy "Name: %s, Age: %d") "Bob" 25) `shouldEqual` "Name: Bob, Age: 25"
        (printf (Proxy :: Proxy "%s: %+.2f") "Value" 3.14159) `shouldEqual` "Value: +3.14"

      it "handles escaped percent signs" do
        (printf (Proxy :: Proxy "100%% complete")) `shouldEqual` "100% complete"
        (printf (Proxy :: Proxy "%%d not a format")) `shouldEqual` "%d not a format"

      it "handles complex padding and precision" do
        (printf (Proxy :: Proxy "%+'_10.2f") 3.14159) `shouldEqual` "_____+3.14"
        (printf (Proxy :: Proxy "%-'#10s") "test") `shouldEqual` "test######"
        (printf (Proxy :: Proxy "%08.2f") 3.14159) `shouldEqual` "00003.14"

