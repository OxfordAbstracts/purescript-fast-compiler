module Test.TrimMarginSpec where

import Test.Prelude

import Webb.String (trimMargin)


spec :: Spec Unit
spec = describe "Trim margin" do 
  it "without '|', nothing is recognized" do 
    let str = """apple wine
      banana
    """
    trimMargin str === ""
    
  it "with a '|', a line is recognized" do
    let str = """|apple wine
      banana
    """ 
    trimMargin str === "apple wine"
    
  it "multiple lines are recognized" do 
    let str = """
      | apple
      | wine
      |
    """
    trimMargin str === " apple\n wine\n"
    
  it "repeated '|' characters on the same line don't cause linebreak" do 
    let str = """
      |apple | banana
      |wine
    """
    trimMargin str === "apple | banana\nwine"
    



