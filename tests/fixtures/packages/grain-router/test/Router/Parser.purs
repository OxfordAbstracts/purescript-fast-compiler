module Test.Router.Parser (testParser) where

import Prelude

import Control.Alt ((<|>))
import Data.Generic.Rep (class Generic)
import Data.Maybe (fromMaybe)
import Data.Show.Generic (genericShow)
import Grain.Router.Parser (end, int, lit, match, param)
import Test.Unit (TestSuite, test)
import Test.Unit.Assert as Assert

data Route
  = Home
  | User Int
  | Users String
  | NotFound

derive instance routeEq :: Eq Route
derive instance genericRoute :: Generic Route _
instance showRoute :: Show Route where
  show = genericShow

route :: String -> Route
route url = fromMaybe NotFound $ match url $
  Home <$ end
  <|>
  Users <$> (lit "users" *> param "name") <* end
  <|>
  User <$> (lit "users" *> int) <* end

testParser :: TestSuite
testParser = test "parser" do
  Assert.equal Home $ route ""
  Assert.equal Home $ route "/"
  Assert.equal (Users "oreshinya") $ route "/users?name=oreshinya"
  Assert.equal (User 42) $ route "/users/42"
  Assert.equal NotFound $ route "/projects"
