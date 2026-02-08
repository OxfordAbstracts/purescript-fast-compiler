module GoJS.Model.Binding.Constructors where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import GoJS.Model.Binding.Methods (makeTwoWay_)
import GoJS.Model.Types (Binding_)
import GoJS.Unsafe (constructor2, constructor3)


newBinding :: forall from to. String -> String -> Maybe (from -> to) -> Maybe (to -> from) -> Effect Binding_
newBinding tgt src go back = case go, back of
    Nothing , Nothing -> constructor2 "Binding" tgt src
    Just go', Nothing -> constructor3 "Binding" tgt src go'
    Nothing , (Just back') -> constructor2 "Binding" tgt src >>= makeTwoWay_  back'
    Just go', (Just back') -> constructor3 "Binding" tgt src go' >>= makeTwoWay_ back'