module GoJS.Model.Transaction.Constructors where

import Effect (Effect)
import GoJS.Model.Types (Transaction_)
import GoJS.Unsafe (constructor0)

newTransaction :: Effect Transaction_
newTransaction = constructor0 "Transaction"