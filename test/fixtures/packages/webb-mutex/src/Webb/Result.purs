module Webb.Result 
( Result
, newResult
, error
, await
, return
, yield
) 
where

import Prelude

import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Effect.Exception (Error)
import Webb.Mutex.Internal.Result as Result


type Result = Result.Result

newResult ∷ ∀ (m ∷ Type -> Type) (a ∷ Type). MonadEffect m ⇒ m (Result a)
newResult = Result.newResult

error ∷ ∀ (m ∷ Type -> Type) (a ∷ Type). MonadEffect m ⇒ Result a → Error → m Unit
error = Result.error

await ∷ ∀ (m ∷ Type -> Type) (a ∷ Type). MonadAff m ⇒ Result a → m a
await = Result.await

return ∷ ∀ (m ∷ Type -> Type) (a ∷ Type). MonadEffect m ⇒ Result a → a → m Unit
return = Result.return

yield ∷ ∀ (m ∷ Type -> Type). MonadAff m ⇒ m Unit
yield = Result.yield