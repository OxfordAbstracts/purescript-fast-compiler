module Threading.Barrier (Barrier, barrier, wait) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (sequence_)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Type.Function (type ($))

-- | A barrier enables multiple threads to synchronize the beginning of some computation.
data Barrier = Barrier Int (Ref $ Array $ Effect Unit)

-- | Create a new barrier that will only unblock waiting threads
-- | when `n` threads are waiting (including this one)
barrier :: Int -> Effect Barrier
barrier n = Barrier n <$> Ref.new []

-- | Wait until the provided number of threads
-- | are also `wait`ing
wait :: Barrier -> Aff Unit
wait (Barrier n wakersRef) = do
  wakers <- liftEffect $ Ref.read wakersRef
  if n <= 1 then
    pure unit
  else if Array.length wakers == (n - 1) then
    liftEffect $ sequence_ wakers
  else Aff.makeAff \cb -> do
    Ref.modify_ (_ <> [ cb $ Right unit ]) wakersRef
    pure $ Aff.nonCanceler
