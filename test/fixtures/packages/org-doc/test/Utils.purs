module Test.Utils where

import Prelude

import Effect.Exception (Error)
import Effect.Class (class MonadEffect)

import Control.Monad.Error.Class (class MonadThrow)

import Data.FoldableWithIndex (foldlWithIndex, class FoldableWithIndex)
import Data.Text.Diff (compareBy, Comparator(..), Limit(..)) as Diff

import Test.Spec (SpecT, it, class Example)

-- Monad m ⇒ Example t arg g ⇒ String → t → SpecT g arg m Unit

--helper :: forall a t. { title :: Int -> a -> String, spec :: a -> t } -> Array a -> Spec Unit
helper
    :: forall
        (f ∷ Type -> Type)
        (idx ∷ Type)
        (a ∷ Type)
        (m ∷ Type -> Type)
        (t ∷ Type)
        (arg ∷ Type)
        (g ∷ Type -> Type)
     . FoldableWithIndex idx f
    => Apply m
    => Monad m
    => Example t arg g
    => { title :: idx -> a -> String
       , spec :: a -> t
       }
    -> f a
    -> SpecT g arg m Unit
helper { title, spec } =
    foldlWithIndex
        (\idx prev a -> do
            prev
            *>
            (it (title idx a) $
                spec a
            )
        )
        (pure unit)


shouldEqual :: forall m. MonadEffect m ⇒ MonadThrow Error m ⇒ String -> String -> m Unit
shouldEqual = Diff.compareBy (Diff.OnlyDifferent $ Diff.Limit 20)