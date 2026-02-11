module Webb.Directory.Action where

import Prelude

import Effect.Aff.Class (class MonadAff, liftAff)
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Internal.Action as Prog

{- Interesting actions and queries to run within the directory. -}

newtype Action = A {}
  
newAction :: forall m. MonadAff m => m Action
newAction = pure $ A { }

eval :: forall m a. MonadAff m => Action -> Prog.Prog a -> m a
eval _action prog = liftAff $ Prog.eval { } prog

-- Remove the directory (verifying that it is a directory) specified by
-- the absolute path. This does not rely on the internal absolute
-- path known by the Action itself.
removeDir :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Unit
removeDir action path = eval action $ Prog.removeDir path

resetDir :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Unit
resetDir action path = eval action $ Prog.resetDir path

-- Ensure the directory exists, and create it if it doesn't.
ensureDir :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Unit
ensureDir action path = eval action $ Prog.ensureDir path

removeDirChildren :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Unit
removeDirChildren action path = eval action $ Prog.removeDirChildren path

forceRemove :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Boolean
forceRemove action path = eval action $ Prog.forceRemove path

makeDir :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Unit
makeDir action path = eval action $ Prog.makeDir path

mkDir :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Unit
mkDir action path = eval action $ Prog.mkDir path

exists :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Boolean
exists action path = eval action $ Prog.exists path
  
-- Does the directory exist at the absolute path?
existsDir :: forall m. MonadAff m => Action -> Abs.AbsPath -> m Boolean
existsDir action path = eval action $ Prog.existsDir path