module Webb.File where

import Prelude

import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Data.Tuple.Nested (type (/\))
import Node.Buffer (Buffer)
import Webb.Directory.Data.Absolute as Abs
import Webb.File.Data.File as File
import Webb.File.Internal.File as Prog
import Webb.Monad.Prelude (notM)
import Webb.State.Prelude (ShowRef, newShowRef)


newtype File = F 
  { file :: ShowRef File.File
  }
  
derive newtype instance Eq File
derive newtype instance Show File 
  
newFile :: forall m. MonadAff m => Abs.AbsPath -> m File
newFile path' = do
  empty <- File.emptyFile path' # liftEffect
  file <- newShowRef empty
  pure $ F { file: file }

eval :: forall m a. MonadAff m => File -> Prog.Prog a -> m a
eval (F s) prog = liftAff do Prog.eval s prog

path :: forall m. MonadAff m => File -> m Abs.AbsPath
path file = eval file Prog.path

position :: forall m. MonadAff m => File -> m Int
position file = eval file Prog.position

isOpen :: forall m. MonadAff m => File -> m Boolean
isOpen file = eval file Prog.isOpen

isClosed :: forall m. MonadAff m => File -> m Boolean
isClosed file = notM $ isOpen file

openTruncated :: forall m. MonadAff m => File -> m Unit
openTruncated file = eval file Prog.openTruncated

openAppending :: forall m. MonadAff m => File -> m Unit
openAppending file = eval file Prog.openAppending

open :: forall m. MonadAff m => File -> m Unit
open file = eval file Prog.open

close :: forall m. MonadAff m => File -> m Unit
close file = eval file Prog.close

size :: forall m. MonadAff m => File -> m Int
size file = eval file Prog.size

isEof :: forall m. MonadAff m => File -> m Boolean
isEof file = eval file Prog.isEof

truncate :: forall m. MonadAff m => File -> Int -> m Unit
truncate file i = eval file $ Prog.truncate i

seek :: forall m. MonadAff m => File -> Int -> m Unit
seek file i = eval file $ Prog.seek i

seekBy :: forall m. MonadAff m => File -> Int -> m Unit
seekBy file i = eval file $ Prog.seekBy i

writeBuffer :: forall m. MonadAff m => File -> Buffer -> m Unit
writeBuffer file i = eval file $ Prog.writeBuffer i

writeString :: forall m. MonadAff m => File -> String -> m Unit
writeString file i = eval file $ Prog.writeString i

peekBuffer :: forall m. MonadAff m => File -> Int -> m (Buffer /\ Int)
peekBuffer file n = eval file $ Prog.peekBuffer n

readBuffer :: forall m. MonadAff m => File -> Int -> m (Buffer /\ Int)
readBuffer file n = eval file $ Prog.readBuffer n

readString :: forall m. MonadAff m => File -> Int -> m String
readString file n = eval file $ Prog.readString n

readLine :: forall m. MonadAff m => File -> m String
readLine file = eval file Prog.readLine

readLineSepBy :: forall m. MonadAff m => File -> String -> m String
readLineSepBy file sep = eval file $ Prog.readLineSepBy sep

readAllText :: forall m. MonadAff m => File -> m String
readAllText file = eval file Prog.readAllText

writeAllText :: forall m. MonadAff m => File -> String -> m Unit
writeAllText file str = eval file $ Prog.writeAllText str